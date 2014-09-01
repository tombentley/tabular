import ceylon.language.meta {
    type,
    modules
}
import ceylon.language.meta.model {
    Model,
    ClassModel,
    Type,
    Class,
    Function,
    Value,
    Applicable,
    Generic,
    ClassOrInterface,
    UnionType,
    IntersectionType,
    nothingType
}
import ceylon.language.meta.declaration {
    Declaration,
    ClassOrInterfaceDeclaration,
    ClassDeclaration,
    InterfaceDeclaration,
    ValueDeclaration,
    TypeParameter,
    Module,
    Package,
    NestableDeclaration,
    FunctionDeclaration,
    GenericDeclaration
}
import ceylon.language.serialization {
    Deconstructor,
    Deconstructed,
    SerializationContext,
    Reference,
    DeserializableReference,
    SerializableReference,
    RealizableReference,
    DeserializationContext,
    deserialization,
    serialization
}
import ceylon.collection {
    ArrayList,
    HashMap,
    HashSet,
    IdentityMap,
    StringBuilder,
    MutableMap,
    Queue,
    LinkedList
}

"Every instance will be identified by a unique String, but let's use an 
 alias for clarity."
alias Id => String;

"Generates ids from the characters in the given alphabet.
 Yields all 1 character ids then all 2 character ids etc."
// We could just use Integers of course, but there's a 
// space saving to be had working in base 62 instead of base 10
class IdGenerator(String alphabet = "0123456789" +
            "ABCDEFGHIJKLMNOPQRSTUVWXYZ" +
            "abcdefghijklmnopqrstuvwxyz") {
    "The characters in the alphabet must not be repeated"
    assert (HashSet { elements = alphabet; }.size == alphabet.size);
    
    value digits = ArrayList<Character>();
    variable value index = alphabet.size;
    
    Character? increment(Character digit) {
        if (exists index = alphabet.firstOccurrence(digit),
            exists next = alphabet[index + 1]) {
            return next;
        }
        return null;
    }
    "Yields the next id."
    shared String next() {
        if (exists digit = alphabet[++index]) {
            digits.set(0, digit);
        } else {
            index = 0;
            assert (exists zero = alphabet[index]);
            variable value ii = 0;
            for (digit in digits) {
                if (exists nd = increment(digit)) {
                    digits.set(ii, nd);
                    break;
                }
                digits.set(ii, zero);
                ii++;
            } else {
                digits.insert(0, zero);
            }
        }
        
        return "".join(digits.reversed);
    }
}

"""Allocates ids (from an [[IdGenerator]]) to instances, such that "the same"
   instance will get the same id. 
   
   The meaning of "the same" depends on the type of the instance.
   """
class IdAllocator() {
    "Mapping of entity to id"
    IdentityMap<Identifiable,Id> ids = IdentityMap<Identifiable,Id>();
    
    "Mapping of value to id"
    HashMap<Object,Id> valueIds = HashMap<Object,Id>();
    
    "The id of null, if it's been allocated, otherwise null"
    variable Id? nullId = null;
    
    "The id generator"
    IdGenerator generator = IdGenerator();
    
    "Obtain an id for the given instance, allocating an id if necessary."
    shared Id allocateId(Object? instance) {
        switch (instance)
        case (is Null) {
            if (exists nid = nullId) {
                return nid;
            } else {
                Id nid = generator.next();
                //print("allocate ``nid`` to null");
                nullId = nid;
                return nid;
            }
        }
        case (is Object) {
            if (is Identifiable instance,
                !(instance is Model || instance is Declaration)) { // treat classes from c.l.m.model as values
                if (exists id = ids[instance]) {
                    return id;
                } else {
                    Id id = generator.next();
                    //print("allocate ``id`` to ``instance`` (``type(instance)``)");
                    ids.put(instance, id);
                    return id;
                }
            } else {
                if (exists id = valueIds[instance]) {
                    return id;
                } else {
                    Id id = generator.next();
                    //print("allocate ``id`` to ``instance`` (``type(instance)``)");
                    valueIds.put(instance, id);
                    return id;
                }
            }
        }
    }
    
    "Whether the given instance has had an id allocated."
    shared Boolean idAllocated(Object? instance) {
        switch (instance)
        case (is Null) {
            return nullId exists;
        }
        case (is Object) {
            if (is Identifiable instance,
                !(instance is Model || instance is Declaration)) { // treat classes from c.l.m.model as values
                return instance in ids.keys;
            } else {
                return instance in valueIds.keys;
            }
        }
    }
}

"Representation of a union type within a [[ValueTable]]"
class Union(shared Id[] cases) extends Object() {
    shared actual Boolean equals(Object other) {
        if (is Union other) {
            // FIXME we don't want separate entries for X&Y versus Y&X, so we need a canonical order
            return cases == other.cases;
        } else {
            return false;
        }
    }
    shared actual Integer hash => cases.hash;
}
"Representation of an intersection type within a [[ValueTable]]"
class Intersection(shared Id[] satisfyeds) extends Object() {
    shared actual Boolean equals(Object other) {
        if (is Intersection other) {
            // FIXME we don't want separate entries for X&Y versus Y&X, so we need a canonical order
            return satisfyeds == other.satisfyeds;
        } else {
            return false;
        }
    }
    shared actual Integer hash => satisfyeds.hash;
}
"Representation of a member access within a [[ValueTable]]"
class Member(shared Id pck, shared [Id+] members) extends Object() {
    shared actual Boolean equals(Object other) {
        if (is Member other) {
            return pck == other.pck && members == other.members;
        } else {
            return false;
        }
    }
    shared actual Integer hash => pck.hash + members.hash;
}
"Representation of a type application within a [[ValueTable]]."
class TypeApplication(shared Id generic, shared [Id*] typeArguments) extends Object() {
    shared actual Boolean equals(Object other) {
        if (is TypeApplication other) {
            return generic == other.generic && typeArguments == other.typeArguments;
        } else {
            return false;
        }
    }
    shared actual Integer hash => generic.hash + typeArguments.hash;
}
"Representation of a function application or class instantiation 
 within a [[ValueTable]]."
class Application(shared Id ctor, shared Id[] arguments) extends Object() {
    shared actual Boolean equals(Object other) {
        if (is Application other) {
            return ctor == other.ctor && arguments == other.arguments;
        } else {
            return false;
        }
    }
    shared actual Integer hash => ctor.hash + arguments.hash;
}

"The language module scalar value types"
alias ValueType => String|Character|Integer|Float|Byte;

ValueDeclaration? getObjectValueDeclaration(Anything o) {
    if (exists o) {
        if (o == true) {
            return `value true`;
        } else if (o == false) {
            return `value false`;
        } else {
            return type(o).declaration.objectValue;
        }
    } else {
        return `value null`;
    }
}

Boolean isObjectDeclaration(Anything o) {
    return getObjectValueDeclaration(o) exists;
}

"""Determines whether this is something we can add to the [[ValueTable]], 
   rather than treating as an entity and putting in a [[Table]](s).
 
   Such values include:
 
   * The language module classes which do not satisfy 
     `Identifiable` (true "value types", including `Sequence`).
   * Values that are `object` declarations (include null, true and false).
   * The Models and Declarations required to construct other values. 
     For example to construct the entry `1->2` 
     we need not only the values `1` and `2`, but also the
     [[Class]] `Entry<Integer,Integer>` which in turn 
     requires the [[Class] `Integer,
     the [[ClassDeclaration]]s for `Integer` and `Entry` and 
     the [[Package]] `ceylon.language`.
   """
Boolean isValue(Anything instance) {
    if (instance is ValueType|Entry<Object,Object>|Sequential<Anything>|Null) {
        return true;
    }
    if (isObjectDeclaration(instance)) {
        return true;
    }
    return false;
}

"Holds values, as defined by [[isValue]]."
class ValueTable(IdAllocator allocator, Reference<Object?> enlist(Anything instance)) {
    "All the things which we store in [[data]]."
    shared alias Puttable => ValueType|Reference<Object?>|Package|Member|TypeApplication|Application|Union|Intersection|ClassDeclaration|ValueDeclaration;
    
    HashMap<Id,Puttable> data = HashMap<Id,Puttable>();
    
    Id alloPut(Puttable cls) {
        value clsId = allocator.allocateId(cls);
        data.put(clsId, cls);
        return clsId;
    }
    Id putOrEnlist(Anything o) {
        if (!isValue(o)) {
            assert (is Id id = enlist(o).id);
            return id;
        } else {
            assert (is Puttable item = o);
            return alloPut(item);
        }
    }
    Id package_(Package p) {
        return alloPut(p);
    }
    Id valueDeclaration(ValueDeclaration vd) {
        if (is Package p = vd.container) {
            return alloPut(Member(package_(p), [vd.name]));
        }
        return nothing; // TODO attributes
    }
    Id classOrInterfaceDeclaration(ClassOrInterfaceDeclaration cd) {
        if (is Package p = cd.container) {
            return alloPut(Member(package_(p), [cd.name]));
        }
        return nothing; // TODO member classes
    }
    Id functionDeclaration(FunctionDeclaration cd) {
        if (is Package p = cd.container) {
            return alloPut(Member(package_(p), [cd.name]));
        }
        return nothing; // TODO methods 
    }
    Id type_(Type ta) {
        if (is ClassOrInterface ta) {
            return classOrInterface(ta);
        } else if (is UnionType ta) {
            return alloPut(Union(ta.caseTypes.collect(type_)));
        } else if (is IntersectionType ta) {
            return alloPut(Intersection(ta.satisfiedTypes.collect(type_)));
        } else if (ta == nothingType) {
            return nothing; //TODO
        }
        assert (false); // should be impossible
    }
    Id[] typeArguments(Generic g) {
        return g.typeArguments.values.collect(type_);
    }
    Id classOrInterface(ClassOrInterface c) {
        if (c.typeArguments.empty) {
            // for non-generic classes let's just record the declaration
            return classOrInterfaceDeclaration(c.declaration);
        } else {
            return alloPut(TypeApplication(classOrInterfaceDeclaration(c.declaration), typeArguments(c)));
        }
    }
    Id func(Function c) {
        if (c.typeArguments.empty) {
            // for non-generic functions let's just record the declaration
            return functionDeclaration(c.declaration);
        } else {
            return alloPut(TypeApplication(functionDeclaration(c.declaration), typeArguments(c)));
        }
    }
    
    Id application(Class|Function applicable, Anything[] arguments) {
        Id a;
        if (is Class applicable) {
            a = classOrInterface(applicable);
        } else if (is Function applicable) {
            a = func(applicable);
        } else {
            assert (false);
        }
        return alloPut(Application(a, arguments.collect(putOrEnlist)));
    }
    
    "Adds the given [[value|val]] to this table."
    shared Id add(Anything val) {
        assert (isValue(val));
        
        if (is ValueType val) {
            value valId = allocator.allocateId(val);
            data.put(valId, val);
            return valId;
        } else if (is Entry<Object,Object> val) {
            assert (is Class cls = type(val));
            return application(cls, [val.key, val.item]);
        } else if (is Sequence<Anything> val) {
            if (is Singleton<Anything> val) {
                assert (is Class cls = type(val));
                return application(cls, [val.first]);
            } else if (is ArraySequence<Anything> val) {
                value fn = `function sequence`.apply<Anything,Nothing>(type(val).typeArguments.values.first else `Object`);
                return application(fn, val);
            } else if (is Range<Anything> val) {
                value name = type(val).declaration.name;
                Function fn;
                Anything[] args;
                if (name == "Span") {
                    fn = `function span`.apply(type(val).typeArguments.values.first else `Object`);
                    args = [val.first, val.last];
                } else if (name == "Measure") {
                    fn = `function measure`.apply(type(val).typeArguments.values.first else `Object`);
                    args = [val.first, val.size];
                } else {
                    throw;
                }
                return application(fn, args);
            } else if (is Tuple<Anything,Anything,Anything[]> val) {
                assert (is Class cls = type(val));
                return application(cls, [val.first, val.rest]);
            } else {
                "unexpected sequence type"
                assert (false);
            }
        } else {
            if (exists vd = getObjectValueDeclaration(val)) {
                return valueDeclaration(vd);
            } else {
                assert (false);
            }
        }
    }
    
    shared Puttable get(Id id) {
        assert (exists val = data[id]);
        return val;
    }
    
    shared Map<Id,Puttable> rows => data;
}

"""A unit type used to know that a value has been set in a `Table.Row`  
   (we can't use null, because that's a valid "value" which could be set).
   """
object unset {
    shared actual String string => "?";
}

"A table made up of rows. 
 Each table holds attribute values of the given [[classModel]] 
 for a number of [[Id]]-identified instances."
class Table(classModel, superModel, cols) {
    shared Id classModel;
    "The class whose state this table serializes"
    shared Id classDeclaration => classModel.declaration;
    
    "The superclass of the classDeclaration at the time the data was serialized*."
    shared Id? superModel;
    
    "The superclass of the classDeclaration at the time the data was serialized*."
    shared Id? superDeclaration => superModel?.declaration;
    
    shared List<TypeParameter> typeParameters => classDeclaration.typeParameterDeclarations;
    
    // TODO abstract?
    
    "The mapping of column index to attribute."
    List<ValueDeclaration> cols;
    
    "The mapping of attribute to column index."
    MutableMap<ValueDeclaration,Integer> schema = HashMap<ValueDeclaration,Integer>();
    variable value ii = 0;
    for (vd in cols) {
        schema.put(vd, ii);
        ii++;
    }
    
    "The columns in this table."
    shared List<ValueDeclaration> columns = cols;
    
    HashMap<Id,Row> data = HashMap<Id,Row>();
    shared Map<Id,Row> rows => data;
    
    "A row within a table"
    shared class Row() {
        // not that values is initialized to all unset
        // and that it's impossible for clients to see an unset value
        
        "The Table this Row is (or will be) a row of."
        shared Table table => outer;
        
        ArrayList<Object> typeArguments_ = ArrayList<Object>();
        for (tp in typeParameters) {
            typeArguments_.add(unset);
        }
        
        ArrayList<Object?> values = ArrayList<Object?>();
        for (vd in schema.keys) {
            values.add(unset);
        }
        
        Integer tpIndex(TypeParameter tp) {
            variable value index = 0;
            for (tpx in typeParameters) {
                if (tpx == tp) {
                    return index;
                }
                index++;
            }
            throw Exception("type parameter not found: ``tp`` in ``classDeclaration``");
        }
        
        shared void setTypeArgument(TypeParameter tp, String className) {
            variable value index = tpIndex(tp);
            typeArguments_.set(index, className);
        }
        
        shared String getTypeArgument(TypeParameter tp) {
            variable value index = tpIndex(tp);
            assert (exists ta = typeArguments_[index]);
            assert (ta != unset);
            assert (is String ta);
            return ta;
        }
        
        shared void setValue(ValueDeclaration vd, Id datum) {
            assert (exists index = schema[vd]);
            // TODO check that the type of val is a subtype of the type of vd
            values.set(index, datum);
        }
        shared Object? getValue(ValueDeclaration vd) {
            if (exists index = schema[vd],
                0 <= index < values.size) {
                Object? datum = values[index];
                if (exists datum,
                    datum == unset) {
                    throw Exception("value not yet set: ``vd``");
                }
                return datum;
            } else {
                throw Exception("value declaration not in table schema: ``vd``");
            }
        }
        
        "null if the row has values for every column, otherwise 
         the first value declaration for which there is a missing value."
        shared TypeParameter|ValueDeclaration? complete {
            variable value i = 0;
            for (tp in typeParameters) {
                if (exists ta = typeArguments_[i],
                    ta == unset) {
                    return tp;
                }
                i++;
            }
            i = 0;
            for (datum in values) {
                if (exists datum,
                    datum == unset) {
                    return columns[i];
                }
                i++;
            }
            return null;
        }
        shared {String*} typeArguments {
            return typeArguments_.map(function(Object o) {
                    assert (is String o);
                    return o;
                });
        }
        
        "The data in this row, in the same order as [[outer.columns"
        shared {Object?*} data => values;
    }
    
    "Adds a row for the instance with the given id to the table."
    shared void addRow(Id id, Row row) {
        if (exists problemVd = row.complete) {
            throw Exception("incomplete row, missing value for ``problemVd``");
        }
        data.put(id, row);
    }
    
    "The row for the instances with the given id"
    shared Row? get(Id id) => data[id];
    
    shared actual String string => "Table(``classDeclaration``, `` superDeclaration else "null" ``, ``columns``)";
}

"Quotes the characters in the given string. Does not enclose in double quotes."
String quoteString(String string) {
    StringBuilder sb = StringBuilder();
    for (char in string) {
        sb.append(quoteCharacter(char));
    }
    return sb.string;
}

"Quotes the given character. Does not enclose in single quotes."
String quoteCharacter(Character char) {
    switch (char)
    case ('\\', '"', '\'', ',', '\n', '\r') {
        return "\\{#``formatInteger(char.integer, 16)``}"; // ceylon syntax
    }
    else {
        return char.string;
    }
}

"Unquotes the characters in the given string, which should not be be enclosed 
 in double quotes."
String unquoteString(String string) {
    StringBuilder sb = StringBuilder();
    value iter = string.iterator();
    variable value ii = -1;
    while (true) {
        value char = iter.next();
        ii++;
        switch (char)
        case (is Finished) {
            break;
        }
        case ('\\') {
            if ('{' != iter.next()) {
                throw Exception("expecting { following \\ ");
            }
            ii++;
            if ('#' != iter.next()) {
                throw Exception("expecting # following \\{ ");
            }
            ii++;
            value start = ii + 1;
            while (true) {
                if (is Character hexDigit = iter.next()) {
                    ii++;
                    if (hexDigit == '}') {
                        if (exists unquoted = unquoteCharacter(string, start, ii - start)) {
                            sb.appendCharacter(unquoted);
                            break;
                        } else {
                            throw Exception("invalid quoted character ``string[start:ii]``");
                        }
                    } else if (!('0' <= hexDigit <= '9' || 'a' <= hexDigit <= 'f')) {
                        // TODO report IDE problem with brace matching here
                        throw Exception("expecting only hexadecimal digits following \\{#");
                    }
                } else {
                    throw Exception("unterminated quoted character");
                }
            }
        }
        case ('"', '\'', ',', '\n', '\r') {
            throw Exception("unquoted quotable character in quoted string: \"``string``\"");
        }
        else {
            assert (is Character char);
            sb.appendCharacter(char);
        }
    }
    return sb.string;
}

Character? unquoteCharacter(String hex, Integer start = 0, Integer end = hex.size) {
    Integer? codepoint = parseInteger(hex[start:end], 16);
    return codepoint?.character;
}

"Formats a datum"
String formatDatum<Type>(Type|Reference<Type> v) {
    if (is Reference<Type> v) {
        // TODO do we use @ or do we infer it's a reference from the metamodel
        // (or from the header: id,@person.id)?
        assert (false);
        //return v.id.string;
    } else {
        if (is Id v) {
            
            return v; //"\"``quoteString(v)``\"";
        } /*else if (is Integer v) {
            return "``v``";
          } else if (is Byte v) {
            return "b``v``";
          } else if (is Null v) {
            return "null";
          } else if (is Boolean v) {
            return v.string;
          } else if (is Character v) {
            return "'``quoteCharacter(v)``'";
          } else if (is Float v) {
            return v.string;
          } else if (is Empty v) { // XXX really?
            return "empty";
          } */ else {
            /*value valueType = type(v);
            if (valueType.declaration.anonymous
                        && valueType.declaration.toplevel) {
                return valueType.declaration.qualifiedName;
            } else {*/
            throw Exception("unsupported datum type ``type(v)``");
            //}
        }
    }
}

"The top level object declaration corresponding to the 
 given fully qualified name."
throws (`class Exception`, "An object with this name could not be found")
Object? findObject(String fqName) {
    if (exists model = classDeclarationFromName(fqName),
        exists obj = model.objectValue) {
        return obj.get() of Object?;
    }
    throw Exception("not an object: ``fqName``");
}

"Parses a datum."
Object? parseDatum(String datum, ValueDeclaration vd) {
    if (exists first = datum.first) {
        if (first.letter) {
            if (datum == "true") {
                return true;
            } else if (datum == "false") {
                return false;
            } else if (datum == "null") {
                return null;
            } else if (datum == "empty") {
                return [];
            } else {
                // FQ object declaration
                return findObject(datum);
            }
        } else if (first.digit) {
            // starts with number => Integer, Byte or Float
            if (datum.contains('.') || datum.contains('E')) {
                value float = parseFloat(datum);
                if (exists float) {
                    return float;
                }
                throw Exception("invalid float: `datum`");
            } else {
                // TODO byte
                value i = parseInteger(datum);
                if (i exists) {
                    return i;
                }
                throw Exception("invalid float: `datum`");
            }
        } else if (first == '"') {
            if (!datum.endsWith("\"")) {
                throw Exception("unterminated string");
            }
            // starts with " => String
            return unquoteString(datum[1 : datum.size - 2]);
        } else if (first == '\'') {
            // starts with ' => character
            if (!datum.endsWith("\'")) {
                throw Exception("unterminated character: ``datum``");
            } else if (datum.size < 3) {
                throw Exception("invalid character: ``datum``");
            } else {
                String s = unquoteString(datum[1 : datum.size - 2]);
                if (s.size != 1) {
                    throw Exception("multiple characters: ``datum``");
                }
                return s;
            }
        } else {
            // TODO starts with [ => sequence ???
            // TODO starts with @ => key
            throw Exception("unhandled datum: ``datum``");
        }
    } else {
        //empty => null
        return null;
    }
}

class TableWriter(StringBuilder output) {
    shared void write(Table table) {
        writeHeader(table);
        for (id->row in table.rows) {
            writeRow(id, row);
        }
    }
    void writeHeader(Table table) {
        // TODO abstractness?
        output.append("# ``table.classModel``");
        if (exists sc = table.superModel) {
            output.append(" extends ``sc``");
        }
        output.appendNewline();
        output.append("# =id");
        for (tp in table.typeParameters) {
            output.appendCharacter(',').append("<``tp.name``>");
        }
        for (vd in table.columns) {
            output.appendCharacter(',').append(vd.name);
        }
        output.appendNewline();
    }
    void writeRow(Id id, Table.Row row) {
        output.append(id.string);
        for (String ta in row.typeArguments) {
            output.appendCharacter(',');
            output.append(ta);
        }
        for (Object? datum in row.data) {
            output.appendCharacter(',');
            output.append(formatDatum(datum));
        }
        output.appendNewline();
    }
}


"Provides a facility for serializing instances to a `String`."
shared class TabularSerializer() {
    
    SerializationContext context = serialization();
    MutableMap<ClassModel,Table> tables = HashMap<ClassModel,Table>();
    value allocator = IdAllocator();
    
    Boolean isSerializable(Object? thing) {
        if (is Identifiable thing) {
            // TODO and is annotated serializable
            return true;
        } else {
            return isValue(thing);
        }
    }
    
    "Queue of instances waiting to be serialized"
    Queue<SerializableReference<Object?>> instances = LinkedList<SerializableReference<Object?>>();
    
    value anotherFuckingMap = HashMap<Id,SerializableReference<Object?>>();
    
    "Adds the given [[instance]] to [[instances]] 
             if it's not been added yet, returns its id."
    SerializableReference<Object?> enlist(Anything instance) {
        assert (is Object? instance);
        Boolean x = !allocator.idAllocated(instance);
        Id id = allocator.allocateId(instance);
        if (x) {
            value reference = context.reference(id, instance);
            instances.offer(reference);
            anotherFuckingMap.put(id, reference);
            return reference;
        }
        assert (exists r = anotherFuckingMap[id]);
        return r;
    }
    
    ValueTable valueTable = ValueTable(allocator, enlist);
    
    class TabularDeconstructor() satisfies Deconstructor {
        variable Id id = "";
        shared variable ClassModel? classModel = null;
        shared variable ClassModel? currentClass = null;
        variable value typeParameters = ArrayList<[TypeParameter, String]>();
        variable value values = ArrayList<[ValueDeclaration, Id]>();
        
        "Called when we start inspecting an instance"
        shared void beginInstance(Id id, Object? instance) {
            "deconstructor should not see values"
            assert (!isValue(instance));
            ClassModel classModel = type(instance);
            this.id = id;
            this.classModel = classModel;
        }
        
        shared void beginClass(ClassModel cd) {
            if (exists cc = currentClass,
                cd != cc) {
                finishRow();
            }
            currentClass = cd;
        }
        "Called when we finish inspecting an instance"
        shared void endInstance() {
            // Here I can check that all the rows in all the tables have been populated
            finishRow();
        }
        
        shared actual void putValue<Type>(ValueDeclaration attribute, Type referenced) {
            Object? ref = referenced of Object?;
            if (isValue(ref)) {
                values.add([attribute, valueTable.add(ref)]);
            } else {
                /* TODO in general other serialization libraries would 
                        use annotations to know which references 
                        they follow */
                
                // need an id, so we can put that
                assert (is Id id = enlist(ref).id);
                values.add([attribute, id]);
            }
        }
        
        shared actual void putTypeArgument(TypeParameter typeParameter, Type argument) {
            typeParameters.add([typeParameter, argument.string]);
        }
        "Gets the table for the given class, creating it if necessary. 
         Note this can only be called after all the values have been added
         otherwise we don't know the schema of the table."
        Table getOrCreateTable(ClassModel cc) {
            Table table;
            if (exists t = tables[cc]) {
                table = t;
            } else {
                table = Table(cc, cc.extendedType,
                    { for (tup in values) tup[0] }.sequence());
                tables.put(cc, table);
            }
            return table;
        }
        
        "Populates and adds a [[row]] to the table for the [[currentClass]], 
         clears the [[values]] and [[typeParameters]], and nullifies [[currentClass]]."
        void finishRow() {
            if (!currentClass exists) {
                return;
            }
            assert (exists cc = currentClass);
            Table table = getOrCreateTable(cc);
            value row = table.Row();
            for (tpName in typeParameters) {
                try {
                    row.setTypeArgument(tpName[0], tpName[1]);
                } catch (Throwable e) {
                    throw Exception("Problem setting type argument for type parameter ``tpName[0]`` in table ``table`` for class ``cc``, id=``id``", e);
                }
            }
            for (tup in values) {
                try {
                    row.setValue(tup[0], tup[1]);
                } catch (Throwable e) {
                    throw Exception("Problem setting value for attribute ``tup[0]`` in table ``table`` for class ``cc``, id=``id``", e);
                }
            }
            table.addRow(id, row);
            typeParameters.clear();
            values.clear();
            currentClass = null;
        }
    }
    value dtor = TabularDeconstructor();
    Deconstructor(ClassModel) dtorFactory = function(ClassModel cd) {
        dtor.beginClass(cd);
        return dtor;
    };
    
    "Register the given instance, and every instance reachable from it, 
     for serialization."
    shared void add(Object instance) {
        enlist(instance);
        while (exists ref = instances.accept()) {
            assert (is Id id = ref.id);
            Object? inst = ref.instance();
            try {
                // and add the instance to the context
                if (isValue(inst)) {
                    valueTable.add(inst);
                } else if (isSerializable(inst)) {
                    value reference = ref; //context.reference(id, inst);
                    dtor.beginInstance(id, inst);
                    reference.serialize(dtorFactory);
                    dtor.endInstance();
                } else {
                    throw Exception("instance `` inst else "null" `` with id ``id`` is not serializable");
                }
            } catch (Exception e) {
                throw Exception("problem while serializing `` inst else "null" `` with id ``id``", e);
            }
        }
    }
    
    "Serialize all the [[registered|add]] instances to the given StringBuilder."
    shared String write() {
        StringBuilder builder = StringBuilder();
        
        ValueTableWriter ctw = ValueTableWriter(builder);
        ctw.write(valueTable);
        
        TableWriter writer = TableWriter(builder);
        for (table in tables.values) {
            writer.write(table);
        }
        return builder.string;
    }
}


"Treat an `Iterator<Character>` as something which can read (and count) lines)."
class LineReader(Character|Finished read()) {
    variable Boolean eof = false;
    
    variable Character|Finished cnext = finished;
    
    StringBuilder line = StringBuilder();
    
    "The line number of the last line returned by [[readLine]]."
    variable value lino = 0;
    
    "The line number of the last line returned by [[readLine]]."
    shared Integer lineNumber => lino;
    
    variable String? lnext = null;
    variable String? llast = null;
    
    "Returns the next line, or null if the stream has finished."
    shared String? readLine() {
        // XXX report def assignment issue here. no need for variable and null assignment,
        // but use of switch within while too difficult for deff assignmentment analysis
        variable String? result = null;
        if (eof) {
            result = null;
        } else if (exists ln = lnext) {
            result = ln;
            lnext = null;
        } else {
            if (is Character cr = cnext) {
                cnext = finished;
                line.appendCharacter(cr);
            }
            while (true) {
                value r = read();
                switch (r)
                case (finished) {
                    eof = true;
                    result = line.string;
                    break;
                }
                case ('\n') {
                    result = eol('\r');
                    break;
                }
                case ('\r') {
                    result = eol('\n');
                    break;
                }
                else {
                    assert (is Character r);
                    line.appendCharacter(r);
                }
            }
        }
        llast = result;
        return result;
    }
    
    shared void unread() {
        assert (llast exists);
        lnext = llast;
        llast = null;
    }
    
    String eol(Character allowed) {
        cnext = read();
        if (is Character cr = cnext) {
            if (cr == allowed) {
                cnext = finished;
            }
        }
        value result = line.string;
        line.reset();
        lino++;
        return result;
    }
}

ClassDeclaration? classDeclarationFromName(String fqClassname) {
    if (exists pkgIndex = fqClassname.firstInclusion("::")) {
        String pkgName = fqClassname[0 .. pkgIndex - 1];
        for (mod in modules.list) {
            if (pkgName.startsWith(mod.name)) {
                if (exists pkg = mod.findPackage(pkgName)) {
                    String className = fqClassname[pkgIndex + 2 ...];
                    if ('.' in className) {
                        throw Exception("member types not supported yet");
                    }
                    value classOrInterface = pkg.getClassOrInterface(className);
                    if (exists classOrInterface) {
                        if (is ClassDeclaration clazz = classOrInterface) {
                            return clazz;
                        } else {
                            throw SchemaException("interface found instead of class: ``fqClassname``");
                        }
                    } else if (exists anon = pkg.getValue(className),
                        anon.objectValue) {
                        return anon.objectClass;
                    } else {
                        throw SchemaException("class not found: ``fqClassname``");
                    }
                } else {
                    throw SchemaException("package not found: ``pkgName``");
                }
            }
        }
        throw SchemaException("no module found for class: ``fqClassname``");
    } else {
        throw Exception("class name not fully qualified: ``fqClassname``");
    }
}

class ParseException(LineReader reader, String message) extends Exception(message + " on line ``reader.lineNumber``") {
}

class SchemaException(String message) extends Exception(message) {
}

"""Formats a [[ValueTable]] using a line oriented format.
   
   The first line is always `# VALUES`.
   
   All other lines consist of:
   
   * an identifier (matching `[0-9A-Za-z]+`)
   * a comma (`,`)
   * a datum, as defined by [[DatumParser]]
"""
class ValueTableWriter(StringBuilder output) {
    shared void write(ValueTable table) {
        writeHeader();
        for (id->val in table.rows) {
            output.append(id.string);
            output.appendCharacter(',');
            output.append(formatDatum2(table, val));
            output.appendNewline();
        }
    }
    void writeHeader() {
        output.append("# VALUES");
        output.appendNewline();
    }
    "Formats a datum"
    String formatDatum2(ValueTable table, ValueTable.Puttable v) {
        if (is Reference<Type> v) {
            // TODO do we use @ or do we infer it's a reference from the metamodel
            // (or from the header: id,@person.id)?
            return v.id.string;
        } else {
            if (is String v) {
                //assert (false);
                return "\"``quoteString(v)``\"";
            } else if (is Integer v) {
                return v >= 0 then "+``v``" else "``v``";
            } else if (is Byte v) {
                return "#``v``"; // TODO hex?
            } else if (is Float v) {
                return v >= 0.0 then "+``v``" else "``v``";
            } else if (is Character v) {
                return "'``quoteCharacter(v)``'";
            } else if (is ValueDeclaration v) {
                return "``v.qualifiedName``";
            } else if (is Package v) {
                return v.qualifiedName;
            } else if (is FunctionDeclaration v) {
                return v.name;
            } else if (is ClassOrInterfaceDeclaration v) {
                return v.name;
            } else if (is Application v) {
                return "``v.ctor``(``",".join(v.arguments)``)";
            } else if (is TypeApplication v) {
                return "``v.generic``<``",".join(v.typeArguments)``>";
            } else if (is Member v) {
                return "``v.pck``::``".".join(v.members)``";
            } else if (is Union v) {
                return "|".join(v.cases);
            } else if (is Intersection v) {
                return "&".join(v.satisfyeds);
            }
        }
        throw Exception("unsupported datum type ``type(v)``");
    }
}

class ValueTableReader(LineReader reader) {
    ValueTable read() {
        // Have we reached eof yet?
        value l = reader.readLine();
        assert (exists l,
            l == "# VALUES");
        while (true) {
            value line = reader.readLine();
            if (exists line) {
                if (line.startsWith("#") {
                    reader.unread();
                    break();
                }
                assert(exists commaIndex = line.firstOccurrence(','));
                String ident = line[...commaIndex-1];
                String datum = line[commaIndex+1...]
                
            } else {
                throw Exception("unexpected end of stream");
            }
        }
    }
}

class TableReader(LineReader reader, TypeParser typeParser) {
    
    "The next table, or null"
    shared Table? read() {
        // Have we reached eof yet?
        value l = reader.readLine();
        if (!l exists) {
            return null;
        }
        reader.unread();
        
        // Read a table
        [ClassModel, ClassModel?] classAndSuper = parseClassNamesHeader(reader);
        assert (exists ClassModel cm = classAndSuper.getFromFirst(0)); //XXX compiler bug
        ClassModel? sm = classAndSuper[1];
        value tpAttributes = parseColumnNamesHeader(reader, cm.declaration);
        value tps = tpAttributes[0];
        value attributes = tpAttributes[1];
        // TODO check the type parameters in the table match the type parameters in 
        // the class (order and name)
        Table table = Table(cm, sm, attributes);
        
        while (true) {
            value line = reader.readLine();
            if (exists line, !line.empty) {
                if (line.startsWith("#")) {
                    reader.unread();
                    break;
                } else {
                    Table.Row row = table.Row();
                    Id id = parseRow(reader, line, tps, table.columns, row);
                    table.addRow(id, row);
                }
            } else {
                break;
            }
        }
        return table;
    }
    
    "Parses the first header row of a table, which is a hash (#) 
     followed by the FQ class name of the declaration the 
     table encodes
     
         # example::Person (extends superclass)?
     "
    [ClassModel, ClassModel?] parseClassNamesHeader(LineReader reader) {
        // TODO Do I care about abstractness too?
        if (exists line = reader.readLine()) {
            if (!line.startsWith("#")) {
                throw ParseException(reader, "expected header row");
            }
            String[] parts = line[1...].trimmed.split().sequence();
            if (exists className = parts[0]) {
                ClassModel? superModel;
                ClassModel classModel;
                // super class
                if (exists superclassName = parts[2]) {
                    if (exists ext = parts[1],
                        ext == "extends") {
                    } else {
                        throw ParseException(reader, "expected <class> extends <superclass>");
                    }
                    if (is ClassModel s = typeParser.parse(superclassName)) {
                        superModel = s;
                    } else {
                        throw SchemaException("``superclassName`` is not a class");
                    }
                } else {
                    superModel = null;
                }
                // the class itself
                if (is ClassModel cd = typeParser.parse(className)) {
                    classModel = cd;
                } else {
                    throw SchemaException("``className`` is not a class");
                }
                return [classModel, superModel];
            } else {
                throw ParseException(reader, "missing class name while reading table header 1");
            }
        } else {
            throw ParseException(reader, "unexpected eof while reading table header 1");
        }
    }
    "Parses the second header row of a table, which is a hash (#)
     followed by the names of the persisted attributes of 
     that class. 
     
         # <id>,name,spose,address
         
     attribute types are not encoded 
     (during deserialization they're obtained from the runtime metamodel)
     "
    [List<TypeParameter>, List<ValueDeclaration>] parseColumnNamesHeader(
        LineReader reader, ClassDeclaration classDeclaration) {
        if (exists line = reader.readLine()) {
            if (!line.startsWith("#")) {
                throw ParseException(reader, "expected header row starting with #");
            }
            value typeParameters = ArrayList<TypeParameter>();
            value attributes = ArrayList<ValueDeclaration>();
            value attributeNames = line[1...].trimmed.split((Character ch) => ch == ',');
            variable value index = 0;
            if (exists id = attributeNames.first, id == "=id") {
            } else {
                throw ParseException(reader, "missing =id column in column names header");
            }
            
            for (attributeName in attributeNames.rest) {
                if (attributeName.startsWith("<"),
                    attributeName.endsWith(">"),
                    exists tp = classDeclaration.getTypeParameterDeclaration(attributeName[1 : attributeName.size - 2])) {
                    typeParameters.add(tp);
                } else if (exists vd = classDeclaration.getDeclaredMemberDeclaration<ValueDeclaration>(attributeName)) {
                    attributes.add(vd);
                } else {
                    throw Exception("class ``classDeclaration.qualifiedName`` lacks the attribute ``attributeName``");
                }
                index++;
            }
            return [typeParameters, attributes];
        } else {
            throw ParseException(reader, "unexpected eof while reading column names header");
        }
    }
    "Parses a row of data"
    Id parseRow(LineReader reader, String line, List<TypeParameter> tps, List<ValueDeclaration> columns, Table.Row row) {
        
        String[] idData = line.split((Character ch) => ch == ',').sequence(); // this will only work if commas within datums are quoted
        if (idData.size - 1 != tps.size + columns.size) {
            throw ParseException(reader, "expected `` tps.size + columns.size + 1 `` values, found ``idData.size`` '``line``' ``idData``");
        }
        
        Id id;
        if (exists datum = idData[0]) {
            id = datum;
            // TODO check contains only characters from the id alphabet
            /*if (exists num = datum) {
                id = num;
            } else {
                throw ParseException(reader, "<id> datum held non-Integer");
            }*/
        } else {
            throw ParseException(reader, "missing <id> datum");
        }
        
        variable value index = 0;
        for (datumStr in idData.rest) {
            if (exists tp = tps[index]) {
                //value ta = nothing; // parse it
                row.setTypeArgument(tp, datumStr);
            } else if (exists vd = columns[index - tps.size]) {
                value datum = parseDatum(datumStr, vd);
                row.setValue(vd, datum);
            } else {
                throw ParseException(reader, "too many columns in row");
            }
            index++;
        }
        return id;
    }
}

"Determine whether `a` is a subclass of `b`."
Boolean isSubclassOf(ClassDeclaration a, ClassDeclaration b) {
    variable ClassDeclaration? aSuper = a;
    while (exists aSup = aSuper) {
        if (aSup == b) {
            // a is a subclass of b
            return true;
        }
        aSuper = aSup.extendedType?.declaration;
    }
    return false;
}

class DbReader(Module mod, LineReader reader) {
    "A map from class to table. This must have iteration order such that 
     more derived classes occur before their super classes, so that 
     [[idToCd]] gets populated with the concrete class for a given id. 
     ids identify the instance across all tables, remember."
    HashMap<ClassDeclaration,Table> tables = HashMap<ClassDeclaration,Table>();
    
    "A map from instance id to the tables in which its state it stored. 
     The tables are in most-refined to least refined order."
    HashMap<Id,ClassDeclaration> idToCd = HashMap<Id,ClassDeclaration>();
    
    TypeParser typeParser = TypeParser(mod);
    
    void readTables(LineReader reader) {
        TableReader tr = TableReader(reader, typeParser);
        value tableList = ArrayList<Table>();
        // read the tables from the stream
        while (exists table = tr.read()) {
            // insert tables into the list so more refined tables occur 
            // before less refined, so when we iterate tables we associate 
            // each id in the stream woth the most derived class.
            variable value index = 0;
            for (t in tableList) {
                if (isSubclassOf(t.classDeclaration, table.classDeclaration)) {
                    tableList.insert(index + 1, table);
                    break;
                } else if (isSubclassOf(table.classDeclaration, t.classDeclaration)) {
                    tableList.insert(index, table);
                    break;
                }
                index++;
            } else {
                tableList.add(table);
            }
        }
        
        // Finally iterate those tables, populating idToTables
        for (table in tableList) {
            //print(table);
            tables.put(table.classDeclaration, table);
            // TODO can speed up this loop if I know table is abstract
            for (id in table.rows.keys) {
                if (!id in idToCd.keys) {
                    idToCd.put(id, table.classDeclaration);
                }
            }
        }
    }
    
    readTables(reader);
    
    // TODO Get rid of this, without reducing test coverage
    deprecated ("replaced by registerReferences")
    shared Iterable<[Id, ClassModel]> instanceRefs {
        return idToCd.map(function(Entry<Id,ClassDeclaration> item) {
                Id id = item.key;
                ClassDeclaration cd = item.item;
                assert (exists table = tables[cd]);
                assert (exists row = table.get(id));
                value parser = TypeParser(`module com.github.tombentley.tabular`);
                return [id, cd.classApply<Anything,Nothing>(*{ for (s in row.typeArguments) parser.parse(s) })];
            });
        //return { for (id->cd in idToCd) [id, cd.classApply<Anything,Nothing>()] };
    }
    
    shared void registerReferences(DeserializationContext context) {
        value parser = TypeParser(mod);
        for (id->cd in idToCd) {
            if (exists table = tables[cd]) {
                if (exists row = table.get(id)) {
                    context.reference(id, cd.classApply<Anything,Nothing>(*{ for (s in row.typeArguments) parser.parse(s) }));
                } else {
                    throw Exception("row not found in table: id: ``id``, ``table``");
                }
            } else {
                throw Exception("table not found for class: ``cd``");
            }
        }
    }
    "The class of the serialized instance with the given id"
    shared ClassModel<Instance,Nothing> classOf<Instance>(Integer id) {
        assert (exists cd = idToCd[id]);
        return cd.classApply<Instance,Nothing>();
    }
    
    "Get a Deconstructed for the instance with the given id, of the given class"
    shared List<Table> get(Object id, ClassModel clazz) {
        assert (is Integer id);
        variable value classDecl = idToCd[id];
        // TODO This List<Table> is not necessary: TabDeconstructed can just follow the
        // link tables[table.superClass] to get the superclass table. Or at least make this return an Iterable
        ArrayList<Table> tabs = ArrayList<Table>();
        while (exists cd = classDecl,
            cd != `class Object` && cd != `class Basic`) {
            assert (exists t = tables[cd]);
            tabs.add(t);
            classDecl = t.superDeclaration;
        }
        return tabs;
    }
}


"Provides a facility for deserializing instances from String previously 
 generated by [[TabularSerializer]]."
shared class TabularDeserializer(Module mod, String serialized) {
    
    DeserializationContext context = deserialization();
    
    value db = DbReader(mod, LineReader(serialized.iterator().next));
    // register references with the context
    db.registerReferences(context);
    
    // now deserialize the references
    for (reference in context) {
        assert (is DeserializableReference<Object?> reference);
        /* XXX DeserializationContext should be Iterable<StatelessReference>?
         or does an element change to StatefulReference once deserialize() 
         has been called? */
        assert (is Id id = reference.id);
        List<Table> tables = db.get(id, reference.clazz);
        class TabDeconstructed() satisfies Deconstructed {
            
            shared actual Type|Reference<Type> getValue<Type>(ValueDeclaration attribute) {
                try {
                    for (table in tables) {
                        if (table.classDeclaration == attribute.container) {
                            assert (exists row = table.get(id));
                            value val = row.getValue(attribute);
                            // TODO Type or Reference??? Depends on table schema
                            // But let's be honest this is a shit way to decide 
                            // whether the integer we got is a reference or a value
                            if (is Integer val, attribute.openType != `class Integer`) {
                                return context.reference(val, db.classOf<Type>(val));
                            } else {
                                if (is Type val) {
                                    return val;
                                } else {
                                    throw Exception("``type(val)``");
                                }
                            }
                        }
                    }
                } catch (Exception e) {
                    throw Exception("id=``id``, vd=``attribute``", e);
                }
                throw Exception("attribute not found: ``attribute``");
            }
            
            shared actual Type getTypeArgument(TypeParameter typeParameter) {
                for (table in tables) {
                    if (table.classDeclaration == typeParameter.container) {
                        assert (exists row = table.get(id));
                        return TypeParser(mod).parse(row.getTypeArgument(typeParameter));
                    }
                }
                throw Exception("type parameter not found: ``typeParameter``");
            }
            
            shared actual Iterator<[ValueDeclaration, Anything]> iterator() {
                object iter satisfies Iterator<[ValueDeclaration, Anything]> {
                    
                    Iterator<Table> titer = tables.iterator();
                    variable Iterator<ValueDeclaration> vds = emptyIterator;
                    variable Table.Row? row = null;
                    
                    shared actual [ValueDeclaration, Anything]|Finished next() {
                        variable value nextVd = vds.next();
                        while (is Finished vd = nextVd) {
                            value table = titer.next();
                            if (!is Finished table) {
                                row = table.get(id);
                                vds = table.columns.iterator();
                                nextVd = vds.next();
                            } else {
                                return finished;
                            }
                        }
                        assert (is ValueDeclaration vd = nextVd);
                        assert (exists r = row);
                        return [vd, getValue<Object?>(vd)];
                    }
                }
                return iter;
            }
        }
        reference.deserialize(TabDeconstructed());
    }
    
    // API for the client to get some deserialized instances
    shared {Type*} select<Type>(ClassModel<Type> from) {
        {RealizableReference<Object?>*} statefulRefs = context.map(function(Reference<Object?> reference) {
                assert (is RealizableReference<Object?> reference);
                return reference;
            });
        {RealizableReference<Object?>*} refs = statefulRefs.filter(function(RealizableReference<Object?> reference) {
                return reference.clazz.subtypeOf(from);
            });
        return refs.map(function(RealizableReference<Object?> ref) {
                assert (is Type instance = ref.instance());
                return instance;
            });
    }
}


class ExperimentSuper(a) {
    shared default String a;
}
class ExperimentSub(String s) extends ExperimentSuper(s) {
    shared actual String a = "b";
    shared String b => super.a;
}
void experiment() {
    value x = `ExperimentSuper.a`;
    value y = `ExperimentSub.a`;
    value z = `ExperimentSub.b`;
    
    print(x.declaration);
    print(y.declaration);
    print(z.declaration);
    
    value sup = ExperimentSuper("A");
    value sub = ExperimentSub("B");
    print(x.bind(sup).get());
    //print(y.bind(sup).get());
    //print(z.bind(sup).get());
    
    print(x.bind(sub).get());
    print(y.bind(sub).get());
    print(z.bind(sub).get());
     
}
// So we could use Attribute in the deconstructed API, but 
// the $serialize$() method would have to just get the declaration
// anyway