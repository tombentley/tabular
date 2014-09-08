import ceylon.language.meta {
    type,
    modules
}
import ceylon.language.meta.model {
    Model,
    ClassModel,
    Type,
    Class,
    FunctionModel,
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
    ValueDeclaration,
    TypeParameter,
    Module,
    Package
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

"The *fundemental* types that are also value types."
alias FundementalValueType => String|Character|Integer|Float|Byte;

"Whether the given instance is a `ceylon.language::Array`."
Boolean isArray(Anything instance) {
    // this is lame but because Array is invariant there's no 
    // type we can use to test for array-ness
    
    return instance is List<Anything> // shortcircuit
            && type(instance).declaration.qualifiedName == "ceylon.language::Array";
}

"Whether the given instance is *fundemental*. 
 An instance is fundemental if it cannot be decomposed 
 in terms of its attributes, that is, is of type
 
 * `String`, `Character`, `Integer`, `Float `or `Byte`, or
 * Array<`T`> for some `T`
 "
Boolean isFundementalType(Anything instance) {
    if (instance is FundementalValueType) {
        return true;
    } else if (isArray(instance)) {
        return true;
    } else {
        return false;
    }
}

"The ValueDeclaration for the `object` declaration if the given instance is 
 the instance of a top level anonymous class, otherwise null."
ValueDeclaration? getObjectValueDeclaration(Anything instance) {
    if (exists instance) {
        if (instance == true) {
            return `value true`;
        } else if (instance == false) {
            return `value false`;
        } else {
            return type(instance).declaration.objectValue;
        }
    } else {
        return `value null`;
    }
}
"Whether the given instance is an anonymous class instance (`object` declaration)."
Boolean isObjectDeclaration(Anything instance) {
    return getObjectValueDeclaration(instance) exists;
}

"Whether the given instance can be serialized. 
 An instance can be serialized if it:
 
 * is `Identifiable` and annotated `serializable` or
 * is an object declaration or
 * is an instance a [[fundemental type|isFundementalType]]
 * is an `ArraySequence`
 "
Boolean isSerializable(Anything thing) {
    if (thing is Identifiable
                || thing is ArraySequence<Anything>) {
        // it can be decomposed
        return true; // TODO and is annotated serializable
    } else if (thing is FundementalValueType) {
        // it's fundemental
        return true;
    } else if (isArray(thing)) {
        return true;
    } else if (isObjectDeclaration(thing)) {
        // we can store a reference to it in the meta table
        return true;
    } else {
        return false;
    }
}

"The type arguments of the given Generic instance, in declaration order."
// see ceylon.language#544
Type[] typeArguments(Generic g) {
    TypeParameter[] tps;
    if (is ClassOrInterface g) {
        tps = g.declaration.typeParameterDeclarations;
    } else if (is FunctionModel g) {
        tps = g.declaration.typeParameterDeclarations;
    } else {
        throw;
    }
    return { for (tp in tps) g.typeArguments[tp] else nothing }.sequence();
}

"Every instance will be identified by a unique `String`, 
 but let's use an alias for clarity."
//alias Id => String;
class Id(shared actual String string) {
    shared actual Boolean equals(Object other) {
        if (is Id other) {
            return this.string == other.string;
        } else {
            return false;
        }
    }
    shared actual Integer hash => string.hash;
}

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
    shared Id next() {
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
        
        return Id("".join(digits.reversed));
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
    
    shared actual String string {
        value sb = StringBuilder();
        sb.appendCharacter('{');
        if (exists nid = nullId) {
            sb.append("null->").append(nid.string);
        }
        for (inst->id in valueIds) {
            sb.append(inst.string).append("->").append(id.string);
        }
        for (inst->id in ids) {
            sb.append(inst.string).append("->").append(id.string);
        }
        sb.appendCharacter('}');
        return sb.string;
    }
    
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

"Representation of a union type within a [[MetaTable]]"
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
"Representation of an intersection type within a [[MetaTable]]"
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
"Representation of a member access within a [[MetaTable]]"
class Member(shared Id pck, shared [String+] members) extends Object() {
    shared actual Boolean equals(Object other) {
        if (is Member other) {
            return pck == other.pck && members == other.members;
        } else {
            return false;
        }
    }
    shared actual Integer hash => pck.hash + members.hash;
}
"Representation of a type application within a [[MetaTable]]."
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

alias MetaValue => Package|Member|TypeApplication|Union|Intersection|ClassDeclaration|ValueDeclaration|Type|String|Id[];

/*"Holds meta information about types and values (but not functions). 
 This table has the special property that it only refers to things also 
 in the meta table, and nothing in other tables."
class MetaTable<Puttable>()
        given Puttable satisfies Object {
    
    "Underlying map"
    HashMap<Id,MetaValue> data = HashMap<Id,MetaValue>();
    
    shared Puttable get(Id id) {
        assert (exists val = data[id],
            is Puttable val);
        return val;
    }
    
    shared Map<Id,MetaValue> rows => data;
}
*/
abstract class Unset() of unset {}

"""A unit type used to know that a value has been set in a `Table.Row`  
   (we can't use null, because that's a valid "value" which could be set).
   """
object unset extends Unset() {
    shared actual String string => "?";
}

abstract class Table<ActualRow>()
        given ActualRow satisfies Row {
    shared formal class Row(Integer a) {
    }
    HashMap<Id,ActualRow> data = HashMap<Id,ActualRow>();
    shared Map<Id,ActualRow> rows => data;
    shared default void addRow(Id id, ActualRow row) {
        data.put(id, row);
    }
}

class ArrayTable() extends Table<Row>() {
    shared actual class Row(size) extends super.Row(size) {
        "The number of elements in the array"
        shared Integer size;
        "Storage for the type argument (the first element) 
         and the array elements."
        value values = arrayOfSize<Id|FundementalValueType?>(size + 1, null);
        "The array's type argument"
        shared Id typeArgument {
            assert (is Id ta = values[0]);
            return ta;
        }
        assign typeArgument {
            values.set(0, typeArgument);
        }
        
        shared void setValue(Integer index, Id|FundementalValueType datum) {
            values.set(index + 1, datum);
        }
        
        shared Id|FundementalValueType getValue(Integer index) {
            assert (exists id = values.get(index + 1));
            return id;
        }
    }
}

"A table made up of rows. 
 Each table holds attribute values of the given [[classDeclaration]] 
 for a number of [[Id]]-identified instances.
 
 We record the superclass model so we know what the reified type 
 parameters held in superclasses are."
class AttributeTable(classDeclaration, typeParameters, superModel, columns)
        extends Table<Row>() {
    "The class whose state this table serializes"
    shared Id classDeclaration;
    
    "The superclass of the classDeclaration 
     *at the time the data was serialized*,
     or null if the superclass was `Basic` or `Object`."
    shared Id? superModel;
    
    //"The superclass of the classDeclaration at the time the data was serialized*."
    //shared ClassDeclaration? superDeclaration => superModel?.declaration;
    
    shared List<TypeParameter> typeParameters; // => classDeclaration.typeParameterDeclarations;
    
    "The mapping of column index to attribute."
    shared List<ValueDeclaration> columns;
    value schema = HashMap<ValueDeclaration,Integer>();
    for (index->vd in columns.indexed) {
        schema.put(vd, index);
    }
    
    //HashMap<Id,Row> data = HashMap<Id,Row>();
    //shared Map<Id,Row> rows => data;
    
    "A row within a table"
    shared actual class Row(Integer s) extends super.Row(s) {
        // not that values is initialized to all unset
        // and that it's impossible for clients to see an unset value
        
        "The Table this Row is (or will be) a row of."
        shared AttributeTable table => outer;
        
        value typeArguments_ = ArrayList<Id?>();
        for (tp in typeParameters) {
            typeArguments_.add(null);
        }
        
        value values = arrayOfSize<Id|FundementalValueType?>(schema.size, null);
        
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
        
        shared void setTypeArgument(TypeParameter tp, Id className) {
            variable value index = tpIndex(tp);
            typeArguments_.set(index, className);
        }
        
        shared Id getTypeArgument(TypeParameter tp) {
            variable value index = tpIndex(tp);
            assert (exists ta = typeArguments_[index]);
            return ta;
        }
        
        shared void setValue(ValueDeclaration vd, Id|FundementalValueType datum) {
            assert (exists index = schema[vd]);
            // TODO check that the type of val is a subtype of the type of vd
            values.set(index, datum);
        }
        shared FundementalValueType|Id getValue(ValueDeclaration vd) {
            if (exists index = schema[vd],
                0 <= index < values.size) {
                value datum = values[index];
                switch (datum)
                case (is Null) {
                    throw Exception("value not yet set: ``vd``");
                }
                case (is Reference<Anything>|FundementalValueType|Id) {
                    return datum;
                }
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
                if (!datum exists) {
                    return columns[i];
                }
                i++;
            }
            return null;
        }
        shared {Id*} typeArguments {
            return typeArguments_.map(function(Id? o) {
                    assert (exists o);
                    return o;
                });
        }
        
        "The data in this row, in the same order as [[outer.columns"
        shared {Id|FundementalValueType*} data => values.map(function(datum) {
                assert (is Id|FundementalValueType datum);
                return datum;
            });
    }
    
    "Adds a row for the instance with the given id to the table."
    shared actual void addRow(Id id, Row row) {
        if (exists problemVd = row.complete) {
            throw Exception("incomplete row, missing value for ``problemVd``");
        }
        super.addRow(id, row);
    }
    
    "The row for the instances with the given id"
    shared Row? get(Id id) => rows[id];
    
    shared actual String string => "Table(``classDeclaration``, `` superModel else "null" ``, ``columns``)";
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


// TODO Get rid of this
"The top level object declaration corresponding to the 
 given fully qualified name."
throws (`class Exception`, "An object with this name could not be found")
Object? findObject(String fqName, Locator? locator = null) {
    if (exists model = classDeclarationFromName(fqName, locator),
        exists obj = model.objectValue) {
        return obj.get() of Object?;
    }
    throw Exception("not an object: ``fqName``");
}

/*"Parses a datum."
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
            throw Exception("unhandled datum: ``datum``");
        }
    } else {
        //empty => null
        return null;
    }
}
*/
abstract class Writer() {
    "Formats a datum"
    see (`class DatumParser`)
    shared String formatDatum(Id|FundementalValueType|MetaValue|Id[] v) {
        if (is Id v) {
            return v.string;
        } else if (is FundementalValueType v) {
            switch (v)
            case (is String) {
                return "\"``quoteString(v)``\"";
            }
            case (is Character) {
                return "'``quoteCharacter(v)``'";
            }
            case (is Integer) {
                if (v.positive || v.zero) {
                    return "+``v``";
                } else {
                    return v.string;
                }
            }
            case (is Float) {
                if (v.positive) {
                    return "+``v``";
                } else {
                    return v.string;
                }
            }
            case (is Byte) {
                return "#``formatInteger(v.unsigned, 16)``";
            }
        } else {
            if (is ValueDeclaration v) {
                return "``v.qualifiedName``";
            } else if (is Package v) {
                return v.qualifiedName;
            } else if (is ClassOrInterfaceDeclaration v) {
                return v.name;
            } else if (is TypeApplication v) {
                return "``v.generic``<``",".join(v.typeArguments)``>";
            } else if (is Member v) {
                return "``v.pck``::``".".join(v.members)``";
            } else if (is Union v) {
                return "|".join(v.cases);
            } else if (is Intersection v) {
                return "&".join(v.satisfyeds);
            } else if (is Id[] v) {
                return "[``",".join(v)``]";
            }
        }
        throw Exception("unsupported datum type ``type(v)``");
    }
}

class AttributeTableWriter(StringBuilder output) extends Writer() {
    shared void write(AttributeTable table) {
        writeHeader(table);
        for (id->row in table.rows) {
            writeRow(id, row);
        }
    }
    void writeHeader(AttributeTable table) {
        // TODO abstractness?
        output.append("# ``table.classDeclaration``");
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
    void writeRow(Id id, AttributeTable.Row row) {
        output.append(formatDatum(id));
        for (ta in row.typeArguments) {
            output.appendCharacter(',');
            output.append(formatDatum(ta));
        }
        for (datum in row.data) {
            output.appendCharacter(',');
            output.append(formatDatum(datum));
        }
        output.appendNewline();
    }
}

"""Formats a [[MetaTable]] using a line oriented format.
   
   The first line is always `# VALUES`.
   
   All other lines consist of:
   
   * an identifier (matching `[0-9A-Za-z]+`)
   * a comma (`,`)
   * a datum, as defined by [[DatumParser]]
   """
class MetaTableWriter(StringBuilder output) extends Writer() {
    shared void write(Map<Id,MetaValue> metaData, String name) {
        writeHeader(name);
        for (id->val in metaData) {
            output.append(formatDatum(id));
            if (isArray(val)) {
                assert (is List<MetaValue> val);
                for (item in val) {
                    output.appendCharacter(',');
                    output.append(formatDatum(item));
                }
            } else {
                output.appendCharacter(',');
                output.append(formatDatum(val));
            }
            output.appendNewline();
        }
    }
    void writeHeader(String name) {
        output.append("## ``name``");
        output.appendNewline();
    }
}

class ArrayTableWriter(Id arrayClassId, StringBuilder output) extends Writer() {
    shared void write(ArrayTable table) {
        output.append("# ``arrayClassId``").appendNewline();
        output.append("# =id,<Element>,...").appendNewline();
        for (id->row in table.rows) {
            output.append(formatDatum(id));
            output.appendCharacter(',');
            output.append(formatDatum(row.typeArgument));
            for (index in 0:row.size) {
                output.appendCharacter(',');
                output.append(formatDatum(row.getValue(index)));
            }
            output.appendNewline();
        }
    }
}

class MetaData(shared HashMap<Id,MetaValue> metaData, IdAllocator allocator, Reference<Object?> enlist(Anything instance)) {
    Id alloPut(MetaValue cls) {
        value clsId = allocator.allocateId(cls);
        metaData.put(clsId, cls);
        return clsId;
    }
    Id putOrEnlist(Anything o) {
        if (!isFundementalType(o)) {
            assert (is Id id = enlist(o).id);
            return id;
        } else {
            assert (is MetaValue item = o);
            return alloPut(item);
        }
    }
    Id package_(Package p) {
        return alloPut(p);
    }
    shared Id valueDeclaration(ValueDeclaration vd) {
        if (is Package p = vd.container) {
            return alloPut(Member(package_(p), [vd.name]));
        }
        return nothing; // TODO attributes
    }
    shared Id classOrInterfaceDeclaration(ClassOrInterfaceDeclaration cd) {
        if (is Package p = cd.container) {
            return alloPut(Member(package_(p), [cd.name]));
        }
        return nothing; // TODO member classes
    }
    shared Id classOrInterface(ClassOrInterface c) {
        if (c.typeArguments.empty) {
            // for non-generic classes let's just record the declaration
            return classOrInterfaceDeclaration(c.declaration);
        } else {
            return alloPut(TypeApplication(classOrInterfaceDeclaration(c.declaration), typeArguments(c)));
        }
    }
    shared Id type_(Type ta) {
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
        return package.typeArguments(g).collect(type_);
    }
    shared Id array(List<Anything> val) {
        Id[] ids = val.collect(putOrEnlist);
        return alloPut(ids);
    }
    shared Id str(String val) => alloPut(val);
}

"Provides a facility for serializing instances to a `String`."
shared class TabularSerializer(Boolean inlineString = true) {
    
    SerializationContext context = serialization();
    value allocator = IdAllocator();
    
    MutableMap<ClassModel,AttributeTable> tables = HashMap<ClassModel,AttributeTable>();
    ArrayTable arrayTable = ArrayTable();
    "Queue of instances waiting to be serialized"
    Queue<SerializableReference<Object?>> instances = LinkedList<SerializableReference<Object?>>();
    
    // TODO Get rid of this fucker
    value anotherFuckingMap = HashMap<Id,SerializableReference<Object?>>();
    
    "Adds the given [[instance]] to [[instances]] 
             if it's not been added yet, returns its id."
    SerializableReference<Object?> enlist(Anything instance) {
        assert (is Object? instance);
        Boolean notAllocated = !allocator.idAllocated(instance);
        Id id = allocator.allocateId(instance);
        if (notAllocated) {
            value reference = context.reference(id, instance);
            instances.offer(reference);
            anotherFuckingMap.put(id, reference);
            return reference;
        }
        assert (exists r = anotherFuckingMap[id]);
        return r;
    }
    
    "Meta data necessary to describe classes and 
     references to object declarations."
    value metaData = MetaData(HashMap<Id,MetaValue>(), allocator, enlist);
    
    class TabularDeconstructor() satisfies Deconstructor {
        variable Id id = Id("");
        shared variable ClassModel? classModel = null;
        shared variable ClassModel? currentClass = null;
        variable value typeParameters = ArrayList<[TypeParameter, Id]>();
        variable value values = ArrayList<[ValueDeclaration, Id|FundementalValueType]>();
        variable value elements = ArrayList<Id|FundementalValueType>();
        
        "Called when we start inspecting an instance"
        shared void beginInstance(Id id, Object? instance) {
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
        "Whether the given value should be added to the table row *inline*, 
         or via a reference. Only values of [[FundementalValueType]] can be included inline."
        Boolean inline<Type>(Type val) {
            return inlineString;
        }
        
        shared actual void putValue<Type>(ValueDeclaration attribute, Type referenced) {
            Object? ref = referenced of Object?;
            if (exists vd = getObjectValueDeclaration(ref)) {
                // it's an object declaration, so add it to the meta table
                values.add([attribute, metaData.valueDeclaration(vd)]);
            } else {
                if (inline(ref), is FundementalValueType ref) {
                    values.add([attribute, ref]);
                } else {
                    assert (is Id id = enlist(ref).id);
                    values.add([attribute, id]);
                }
            }
        }
        shared actual void putElement<Type>(Integer index, Type referenced) {
            Object? ref = referenced of Object?;
            if (exists vd = getObjectValueDeclaration(ref)) {
                // it's an object declaration, so add it to the meta table
                elements.add(metaData.valueDeclaration(vd));
            } else {
                if (inline(ref), is FundementalValueType ref) {
                    elements.add(ref);
                } else {
                    assert (is Id id = enlist(ref).id);
                    elements.add(id);
                }
            }
        }
        
        shared actual void putTypeArgument(TypeParameter typeParameter, Type argument) {
            //values.add([attribute, metaTable.add(vd)]);
            //typeParameters.add([typeParameter, argument.string]);
            typeParameters.add([typeParameter, metaData.type_(argument)]);
        }
        "Gets the table for the given class, creating it if necessary. 
         Note this can only be called after all the values have been added
         otherwise we don't know the schema of the table."
        AttributeTable|ArrayTable getOrCreateTable(ClassModel cc) {
            if (cc.declaration == `class Array`) {
                return arrayTable;
            }
            AttributeTable table;
            if (exists t = tables[cc]) {
                table = t;
            } else {
                assert (is ClassModel s = cc.extendedType);
                table = AttributeTable(metaData.classOrInterfaceDeclaration(cc.declaration), cc.declaration.typeParameterDeclarations,
                    s != `Object` && s != `Basic` then metaData.classOrInterface(s) else null,
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
            AttributeTable|ArrayTable table = getOrCreateTable(cc);
            switch (table)
            case (is AttributeTable) {
                value row = table.Row(-1);
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
            }
            case (is ArrayTable) {
                value row = table.Row(elements.size);
                assert (typeParameters.size == 1,
                    exists tpName = typeParameters[0]);
                try {
                    row.typeArgument = tpName[1];
                } catch (Throwable e) {
                    throw Exception("Problem setting type argument for type parameter ``tpName[0]`` in table ``table`` for class ``cc``, id=``id``", e);
                }
                for (index->tup in elements.indexed) {
                    try {
                        row.setValue(index, tup);
                    } catch (Throwable e) {
                        throw Exception("Problem setting value for element ``tup`` at index ``index`` in table ``table`` for class ``cc``, id=``id``", e);
                    }
                }
                table.addRow(id, row);
            }
            
            typeParameters.clear();
            values.clear();
            elements.clear();
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
                if (is FundementalValueType inst) {
                    switch (inst)
                    case (is String) {
                        //if (internStrings) {
                        metaData.str(inst);
                        //}
                        // TODO do what?
                    }
                    case (is Character) {
                    }
                    case (is Integer) {
                    }
                    case (is Byte) {
                    }
                    case (is Float) {
                    }
                } else if (exists vd = getObjectValueDeclaration(inst)) {
                    metaData.valueDeclaration(vd);
                } else if (isSerializable(inst)) {
                    value reference = ref;
                    dtor.beginInstance(id, inst);
                    reference.serialize(dtorFactory);
                    dtor.endInstance();
                } else {
                    throw Exception("instance `` inst else "null" `` (type ``type(inst)``) with id ``id`` is not serializable");
                }
            } catch (Exception e) {
                throw Exception("problem while serializing `` inst else "null" `` with id ``id``", e);
            }
        }
    }
    
    "Serialize all the [[registered|add]] instances to the given StringBuilder."
    shared String write() {
        StringBuilder builder = StringBuilder();
        
        value arrayId = metaData.classOrInterfaceDeclaration(`class Array`);
        
        value ctw = MetaTableWriter(builder);
        ctw.write(metaData.metaData, "META");
        
        ArrayTableWriter atw = ArrayTableWriter(arrayId, builder);
        atw.write(arrayTable);
        
        AttributeTableWriter writer = AttributeTableWriter(builder);
        for (table in tables.items) {
            writer.write(table);
        }
        return builder.string;
    }
}

interface Locator {
    shared formal Integer lineNumber;
}

"Treat an `Iterator<Character>` as something which can read (and count) lines)."
class LineReader(Character|Finished read()) satisfies Locator {
    variable Boolean eof = false;
    
    variable Character|Finished cnext = finished;
    
    StringBuilder line = StringBuilder();
    
    "The line number of the last line returned by [[readLine]]."
    variable value lino = 0;
    
    "The line number of the last line returned by [[readLine]]."
    shared actual Integer lineNumber => lino;
    
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

ClassDeclaration? classDeclarationFromName(String fqClassname, Locator? locator = null) {
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
                            throw SchemaException("interface found instead of class: ``fqClassname``", locator);
                        }
                    } else if (exists anon = pkg.getValue(className),
                        anon.objectValue) {
                        return anon.objectClass;
                    } else {
                        throw SchemaException("class not found: ``fqClassname``", locator);
                    }
                } else {
                    throw SchemaException("package not found: ``pkgName``", locator);
                }
            }
        }
        throw SchemaException("no module found for class: ``fqClassname``", locator);
    } else {
        throw Exception("class name not fully qualified: ``fqClassname``");
    }
}

String msg(String message, Locator? locator = null) {
    if (exists locator) {
        return message + " on line " + locator.lineNumber.string;
    } else {
        return message;
    }
}

class ParseException(String message, Locator? locator = null) extends Exception(msg(message, locator)) {
}

class SchemaException(String message, Locator? locator = null) extends Exception(msg(message, locator)) {
}

class MetaD(Map<Id,MetaValue> map) {
    
    shared ValueDeclaration? objectDeclaration(Id id) {
        value item = map.get(id);
        if (exists item) {
            if (is ClassDeclaration item) {
                return item.objectValue;
            }
            throw Exception("item with id ``id`` is neither class nor class declaration: ``type(item)``");
        } else {
            return null;
        }
    }
    
    shared ClassDeclaration classDeclaration(Id id) {
        value item = map.get(id);
        if (exists item) {
            if (is ClassDeclaration item) {
                return item;
            } else if (is Class item) {
                return item.declaration;
            }
            throw Exception("item with id ``id`` is neither class nor class declaration: ``type(item)``");
        } else {
            throw Exception("no meta item has id ``id``");
        }
    }
    
    shared ClassModel<Type> classModel<Type = Anything>(Id id) {
        value item = map.get(id);
        if (exists item) {
            if (is ClassDeclaration item) {
                return item.classApply<Type,Nothing>();
            } else if (is Class<Type> item) {
                return item;
            } else {
                throw Exception("item with id ``id`` is neither class nor class declaration: ``type(item)``");
            }
        } else {
            throw Exception("no meta item has id ``id``");
        }
    }
    
    shared Type<Anything> typeArgument(Id id) {
        value item = map.get(id);
        if (exists item) {
            if (is ClassOrInterfaceDeclaration item) {
                return item.apply<Anything>();
            } else if (is ClassOrInterface<Anything> item) {
                return item;
            } else if (is Union item) {
                throw Exception("union type arguments not yet supported");
            } else if (is Intersection item) {
                throw Exception("intersection type arguments not yet supported");
            } else {
                throw Exception("item with id ``id`` is not a type: ``type(item)``");
            }
        } else {
            throw Exception("no meta item has id ``id``");
        }
    }
}

class MetaTableReader(LineReader reader) {
    HashMap<Id,MetaValue> result = HashMap<Id,MetaValue>();
    shared DatumParser parser = DatumParser(result);
    shared MetaD read() {
        // Have we reached eof yet?
        value l = reader.readLine();
        assert (exists l,
            l == "## META");
        //IdAllocator allocator, Reference<Object?> enlist(Anything instance)
        
        while (true) {
            value line = reader.readLine();
            if (exists line) {
                if (line.startsWith("#")) {
                    reader.unread();
                    break;
                }
                assert (exists commaIndex = line.firstOccurrence(','));
                Id ident = Id(line[... commaIndex - 1]);
                String datum = line[commaIndex + 1 ...];
                try {
                    assert (is MetaValue parsed = parser.parse(datum));
                    print("putting ``ident``->``parsed``");
                    result.put(ident, parsed);
                } catch (Throwable e) {
                    throw Exception("problem parsing ``datum`` for id ``ident`` on line ``reader.lineNumber``", e);
                }
            } else {
                throw Exception("unexpected end of stream");
            }
        }
        
        return MetaD(result);
    }
}

class ArrayTableReader(DatumParser parser, MetaD metaData, LineReader reader) {
    shared ArrayTable? read() {
        // Have we reached eof yet?
        value l = reader.readLine();
        if (!l exists) {
            return null;
        }
        reader.unread();
        
        readHeader1();
        readHeader2();
        
        ArrayTable table = ArrayTable();
        
        while (true) {
            value line = reader.readLine();
            if (exists line, !line.empty) {
                if (line.startsWith("#")) {
                    reader.unread();
                    break;
                } else {
                    value row = table.Row(2);
                    Id id = parseRow(line, table);
                }
            } else {
                break;
            }
        }
        
        return table;
    }
    
    void readHeader1() {
        if (exists l = reader.readLine()) {
            if (!l.startsWith("#")) {
                throw Exception();
            }
            assert (is Id cdId = parser.parse(l[1...].trimmed));
            ClassDeclaration cd = metaData.classDeclaration(cdId);
            assert (cd == `class Array`);
        } else {
            throw Exception();
        }
    }
    void readHeader2() {
        if (exists l = reader.readLine()) {
            if (l != "# =id,<Element>,...") {
                throw Exception();
            }
        } else {
            throw Exception();
        }
    }
    Id parseRow(String line, ArrayTable table) {
        
        String[] idData = line.split((Character ch) => ch == ',').sequence(); // this will only work if commas within datums are quoted
        Id id;
        if (exists i = idData[0]) {
            id = Id(i);
        } else {
            throw Exception("missing =id on row");
        }
        Id taId;
        if (exists i = idData[1]) {
            taId = Id(i);
        } else {
            throw Exception("missing <Element> on row");
        }
        value row = table.Row(idData.size - 2);
        row.typeArgument = taId;
        for (index->datum in idData[2...].indexed) {
            "we don't have arrays of MetaValue"
            assert (is Id|FundementalValueType x = parser.parse(datum));
            row.setValue(index, x);
        }
        table.addRow(id, row);
        return id;
    }
}

class AttributeTableReader(LineReader reader, DatumParser parser, MetaD metaData) {
    
    "The next table, or null"
    shared AttributeTable? read() {
        // Have we reached eof yet?
        value l = reader.readLine();
        if (!l exists) {
            return null;
        }
        reader.unread();
        
        // Read a table
        [Id, ClassDeclaration, Id?, ClassModel?] classAndSuper = parseClassNamesHeader(reader);
        Id cid = classAndSuper[0];
        ClassDeclaration cd = classAndSuper[1];
        Id? sid = classAndSuper[2];
        ClassModel? sm = classAndSuper[3];
        value tpAttributes = parseColumnNamesHeader(reader, cd);
        value tps = tpAttributes[0];
        value attributes = tpAttributes[1];
        // TODO check the type parameters in the table match the type parameters in 
        // the class (order and name)
        AttributeTable table = AttributeTable(cid, cd.typeParameterDeclarations, sid, attributes);
        
        while (true) {
            value line = reader.readLine();
            if (exists line, !line.empty) {
                if (line.startsWith("#")) {
                    reader.unread();
                    break;
                } else {
                    AttributeTable.Row row = table.Row(-1);
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
     
         # F (extends G)?
     "
    [Id, ClassDeclaration, Id?, ClassModel?] parseClassNamesHeader(LineReader reader) {
        // TODO Do I care about abstractness too?
        if (exists line = reader.readLine()) {
            if (!line.startsWith("#")) {
                throw ParseException("expected header row", reader);
            }
            String[] parts = line[1...].trimmed.split().sequence();
            Id cid;
            ClassDeclaration classDeclaration;
            Id? sid;
            ClassModel? superModel;
            if (exists cpart = parts[0]) {
                cid = Id(cpart);
                // super class
                if (exists superId = parts[2]) {
                    if (exists ext = parts[1],
                        ext == "extends") {
                    } else {
                        throw ParseException("expected <class> extends <superclass>", reader);
                    }
                    sid = Id(superId);
                    superModel = metaData.classModel<Anything>(sid else nothing);
                } else {
                    sid = null;
                    superModel = null;
                }
                // the class itself
                classDeclaration = metaData.classDeclaration(cid);
                if (exists superModel,
                    exists s = classDeclaration.extendedType?.declaration,
                    s != superModel.declaration) {
                    throw SchemaException("``classDeclaration`` no longer extends ``superModel`` but rather `` classDeclaration.extendedType else "null" ``", reader);
                }
                return [cid, classDeclaration, sid, superModel];
            } else {
                throw ParseException("missing class name while reading table header 1", reader);
            }
        } else {
            throw ParseException("unexpected eof while reading table header 1", reader);
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
                throw ParseException("expected header row starting with #", reader);
            }
            value typeParameters = ArrayList<TypeParameter>();
            value attributes = ArrayList<ValueDeclaration>();
            value attributeNames = line[1...].trimmed.split((Character ch) => ch == ',');
            variable value index = 0;
            if (exists id = attributeNames.first, id == "=id") {
            } else {
                throw ParseException("missing =id column in column names header", reader);
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
            throw ParseException("unexpected eof while reading column names header", reader);
        }
    }
    "Parses a row of data"
    Id parseRow(LineReader reader, String line, List<TypeParameter> tps, List<ValueDeclaration> columns, AttributeTable.Row row) {
        
        String[] idData = line.split((Character ch) => ch == ',').sequence(); // this will only work if commas within datums are quoted
        if (idData.size - 1 != tps.size + columns.size) {
            throw ParseException("expected `` tps.size + columns.size + 1 `` values, found ``idData.size`` '``line``' ``idData``", reader);
        }
        
        Id id;
        if (exists datum = idData[0]) {
            assert (is Id i = parser.parse(datum));
            id = i;
            // TODO check contains only characters from the id alphabet
            /*if (exists num = datum) {
                id = num;
            } else {
                throw ParseException(reader, "<id> datum held non-Integer");
            }*/
        } else {
            throw ParseException("missing <id> datum", reader);
        }
        
        variable value index = 0;
        for (datumStr in idData.rest) {
            if (exists tp = tps[index]) {
                //value ta = nothing; // parse it
                assert (is Id taId = parser.parse(datumStr));
                row.setTypeArgument(tp, taId);
            } else if (exists vd = columns[index - tps.size]) {
                value datum = parser.parse(datumStr);
                assert (is Id|FundementalValueType datum);
                row.setValue(vd, datum);
            } else {
                throw ParseException("too many columns in row", reader);
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

"Provides a facility for deserializing instances from String previously 
 generated by [[TabularSerializer]]."
shared class TabularDeserializer(Module mod, String serialized) {
    
    DeserializationContext context = deserialization();
    
    "A map from class to table. This must have iteration order such that 
     more derived classes occur before their super classes, so that 
     [[idToCd]] gets populated with the instance class for a given id 
     (rather than some superclass of the instance)."
    HashMap<ClassDeclaration,AttributeTable> tables = HashMap<ClassDeclaration,AttributeTable>();
    
    "A map from instance id to the tables in which its state is stored. 
     The tables are in most-refined to least refined order."
    HashMap<Id,ClassDeclaration> idToCd = HashMap<Id,ClassDeclaration>();
    
    value reader = LineReader(serialized.iterator().next);
    MetaTableReader mtr = MetaTableReader(reader);
    MetaD metaTable = mtr.read();
    value parser = mtr.parser;
    assert (exists arrayTable = ArrayTableReader(parser, metaTable, reader).read());
    void readAttributeTables(LineReader reader) {
        
        AttributeTableReader tr = AttributeTableReader(reader, parser, metaTable);
        value tableList = ArrayList<AttributeTable>();
        // read the tables from the stream
        while (exists table = tr.read()) {
            // insert tables into the list so more refined tables occur 
            // before less refined, so when we iterate tables we associate 
            // each id in the stream woth the most derived class.
            variable value index = 0;
            for (t in tableList) {
                ClassDeclaration cd = metaTable.classDeclaration(t.classDeclaration);
                ClassDeclaration cd2 = metaTable.classDeclaration(table.classDeclaration);
                if (isSubclassOf(cd, cd2)) {
                    tableList.insert(index + 1, table);
                    break;
                } else if (isSubclassOf(cd2, cd)) {
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
            ClassDeclaration cd = metaTable.classDeclaration(table.classDeclaration);
            tables.put(cd, table);
            // TODO can speed up this loop if I know table is abstract
            for (id in table.rows.keys) {
                if (!id in idToCd.keys) {
                    idToCd.put(id, cd);
                }
            }
        }
    }
    
    readAttributeTables(reader);
    
    void registerReferences() {
        
        for (id->row in arrayTable.rows) {
            context.reference(id, `class Array`.classApply<Anything,Nothing>(metaTable.typeArgument(row.typeArgument)));
        }
        
        for (id->cd in idToCd) {
            if (exists table = tables[cd]) {
                if (exists row = table.get(id)) {
                    context.reference(id, cd.classApply<Anything,Nothing>(*row.typeArguments.map(metaTable.typeArgument)));
                    /*{
                     if (is Type ta = metaData.get(taId)) {
                     return ta;
                     } else {
                     throw Exception("``metaData.get(taId) else "null`="`` ``type(metaData.get(taId))``");
                     }
                     })));*/
                } else {
                    throw Exception("row not found in table: id: ``id``, ``table``");
                }
            } else {
                throw Exception("table not found for class: ``cd``");
            }
        }
    }
    
    "The class of the serialized instance with the given id"
    ClassModel<Instance,Nothing> classOf<Instance>(Id id) {
        if (exists aa = arrayTable.rows.get(id)) {
            Type<Anything> ta = metaTable.typeArgument(aa.typeArgument);
            return `class Array`.classApply<Instance,Nothing>(ta);
        } else if (exists cd = idToCd[id]) {
            if (exists table = tables[cd]) {
                if (exists row = table.get(id)) {
                    return cd.classApply<Instance,Nothing>(*row.typeArguments.map(metaTable.typeArgument));
                }
            }
            throw Exception("type arguments not found for ``cd`` with id ``id``");
        } else {
            throw Exception("id not found in idToCd: ``id``");
        }
    }
    
    "Get a Deconstructed for the instance with the given id, of the given class"
    List<AttributeTable> getState(Id id, ClassModel clazz) {
        
        variable value classDecl = idToCd[id];
        // TODO This List<Table> is not necessary: TabDeconstructed can just follow the
        // link tables[table.superClass] to get the superclass table. Or at least make this return an Iterable
        ArrayList<AttributeTable> tabs = ArrayList<AttributeTable>();
        while (exists cd = classDecl,
            cd != `class Object` && cd != `class Basic`) {
            assert (exists t = tables[cd]);
            tabs.add(t);
            if (exists s = t.superModel) {
                classDecl = metaTable.classDeclaration(s);
            } else {
                classDecl = null;
            }
        }
        return tabs;
    }
    
    // register references with the context
    registerReferences();
    
    // now deserialize the references
    for (reference in context) {
        assert (is DeserializableReference<Object?> reference);
        /* XXX DeserializationContext should be Iterable<StatelessReference>?
         or does an element change to StatefulReference once deserialize() 
         has been called? */
        assert (is Id id = reference.id);
        
        class TabDeconstructed() satisfies Deconstructed {
            value arrayRow = arrayTable.rows.get(id);
            List<AttributeTable> tabs = getState(id, reference.clazz);
            Type|Reference<Type> fooble<Type>(Anything val) {
                if (is Id val) {
                    // Is it an object? 
                    if (exists vd = metaTable.objectDeclaration(val)) {
                        assert (is Type r = vd.get());
                        if (exists r,
                            r.string.startsWith("ceylon.language.null_@")) {
                            assert (is Type f = null);
                            return f;
                        }
                        return r;
                    }
                    return context.reference(val, classOf<Type>(val));
                } else if (is Type val) {
                    return val;
                } else {
                    throw Exception("``type(val)``");
                }
            }
            
            shared actual Type|Reference<Type> getValue<Type>(ValueDeclaration attribute) {
                if (exists arrayRow) {
                    value size = arrayRow.size;
                    assert (is Type|Reference<Type> size);
                    return size;
                } else {
                    try {
                        for (table in tabs) {
                            ClassDeclaration cd = metaTable.classDeclaration(table.classDeclaration);
                            if (cd == attribute.container) {
                                assert (exists row = table.get(id));
                                value val = row.getValue(attribute);
                                
                                return fooble<Type>(val);
                            }
                        }
                        throw Exception("attribute not found: ``attribute`` in ``tabs``");
                    } catch (Throwable e) {
                        throw Exception("id=``id``, vd=``attribute``", e);
                    }
                }
            }
            
            shared actual Type|Reference<Type> getElement<Type>(Integer index) {
                assert (exists arrayRow);
                value val = arrayRow.getValue(index);
                return fooble<Type>(val);
            }
            
            shared actual Type getTypeArgument(TypeParameter typeParameter) {
                if (exists arrayRow) {
                    return metaTable.typeArgument(arrayRow.typeArgument);
                }
                for (table in tabs) {
                    ClassDeclaration cd = metaTable.classDeclaration(table.classDeclaration);
                    if (cd == typeParameter.container) {
                        assert (exists row = table.get(id));
                        Id taId = row.getTypeArgument(typeParameter);
                        return metaTable.typeArgument(taId);
                    }
                }
                throw Exception("type parameter not found: ``typeParameter`` in tables ``tables`` for id ``id``  clazz ``reference.clazz``");
            }
            
            shared actual Iterator<[ValueDeclaration, Anything]> iterator() {
                object iter satisfies Iterator<[ValueDeclaration, Anything]> {
                    
                    Iterator<AttributeTable> titer = tabs.iterator();
                    variable Iterator<ValueDeclaration> vds = emptyIterator;
                    variable AttributeTable.Row? row = null;
                    
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
    
    // END OF INITIALIZER
    
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

/*
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
*/
