import ceylon.language.meta {
    type,
    modules
}
import ceylon.language.meta.model {
    ClassModel
}
import ceylon.language.meta.declaration {
    ClassDeclaration,
    ValueDeclaration
}
import ceylon.language.serialization {
    Deconstructor,
    Deconstructed,
    SerializationContext,
    Reference,
    StatelessReference,
    StatefulReference,
    DeserializationContext,
    deserialization,
    serialization
}
import ceylon.collection {
    ArrayList,
    HashMap,
    TreeMap,
    IdentityMap,
    StringBuilder,
    MutableMap,
    Queue,
    LinkedList
}

"""A unit type to know that something's been set 
   (can't use null, because that's a valid "value" which could be set).
"""
object unset {
    shared actual String string => "?";
}

"A table made up of rows. 
 Each table holds attribute values of the given [[classDeclaration]] 
 for a number of `Integer`-identified instances."
class Table(classDeclaration, superClass, cols) {
    "The class whose state this table serializes"
    shared ClassDeclaration classDeclaration;
    
    "The superclass of the classDeclaration *at the time the data was serialized*."
    shared ClassDeclaration? superClass;
    
    // TODO abstract?
    
    "The mapping of attribute to column index."
    MutableMap<ValueDeclaration,Integer> schema = HashMap<ValueDeclaration,Integer>();
    
    "Reverse mapping to [[schema]]."
    List<ValueDeclaration> cols;
    variable value ii = 0;
    for (vd in cols) {
        schema.put(vd, ii);
        ii++;
    }
    "The columns in this table."
    shared List<ValueDeclaration> columns = cols;
    
    shared String name => classDeclaration.qualifiedName;
    
    "The number of columns in the table."
    shared Integer numColumns => schema.size;
    
    HashMap<Integer,Row> data = HashMap<Integer,Row>();
    shared Map<Integer,Row> rows => data;
    
    "A row within a table"
    shared class Row() satisfies Iterable<Object?> {
        // not that values is initialized to all unset
        // and that it's impossible for clients to see an unset value
        
        "The Table this Row is (or will be) a row of."
        shared Table table => outer;
        
        ArrayList<Object?> values = ArrayList<Object?>();
        for (vd in schema.keys) {
            values.add(unset);
        }
        
        shared void setValue(ValueDeclaration vd, Object? datum) {
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
        shared ValueDeclaration? complete {
            variable value i = 0;
            for (datum in values) {
                if (exists datum,
                    datum == unset) {
                    return columns[i];
                }
                i++;
            }
            return null;
        }
        "The data in this row, in the same order as [[outer.columns"
        shared actual Iterator<Object?> iterator() => values.iterator();
    }
    
    "Adds a row for the instance with the given id to the table."
    shared void addRow(Integer id, Row row) {
        if (exists problemVd = row.complete) {
            throw Exception("incomplete row, missing value for ``problemVd``");
        }
        data.put(id, row);
    }
    
    "The row for the instances with the given id"
    shared Row? get(Integer id) => data[id];
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

"Unquotes the characters in the given string, which should be be enclosed 
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
            value start = ii;
            while (true) {
                if (is Character hexDigit = iter.next()) {
                    ii++;
                    if (hexDigit == '}') {
                        sb.appendCharacter(unquoteCharacter(string, start, ii));
                        break;
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
            throw Exception("unquoted quotable character in quoted string");
        }
        else {
            assert (is Character char);
            sb.appendCharacter(char);
        }
    }
    return sb.string;
}

Character unquoteCharacter(String hex, Integer start = 0, Integer end = hex.size) {
    Integer? codepoint = parseInteger(hex[start:end], 16);
    if (exists codepoint) {
        return codepoint.character;
    }
    throw Exception("invalid quoted character");
}

"Formats a datum"
String formatDatum<Type>(Type|Reference<Type> v) {
    if (is Reference<Type> v) {
        // TODO do we use @ or do we infer it's a reference from the metamodel
        // (or from the header: id,@person.id)?
        return v.id.string;
    } else {
        if (is String v) {
            return "\"``quoteString(v)``\"";
        } else if (is Integer v) {
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
        } else {
            value valueType = type(v);
            if (valueType.declaration.anonymous
                        && valueType.declaration.toplevel) {
                return valueType.declaration.qualifiedName;
            } else {
                throw Exception("unsupported datum type ``type(v)``");
            }
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
            return unquoteString(datum[1 .. datum.size - 2]);
        } else if (first == '\'') {
            // starts with ' => character
            if (!datum.endsWith("\'")) {
                throw Exception("unterminated character: ``datum``");
            } else if (datum.size < 3) {
                throw Exception("invalid character: ``datum``");
            } else {
                String s = unquoteString(datum[1 .. datum.size - 2]);
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
        output.append("# ``table.classDeclaration.qualifiedName``");
        if (exists sc = table.superClass) {
            output.append(" extends ``sc.qualifiedName``");
        }
        output.appendNewline();
        output.append("# <id>");
        for (vd in table.columns) {
            output.appendCharacter(',').append(vd.name);
        }
        output.appendNewline();
    }
    void writeRow(Integer id, Table.Row row) {
        output.append(id.string);
        for (Object? datum in row) {
            output.appendCharacter(',');
            output.append(formatDatum(datum));
        }
        output.appendNewline();
    }
}

"Provides a facility for serializing instances to a `String`."
shared class TabularSerializer() {
    
    SerializationContext context = serialization();
    
    "Mapping of entity to id"
    IdentityMap<Identifiable,Integer> ids = IdentityMap<Identifiable,Integer>();
    
    "Mapping of value to id" // TODO What about mutable values
    HashMap<Object,Integer> valueIds = HashMap<Object,Integer>();
    
    "The last allocated id"
    variable Integer lastId = 0;
    
    MutableMap<ClassDeclaration,Table> tables = HashMap<ClassDeclaration,Table>();
    
    "Obtain an id for the given instance"
    Integer allocateId(Object? instance) {
        switch (instance)
        case (is Null) {
            return 0;
        }
        case (is Object) {
            if (is Identifiable instance) {
                if (exists id = ids[instance]) {
                    return id;
                } else {
                    value id = ++lastId;
                    ids.put(instance, id);
                    return id;
                }
            } else {
                if (exists id = valueIds[instance]) {
                    return id;
                } else {
                    value id = ++lastId;
                    valueIds.put(instance, id);
                    return id;
                }
            }
        }
    }
    
    Boolean idAllocated(Object? instance) {
        switch (instance)
        case (is Null) {
            return true;
        }
        case (is Object) {
            if (is Identifiable instance) {
                return instance in ids.keys;
            } else {
                return instance in valueIds.keys;
            }
        }
    }
    
    Boolean isSerializable(Object? thing) {
        if (is Identifiable thing) {
            // TODO and is annotated serializable
            return true;
        } else {
            return isValue(thing);
        }
    }
    
    Boolean isValue(Object? thing) {
        switch (thing)
        case (is Null) {
            return true;
        }
        case (is String) {
            return true;
        }
        case (is Integer) {
            return true;
        }
        case (is Float) {
            return true;
        }
        case (is Byte) {
            return true;
        }
        case (is Character) {
            return true;
        }
        case (is Array<Anything>) {
            throw Exception("Not yet supported value type: ``type(thing)``");
        }
        case (is Entry<Object,Object>) {
            throw Exception("Not yet supported value type: ``type(thing)``");
        }
        else {
            if (is Sequence<Anything> thing) {
                // can't put this as a case because it's not disjoint from identifiable
                throw Exception("Not yet supported value type: ``type(thing)``");
            }
            return false;
        }
    }
    
    "Register the given instance, and every instance reachable from it, 
     for serialization."
    shared void add(Object instance) {
        Queue<Object?> instances = LinkedList<Object?>();
        class TabularDeconstructor() satisfies Deconstructor {
            variable Integer id = -1;
            variable ClassDeclaration? lastClass = null;
            variable value fiddle = ArrayList<[ValueDeclaration, Object?]>();
            "Called when we start inspecting an instance"
            shared void beginInstance(Integer id) {
                this.id = id;
            }
            
            // XXX We don't directly know when we finish with one class and start on a super class 
            // for the same instance. I.e. when we need to allocate a new Row
            // so we have to have this rigmarole with current -- yuk 
            shared actual void put<Type>(ValueDeclaration attribute, Type referenced) {
                if (exists lc = lastClass) {
                    if (lc != attribute.container) {
                        // finish the row of the last class
                        finishRow(lc);
                    }
                }
                assert (is ClassDeclaration currentClass = attribute.container);
                lastClass = currentClass;
                
                Object? ref = referenced of Object?;
                if (isValue(ref)) {
                    fiddle.add([attribute, ref]);
                } else {
                    /* TODO according to annotations we need to also add 
                     instances reachable from the instance. */
                    
                    assert (exists ref);
                    // XXX this test is wrong, because it fails to cope with self-refs
                    
                    if (!idAllocated(ref)) {
                        instances.offer(ref);
                    }
                    Integer referredId = allocateId(ref);
                    // need an id, so we can put that
                    fiddle.add([attribute, referredId]);
                }
            }
            
            void finishRow(ClassDeclaration lc) {
                Table table;
                if (exists t = tables[lc]) {
                    table = t;
                } else {
                    // It's here, stupid
                    table = Table(lc, lc.extendedType?.declaration, { for (tup in fiddle) tup[0] }.sequence());
                    tables.put(lc, table);
                }
                value row = table.Row();
                for (tup in fiddle) {
                    try {
                        row.setValue(tup[0], tup[1]);
                    } catch (Throwable e) {
                        throw Exception("Problem setting ``tup[0]``, id=``id``", e);
                    }
                }
                table.addRow(id, row);
                lastClass = null;
                fiddle.clear();
            }
            "Called when we finish inspecting an instance"
            shared void endInstance() {
                // Here I can check that all the rows in all the tables have been populated
                if (exists last = lastClass) {
                    finishRow(last);
                }
            }
        }
        value dtor = TabularDeconstructor();
        
        instances.offer(instance);
        while (exists inst = instances.accept()) {
            //if (idAllocated(inst)) {
            //    continue;
            //}
            value id = allocateId(inst);
            try {
                dtor.beginInstance(id);
                if (!isSerializable(inst)) {
                    // XXX poor error message. we should give a path from instance to inst
                    throw Exception("instance is not serializable");
                }
                
                // and add the instance to the context
                value reference = context.reference(id, inst);
                reference.serialize(dtor);
                dtor.endInstance();
            } catch (Exception e) {
                throw Exception("problem while serializing ``instance`` with id ``id``", e);
            }
        }
    }
    
    
    "Serialize all the [[registered|add]] instances to the given StringBuilder."
    shared String write() {
        StringBuilder builder = StringBuilder();
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

class TableReader(LineReader reader) {
    
    "The next table, or null"
    shared Table? read() {
        // Have we reached eof yet?
        value l = reader.readLine();
        if (!l exists) {
            return null;
        }
        reader.unread();
        
        // Read a table
        [ClassDeclaration, ClassDeclaration?] classAndSuper = parseClassNamesHeader(reader);
        value attributes = parseColumnNamesHeader(reader, classAndSuper[0]);
        Table table = Table(classAndSuper[0], classAndSuper[1], attributes);
        
        while (true) {
            value line = reader.readLine();
            if (exists line, !line.empty) {
                if (line.startsWith("#")) {
                    reader.unread();
                    break;
                } else {
                    Table.Row row = table.Row();
                    Integer id = parseRow(reader, line, table.columns, row);
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
    [ClassDeclaration, ClassDeclaration?] parseClassNamesHeader(LineReader reader) {
        // TODO Do I care about abstractness too?
        if (exists line = reader.readLine()) {
            if (!line.startsWith("#")) {
                throw ParseException(reader, "expected header row");
            }
            String[] parts = line[1...].trimmed.split().sequence();
            if (exists className = parts[0]) {
                ClassDeclaration? superclassDeclaration;
                ClassDeclaration classDeclaration;
                // super class
                if (exists superclassName = parts[2]) {
                    if (exists ext = parts[1],
                        ext == "extends") {
                    } else {
                        throw ParseException(reader, "expected <class> extends <superclass>");
                    }
                    superclassDeclaration = classDeclarationFromName(superclassName);
                    if (!superclassDeclaration exists) {
                        throw SchemaException("class ``superclassName`` cannot be found");
                    }
                } else {
                    superclassDeclaration = null;
                }
                // the class itself
                if (exists cd = classDeclarationFromName(className)) {
                    classDeclaration = cd;
                } else {
                    throw SchemaException("class ``className`` cannot be found");
                }
                return [classDeclaration, superclassDeclaration];
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
    List<ValueDeclaration> parseColumnNamesHeader(LineReader reader, ClassDeclaration classDeclaration) {
        if (exists line = reader.readLine()) {
            if (!line.startsWith("#")) {
                throw ParseException(reader, "expected header row starting with #");
            }
            value attributes = ArrayList<ValueDeclaration>();
            value attributeNames = line[1...].trimmed.split((Character ch) => ch == ',');
            variable value index = 0;
            if (exists id = attributeNames.first, id == "<id>") {
            } else {
                throw ParseException(reader, "missing <id> column in column names header");
            }
            
            for (attributeName in attributeNames.rest) {
                if (exists vd = classDeclaration.getDeclaredMemberDeclaration<ValueDeclaration>(attributeName)) {
                    attributes.add(vd);
                } else {
                    throw Exception("class ``classDeclaration.qualifiedName`` lacks the attribute ``attributeName``");
                }
                index++;
            }
            return attributes;
        } else {
            throw ParseException(reader, "unexpected eof while reading column names header");
        }
    }
    "Parses a row of data"
    Integer parseRow(LineReader reader, String line, List<ValueDeclaration> columns, Table.Row row) {
        
        String[] idData = line.split((Character ch) => ch == ',').sequence(); // this will only work if commas within datums are quoted
        if (idData.size - 1 != columns.size) {
            throw ParseException(reader, "expected `` columns.size + 1 `` values, found ``idData.size`` '``line``' ``idData``");
        }
        
        Integer id;
        if (exists datum = idData[0]) {
            if (exists num = parseInteger(datum)) {
                id = num;
            } else {
                throw ParseException(reader, "<id> datum held non-Integer");
            }
        } else {
            throw ParseException(reader, "missing <id> datum");
        }
        
        variable value index = 0;
        for (datumStr in idData.rest) {
            if (exists vd = columns[index]) {
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

class DbReader(LineReader reader) {
    TreeMap<ClassDeclaration,Table> tables = TreeMap<ClassDeclaration,Table>(
        // Topologically sort the class declarations into most derived order first
        function(ClassDeclaration a, ClassDeclaration b) {
            Comparison result;
            if (a == b) {
                result = equal;
            } else if (isSubclassOf(a, b)) {
                result = smaller;
            } else if (isSubclassOf(b, a)) {
                result = larger;
            } else {
                result = a.qualifiedName <=> b.qualifiedName;
            }
            return result;
        });
    
    "A map from instance id to the tables in which its state it stored. 
     The tables are in most-refined to least refined order."
    HashMap<Integer,ClassDeclaration> idToCd = HashMap<Integer,ClassDeclaration>();
    
    void readTables(LineReader reader) {
        TableReader tr = TableReader(reader);
        while (exists table = tr.read()) {
            tables.put(table.classDeclaration, table);
        }
        
        // Then iterate those tables, populating idToTables
        for (cd->table in tables) {
            // TODO can speed up this loop if I know table is abstract
            for (id in table.rows.keys) {
                if (!id in idToCd.keys) {
                    idToCd.put(id, cd);
                }
            }
        }
    }
    
    readTables(reader);
    
    // TODO Get rid of this, without reducing test coverage
    shared Iterable<[Integer, ClassModel]> instanceRefs {
        /* XXX for this we need to iterate the rows in each table, but need to 
           be careful about subclasses (need to return the subclass model and it's 
           id rather than a superclass model and its it) */
        // No, so we can share ids!
        return { for (id->cd in idToCd) [id, cd.classApply<Anything,Nothing>()] };
    }
    
    shared void registerReferences(DeserializationContext context) {
        for (id->cd in idToCd) {
            context.reference(id, cd.classApply<Anything,Nothing>());
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
            classDecl = t.superClass;
        }
        return tabs;
    }
}


"Provides a facility for deserializing instances from String previously 
 generated by [[TabularSerializer]]."
shared class TabularDeserializer(String serialized) {
    
    DeserializationContext context = deserialization();
    
    value db = DbReader(LineReader(serialized.iterator().next));
    // register references with the context
    db.registerReferences(context);
    
    // now deserialize the references
    for (reference in context) {
        assert (is StatelessReference<Object?> reference);
        /* XXX DeserializationContext should be Iterable<StatelessReference>?
         or does an element change to StatefulReference once deserialize() 
         has been called? */
        assert (is Integer id = reference.id);
        List<Table> tables = db.get(id, reference.clazz);
        class TabDeconstructed() satisfies Deconstructed {
            
            shared actual Type|Reference<Type> get<Type>(ValueDeclaration attribute) {
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
            shared actual Iterator<[ValueDeclaration, Anything]> iterator() {
                object iter satisfies Iterator<[ValueDeclaration, Anything]> {
                    
                    Iterator<Table> titer = tables.iterator();
                    variable Iterator<ValueDeclaration> vds = emptyIterator;
                    variable Table.Row? row = null;
                    
                    shared actual [ValueDeclaration, Anything]|Finished next() {
                        variable value nextVd = vds.next();
                        if (is Finished vd = nextVd) {
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
                        return [vd, get<Object?>(vd)];
                    }
                }
                return iter;
            }
        }
        reference.deserialize(TabDeconstructed());
    }
    
    // API for the client to get some deserialized instances
    shared {Type*} select<Type>(ClassModel<Type> from) {
        {StatefulReference<Object?>*} statefulRefs = context.map(function(Reference<Object?> reference) {
                assert (is StatefulReference<Object?> reference);
                return reference;
            });
        {StatefulReference<Object?>*} refs = statefulRefs.filter(function(StatefulReference<Object?> reference) {
                return reference.clazz.subtypeOf(from);
            });
        return refs.map(function(StatefulReference<Object?> ref) {
                assert (is Type instance = ref.instance());
                return instance;
            });
    }
}
