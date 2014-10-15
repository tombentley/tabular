import ceylon.language.meta {
    classModelOf=type
}
import ceylon.collection {
    HashMap,
    ArrayList
}
import ceylon.language.meta.model {
    Class,
    ClassModel,
    ClassOrInterface,
    Type,
    UnionType,
    IntersectionType
}
import ceylon.language.meta.declaration {
    ClassOrInterfaceDeclaration,
    ClassDeclaration,
    ValueDeclaration,
    TypeParameter
}

interface Locator {
    shared formal Integer lineNumber;
}

"Treat an `Iterator<Character>` as something which can read (and count) lines)."
class LineReader(Character|Finished read()) satisfies Locator {
    variable Boolean eof = false;
    
    variable Character|Finished cnext = finished;
    
    variable StringBuilder line = StringBuilder();
    
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
        line = StringBuilder();
        lino++;
        return result;
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
            throw Exception("item with id ``id`` is neither class nor class declaration: ``classModelOf(item)``");
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
            throw Exception("item with id ``id`` is neither class nor class declaration: ``classModelOf(item)``");
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
                throw Exception("item with id ``id`` is neither class nor class declaration: ``classModelOf(item)``");
            }
        } else {
            throw Exception("no meta item has id ``id``");
        }
    }
    
    shared Type<T> type<T = Anything>(Id id) {
        value item = map.get(id);
        if (exists item) {
            if (is ClassOrInterfaceDeclaration item) {
                return item.apply<T>();
            } else if (is ClassOrInterface<T> item) {
                return item;
            } else if (is UnionType<T> item) {
                return item;
            } else if (is IntersectionType<T> item) {
                return item;
            } else if (is NothingMeta item) {
                return `Nothing`;
            } else {
                throw Exception("item with id ``id`` is not a type: ``classModelOf(item)``");
            }
        } else {
            throw Exception("no meta item has id ``id``");
        }
    }
    
    "Returns the id of the class that's outer to the given class, 
     or null if the given class was toplevel. Note this "
    shared Id? outerClassOf(Id cid) {
        // TODO Implement this
        //if (cid.string == "4") {
        //    return Id("3");
        //}
        return null;
        /*
        if (is ClassDeclaration meta = map.get(cid),
            !meta.toplevel) {
            return meta.container;
        } else {
            return null;
        }*/
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
                    //print("putting ``ident``->``parsed``");
                    result.put(ident, parsed);
                } catch (Throwable e) {
                    throw Exception("problem parsing \"``datum``\" for id ``ident`` on line ``reader.lineNumber``", e);
                }
            } else {
                throw Exception("unexpected end of stream");
            }
        }
        
        return MetaD(result);
    }
}

abstract class Reader() {
    """Parses a class name header:
       
           line ::= '@'? ident ('extends' ident)?
           
       The extends clause may be omitted when the superclass was 
       `Object` or `Basic`.
       """
    shared [Boolean, Id, Id?] parseClassNamesHeader(String line, Locator locator) {
        
        if (!line.startsWith("#")) {
            throw ParseException("expected header row", locator);
        }
        
        Boolean classAbstract;
        String[] parts = line[1...].trimmed.split().sequence();
        Id cid;
        Id? sid;
        switch (parts.size)
        case (1) { //# ident
            classAbstract = false;
            assert (exists cpart = parts[0]);
            cid = Id(cpart);
            sid = null;
        }
        case (2) { //# @ ident
            assert (exists at = parts[0],
                at == "@");
            classAbstract = true;
            assert (exists cpart = parts[1]);
            cid = Id(cpart);
            sid = null;
        }
        case (3) { //# ident extends ident
            classAbstract = false;
            assert (exists cpart = parts[0]);
            cid = Id(cpart);
            assert (exists ext = parts[1],
                ext == "extends");
            assert (exists spart = parts[2]);
            sid = Id(spart);
            assert (exists sid);
            //superModel = metaData.classModel<Anything>(sid);
        }
        case (4) { //# @ ident extends ident
            assert (exists at = parts[0],
                at == "@");
            classAbstract = true;
            assert (exists cpart = parts[1]);
            cid = Id(cpart);
            assert (exists ext = parts[2],
                ext == "extends");
            assert (exists spart = parts[3]);
            sid = Id(spart);
            assert (exists sid);
        }
        else {
            throw ParseException("missing class name while reading table header 1", locator);
        }
        
        return [classAbstract, cid, sid];
    }
}

class ArrayTableReader(DatumParser parser, MetaD metaData, LineReader reader)
        extends Reader() {
    shared ArrayTable read() {
        // Have we reached eof yet?
        ArrayTable table = ArrayTable();
        value l = reader.readLine();
        if (!l exists) {
            return table;
        }
        reader.unread();
        if (!readHeader1()) {
            return table;
        }
        readHeader2();
        
        while (true) {
            value line = reader.readLine();
            if (exists line, !line.empty) {
                if (line.startsWith("#")) {
                    reader.unread();
                    break;
                } else {
                    parseRow(line, table);
                }
            } else {
                break;
            }
        }
        
        return table;
    }
    "true if the table is the array table"
    Boolean readHeader1() {
        if (exists l = reader.readLine()) {
            if (!l.startsWith("#")) {
                throw Exception();
            }
            [Boolean, Id, Id?] tuple = parseClassNamesHeader(l, reader);
            value abstractClass = tuple[0];
            value cdId = tuple[1];
            value superclass = tuple[2];
            ClassDeclaration cd = metaData.classDeclaration(cdId);
            if (cd != `class Array`) {
                // it's not the array table!
                reader.unread();
                return false;
            }
            "Array is not abstract"
            assert (!abstractClass);
            "superclass of Array is Object/Basic"
            assert (!superclass exists);
            return true;
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
    void parseRow(String line, ArrayTable table) {
        
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
    }
}

class AttributeTableReader(LineReader reader, DatumParser parser, MetaD metaData)
        extends Reader() {
    
    "The next table, or null"
    shared AttributeTable? read() {
        // Have we reached eof yet?
        value l = reader.readLine();
        if (!l exists) {
            return null;
        }
        assert (exists l);
        
        // Read a table
        [Boolean, Id, Id?] tuple = parseClassNamesHeader(l, reader);
        Boolean classAbstract = tuple[0];
        Id cid = tuple[1];
        ClassDeclaration cd = metaData.classDeclaration(cid);
        Id? sid = tuple[2];
        if (exists sid) {
            value superModel = metaData.classModel<Anything>(sid);
            if (exists s = cd.extendedType?.declaration,
                s != superModel.declaration) {
                throw SchemaException("``cd`` no longer extends ``superModel`` but rather `` cd.extendedType else "null" ``", reader);
            }
        }
        value tpAttributes = parseColumnNamesHeader(reader, cd);
        value tps = tpAttributes[1];
        value attributes = tpAttributes[2];
        // TODO check the type parameters in the table match the type parameters in 
        // the class (order and name)
        AttributeTable table = AttributeTable(classAbstract, cid, cd.typeParameterDeclarations, sid, attributes);
        // look up the outer class from the metadata
        table.outerClass = metaData.outerClassOf(cid);
        // TODO check the outer class as Ser time is the same as the outer class now
        
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
    
    "Parses the second header row of a table, which is a hash (#)
     followed by the names of the persisted attributes of 
     that class. 
     
         # <id>,name,spose,address
         
     attribute types are not encoded 
     (during deserialization they're obtained from the runtime metamodel)
     "
    [Boolean, List<TypeParameter>, List<ValueDeclaration>] parseColumnNamesHeader(
        LineReader reader, ClassDeclaration classDeclaration) {
        if (exists line = reader.readLine()) {
            if (!line.startsWith("#")) {
                throw ParseException("expected header row starting with #", reader);
            }
            value typeParameters = ArrayList<TypeParameter>();
            value attributes = ArrayList<ValueDeclaration>();
            variable value attributeNames = line[1...].trimmed.split((Character ch) => ch == ',');
            variable value index = 0;
            if (exists id = attributeNames.first, id == "=id") {
                attributeNames = attributeNames.rest;
            } else {
                throw ParseException("missing =id column in column names header", reader);
            }
            Boolean hasOuter;
            if (exists outr = attributeNames.first, outr == "outer") {
                hasOuter = true;
                attributeNames = attributeNames.rest;
            } else {
                hasOuter = false;
            }
            
            for (attributeName in attributeNames) {
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
            return [hasOuter, typeParameters, attributes];
        } else {
            throw ParseException("unexpected eof while reading column names header", reader);
        }
    }
    "Parses a row of data"
    Id parseRow(LineReader reader, String line, List<TypeParameter> tps, List<ValueDeclaration> columns, AttributeTable.Row row) {
        
        variable String[] idData = line.split {
            splitting(Character ch) => ch == ',';
            groupSeparators = false;
        }.sequence(); // this only works because commas within datums are quoted
        variable value expectedValues = tps.size + columns.size;
        if (row.table.outerClass exists) {
            expectedValues++;
        }
        if (idData.size - 1 != expectedValues) {
            throw ParseException("expected ``expectedValues`` values, found `` idData.size - 1 `` '``line``' ``idData``", reader);
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
            idData = idData.rest;
        } else {
            throw ParseException("missing <id> datum", reader);
        }
        if (row.table.outerClass exists) {
            assert (exists datumStr = idData.first);
            assert (is Id outerId = parser.parse(datumStr));
            row.outerInstance = outerId;
            idData = idData.rest;
        }
        
        variable value index = 0;
        for (datumStr in idData) {
            if (exists tp = tps[index]) {
                if (datumStr.empty) {
                    row.concrete = false;
                } else {
                    assert (is Id taId = parser.parse(datumStr));
                    row.setTypeArgument(tp, taId);
                }
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
