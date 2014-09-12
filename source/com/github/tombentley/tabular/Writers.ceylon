import ceylon.collection {
    StringBuilder
}
import ceylon.language.meta {
    type
}
import ceylon.language.meta.declaration {
    ClassOrInterfaceDeclaration,
    Package,
    ValueDeclaration
}

abstract class Writer() {
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
                if (v.toplevel) {
                    return "``v.container``::``v.memberName``";
                } else {
                    return "``v.container``.``v.memberName``";
                }
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
            writeRow(id, table, row);
        }
    }
    void writeHeader(AttributeTable table) {
        output.append("# ");
        if (table.classAbstract) {
            output.append("@ ");
        }
        output.append("``table.classDeclaration``");
        if (exists sc = table.superModel) {
            output.append(" extends ``sc``");
        }
        output.appendNewline();
        output.append("# =id");
        if (table.outerClass exists) {
            output.appendCharacter(',').append("outer");
        }
        if (!table.classAbstract) {
            for (tp in table.typeParameters) {
                output.appendCharacter(',').append("<``tp.name``>");
            }
        }
        for (vd in table.columns) {
            output.appendCharacter(',').append(vd.name);
        }
        output.appendNewline();
    }
    void writeRow(Id id, AttributeTable table, AttributeTable.Row row) {
        output.append(formatDatum(id));
        if (exists outerId = row.outerInstance) {
            output.appendCharacter(',');
            output.append(formatDatum(outerId));
        }
        if (!table.classAbstract) {
            for (ta in row.typeArguments) {
                output.appendCharacter(',');
                if (row.concrete) {
                    // if the class is generic but the class of the instance is not
                    // we don't need to persis the type arguments at all
                    output.append(formatDatum(ta));
                }
            }
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
