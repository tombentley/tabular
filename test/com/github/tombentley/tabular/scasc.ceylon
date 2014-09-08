import ceylon.collection {
    StringBuilder
}
import ceylon.language.meta.declaration {
    ValueDeclaration
}
/*
void testFormating() {
    // formatting and quoting
    
    // character and quoting
    assert ("'a'" == formatDatum('a'));
    assert ("'\\{#27}'" == formatDatum('\''));
    assert ("'\\{#a}'" == formatDatum('\n'));
    assert ("'\\{#d}'" == formatDatum('\r'));
    assert ("'\\{#22}'" == formatDatum('"'));
    assert ("'\\{#5c}'" == formatDatum('\\'));
    assert ("'\\{#2c}'" == formatDatum(','));
    // string and string quoting
    assert ("\"\"" == formatDatum(""));
    assert ("\"hello\"" == formatDatum("hello"));
    assert ("\"\\{#27}\\{#a}\\{#d}\\{#22}\\{#5c}\\{#2c}\"" == formatDatum("\'\n\r\"\\,"));
    
    // integer, byte, float
    assert ("#1" == formatDatum(1));
    assert ("#b1" == formatDatum(1.byte));
    assert ("1.0" == formatDatum(1.0));
    assert ("1.0E64" == formatDatum(1.0E64));
    
    // objects
    assert ("true" == formatDatum(true));
    assert ("false" == formatDatum(false));
    assert ("null" == formatDatum(null));
    assert ("empty" == formatDatum([]));
    assert ("ceylon.language::smaller" == formatDatum(smaller));
}

void testClassDeclarationFromName() {
    print(classDeclarationFromName("ceylon.language::String"));
    print(classDeclarationFromName("ceylon.language::Integer"));
    print(classDeclarationFromName("ceylon.language::Boolean"));
    print(classDeclarationFromName("ceylon.language::true"));
    print(classDeclarationFromName("ceylon.language::false"));
    // iface print(classDeclarationFromName("ceylon.language::Empty"));
    print(classDeclarationFromName("ceylon.language::empty"));
    print(classDeclarationFromName("ceylon.language::Null"));
    print(classDeclarationFromName("ceylon.language::null"));
    print(classDeclarationFromName("ceylon.language::smaller"));
    try {
        classDeclarationFromName("ceylon.language::Empty");
        assert (false);
    } catch (Exception e) {
        assert ("interface found instead of class: ceylon.language::Empty" == e.message);
    }
}

void testParsing() {
    // parsing and unquoting
    // TODO String and Character 
    
    assert (exists one = parseDatum("#1", `value true`),
        one == 1);
    assert (exists oneByte = parseDatum("#b1", `value true`),
        oneByte == 1.byte);
    assert (exists oneFloat = parseDatum("1.0", `value true`),
        oneFloat == 1.0);
    assert (exists oneEFloat = parseDatum("1e64", `value true`),
        oneEFloat == 1.0e64);
    assert (exists t = parseDatum("true", `value true`),
        t == true);
    assert (exists f = parseDatum("false", `value true`),
        f == false);
    assert (exists e = parseDatum("empty", `value true`),
        e == []);
    assert (!parseDatum("null", `value true`) exists);
    
    assert (exists s = parseDatum("ceylon.language::smaller", `value smaller`),
        s == smaller);
}

class Foo(name) {
    shared String name;
}

class Bar(shared String blah) extends Foo("bar") {
}

Table makeTable() {
    return Table(`class Foo`, `class Basic`, [`value Foo.name`]);
}

void testTable() {
    value vd = `value Foo.name`;
    Table table = makeTable(); //Table(`class Foo`, `class Basic`, map);
    value row = table.Row();
    try {
        row.getValue(vd);
        assert (false);
    } catch (Exception e) {
        assert ("value not yet set: ``vd``" == e.message);
    }
    try {
        row.getValue(`value true`);
        assert (false);
    } catch (Exception e) {
        assert ("value declaration not in table schema: value ceylon.language::true" == e.message);
    }
    row.setValue(vd, "foo");
    table.addRow(0, row);
    assert (exists otherRow = table.get(0));
    assert (exists val = otherRow.getValue(vd),
        "foo" == val);
    assert (!table.get(1) exists);
}

void testTableWriter() {
    value vd = `value Foo.name`;
    variable value sb = StringBuilder();
    value table = makeTable();
    TableWriter(sb).write(table);
    //print(sb.string);
    assert ("# com.github.tombentley.tabular::Foo extends ceylon.language::Basic
             # <id>,name
             " == sb.string);
    
    sb = StringBuilder();
    value row = table.Row();
    row.setValue(vd, "foo");
    table.addRow(0, row);
    TableWriter(sb).write(table);
    //print(sb.string);
    assert ("# com.github.tombentley.tabular::Foo extends ceylon.language::Basic
             # <id>,name
             0,\"foo\"
             " == sb.string);
}

void testLineReader() {
    variable value lr = LineReader("line1\nline2\nline3".iterator().next);
    assert (exists l1 = lr.readLine(),
        l1 == "line1");
    assert (exists l2 = lr.readLine(),
        l2 == "line2");
    assert (exists l3 = lr.readLine(),
        l3 == "line3");
    assert (!lr.readLine() exists);
    
    lr = LineReader("line1\n\rline2\r\nline3".iterator().next);
    assert (exists l4 = lr.readLine(),
        l4 == "line1");
    assert (exists l5 = lr.readLine(),
        l5 == "line2");
    assert (exists l6 = lr.readLine(),
        l6 == "line3");
    assert (!lr.readLine() exists);
    
    lr = LineReader("line1\nline2\rline3".iterator().next);
    assert (exists l7 = lr.readLine(),
        l7 == "line1");
    assert (exists l8 = lr.readLine(),
        l8 == "line2");
    assert (exists l9 = lr.readLine(),
        l9 == "line3");
    assert (!lr.readLine() exists);
    
    lr = LineReader("line1\nline2\nline3".iterator().next);
    assert (exists l10 = lr.readLine(),
        l10 == "line1");
    lr.unread();
    assert (exists l11 = lr.readLine(),
        l11 == "line1");
    assert (exists l12 = lr.readLine(),
        l12 == "line2");
    assert (exists l13 = lr.readLine(),
        l13 == "line3");
    assert (!lr.readLine() exists);
}

void testTableReader() {
    value tr = TableReader(LineReader(
            "# com.github.tombentley.tabular::Foo extends ceylon.language::Basic
             # <id>,name
             0,\"foo\"
             # com.github.tombentley.tabular::Foo extends ceylon.language::Basic
             # <id>,name
             1,\"bar\"
             ".iterator().next));
    assert (exists table1 = tr.read());
    assert (table1.classDeclaration == `class Foo`);
    assert (exists sc1 = table1.superClass,
        sc1 == `class Basic`);
    assert (table1.columns.size == 1);
    assert (exists col1 = table1.columns.first,
        col1 == `value Foo.name`);
    assert (exists name1 = table1.get(0)?.getValue(`value Foo.name`),
        "foo" == name1);
    
    assert (exists table2 = tr.read());
    assert (table2.classDeclaration == `class Foo`);
    assert (exists sc2 = table2.superClass,
        sc2 == `class Basic`);
    assert (table2.columns.size == 1);
    assert (exists col2 = table2.columns.first,
        col2 == `value Foo.name`);
    assert (exists name2 = table2.get(1)?.getValue(`value Foo.name`),
        "bar" == name2);
    
    assert (!tr.read() exists);
}

void testIsSubclassOf() {
    assert (isSubclassOf(`class Basic`, `class Object`));
    assert (!isSubclassOf(`class Object`, `class Basic`));
    assert (isSubclassOf(`class String`, `class Object`));
    assert (isSubclassOf(`class Integer`, `class Object`));
    assert (!isSubclassOf(`class Integer`, `class String`));
    assert (!isSubclassOf(`class String`, `class Integer`));
    assert (isSubclassOf(`class Foo`, `class Object`));
    assert (isSubclassOf(`class Foo`, `class Basic`));
}

void testDb() {
    value dbr = DbReader(`module com.github.tombentley.tabular`, LineReader(
            "# com.github.tombentley.tabular::Foo extends ceylon.language::Basic
             # <id>,name
             0,\"foo1\"
             1,\"foo2\"
             2,\"just foo\"
             # com.github.tombentley.tabular::Bar extends com.github.tombentley.tabular::Foo
             # <id>,blah
             0,\"blah1\"
             1,\"blah2\"
             ".iterator().next));
    value irefs = dbr.instanceRefs.sequence();
    assert (exists ref1 = irefs[0]);
    assert (0 == ref1[0]);
    assert (`Bar` == ref1[1]);
    
    assert (exists ref2 = irefs[1]);
    assert (1 == ref2[0]);
    assert (`Bar` == ref2[1]);
    
    assert (exists ref3 = irefs[2]);
    assert (2 == ref3[0]);
    assert (`Foo` == ref3[1]);
}
*/
