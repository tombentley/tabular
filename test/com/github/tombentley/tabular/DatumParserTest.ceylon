import ceylon.collection {
    HashMap
}
import ceylon.test {
    test,
    assertEquals,
    assertTrue,
    fail
}

shared class DatumParserTest() {
    // The ids would usually be gibberish, but we might as well make the 
    // mnemonic for the test
    value parser = DatumParser(HashMap {
            Id("cl")->`package ceylon.language`,
            Id("cc")->`package ceylon.collection`,
            Id("ct")->`package ceylon.test`,
            Id("cgtt")->`package com.github.tombentley.tabular`,
            Id("Character")->`class Character`,
            Id("Integer")->`class Integer`,
            Id("String")->`class String`,
            Id("Entry")->`class Entry`,
            Id("Tuple")->`class Tuple`,
            Id("List")->`interface List`,
            Id("ListInteger")->`List<Integer>`,
            Id("ListString")->`List<String>`,
            Id("ListCharacter")->`List<Character>`,
            Id("EntryIntegerInteger")->`Entry<Integer,Integer>`
        });
    
    shared test
    void parseCharacter() {
        assertEquals('h', parser.parse("'h'"));
        assertEquals('\"', parser.parse("'\\{#22}'"));
        try {
            parser.parse("''");
            fail("empty char");
        } catch (Exception e) {
            assertEquals("empty quoted character", e.message);
        }
    }
    
    shared test
    void parseString() {
        assertEquals("hello", parser.parse("\"hello\""));
        assertEquals("", parser.parse("\"\""));
        assertEquals("\"hello\"", parser.parse("\"\\{#22}hello\\{#22}\""));
    }
    
    shared test
    void parseInteger() {
        assertEquals(123, parser.parse("+123"));
        assertEquals(-1, parser.parse("-1"));
        assertEquals(0, parser.parse("+0"));
        assertEquals(0, parser.parse("-0"));
        // TODO max and min integer
    }
    
    shared test
    void parseFloat() {
        assertEquals(0.5, parser.parse("+0.5"));
        assertEquals(-0.5, parser.parse("-0.5"));
        assertEquals(0.0, parser.parse("+0.0"));
        assert (is Float mz = parser.parse("-0.0"));
        assertEquals(0.0, mz);
        assertTrue(mz.strictlyNegative);
        assertEquals(-1.0E1, parser.parse("-1.0E1"));
        assertEquals(-1.0E-1, parser.parse("-1.0E-1"));
        assertEquals(infinity, parser.parse("+Inf"));
        assertEquals(-infinity, parser.parse("-Inf"));
        assert (is Float nan = parser.parse("+NaN"));
        assertTrue(nan.undefined);
    }
    
    shared test
    void parseByte() {
        assertEquals(#f.byte, parser.parse("#f"));
        assertEquals(#ff.byte, parser.parse("#ff"));
        try {
            parser.parse("#");
            fail();
        } catch (Exception e) {
            assertEquals("invalid byte literal: expected two or two hex digits", e.message);
        }
        try {
            parser.parse("#fff");
            fail();
        } catch (Exception e) {
            assertEquals("invalid byte literal: expected two or two hex digits", e.message);
        }
    }
    
    shared test
    void parseId() {
        assertEquals(Id("1"), parser.parse("1"));
        assertEquals(Id("a"), parser.parse("a"));
        assertEquals(Id("A"), parser.parse("A"));
        assertEquals(Id("123a"), parser.parse("123a"));
        assertEquals(Id("ceylon"), parser.parse("ceylon"));
    }
    
    shared test
    void parsePackage() {
        assertEquals(`package ceylon.language`, parser.parse("ceylon.language"));
        assertEquals(`package ceylon.test`, parser.parse("ceylon.test"));
        assertEquals(`package com.github.tombentley.tabular`, parser.parse("com.github.tombentley.tabular"));
    }
    
    shared test
    void parseClassOrInterfaceDeclaration() {
        assertEquals(`class String`, parser.parse("cl::String"));
        assertEquals(`class Entry`, parser.parse("cl::Entry"));
        assertEquals(`interface List`, parser.parse("cl::List"));
        assertEquals(`class Tuple`, parser.parse("cl::Tuple"));
        try {
            parser.parse("cgtt::String");
        } catch (AssertionError e) {
            // TODO assertEquals("", e.message);
        }
        assertEquals(`class DatumParserTest`, parser.parse("cgtt::DatumParserTest"));
    }
    
    shared test
    void parseClassModel() {
        assertEquals(`Entry<String,String>`, parser.parse("Entry<String,String>"));
    }
    
    shared test
    void parseInterfaceModel() {
        assertEquals(`List<String>`, parser.parse("List<String>"));
    }
    
    shared test
    void parseMemberClassModel() {
        throw; // TODO 
    }
    
    shared test
    void parseUnion() {
        assertEquals(`List<Integer>|Entry<Integer,Integer>`, parser.parse("ListInteger|EntryIntegerInteger"));
        assertEquals(`Integer|String|Character`, parser.parse("Integer|String|Character"));
    }
    
    shared test
    void parseIntersection() {
        assertEquals(`List<Integer>&Entry<Integer,Integer>`, parser.parse("ListInteger&EntryIntegerInteger"));
        assertEquals(`List<Integer>&List<String>`, parser.parse("ListInteger&ListString"));
        assertEquals(`List<Integer>&List<String>&List<Character>`, parser.parse("ListInteger&ListString&ListCharacter"));
    }
}
