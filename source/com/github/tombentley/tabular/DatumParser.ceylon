import ceylon.language.meta {
    modules
}
import ceylon.language.meta.declaration {
    Package,
    Module,
    ClassDeclaration,
    ClassOrInterfaceDeclaration,
    FunctionDeclaration,
    ValueDeclaration,
    InterfaceDeclaration,
    GenericDeclaration,
    NestableDeclaration,
    FunctionalDeclaration
}
import ceylon.language.meta.model {
    Applicable,
    Generic,
    Class,
    Function,
    Value,
    Interface,
    Type
}
import ceylon.collection {
    ArrayList
}
import ceylon.language.serialization {
    Reference,
    serialization
}

abstract class DatumTokenType(shared actual String string)
        of dtAnd | dtOr | dtDot | dtComma | dtDColon | dtGt | dtLt | dtLParen | dtRParen | dtDQuote | dtSQuote | dtPlus | dtMinus | dtHash | dtDollar | dtDigit | dtAlpha | dtEoi {}

object dtAnd extends DatumTokenType("&") {}
object dtOr extends DatumTokenType("|") {}
object dtDot extends DatumTokenType(".") {}
object dtComma extends DatumTokenType(",") {}
object dtDColon extends DatumTokenType("::") {}
object dtGt extends DatumTokenType(">") {}
object dtLt extends DatumTokenType("<") {}
object dtLParen extends DatumTokenType("(") {}
object dtRParen extends DatumTokenType(")") {}
object dtDQuote extends DatumTokenType("\"") {}
object dtSQuote extends DatumTokenType("'") {}
object dtPlus extends DatumTokenType("+") {}
object dtMinus extends DatumTokenType("-") {}
object dtHash extends DatumTokenType("#") {}
object dtDollar extends DatumTokenType("$") {}
object dtDigit extends DatumTokenType("digit") {}
object dtAlpha extends DatumTokenType("alpha") {}
object dtEoi extends DatumTokenType("<eoi>") {}

"The tokenizer used by [[DatumParser]]."
class DatumTokenizer(input) {
    "The input stream that we're tokenizing."
    shared String input;
    
    "Our index into the input."
    variable value ii = 0;
    Token at(Integer index) {
        if (exists char = input[ii]) {
            switch (char)
            case ('&') {
                return Token(dtAnd, char.string, ii);
            }
            case ('|') {
                return Token(dtOr, char.string, ii);
            }
            case ('.') {
                return Token(dtDot, char.string, ii);
            }
            case (',') {
                return Token(dtComma, char.string, ii);
            }
            case ('<') {
                return Token(dtLt, char.string, ii);
            }
            case ('>') {
                return Token(dtGt, char.string, ii);
            }
            case ('(') {
                return Token(dtLParen, char.string, ii);
            }
            case (')') {
                return Token(dtRParen, char.string, ii);
            }
            case ('"') {
                return Token(dtDQuote, char.string, ii);
            }
            case ('\'') {
                return Token(dtSQuote, char.string, ii);
            }
            case ('+') {
                return Token(dtPlus, char.string, ii);
            }
            case ('-') {
                return Token(dtMinus, char.string, ii);
            }
            case ('#') {
                return Token(dtHash, char.string, ii);
            }
            case ('$') {
                return Token(dtDollar, char.string, ii);
            }
            case (':') {
                // check next is also :
                if (exists char2 = input[ii + 1]) {
                    if (char2 == ':') {
                        return Token(dtDColon, input[ii:2], ii);
                    } else {
                        throw Exception("tokenization error, expected ::, not :``char2`` at index ``ii``");
                    }
                }
                throw Exception("unexpected end of input");
            }
            else {
                if ('0' <= char <= '9') {
                    return Token(dtDigit, char.string, ii);
                } else if ('a' <= char <= 'z'
                            || 'A' <= char <= 'Z') {
                    return Token(dtAlpha, char.string, ii);
                } else {
                    throw Exception("unexpected character ``char`` at index ``ii``");
                }
            }
        } else {
            return Token(dtEoi, "", ii);
        }
    }
    variable Token current_ = at(0);
    
    "The current token."
    shared Token current {
        return current_;
    }
    
    "Consume the current token, moving on to the next token."
    shared void consume() {
        ii += current_.token.size;
        current_ = at(index);
    }
    
    "The index of the current token in the input."
    shared Integer index => ii;
}
//TODO union and intersection types (required for type arguments)
"""
   A parser for "datums", the values store in a [[ValueTable]] as 
   emitted by [[ValueTableWriter]] and read by [[ValueTableReader]]. 
   The following grammar is parsed: 
 
       input ::= constant
       constant ::= string | character | number | byte | meta
       string ::= '\"' escapedCharacter* '\"'
       character ::= '\\'' escapedCharacter '\\''
       number ::= ('+'|'-') digits (('.') digits ('E' ('+'|'-') digits )?)?
       digits ::= ('0'-'9')*;
       byte ::= '#' hexDigit*
 
       meta ::= package | declaration | model | application | ref
 
       package ::= ident ('.' ident)*;
       ref ::= ident
       declaration ::= ident '::' declarationMember
       declarationMember ::= ident ('.' ident)*
 
       model ::= typeApplication
       typeApplication ::= ident '<' typeArgumentList? '>'
       typeArgumentList ::= type (',' type)*
       type ::= intersectionType;
       intersectionType ::= unionType ('&' unionType)*
       unionType ::= model ('&' model)* 
 
       application ::= ident '(' argumentList? ')'
       argumentList ::= ident (',' ident)*
 """
class DatumParser(Map<Id,String> table) {
    shared Anything input(String input) {
        value tokenizer = DatumTokenizer(input);
        return constant(tokenizer);
    }
    Anything constant(DatumTokenizer tokenizer) {
        value ct = tokenizer.current.type;
        switch (ct)
        case (dtDQuote) {
            return str(tokenizer);
        }
        case (dtSQuote) {
            return char(tokenizer);
        }
        case (dtPlus, dtMinus) {
            return number(tokenizer);
        }
        case (dtHash) {
            return byte(tokenizer);
        }
        case (dtDigit, dtAlpha) {
            return meta(tokenizer);
        }
        else {
            throw Exception("unexpected token ``tokenizer.current``");
        }
    }
    "string ::= '\\\"' escapedCharacter* '\\\"'"
    String str(DatumTokenizer tokenizer) {
        assert (tokenizer.current.type == dtDQuote);
        //tokenizer.consume();
        value start = tokenizer.index + 1;
        if (exists end = tokenizer.input[start...].firstOccurrence('\"')) {
            return end > start then unquoteString(tokenizer.input[start..end]) else "";
        } else {
            throw Exception("unterminated string: starting at ``start``");
        }
        // TODO the tokenizer state is now fucked
    }
    "character ::= '\\\\'' escapedCharacter '\\\\''"
    Character char(DatumTokenizer tokenizer) {
        assert (tokenizer.current.type == dtSQuote);
        //tokenizer.consume();
        value start = tokenizer.index + 1;
        if (exists end = tokenizer.input[start...].firstOccurrence('\'')) {
            if (exists unquoted = unquoteCharacter(tokenizer.input[start .. end - 1])) {
                return unquoted;
            } else {
                throw Exception("invalid quoted character: ``tokenizer.input[start .. end - 1]``");
            }
        } else {
            throw Exception("unterminated character: starting at ``start``");
        }
        // TODO the tokenizer state is now fucked
    }
    "number ::= ('+'|'-') digits (('.') digits ('E' ('+'|'-')? digits )?)?"
    Integer|Float number(DatumTokenizer tokenizer) {
        Integer start = tokenizer.index;
        Boolean plus;
        if (tokenizer.current.type == dtPlus) {
            plus = true;
        } else if (tokenizer.current.type == dtMinus) {
            plus = false;
        } else {
            assert (false);
        }
        tokenizer.consume();
        
        if (tokenizer.current.type != dtDigit) {
            throw Exception("expected digit following `` plus then "+" else "-" `` but found ``tokenizer.current``");
        }
        while (tokenizer.current.type == dtDigit) {
            tokenizer.consume();
        }
        
        if (tokenizer.current.type == dtDot) {
            tokenizer.consume();
            while (tokenizer.current.type == dtDigit) {
                tokenizer.consume();
            }
            if (tokenizer.current.type == dtAlpha
                        && tokenizer.current.token in "eE") {
                tokenizer.consume();
                if (tokenizer.current.type == dtPlus || tokenizer.current.type == dtMinus) {
                    tokenizer.consume();
                }
                if (tokenizer.current.type != dtDigit) {
                    throw Exception("expected digit in exponent but found ``tokenizer.current``");
                }
                while (tokenizer.current.type == dtDigit) {
                    tokenizer.consume();
                }
            }
            // TODO +Inf, -Inf, NaN
            "invalid float"
            assert (exists float = parseFloat(tokenizer.input[start..tokenizer.index]));
            return float;
        } else {
            "invalid integer" // should be impossible
            assert (exists int = parseInteger(tokenizer.input[start..tokenizer.index]));
            return int;
        }
    }
    "byte ::= '#' hexDigit*"
    Byte byte(DatumTokenizer tokenizer) {
        assert (tokenizer.current.type == dtHash);
        tokenizer.consume();
        Integer start = tokenizer.index;
        while (tokenizer.current.type == dtDigit
                    || (tokenizer.current.type == dtAlpha && tokenizer.current.token in "abcdefABCDEF")) {
            tokenizer.consume();
        }
        "invalid byte" // should be impossible
        assert (exists int = parseInteger(tokenizer.input[start..tokenizer.index], 16));
        return int.byte;
    }
    
    String identifier(DatumTokenizer tokenizer) {
        assert (tokenizer.current.type == dtAlpha
                    || tokenizer.current.type == dtDigit);
        value start = tokenizer.index;
        while (tokenizer.current.type == dtAlpha
                    || tokenizer.current.type == dtDigit) {
            tokenizer.consume();
        }
        return tokenizer.input[start .. tokenizer.index - 1];
    }
    
    Anything meta(DatumTokenizer tokenizer) {
        String ident = identifier(tokenizer);
        switch (tokenizer.current.type)
        case (dtEoi) {
            // plain ident, though actually ambiguous wrt a package name of one component
            // TODO lookup in some context
            return ident;
        }
        case (dtDot) {
            //package name
            return pkg(ident, tokenizer);
        }
        case (dtDColon) {
            // declaration
            return member(ident, tokenizer);
        }
        case (dtLt) {
            //model
            // XXX not all model things are generic, e.g. value
            return typeApplication(ident, tokenizer);
        }
        case (dtLParen) {
            //application
            return application(ident, tokenizer);
        }
        else {
            throw Exception("unexpected token ``tokenizer.current``");
        }
        //return nothing;
    }
    
    String checkLident(String ident) {
        if (!(ident[0]?.lowercase else false)) {
            throw Exception("illegal package name component: ``ident``");
        }
        return ident;
    }
    
    String lident(DatumTokenizer tokenizer) => checkLident(identifier(tokenizer));
    
    Package pkg(String ident, DatumTokenizer tokenizer) {
        variable String pkgName = checkLident(ident);
        variable Module? mod = null;
        assert (tokenizer.current.type == dtDot);
        while (tokenizer.current.type == dtDot) {
            tokenizer.consume();
            pkgName += "." + lident(tokenizer);
            for (m in modules.list) {
                if (m.name == pkgName) {
                    mod = m;
                    break;
                }
            }
        }
        if (exists m = mod) {
            if (exists p = m.findPackage(pkgName)) {
                return p;
            } else {
                throw Exception("cannot find package ``pkgName`` in module ``m.name``");
            }
        } else {
            throw Exception("cannot find module for package ``pkgName``");
        }
    }
    
    NestableDeclaration member(String pident, DatumTokenizer tokenizer) {
        assert (tokenizer.current.type == dtDColon);
        tokenizer.consume();
        assert (is Package pkg = table.get(pident));
        variable Package|ClassOrInterfaceDeclaration container = pkg;
        variable NestableDeclaration? nestable = null;
        while (true) {
            String name = identifier(tokenizer);
            if (is Package p = container) {
                nestable = p.getMember<NestableDeclaration>(name);
            } else if (is ClassOrInterfaceDeclaration c = container) {
                nestable = c.getMemberDeclaration<NestableDeclaration>(name);
            } else {
                assert (false);
            }
            assert (exists n = nestable);
            if (is ClassOrInterfaceDeclaration n) {
                container = n;
            }
            if (tokenizer.current.type != dtDot) {
                break;
            } else {
                tokenizer.consume();
            }
        }
        assert (exists n = nestable);
        return n;
    }
    
    "typeApplication ::= ident typeArgumentList"
    Generic typeApplication(String ident, DatumTokenizer tokenizer) {
        assert (tokenizer.current.type == dtLt);
        value callable = table.get(ident);
        value tas = typeArgumentList(tokenizer);
        if (is FunctionDeclaration callable) {
            return callable.apply<Anything,Nothing>(*tas);
        } else if (is ClassDeclaration callable) {
            return callable.apply<Anything>(*tas);
        } else if (is GenericDeclaration callable) {
            throw Exception("unexpected kind of generic declaration ``callable``");
        } else {
            throw Exception("expected a generic declaration ``callable``");
        }
    }
    "typeArgumentList ::= '<' ident (',' ident)* '>'"
    Type[] typeArgumentList(DatumTokenizer tokenizer) {
        assert (tokenizer.current.type == dtLt);
        value args = ArrayList<Type>();
        tokenizer.consume();
        assert (is Type t = table.get(identifier(tokenizer)));
        args.add(t);
        while (tokenizer.current.type == dtComma) {
            tokenizer.consume();
            assert (is Type t2 = table.get(identifier(tokenizer)));
            args.add(t2);
        }
        return args.sequence();
    }
    "application ::= ident '(' argumentList? ')'"
    Anything application(String ident, DatumTokenizer tokenizer) {
        assert (tokenizer.current.type == dtLParen);
        value functional = table.get(ident);
        Anything[] arguments = argumentList(tokenizer);
        if (is FunctionDeclaration functional) {
            return functional.invoke([], *arguments);
        } else if (is ClassDeclaration functional) {
            return functional.instantiate([], *arguments);
        } else if (is Applicable functional) {
            return functional.apply(*arguments);
        } else {
            throw Exception("expected a function declaration, class declaration, or an applicable model: ``functional``");
        }
    }
    "argumentList ::= '(' ident (',' ident)* ')'"
    Anything[] argumentList(DatumTokenizer tokenizer) {
        assert (tokenizer.current.type == dtLt);
        value args = ArrayList<Anything>();
        tokenizer.consume();
        args.add(table.get(identifier(tokenizer)));
        while (tokenizer.current.type == dtComma) {
            tokenizer.consume();
            args.add(table.get(identifier(tokenizer)));
        }
        return args.sequence();
    }
    /*
    Generic typeApply(GenericDeclaration g, DatumTokenizer tokenizer) {
        value tas = typeArguments(tokenizer);
        if (is FunctionDeclaration g) {
            return g.apply(*tas);
        } else if (is ClassOrInterfaceDeclaration g) {
            return g.apply(*tas);
        }
        throw Exception(g.string);
    }
    
    
     */
}

void testDatumParser() {
    object die {}
    value sc = serialization();
    value alloc = IdAllocator();
    Reference<Object?> enlist(Anything instance) => sc.reference(alloc.allocateId(instance of Object?), instance of Object?);
    value ct = ValueTable(alloc, enlist);
    value p = DatumParser(ct);
    assert (123 == (p.input("+123") else die));
    assert (-1 == (p.input("-1") else die));
    assert (0.5 == (p.input("+0.5") else die));
    assert (0.0 == (p.input("+0.0") else die));
    assert (-0.0 == (p.input("-0.0") else die)); // TODO proper test for -0.0, Inf, -Inf, NaN
    assert (-1.0E1 == (p.input("-1.0E1") else die));
    
    assert (#ff.byte == (p.input("#ff") else die));
    assert (#ff.byte == (p.input("#fff") else die));
    
    assert ("hello" == (p.input("\"hello\"") else die));
    assert ("" == (p.input("\"\"") else die));
    assert ("hello" == (p.input("\"hello\"") else die));
    assert ("\"hello\"" == (p.input("\"\\{#22}hello\\{#22}\"") else die));
    // TODO parsing characters
    
    // reference
    assert ("123a" == (p.input("123a") else die));
    //package
    assert (`package ceylon.language` == (p.input("ceylon.language") else die));
    
    String cl = ct.add(`package ceylon.language`);
    assert (`class String` == (p.input("``cl``::String") else die));
    assert (`function sequence` == (p.input("``cl``::sequence") else die));
    assert (`value null` == (p.input("``cl``::null") else die));
    // XXX do we want null or the ValueDeclaration of null?
    // compare: function application, where we get the value when we call () the function 
    assert (`value String.size` == (p.input("``cl``::String.size") else die));
    assert (`function String.trim` == (p.input("``cl``::String.trim") else die));
    assert (`value List.first` == (p.input("``cl``::List.first") else die));
    value stringId = ct.add(`String`);
    value sequenceId = ct.add(`function sequence`);
    value listId = ct.add(`interface List`);
    value entryId = ct.add(`class Entry`);
    value integerId = ct.add(`Integer`);
    assert (`String->Integer` == (p.input("``entryId``<``stringId``,``integerId``>") else die));
}
