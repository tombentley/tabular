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
    Type,
    ClassOrInterface
}
import ceylon.collection {
    ArrayList,
    HashMap
}
import ceylon.language.serialization {
    Reference,
    serialization
}

abstract class DatumTokenType(shared actual String string)
        of dtAnd | dtOr | dtDot | dtComma | dtDColon | dtGt | dtLt | dtLSq | dtRSq | /*dtLParen | dtRParen |*/ dtDQuote | dtSQuote | dtPlus | dtMinus | dtHash | dtDollar | dtDigit | dtAlpha | dtEoi {}

object dtAnd extends DatumTokenType("&") {}
object dtOr extends DatumTokenType("|") {}
object dtDot extends DatumTokenType(".") {}
object dtComma extends DatumTokenType(",") {}
object dtDColon extends DatumTokenType("::") {}
object dtGt extends DatumTokenType(">") {}
object dtLt extends DatumTokenType("<") {}
object dtLSq extends DatumTokenType("[") {}
object dtRSq extends DatumTokenType("]") {}
//object dtLParen extends DatumTokenType("(") {}
//object dtRParen extends DatumTokenType(")") {}
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
            case ('[') {
                return Token(dtLSq, char.string, ii);
            }
            case (']') {
                return Token(dtRSq, char.string, ii);
            }
            /*case ('(') {
                return Token(dtLParen, char.string, ii);
            }
            case (')') {
                return Token(dtRParen, char.string, ii);
            }*/
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
 
       input ::= ::= value | meta
       value ::= string | character | number | byte | ref | array
       string ::= '\"' escapedCharacter* '\"'
       character ::= '\\'' escapedCharacter '\\''
       number ::= ('+'|'-') digits (('.') digits ('E' ('+'|'-') digits )?)?
       digits ::= ('0'-'9')*;
       byte ::= '#' hexDigit*
       
       array ::= '[' valueList? ']'
       valueList ::= value (',' value)*
 
       meta ::= package | declaration | model | application 
 
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
 """
class DatumParser(Map<Id,FundementalValueType|MetaValue> table) {
    shared FundementalValueType|MetaValue|Id[]|Id parse(String datum) {
        value tokenizer = DatumTokenizer(datum);
        return input(tokenizer);
    }
    FundementalValueType|MetaValue|Id[]|Id input(DatumTokenizer tokenizer) {
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
        case (dtLSq) {
            return array(tokenizer);
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
    
    Id identifier(DatumTokenizer tokenizer) {
        assert (tokenizer.current.type == dtAlpha
                    || tokenizer.current.type == dtDigit);
        value start = tokenizer.index;
        while (tokenizer.current.type == dtAlpha
                    || tokenizer.current.type == dtDigit) {
            tokenizer.consume();
        }
        return Id(tokenizer.input[start .. tokenizer.index - 1]);
    }
    
    MetaValue|Id[]|Id meta(DatumTokenizer tokenizer) {
        Id ident = identifier(tokenizer);
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
        /*case (dtLParen) {
            //application
            return application(ident, tokenizer);
        }*/
        else {
            throw Exception("unexpected token ``tokenizer.current``");
        }
        //return nothing;
    }
    
    Id checkLident(Id ident) {
        if (!(ident.string[0]?.lowercase else false)) {
            throw Exception("illegal package name component: ``ident``");
        }
        return ident;
    }
    
    Id lident(DatumTokenizer tokenizer) => checkLident(identifier(tokenizer));
    
    Package pkg(Id ident, DatumTokenizer tokenizer) {
        variable String pkgName = checkLident(ident).string; // XXX Wrong! and ident is not the same production as a member name
        variable Module? mod = null;
        assert (tokenizer.current.type == dtDot);
        while (tokenizer.current.type == dtDot) {
            tokenizer.consume();
            pkgName += "." + lident(tokenizer).string; // XXX Wrong! and ident is not the same production as a member name
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
    
    ClassDeclaration|ValueDeclaration member(Id pident, DatumTokenizer tokenizer) {
        assert (tokenizer.current.type == dtDColon);
        tokenizer.consume();
        assert (is Package pkg = table.get(pident));
        variable Package|ClassOrInterfaceDeclaration container = pkg;
        variable NestableDeclaration? nestable = null;
        while (true) {
            String name = identifier(tokenizer).string; // XXX Wrong! and ident is not the same production as a member name
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
        assert (is ClassDeclaration|ValueDeclaration n = nestable);
        return n;
    }
    
    "typeApplication ::= ident typeArgumentList"
    ClassOrInterface<Anything> typeApplication(Id ident, DatumTokenizer tokenizer) {
        assert (tokenizer.current.type == dtLt);
        value callable = table.get(ident);
        value tas = typeArgumentList(tokenizer);
        if (is FunctionDeclaration callable) {
            assert (false);
            //return callable.apply<Anything,Nothing>(*tas);
        } else if (is ClassDeclaration callable) {
            return callable.apply<Anything>(*tas);
        } else if (is GenericDeclaration callable) {
            throw Exception("unexpected kind of generic declaration ``callable``");
        } else {
            throw Exception("expected a generic declaration `` callable else "null" ``");
        }
    }
    "typeArgumentList ::= '<' ident (',' ident)* '>'"
    Type[] typeArgumentList(DatumTokenizer tokenizer) {
        assert (tokenizer.current.type == dtLt);
        value args = ArrayList<Type>();
        tokenizer.consume();
        args.add(toType(table.get(identifier(tokenizer))));
        while (tokenizer.current.type == dtComma) {
            tokenizer.consume();
            args.add(toType(table.get(identifier(tokenizer))));
        }
        return args.sequence();
    }
    
    Type toType(FundementalValueType|MetaValue? typeOrDeclaration) {
        Type t;
        if (is ClassOrInterfaceDeclaration typeOrDeclaration) {
            t = typeOrDeclaration.apply<Anything>();
        } else if (is Type typeOrDeclaration) {
            t = typeOrDeclaration;
        } else {
            assert (false);
        }
        return t;
    }
    
    Id[] array(DatumTokenizer tokenizer) {
        assert (tokenizer.current.type == dtLSq);
        tokenizer.consume();
        while (tokenizer.current.type != dtRSq) {
            // I know it's an Array. I'll need to know what it's an array of
            // then I can create the reference
            identifier(tokenizer);
        }
        return nothing;
    }
    
    /*"application ::= ident '(' argumentList? ')'"
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
            throw Exception("expected a function declaration, class declaration, or an applicable model: `` functional else "null" ``");
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
    }*/
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
    value ct = HashMap<Id,MetaValue>();
    value p = DatumParser(ct);
    assert (123 == (p.parse("+123") else die));
    assert (-1 == (p.parse("-1") else die));
    assert (0.5 == (p.parse("+0.5") else die));
    assert (0.0 == (p.parse("+0.0") else die));
    assert (-0.0 == (p.parse("-0.0") else die)); // TODO proper test for -0.0, Inf, -Inf, NaN
    assert (-1.0E1 == (p.parse("-1.0E1") else die));
    
    assert (#ff.byte == (p.parse("#ff") else die));
    assert (#ff.byte == (p.parse("#fff") else die));
    
    assert ("hello" == (p.parse("\"hello\"") else die));
    assert ("" == (p.parse("\"\"") else die));
    assert ("hello" == (p.parse("\"hello\"") else die));
    assert ("\"hello\"" == (p.parse("\"\\{#22}hello\\{#22}\"") else die));
    // TODO parsing characters
    
    // reference
    assert ("123a" == (p.parse("123a") else die));
    //package
    assert (`package ceylon.language` == (p.parse("ceylon.language") else die));
    
    ct.put(Id("1"), `package ceylon.language`);
    assert (`class String` == (p.parse("1::String") else die));
    assert (`function sequence` == (p.parse("1::sequence") else die));
    assert (`value null` == (p.parse("1::null") else die));
    // XXX do we want null or the ValueDeclaration of null?
    // compare: function application, where we get the value when we call () the function 
    assert (`value String.size` == (p.parse("1::String.size") else die));
    assert (`function String.trim` == (p.parse("1::String.trim") else die));
    assert (`value List.first` == (p.parse("`1::List.first") else die));
    ct.put(Id("2"), `String`);
    //ct.put(Id("3"), `function sequence`);
    //ct.put(Id("4"), `interface List`);
    ct.put(Id("5"), `class Entry`);
    ct.put(Id("6"), `Integer`);
    assert (`String->Integer` == (p.parse("5<2,6>") else die));
}

/*
shared interface Externalizable<Other> of Other
        given Other satisfies Externalizable<Other> {
    shared formal Factory<Other> factory();
}

Factory<Product>? externalize<Product>(Product p) {
    Factory<Anything>? f;
    if (is Package p) {
        f = PackageFactory(p.qualifiedName);
    } else if (is NestableDeclaration p) {
        assert (is Package pck = p.container);
        f = ToplevelDeclarationFactory<NestableDeclaration>(pck, p.name);
    } else if (is Value p) {
        f = ValueFactory(p);
    } else if (is Class p) {
        f = ClassFactory(p);
    } else if (is Externalizable<Product> p) {
        f = p.factory();
    } else {
        f = null;
    }
    assert (is Factory<Product>? f);
    return f;
}

shared class Example() satisfies Externalizable<Example> {
    shared actual Factory<Example> factory() {
        return ApplicableFactory(`Example`, []);
    }
}

shared interface Factory<out Product> {
    shared formal Product create();
}

shared serializable
class PackageFactory(String name) satisfies Factory<Package> {
    shared actual Package create() {
        return nothing;
    }
}
shared serializable
class ToplevelDeclarationFactory<Kind>(Package p, String name)
        satisfies Factory<Kind>
        given Kind satisfies NestableDeclaration {
    PackageFactory pf = PackageFactory(p.qualifiedName); //p.factory();
    shared actual Kind create() {
        assert (exists c = pf.create().getMember<Kind>(name));
        return c;
    }
}

shared serializable
class ValueFactory<CType>(Value<CType> c)
        satisfies Factory<Value<CType>> {
    ToplevelDeclarationFactory<ValueDeclaration> cdf = nothing; //c.factory()
    shared actual Value<CType> create() {
        return cdf.create().apply<CType>();
    }
}

shared interface TypeFactory<out Product>
        satisfies Factory<Product>
        given Product satisfies Type<Anything> {}

shared serializable
class TypeArgumentFactory(TypeFactory<Type<Anything>>[] t)
        satisfies Factory<Type<Anything>[]> {
    shared actual Type<Anything>[] create() => t*.create();
}

TypeArgumentFactory typeArgumentFactory(Generic g) {
    return TypeArgumentFactory(typeArguments(g));
}

shared serializable
class ClassFactory<CType,Arguments>(Class<CType,Arguments> c)
        satisfies TypeFactory<Class<CType,Arguments>>
        given Arguments satisfies Anything[] {
    ToplevelDeclarationFactory<ClassDeclaration> cdf = ToplevelDeclarationFactory(c.declaration.container, c.declatation.name); //c.factory()
    TypeArgumentFactory tpfs = typeArgumentFactory(c);
    shared actual Class<CType,Arguments> create() {
        return cdf.create().classApply<CType,Arguments>(*tpfs.create());
    }
}

shared serializable
class InterfaceFactory<CType>(Interface<CType> c)
        satisfies TypeFactory<Interface<CType>> {
    ToplevelDeclarationFactory<InterfaceDeclaration> cdf = nothing; //c.factory()
    TypeArgumentFactory tpfs = typeArgumentFactory(c);
    shared actual Interface<CType> create() {
        return cdf.create().interfaceApply<CType>(*tpfs.create());
    }
}

shared serializable
class ApplicableFactory<out Product>(Class<Product> c, Anything[] arguments)
        satisfies Factory<Product> {
    ClassFactory<Product,Anything[]> cf = nothing;
    shared actual Product create() {
        return cf.create().apply(*arguments);
    }
}
*/
