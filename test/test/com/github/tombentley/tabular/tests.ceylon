import ceylon.test {
    test,
    assertEquals,
    assertTrue,
    fail
}
import com.github.tombentley.tabular {
    TabularSerializer,
    TabularDeserializer
}
import test.com.github.tombentley.tabular.person {
    ...
}

serializable
class StringWrapper(shared String val) {
    shared actual String string => val.string;
}
"that we can round trip a class containing a string"
shared test
void testStringWrapper() {
    
    value ser = TabularSerializer();
    ser.add(StringWrapper("foo"));
    value serialized = ser.write();
    print(serialized);
    value deser = TabularDeserializer(`module test.com.github.tombentley.tabular`, serialized);
    value deserialized = deser.select(`StringWrapper`).sequence();
    assertEquals(1, deserialized.size);
    assert (exists i = deserialized[0]);
    assertEquals("foo", i.val);
}

serializable
class IntegerWrapper(shared Integer val) {
    shared actual String string => val.string;
}
"that we can round trip a class containing a integer"
shared test
void testIntegerWrapper() {
    
    value ser = TabularSerializer();
    ser.add(IntegerWrapper(42));
    value serialized = ser.write();
    print(serialized);
    value deser = TabularDeserializer(`module test.com.github.tombentley.tabular`, serialized);
    value deserialized = deser.select(`IntegerWrapper`).sequence();
    assertEquals(1, deserialized.size);
    assert (exists i = deserialized[0]);
    assertEquals(42, i.val);
}
serializable
class ByteWrapper(shared Byte val) {
    shared actual String string => val.string;
}
"that we can round trip a class containing a byte"
shared test
void testByteWrapper() {
    
    value ser = TabularSerializer();
    ser.add(ByteWrapper(42.byte));
    value serialized = ser.write();
    print(serialized);
    value deser = TabularDeserializer(`module test.com.github.tombentley.tabular`, serialized);
    value deserialized = deser.select(`ByteWrapper`).sequence();
    assertEquals(1, deserialized.size);
    assert (exists i = deserialized[0]);
    assertEquals(42.byte, i.val);
}
serializable
class FloatWrapper(shared Float val) {
    shared actual String string => val.string;
}
"that we can round trip a class containing a float"
shared test
void testFloatWrapper() {
    
    value ser = TabularSerializer();
    ser.add(FloatWrapper(42.0));
    value serialized = ser.write();
    print(serialized);
    value deser = TabularDeserializer(`module test.com.github.tombentley.tabular`, serialized);
    value deserialized = deser.select(`FloatWrapper`).sequence();
    assertEquals(1, deserialized.size);
    assert (exists i = deserialized[0]);
    assertEquals(42.0, i.val);
}
serializable
class CharacterWrapper(shared Character val) {
    shared actual String string => val.string;
}
"that we can round trip a class containing a character"
shared test
void testCharacterWrapper() {
    
    value ser = TabularSerializer();
    ser.add(CharacterWrapper('\{:-)}'));
    value serialized = ser.write();
    print(serialized);
    value deser = TabularDeserializer(`module test.com.github.tombentley.tabular`, serialized);
    value deserialized = deser.select(`CharacterWrapper`).sequence();
    assertEquals(1, deserialized.size);
    assert (exists i = deserialized[0]);
    assertEquals('\{:-)}', i.val);
    //TODO quotable characters
}
serializable
class BooleanWrapper(shared Boolean val) {
    shared actual String string => val.string;
}
"that we can round trip a class containing a character"
shared test
void testBooleanWrapper() {
    
    value ser = TabularSerializer();
    ser.add(BooleanWrapper(true));
    value serialized = ser.write();
    print(serialized);
    value deser = TabularDeserializer(`module test.com.github.tombentley.tabular`, serialized);
    value deserialized = deser.select(`BooleanWrapper`).sequence();
    assertEquals(1, deserialized.size);
    assert (exists i = deserialized[0]);
    assertTrue(i.val);
}
serializable
class ComparisonWrapper(shared Comparison val) {
    shared actual String string => val.string;
}
"that we can round trip a class containing a Comparison"
shared test
void testComparisonWrapper() {
    
    value ser = TabularSerializer();
    ser.add(ComparisonWrapper(smaller));
    value serialized = ser.write();
    print(serialized);
    value deser = TabularDeserializer(`module test.com.github.tombentley.tabular`, serialized);
    value deserialized = deser.select(`ComparisonWrapper`).sequence();
    assertEquals(1, deserialized.size);
    assert (exists i = deserialized[0]);
    assertEquals(smaller, i.val);
}
serializable
class GenericWrapper<Value>(shared Value? val)
        given Value satisfies Object {
    shared actual String string => val?.string else "null";
}
"that we can round trip a generic class"
shared test
void testGenericWrapper() {
    
    value ser = TabularSerializer();
    ser.add(GenericWrapper(42));
    value serialized = ser.write();
    print(serialized);
    value deser = TabularDeserializer(`module test.com.github.tombentley.tabular`, serialized);
    value deserialized = deser.select(`GenericWrapper<Integer>`).sequence();
    assertEquals(1, deserialized.size);
    assert (exists i = deserialized[0]);
    assertEquals(42, i.val);
    assertTrue(deser.select(`GenericWrapper<String>`).size == 0);
}
"that we can round trip a union as a type argument"
shared test
void testGenericWrapperUnion() {
    value ser = TabularSerializer();
    ser.add(GenericWrapper<String|Integer>(42));
    value serialized = ser.write();
    print(serialized);
    value deser = TabularDeserializer(`module test.com.github.tombentley.tabular`, serialized);
    variable value deserialized = deser.select(`GenericWrapper<Integer|String>`).sequence();
    assertEquals(1, deserialized.size);
    assert (exists i = deserialized[0]);
    assertEquals(42, i.val);
    
    deserialized = deser.select(`GenericWrapper<String|Integer>`).sequence();
    assertEquals(1, deserialized.size);
    assert (exists i2 = deserialized[0]);
    assertEquals(42, i2.val);
}

interface IfaceFoo {}
serializable
class Foo() satisfies IfaceFoo {}
interface IfaceBar {}
serializable
class Bar() satisfies IfaceBar {}
serializable
class FooBar() satisfies IfaceFoo & IfaceBar {}
"that we can round trip an intersection as a type argument"
shared test
void testGenericWrapperIntersection() {
    
    value ser = TabularSerializer();
    ser.add(GenericWrapper<IfaceFoo&IfaceBar>(null));
    value serialized = ser.write();
    print(serialized);
    value deser = TabularDeserializer(`module test.com.github.tombentley.tabular`, serialized);
    variable value deserialized = deser.select(`GenericWrapper<IfaceFoo&IfaceBar>`).sequence();
    assertEquals(1, deserialized.size);
    assert (exists i = deserialized[0]);
    assertTrue(!i.val exists);
    
    deserialized = deser.select(`GenericWrapper<IfaceBar&IfaceFoo>`).sequence();
    assertEquals(1, deserialized.size);
    assert (exists i2 = deserialized[0]);
    assertTrue(!i2.val exists);
}
"that we can round trip Nothing as a type argument"
shared test
void testGenericWrapperNothing() {
    
    value ser = TabularSerializer();
    ser.add(GenericWrapper<Nothing>(null));
    value serialized = ser.write();
    print(serialized);
    value deser = TabularDeserializer(`module test.com.github.tombentley.tabular`, serialized);
    value deserialized = deser.select(`GenericWrapper<Nothing>`).sequence();
    assertEquals(1, deserialized.size);
    assert (exists i = deserialized[0]);
    assertEquals(null, i.val);
}

serializable
class GenericWrapperSub(String s) extends GenericWrapper<String>(s) {
}

"that we don't include type arguments in rows of tables for generic classes 
 when the instance is an instance of a non-generic subclass (i.e. the subclass
 has supplied the type argument)."
shared test
void testTypeArgumentsOmittedForUnparameterizedConcreteClass() {
    value ser = TabularSerializer();
    ser.add(GenericWrapperSub("foo"));
    ser.add(GenericWrapper<String>("bar"));
    value serialized = ser.write();
    print(serialized);
    value deser = TabularDeserializer(`module test.com.github.tombentley.tabular`, serialized);
    value deserialized = deser.select(`GenericWrapperSub`).sequence();
    assertEquals(1, deserialized.size);
    assert (exists i = deserialized[0]);
    assertEquals("foo", i.val);
    assertEquals("""## META
                    1,ceylon.language
                    2,1::String
                    3,test.com.github.tombentley.tabular
                    4,3::GenericWrapper
                    5,3::GenericWrapperSub
                    6,4<2>
                    # 4
                    # =id,<Value>,val
                    0,,"foo"
                    7,2,"bar"
                    # 5 extends 6
                    # =id
                    0
                    """, serialized);
}

"that when we have an abstract generic class we don't bother with tp columns 
 for that class at all, since the tas must be supplied by the subclasses"
abstract serializable
class AbstractGeneric<out X>() {}
serializable
class ConcreteNonGeneric() extends AbstractGeneric<String>() {}
serializable
class ConcreteGeneric<Y>() extends AbstractGeneric<Y>() {}

shared test
void testTypeParametersOmittedFromAbstractGeneric() {
    value ser = TabularSerializer();
    ser.add(ConcreteNonGeneric());
    ser.add(ConcreteGeneric<Integer>());
    value serialized = ser.write();
    print(serialized);
    value deser = TabularDeserializer(`module test.com.github.tombentley.tabular`, serialized);
    value deserialized = deser.select(`AbstractGeneric<Anything>`).sequence();
    assertEquals(2, deserialized.size);
    // check that the table for AbstractGeneric lacks a column for <X>
    assertEquals("""## META
                    1,ceylon.language
                    2,1::String
                    3,test.com.github.tombentley.tabular
                    4,3::AbstractGeneric
                    5,3::ConcreteNonGeneric
                    6,4<2>
                    8,1::Integer
                    9,3::ConcreteGeneric
                    A,4<8>
                    # @ 4
                    # =id
                    0
                    7
                    # 5 extends 6
                    # =id
                    0
                    # 9 extends A
                    # =id,<Y>
                    7,8
                    """, serialized);
}

"that we can round trip a Singleton"
shared test
void testSingleton() {
    value ser = TabularSerializer();
    ser.add(Singleton(true));
    value serialized = ser.write();
    print(serialized);
    value deser = TabularDeserializer(`module test.com.github.tombentley.tabular`, serialized);
    value deserialized = deser.select(`Singleton<Boolean>`).sequence();
    assertEquals(1, deserialized.size);
    assert (exists i = deserialized[0]);
    assertTrue(i.first);
}

"that we can round trip a ArraySequence"
shared test
void testArraySequence() {
    value ser = TabularSerializer();
    ser.add(sequence({ true, "hello", 42 }));
    value serialized = ser.write();
    print(serialized);
    value deser = TabularDeserializer(`module test.com.github.tombentley.tabular`, serialized);
    value deserialized = deser.select(`ArraySequence<Boolean|String|Integer>`).sequence();
    assertEquals(1, deserialized.size);
    assert (exists i = deserialized[0]);
    assertEquals(true, i[0]);
    assertEquals("hello", i[1]);
    assertEquals(42, i[2]);
}

"that we can round trip a Measure"
shared test
void testMeasure() {
    value ser = TabularSerializer();
    ser.add(1:10);
    value serialized = ser.write();
    print(serialized);
    value deser = TabularDeserializer(`module test.com.github.tombentley.tabular`, serialized);
    value deserialized = deser.select(`Range<Integer>`).sequence();
    assertEquals(1, deserialized.size);
    assert (exists i = deserialized[0]);
    assertEquals(1:10, i);
}

"that we can round trip a Span"
shared test
void testSpan() {
    value ser = TabularSerializer();
    ser.add(45..54);
    value serialized = ser.write();
    print(serialized);
    value deser = TabularDeserializer(`module test.com.github.tombentley.tabular`, serialized);
    value deserialized = deser.select(`Range<Integer>`).sequence();
    assertEquals(1, deserialized.size);
    assert (exists i = deserialized[0]);
    assertEquals(45..54, i);
}

"that we can round trip a Tuple"
shared test
void testTuple() {
    value ser = TabularSerializer();
    ser.add(["hello", 42, smaller]);
    value serialized = ser.write();
    print(serialized);
    value deser = TabularDeserializer(`module test.com.github.tombentley.tabular`, serialized);
    value deserialized = deser.select(`[String, Integer, Comparison]`).sequence();
    assertEquals(1, deserialized.size);
    assert (exists i = deserialized[0]);
    assertEquals(["hello", 42, smaller], i);
}
shared test
void testTupleRangeTail() {
    value ser = TabularSerializer();
    ser.add(["hello", 42, *(1..3)]);
    value serialized = ser.write();
    print(serialized);
    value deser = TabularDeserializer(`module test.com.github.tombentley.tabular`, serialized);
    value deserialized = deser.select(`[String, Integer, Range<Integer>]`).sequence();
    assertEquals(1, deserialized.size);
    assert (exists i = deserialized[0]);
    assertEquals(["hello", 42, *(1..3)], i);
}
"that we can round trip an Array<Integer>"
shared test
void testArrayOfInteger() {
    value ser = TabularSerializer();
    ser.add(arrayOfSize<Integer>(1, 42));
    value serialized = ser.write();
    print(serialized);
    value deser = TabularDeserializer(`module test.com.github.tombentley.tabular`, serialized);
    value deserialized = deser.select(`Array<Integer>`).sequence();
    assertEquals(1, deserialized.size);
    assert (exists i = deserialized[0]);
    assertEquals(arrayOfSize<Integer>(1, 42), i);
}
"that we can round trip an Array<Character>"
shared test
void testArrayOfCharacter() {
    value ser = TabularSerializer();
    ser.add(arrayOfSize<Character>(1, '\{:-)}'));
    value serialized = ser.write();
    print(serialized);
    value deser = TabularDeserializer(`module test.com.github.tombentley.tabular`, serialized);
    value deserialized = deser.select(`Array<Character>`).sequence();
    assertEquals(1, deserialized.size);
    assert (exists i = deserialized[0]);
    assertEquals(arrayOfSize<Character>(1, '\{:-)}'), i);
}
"that we can round trip an Array<Boolean>"
shared test
void testArrayOfBoolean() {
    value ser = TabularSerializer();
    ser.add(Array<Boolean> { true, false });
    value serialized = ser.write();
    print(serialized);
    value deser = TabularDeserializer(`module test.com.github.tombentley.tabular`, serialized);
    value deserialized = deser.select(`Array<Boolean>`).sequence();
    assertEquals(1, deserialized.size);
    assert (exists i = deserialized[0]);
    assertEquals(Array<Boolean> { true, false }, i);
}
"that we can round trip an Array that references itself"
shared test
void testArrayWithCycle() {
    value ser = TabularSerializer();
    value arr = arrayOfSize<Identifiable>(1, Foo());
    arr.set(0, arr);
    ser.add(arr);
    value serialized = ser.write();
    print(serialized);
    value deser = TabularDeserializer(`module test.com.github.tombentley.tabular`, serialized);
    value deserialized = deser.select(`Array<Identifiable>`).sequence();
    assertEquals(1, deserialized.size);
    assert (exists i = deserialized[0],
        exists i2 = i[0]);
    assert (i === i2);
}

serializable
class ClassWithCycle() {
    shared late ClassWithCycle other;
}
shared test
void testClassWithCycle() {
    value ser = TabularSerializer();
    value c = ClassWithCycle();
    c.other = c;
    ser.add(c);
    value serialized = ser.write();
    print(serialized);
    value deser = TabularDeserializer(`module test.com.github.tombentley.tabular`, serialized);
    value deserialized = deser.select(`ClassWithCycle`).sequence();
    assertEquals(1, deserialized.size);
    assert (exists i = deserialized[0],
        i === i.other);
}

class NotSerializable() {
}
shared test
void testNotSerializable() {
    value ser = TabularSerializer();
    value c = NotSerializable();
    try {
        ser.add(c);
        fail();
    } catch (AssertionError e) {
    }
}

abstract serializable
class Abstract(String name) {
    shared String name1 => name;
    shared formal String name2;
    shared default String name3 = name;
}
serializable
class Concrete(name2) extends Abstract("foo") {
    shared actual String name2;
}
shared test
void testAbstractSuper() {
    value ser = TabularSerializer();
    value c = Concrete("bar");
    ser.add(c);
    value serialized = ser.write();
    print(serialized);
    value deser = TabularDeserializer(`module test.com.github.tombentley.tabular`, serialized);
    value deserialized = deser.select(`Abstract`).sequence();
    assertEquals(1, deserialized.size);
    assert (exists i = deserialized[0]);
    assertEquals("foo", i.name1);
    assertEquals("bar", i.name2);
    assertEquals("foo", i.name3);
}

serializable
class NonIdentifiable(shared actual String string) extends Object() {
    shared actual Boolean equals(Object other) {
        if (is NonIdentifiable other) {
            return this.string == other.string;
        } else {
            return false;
        }
    }
    shared actual Integer hash => string.hash;
}
shared test
void testNonIdentifiable() {
    value ser = TabularSerializer();
    value c = NonIdentifiable("bar");
    ser.add(c);
    value serialized = ser.write();
    print(serialized);
    value deser = TabularDeserializer(`module test.com.github.tombentley.tabular`, serialized);
    value deserialized = deser.select(`NonIdentifiable`).sequence();
    assertEquals(1, deserialized.size);
    assert (exists i = deserialized[0]);
    assertEquals("bar", i.string);
    assertEquals(c, i);
}

serializable
class NoAttributes() extends Basic() {}
serializable
class NoAttributesSub() extends NoAttributes() {}

shared test
void testNoAttributes() {
    value ser = TabularSerializer();
    value c = NoAttributesSub();
    ser.add(c);
    value serialized = ser.write();
    print(serialized);
    value deser = TabularDeserializer(`module test.com.github.tombentley.tabular`, serialized);
    value deserialized = deser.select(`NoAttributes`).sequence();
    assertEquals(1, deserialized.size);
    assert (is NoAttributesSub i = deserialized[0]);
}
serializable
abstract class MemberClasses() {
    serializable
    class NonSharedMember() {}
    shared Object m() => NonSharedMember();
    shared serializable
    class SharedMember() {}
    shared serializable
    default class DefaultMember() {}
    shared serializable
    formal class FormalMember() {}
}
serializable
class MemberClassesSub() extends MemberClasses() {
    shared actual serializable
    class DefaultMember() extends super.DefaultMember() {}
    shared actual serializable
    class FormalMember() extends super.FormalMember() {}
}
shared test
void testNonSharedMember() {
    //value mc = `class MemberClasses`.classApply<Anything,Nothing>();
    //value mcInst = mc.apply();
    //print(mcInst);
    //value mcSm = `class MemberClasses.SharedMember`.memberClassApply<MemberClasses,Anything,Nothing>(`MemberClasses`);
    //print(mcSm.bind(mcInst).apply());
    
    value container = MemberClassesSub();
    value member = container.m();
    value ser = TabularSerializer();
    ser.add(member);
    value serialized = ser.write();
    print(serialized);
    value deser = TabularDeserializer(`module test.com.github.tombentley.tabular`, serialized);
    value deserialized = deser.select(`Anything`).sequence();
    assertEquals(2, deserialized.size);
}
// TODO SharedMember with MemberClasses outer
// TODO SharedMember with MemberClasses outer
// TODO DefaultMember with MemberClasses outer
// TODO DefaultMember with MemberClassesSub outer
// TODO FormalMember with MemberClassesSub outer

// TODO Member classes of interfaces

// TODO Tuple

"Round-trip a small object graph, which includes some cycles"
shared test
void testPersonAddress() {
    print(`value null`.get());
    value aliceHome = Address("home", "near london");
    value goodCorp = Organization("good corp");
    value alice = EmployedPerson("alice", aliceHome, goodCorp);
    
    value bob = Person("bob", aliceHome);
    value carolAddress = Address("somewhere", "in NYC");
    value carol = EmployedPerson("carol", carolAddress, goodCorp);
    value dave = Person("dave", carolAddress);
    alice.spouse = bob;
    bob.spouse = alice;
    alice.boss = carol;
    carol.spouse = dave;
    dave.spouse = carol;
    
    value aliceEmployment = EmploymentContract(goodCorp, alice);
    value carolEmployment = EmploymentContract(goodCorp, carol);
    
    value ser = TabularSerializer();
    
    // Note: we only add the contracts to the serializer 
    ser.add(aliceEmployment);
    ser.add(carolEmployment);
    value serialized = ser.write();
    
    print(serialized);
    
    value deser = TabularDeserializer(`module test.com.github.tombentley.tabular`, serialized);
    value people = deser.select(`Person`);
    print(people);
    assertEquals(4, people.size);
    assert (alice in people);
    assert (bob in people);
    assert (carol in people);
    assert (dave in people);
    
    value employedPeople = deser.select(`EmployedPerson`);
    print(employedPeople);
    assertEquals(2, employedPeople.size);
    assert (alice in employedPeople);
    assert (!bob in employedPeople);
    assert (carol in employedPeople);
    assert (!dave in employedPeople);
    value organizations = deser.select(`Organization`);
    print(organizations);
    assertEquals(1, organizations.size);
    assert (goodCorp in organizations);
    value addresses = deser.select(`Address`);
    print(addresses);
    assertEquals(2, addresses.size);
    assert (aliceHome in addresses);
    assert (carolAddress in addresses);
    value contracts = deser.select(`Contract<Organization,Person>`);
    print(contracts);
    assertEquals(2, contracts.size);
    assert (aliceEmployment in contracts);
    assert (carolEmployment in contracts);
}
