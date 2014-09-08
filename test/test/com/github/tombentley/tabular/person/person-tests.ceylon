import ceylon.test {
    test
}
import com.github.tombentley.tabular {
    TabularSerializer,
    TabularDeserializer
}

"Round-trip a person and an address"
shared test
void testPersonAddress() {
    print(`value null`.get());
    value home = Address("home", "near hexham");
    value tom = Person("tom", home);
    value nhs = Organization("nhs");
    value rhu = EmployedPerson("rhu", home, nhs);
    value da = Address("somewhere", "in hexham");
    value dianne = EmployedPerson("dianne", da, nhs);
    value bob = Person("bob", da);
    tom.spouse = rhu;
    rhu.spouse = tom;
    rhu.boss = dianne;
    dianne.spouse = bob;
    bob.spouse = dianne;
    
    value rhuEmployment = EmploymentContract(nhs, rhu);
    
    //print(tom);
    //print(rhu);
    value ser = TabularSerializer();
    //ser.add({ tom, rhuEmployment }.sequence());
    ser.add(tom);
    ser.add(rhuEmployment);
    value serialized = ser.write();
    
    print(serialized);
    
    value deser = TabularDeserializer(`module test.com.github.tombentley.tabular`, serialized);
    print(deser.select(`Person`));
    print(deser.select(`EmployedPerson`));
    print(deser.select(`Organization`));
    print(deser.select(`Address`));
    print(deser.select(`Contract<Organization,Person>`));
}

/*
 tests with each of the components of tabular
 refactor tabular so it's a bit nicer
 
 
 class with single String attribute 
 class with single Integer attribute
 class with single Byte attribute
 class with single Float attribute
 class with single Character attribute
 class with single Boolean attribute
 class with single Comparable attribute
 class with single generic attribute
 
 class with abstract superclass
 subclass with no attributes
 
 member class 
 
 range
 singleton
 tuple
 arraylist
 
 array
 
 class that extends Object (not Basic)
 
 
 
 */
