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
    
    value home = Address("home", "near hexham");
    value tom = Person("tom", home);
    value nhs = Organization("nhs");
    value rhu = EmployedPerson("rhu", home, nhs);
    value dianne = EmployedPerson("dianne", Address("somewhere", "in hexham"), nhs);
    tom.spouse = rhu;
    rhu.spouse = tom;
    rhu.boss = dianne;
    
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
