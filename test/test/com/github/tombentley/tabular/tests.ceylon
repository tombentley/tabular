import ceylon.test {
    test
}
import test.com.github.tombentley.tabular.person {
    Person,
    EmployedPerson,
    Address,
    Organization
}
import com.github.tombentley.tabular {
    TabularSerializer,
    TabularDeserializer
}


"Round-trip a person and an address"
shared test
void testPersonAddress() {
    value home = Address("home");
    value tom = Person("tom", home);
    value nhs = Organization("nhs");
    value rhu = EmployedPerson("rhu", home, nhs);
    value dianne = EmployedPerson("dianne", Address("hexham"), nhs);
    tom.spouse = rhu;
    rhu.spouse = tom;
    rhu.boss = dianne;
    //print(tom);
    //print(rhu);
    value ser = TabularSerializer();
    ser.add(tom);
    value serialized = ser.write();
    
    print(serialized);
    
    value deser = TabularDeserializer(serialized);
    {Person*} people = deser.select(`Person`);
    print(people);
    {EmployedPerson*} employedPeople = deser.select(`EmployedPerson`);
    print(employedPeople);
    
    {Organization*} orgs = deser.select(`Organization`);
    print(orgs);
    
    {Address*} addresses = deser.select(`Address`);
    print(addresses);
}
