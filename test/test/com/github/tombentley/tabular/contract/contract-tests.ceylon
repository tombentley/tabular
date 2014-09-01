import ceylon.test {
    test
}
import com.github.tombentley.tabular {
    TabularSerializer,
    TabularDeserializer
}
shared test
void contractTests() {
    value rod = Person("rod", male);
    value trish = Person("trish", female);
    rod.marry(trish);
    value ruth = Person("ruth", female);
    ruth.bornTo(rod, trish);
    value tom = Person("tom", male);
    tom.bornTo(rod, trish);
    
    value frank = Person("frank", male);
    value betty = Person("betty", female);
    frank.marry(betty);
    value tony = Person("tony", male);
    tony.bornTo(frank, betty);
    value angela = Person("angela", male);
    angela.bornTo(frank, betty);
    value catherine = Person("catherine", male);
    catherine.bornTo(frank, betty);
    
    frank.divorce();
    
    value carol = Person("carol", female);
    value jo = Person("jo", female);
    jo.bornTo(frank, carol);
    value rodney = Person("rodney", male);
    rodney.bornTo(frank, carol);
    
    frank.marry(carol);
    
    value rhu = Person("rhu", female);
    rhu.bornTo(frank, carol);
    
    value bex = Person("bex", female);
    bex.bornTo(frank, carol);
    
    tom.marry(rhu);
    
    value guy = Person("guy", male);
    guy.bornTo(tom, rhu);
    value bea = Person("bea", female);
    bea.bornTo(tom, rhu);
    
    value ser = TabularSerializer();
    ser.add(tom);
    value serialized = ser.write();
}
