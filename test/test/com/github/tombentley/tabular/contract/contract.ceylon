import ceylon.collection {
    ArrayList
}

shared interface LegalEntity {
    shared formal String name;
}

shared abstract serializable
class Sex(shared actual String string) of male | female {}
shared object male extends Sex("male") {}
shared object female extends Sex("female") {}

shared serializable
class Person(name, sex)
        satisfies LegalEntity {
    
    shared actual variable String name;
    
    shared variable Sex sex;
    
    shared variable Address? address = null;
    
    shared variable Person[] parents = [];
    shared variable Person[] children = [];
    variable Marriage? marriage = null;
    
    shared void bornTo(Person father, Person mother) {
        assert (father.sex == male);
        assert (mother.sex == female);
        this.parents = [father, mother];
        father.children = [this, *father.children];
        mother.children = [this, *mother.children];
    }
    
    value sibs =>
            { for (parent in parents) for (child in parent.children) if (child != this) child };
    
    shared Person[] siblings => sibs.sequence();
    
    shared Person[] brothers => sibs.select((Person s) => s.sex == male);
    
    shared Person[] sisters => sibs.select((Person s) => s.sex == female);
    
    shared Person[] uncles =>
            { for (parent in parents) for (uncle in parent.brothers) uncle }.sequence();
    
    shared Person[] aunts =>
            { for (parent in parents) for (uncle in parent.sisters) uncle }.sequence();
    
    shared Person[] grandParents =>
            { for (parent in parents) for (gp in parent.parents) gp }.sequence();
    
    shared Marriage marry(Person other) {
        "cannot marry self"
        assert (this != other);
        "bigamy!"
        assert (!marriage exists);
        
        value m = Marriage(this, other);
        marriage = m;
        return m;
    }
    
    shared void divorce() {
        "not married; cannot divorce"
        assert (marriage exists);
        marriage = null;
    }
    
    shared Person? spouse {
        if (exists m = marriage) {
            if (m.p1 == this) {
                return m.p2;
            } else {
                return m.p1;
            }
        } else {
            return null;
        }
    }
    
    shared actual default String string {
        variable value s = name;
        if (exists a = address) {
            s = s + " who lives at ``a``";
        }
        if (exists sp = spouse) {
            s = s + " and has spouse ``sp.name``";
        }
        return s;
    }
}

shared serializable
class Address(lines) {
    shared String lines;
    shared actual String string => lines;
}

shared serializable
class Organization(name)
        satisfies LegalEntity {
    shared actual String name;
    shared actual String string => name;
    value employments = ArrayList<EmploymentContract>();
    shared List<Person> employees => ArrayList {
        elements = { for (e in employments) e.employee };
    };
    shared EmploymentContract employ(Person employee) {
        value contract = EmploymentContract(this, employee);
        employments.add(contract);
        return contract;
    }
    shared void terminate(EmploymentContract contract) {
        employments.remove(contract);
    }
}

shared abstract serializable
class Contract<Parties>(parties)
        given Parties satisfies [LegalEntity, LegalEntity+] {
    assert (parties.size >= 2);
    shared Parties parties;
    // start date
}

shared serializable
class EmploymentContract(shared Organization employer, shared Person employee)
        extends Contract<[Organization, Person]>([employer, employee]) {
}

shared serializable
class Marriage(shared Person p1, shared Person p2)
        extends Contract<[Person, Person]>([p1, p2]) {
}
