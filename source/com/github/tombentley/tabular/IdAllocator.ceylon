import ceylon.collection {
    IdentityMap,
    HashMap,
    StringBuilder
}
import ceylon.language.meta.model {
    Model
}
import ceylon.language.meta.declaration {
    Declaration
}

"""Allocates ids (from an [[IdGenerator]]) to instances, such that "the same"
   instance will get the same id. 
   
   The meaning of "the same" depends on the type of the instance.
   """
class IdAllocator() {
    "Mapping of entity to id"
    IdentityMap<Identifiable,Id> ids = IdentityMap<Identifiable,Id>();
    
    "Mapping of value to id"
    HashMap<Object,Id> valueIds = HashMap<Object,Id>();
    
    "The id of null, if it's been allocated, otherwise null"
    variable Id? nullId = null;
    
    "The id generator"
    IdGenerator generator = IdGenerator();
    
    shared actual String string {
        value sb = StringBuilder();
        sb.appendCharacter('{');
        if (exists nid = nullId) {
            sb.append("null->").append(nid.string);
        }
        for (inst->id in valueIds) {
            sb.append(inst.string).append("->").append(id.string);
        }
        for (inst->id in ids) {
            sb.append(inst.string).append("->").append(id.string);
        }
        sb.appendCharacter('}');
        return sb.string;
    }
    
    "Obtain an id for the given instance, allocating an id if necessary."
    shared Id allocateId(Object? instance) {
        switch (instance)
        case (is Null) {
            if (exists nid = nullId) {
                return nid;
            } else {
                Id nid = generator.next();
                //print("allocate ``nid`` to null");
                nullId = nid;
                return nid;
            }
        }
        case (is Object) {
            if (is Identifiable instance,
                !(instance is Model || instance is Declaration)) { // treat classes from c.l.m.model as values
                if (exists id = ids[instance]) {
                    return id;
                } else {
                    Id id = generator.next();
                    //print("allocate ``id`` to ``instance`` (``type(instance)``)");
                    ids.put(instance, id);
                    return id;
                }
            } else {
                if (exists id = valueIds[instance]) {
                    return id;
                } else {
                    Id id = generator.next();
                    //print("allocate ``id`` to ``instance`` (``type(instance)``)");
                    valueIds.put(instance, id);
                    return id;
                }
            }
        }
    }
    
    "Whether the given instance has had an id allocated."
    shared Boolean idAllocated(Object? instance) {
        switch (instance)
        case (is Null) {
            return nullId exists;
        }
        case (is Object) {
            if (is Identifiable instance,
                !(instance is Model || instance is Declaration)) { // treat classes from c.l.m.model as values
                return instance in ids.keys;
            } else {
                return instance in valueIds.keys;
            }
        }
    }
}
