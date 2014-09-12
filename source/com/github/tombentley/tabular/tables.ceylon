import ceylon.language.meta.model {
    Class,
    ClassModel,
    ClassOrInterface,
    Type,
    UnionType,
    IntersectionType,
    Generic,
    nothingType
}
import ceylon.collection {
    HashMap,
    ArrayList
}
import ceylon.language.serialization {
    Reference
}
import ceylon.language.meta.declaration {
    ClassOrInterfaceDeclaration,
    ClassDeclaration,
    Package,
    ValueDeclaration,
    TypeParameter
}

"abstraction for ArrayTable and AttributeTable"
abstract class Table<ActualRow>()
        given ActualRow satisfies Row {
    shared formal class Row(Integer a) {
    }
    HashMap<Id,ActualRow> data = HashMap<Id,ActualRow>();
    shared Map<Id,ActualRow> rows => data;
    shared default void addRow(Id id, ActualRow row) {
        data.put(id, row);
    }
}

"The table in which arrays are stored"
class ArrayTable() extends Table<Row>() {
    shared actual class Row(size) extends super.Row(size) {
        "The number of elements in the array"
        shared Integer size;
        "Storage for the type argument (the first element) 
         and the array elements."
        value values = arrayOfSize<Id|FundementalValueType?>(size + 1, null);
        "The array's type argument"
        shared Id typeArgument {
            assert (is Id ta = values[0]);
            return ta;
        }
        assign typeArgument {
            values.set(0, typeArgument);
        }
        
        shared void setValue(Integer index, Id|FundementalValueType datum) {
            values.set(index + 1, datum);
        }
        
        shared Id|FundementalValueType getValue(Integer index) {
            assert (exists id = values.get(index + 1));
            return id;
        }
    }
}

"A table which holds attribute values of the given [[classDeclaration]] 
 for a number of [[Id]]-identified instances.
 
 We record the superclass *model* so we know what the reified type 
 parameters held in superclasses are."
class AttributeTable(classAbstract, classDeclaration, typeParameters, superModel, columns)
        extends Table<Row>() {
    "Whether this class is abstract."
    shared Boolean classAbstract;
    
    "The class whose state this table serializes"
    shared Id classDeclaration;
    
    shared List<TypeParameter> typeParameters;
    
    "The superclass of the classDeclaration 
     *at the time the data was serialized*,
     or null if the superclass was `Basic` or `Object`."
    shared Id? superModel;
    
    shared variable Id? outerClass = null;
    
    "The mapping of column index to attribute."
    shared List<ValueDeclaration> columns;
    value schema = HashMap<ValueDeclaration,Integer>();
    for (index->vd in columns.indexed) {
        schema.put(vd, index);
    }
    
    "A row within a table"
    shared actual class Row(Integer s) extends super.Row(s) {
        
        "Whether this row is for an instance whose instantiated class 
         is this rows tables class. In other words, if this is false then the 
         row is holding superclass state."
        shared variable Boolean concrete = false;
        
        "The Table this Row is (or will be) a row of."
        shared AttributeTable table => outer;
        
        // note that both typeArguments_ and values are initialized to all null
        // so that it's impossible for clients to see an unset value
        value typeArguments_ = ArrayList<Id?>(typeParameters.size);
        for (tp in typeParameters) {
            typeArguments_.add(null);
        }
        
        value values = arrayOfSize<Id|FundementalValueType?>(schema.size, null);
        
        Integer tpIndex(TypeParameter tp) {
            variable value index = 0;
            for (tpx in typeParameters) {
                if (tpx == tp) {
                    return index;
                }
                index++;
            }
            throw Exception("type parameter not found: ``tp`` in ``classDeclaration``");
        }
        
        shared void setTypeArgument(TypeParameter tp, Id className) {
            variable value index = tpIndex(tp);
            typeArguments_.set(index, className);
        }
        
        shared Id getTypeArgument(TypeParameter tp) {
            variable value index = tpIndex(tp);
            assert (exists ta = typeArguments_[index]);
            return ta;
        }
        
        shared variable Id? outerInstance = null;
        
        shared void setValue(ValueDeclaration vd, Id|FundementalValueType datum) {
            assert (exists index = schema[vd]);
            // TODO check that the type of val is a subtype of the type of vd
            values.set(index, datum);
        }
        shared FundementalValueType|Id getValue(ValueDeclaration vd) {
            if (exists index = schema[vd],
                0 <= index < values.size) {
                value datum = values[index];
                switch (datum)
                case (is Null) {
                    throw Exception("value not yet set: ``vd``");
                }
                case (is Reference<Anything>|FundementalValueType|Id) {
                    return datum;
                }
            } else {
                throw Exception("value declaration not in table schema: ``vd``");
            }
        }
        
        "null if the row has values for every column, otherwise 
         an error message."
        shared String? complete {
            variable value i = 0;
            if (!classAbstract && concrete) {
                for (tp in typeParameters) {
                    if (!typeArguments_[i] exists) {
                        return "missing type argument for ``tp``";
                    }
                    i++;
                }
                i = 0;
            }
            for (datum in values) {
                if (!datum exists) {
                    return "missing value for `` columns[i] else "null" ``";
                }
                i++;
            }
            if (outerClass exists && !outerInstance exists) {
                return "missing value for outer instance";
            }
            return null;
        }
        shared {Id*} typeArguments {
            return typeArguments_.map(function(Id? o) {
                    assert (exists o);
                    return o;
                });
        }
        
        "The data in this row, in the same order as [[outer.columns"
        shared {Id|FundementalValueType*} data => values.map(function(datum) {
                assert (is Id|FundementalValueType datum);
                return datum;
            });
    }
    
    "Adds a row for the instance with the given id to the table."
    shared actual void addRow(Id id, Row row) {
        if (exists msg = row.complete) {
            throw AssertionError(msg);
        }
        
        super.addRow(id, row);
    }
    
    "The row for the instances with the given id"
    shared Row? get(Id id) => rows[id];
    
    shared actual String string => "Table(``classDeclaration``, `` superModel else "null" ``, ``columns``)";
}

class MetaData(shared HashMap<Id,MetaValue> metaData, IdAllocator allocator, Reference<Object?> enlist(Anything instance)) {
    Id alloPut(MetaValue cls) {
        value clsId = allocator.allocateId(cls);
        metaData.put(clsId, cls);
        return clsId;
    }
    Id putOrEnlist(Anything o) {
        if (!isFundementalType(o)) {
            assert (is Id id = enlist(o).id);
            return id;
        } else {
            assert (is MetaValue item = o);
            return alloPut(item);
        }
    }
    Id package_(Package p) {
        return alloPut(p);
    }
    shared Id valueDeclaration(ValueDeclaration vd) {
        if (is Package p = vd.container) {
            return alloPut(Member(true, package_(p), vd.name));
        }
        return nothing; // TODO attributes
    }
    shared Id classOrInterfaceDeclaration(ClassOrInterfaceDeclaration cd) {
        if (is Package p = cd.container) {
            return alloPut(Member(true, package_(p), cd.name));
        } else if (is ClassOrInterfaceDeclaration outr = cd.container) {
            return alloPut(Member(false, classOrInterfaceDeclaration(outr), cd.name));
        }
        return nothing; // TODO member classes
    }
    shared Id classOrInterface(ClassOrInterface c) {
        if (c.typeArguments.empty) {
            // for non-generic classes let's just record the declaration
            return classOrInterfaceDeclaration(c.declaration);
        } else {
            return alloPut(TypeApplication(classOrInterfaceDeclaration(c.declaration), typeArguments(c)));
        }
    }
    shared Id type_(Type ta) {
        if (is ClassOrInterface ta) {
            return classOrInterface(ta);
        } else if (is UnionType ta) {
            return alloPut(Union(ta.caseTypes.collect(type_)));
        } else if (is IntersectionType ta) {
            return alloPut(Intersection(ta.satisfiedTypes.collect(type_)));
        } else if (ta == nothingType) {
            return alloPut(Member(true, package_(`package ceylon.language`), "Nothing"));
        }
        assert (false); // should be impossible
    }
    Id[] typeArguments(Generic g) {
        return package.typeArguments(g).collect(type_);
    }
    shared Id array(List<Anything> val) {
        Id[] ids = val.collect(putOrEnlist);
        return alloPut(ids);
    }
    shared Id str(String val) => alloPut(val);
}
