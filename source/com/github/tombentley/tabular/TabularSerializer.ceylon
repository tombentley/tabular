import ceylon.language.meta {
    type
}
import ceylon.language.meta.model {
    ClassModel,
    Type
}
import ceylon.language.meta.declaration {
    ClassOrInterfaceDeclaration,
    ClassDeclaration,
    ValueDeclaration,
    TypeParameter
}
import ceylon.language.serialization {
    Deconstructor,
    SerializationContext,
    SerializableReference,
    serialization
}
import ceylon.collection {
    ArrayList,
    HashMap,
    MutableMap,
    Queue,
    LinkedList
}
"Provides a facility for serializing instances to a `String`."
shared class TabularSerializer(Boolean inlineString = true) {
    
    SerializationContext context = serialization();
    value allocator = IdAllocator();
    
    MutableMap<ClassDeclaration,AttributeTable> tables = HashMap<ClassDeclaration,AttributeTable>();
    ArrayTable arrayTable = ArrayTable();
    "Queue of instances waiting to be serialized"
    Queue<SerializableReference<Object?>> instances = LinkedList<SerializableReference<Object?>>();
    
    // TODO Get rid of this fucker
    value anotherFuckingMap = HashMap<Id,SerializableReference<Object?>>();
    
    "Adds the given [[instance]] to [[instances]] 
             if it's not been added yet, returns its id."
    SerializableReference<Object?> enlist(Anything instance) {
        assert (is Object? instance);
        Boolean notAllocated = !allocator.idAllocated(instance);
        Id id = allocator.allocateId(instance);
        if (notAllocated) {
            value reference = context.reference(id, instance);
            instances.offer(reference);
            anotherFuckingMap.put(id, reference);
            return reference;
        }
        assert (exists r = anotherFuckingMap[id]);
        return r;
    }
    
    "Meta data necessary to describe classes and 
     references to object declarations."
    value metaData = MetaData(HashMap<Id,MetaValue>(), allocator, enlist);
    
    class TabularDeconstructor() satisfies Deconstructor {
        variable Id id = Id("");
        
        shared variable ClassModel? instantiatedClassModel = null;
        shared variable ClassModel? currentClassModel = null;
        variable value typeParameters = ArrayList<[TypeParameter, Id]>();
        variable Id? outerInstance = null;
        variable value values = ArrayList<[ValueDeclaration, Id|FundementalValueType]>();
        variable value elements = ArrayList<Id|FundementalValueType>();
        
        "Called when we start inspecting an instance"
        shared void beginInstance(Id id, Object? instance) {
            ClassModel classModel = type(instance);
            this.id = id;
            this.instantiatedClassModel = classModel;
        }
        
        shared void beginClass(ClassModel cd) {
            if (exists cc = currentClassModel,
                cd != cc) {
                finishRow();
            }
            currentClassModel = cd;
        }
        "Called when we finish inspecting an instance"
        shared void endInstance() {
            // Here I can check that all the rows in all the tables have been populated
            finishRow();
        }
        "Whether the given value should be added to the table row *inline*, 
         or via a reference. Only values of [[FundementalValueType]] can be included inline."
        Boolean inline<Type>(Type val) {
            return inlineString;
        }
        
        shared actual void putOuterInstance<Type>(Type outerInstance) {
            assert (is Id id = enlist(outerInstance).id);
            this.outerInstance = id;
        }
        
        shared actual void putValue<Type>(ValueDeclaration attribute, Type referenced) {
            Object? ref = referenced of Object?;
            if (exists vd = getObjectValueDeclaration(ref)) {
                // it's an object declaration, so add it to the meta table
                values.add([attribute, metaData.valueDeclaration(vd)]);
            } else {
                if (inline(ref), is FundementalValueType ref) {
                    values.add([attribute, ref]);
                } else {
                    assert (is Id id = enlist(ref).id);
                    values.add([attribute, id]);
                }
            }
        }
        shared actual void putElement<Type>(Integer index, Type referenced) {
            Object? ref = referenced of Object?;
            if (exists vd = getObjectValueDeclaration(ref)) {
                // it's an object declaration, so add it to the meta table
                elements.add(metaData.valueDeclaration(vd));
            } else {
                if (inline(ref), is FundementalValueType ref) {
                    elements.add(ref);
                } else {
                    assert (is Id id = enlist(ref).id);
                    elements.add(id);
                }
            }
        }
        
        shared actual void putTypeArgument(TypeParameter typeParameter, Type argument) {
            //values.add([attribute, metaTable.add(vd)]);
            //typeParameters.add([typeParameter, argument.string]);
            typeParameters.add([typeParameter, metaData.type_(argument)]);
        }
        "Gets the table for the given class, creating it if necessary. 
         Note this can only be called after all the values have been added
         otherwise we don't know the schema of the table."
        AttributeTable|ArrayTable getOrCreateTable(ClassModel cc) {
            if (cc.declaration == `class Array`) {
                return arrayTable;
            }
            AttributeTable table;
            if (exists t = tables[cc.declaration]) {
                table = t;
            } else {
                assert (is ClassModel s = cc.extendedType);
                table = AttributeTable(cc.declaration.abstract, metaData.classOrInterfaceDeclaration(cc.declaration), cc.declaration.typeParameterDeclarations,
                    s != `Object` && s != `Basic` then metaData.classOrInterface(s) else null,
                    { for (tup in values) tup[0] }.sequence());
                tables.put(cc.declaration, table);
            }
            if (is ClassOrInterfaceDeclaration outerClass = cc.declaration.container) {
                table.outerClass = metaData.classOrInterfaceDeclaration(outerClass);
            }
            return table;
        }
        
        "Populates and adds a [[row]] to the table for the [[currentClassModel]], 
         clears the [[values]] and [[typeParameters]], and nullifies [[currentClassModel]]."
        void finishRow() {
            if (!currentClassModel exists) {
                return;
            }
            assert (exists cc = currentClassModel);
            assert (exists ic = instantiatedClassModel);
            AttributeTable|ArrayTable table = getOrCreateTable(cc);
            switch (table)
            case (is AttributeTable) {
                value row = table.Row(-1);
                row.concrete = ic == cc;
                row.outerInstance = this.outerInstance;
                for (tpName in typeParameters) {
                    try {
                        row.setTypeArgument(tpName[0], tpName[1]);
                    } catch (Throwable e) {
                        throw Exception("Problem setting type argument for type parameter ``tpName[0]`` in table ``table`` for class ``cc``, id=``id``", e);
                    }
                }
                for (tup in values) {
                    try {
                        row.setValue(tup[0], tup[1]);
                    } catch (Throwable e) {
                        throw Exception("Problem setting value for attribute ``tup[0]`` in table ``table`` for class ``cc``, id=``id``", e);
                    }
                }
                table.addRow(id, row);
            }
            case (is ArrayTable) {
                value row = table.Row(elements.size);
                assert (typeParameters.size == 1,
                    exists tpName = typeParameters[0]);
                try {
                    row.typeArgument = tpName[1];
                } catch (Throwable e) {
                    throw Exception("Problem setting type argument for type parameter ``tpName[0]`` in table ``table`` for class ``cc``, id=``id``", e);
                }
                for (index->tup in elements.indexed) {
                    try {
                        row.setValue(index, tup);
                    } catch (Throwable e) {
                        throw Exception("Problem setting value for element ``tup`` at index ``index`` in table ``table`` for class ``cc``, id=``id``", e);
                    }
                }
                table.addRow(id, row);
            }
            this.outerInstance = null;
            this.typeParameters.clear();
            this.values.clear();
            this.elements.clear();
            this.currentClassModel = null;
        }
    }
    value dtor = TabularDeconstructor();
    Deconstructor(ClassModel) dtorFactory = function(ClassModel cd) {
        dtor.beginClass(cd);
        return dtor;
    };
    
    "Register the given instance, and every instance reachable from it, 
     for serialization."
    shared void add(Object instance) {
        enlist(instance);
        while (exists ref = instances.accept()) {
            assert (is Id id = ref.id);
            Object? inst = ref.instance();
            try {
                // and add the instance to the context
                if (is FundementalValueType inst) {
                    switch (inst)
                    case (is String) {
                        //if (internStrings) {
                        metaData.str(inst);
                        //}
                        // TODO do what?
                    }
                    case (is Character) {
                    }
                    case (is Integer) {
                    }
                    case (is Byte) {
                    }
                    case (is Float) {
                    }
                } else if (exists vd = getObjectValueDeclaration(inst)) {
                    metaData.valueDeclaration(vd);
                } else if (isSerializable(inst)) {
                    value reference = ref;
                    dtor.beginInstance(id, inst);
                    reference.serialize(dtorFactory);
                    dtor.endInstance();
                } else {
                    throw AssertionError("instance `` inst else "null" `` (type ``type(inst)``) with id ``id`` is not serializable");
                }
            } catch (Exception e) {
                throw Exception("problem while serializing `` inst else "null" `` with id ``id``", e);
            }
        }
    }
    
    "Serialize all the [[registered|add]] instances to the given StringBuilder."
    shared String write() {
        StringBuilder builder = StringBuilder();
        
        Id? arrayId;
        if (!arrayTable.rows.empty) {
            arrayId = metaData.classOrInterfaceDeclaration(`class Array`);
        } else {
            arrayId = null;
        }
        
        value ctw = MetaTableWriter(builder);
        ctw.write(metaData.metaData, "META");
        
        if (exists arrayId) {
            ArrayTableWriter atw = ArrayTableWriter(arrayId, builder);
            atw.write(arrayTable);
        }
        
        AttributeTableWriter writer = AttributeTableWriter(builder);
        for (table in tables.items) {
            writer.write(table);
        }
        return builder.string;
    }
}
