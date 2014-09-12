"""An example serialization library which serializes/deserializes objects to/from 
   `String`s.
   
   This module can serialize:
   
   * instances of toplevel classes annotated `serializable`, including 
     generic classes, 
   * instances of `ceylon.language::Array`.
   * instances of `String`, `Integer`, `Byte`, `Character` and `Float`
   * references to toplevel `object` declarations (including `true`, 
     `false` and `null`).
   
   Reference cycles between instances are permitted.
   
   ## Serial form
   
   The serial form is text-based, line-oriented and is composed of 
   a number of *tables*. Each line in the serial form is a row in a table, 
   so the terms *row* and *line* are interchangable. 
   
   There are three types of table that appear in a stream: 
   a single metadata table, an optional 
   array table and zero or more attribute tables.
   
       stream ::= metaTable arrayTable? attributeTable* 
   
   ### Lexical structure
   
   Tables are composed of one or two
   *header rows* and one or more *data rows*. 
   Header lines always begin with a hash (`#`) character. Data lines always
   begin with an *identifier* (composed of the digits `0` to `9`
   and the letters `a` to `z` and `A` to `Z`). Following a comma (`,`)
   lines are composed of comma separated *values*.
   
   ### Fundemental types
   
   Instances of the classes `Integer`, `Byte`, `Float`, `Character` and 
   `String` are condisered *fundemental*. Whether a particular instance 
   exists only "once" in the serial form or multiple times is considered 
   an implementation detail. 
   
       value ::= ref | fvalue
       ref ::= identifier
       fvalue ::= string | character | number | byte
       string ::= '"' quotedCharacter* '"'
       character ::= '\'' quotedCharacter '\''
       number ::= (+|-) digit+ ('.' digit+ ('E' (+|-) digit+)?)?
       byte ::= '#{' hex '}'
       quotedCharacter ::= /* TODO */
   
   ### Metadata table

   The first table contains 
   metadata about the classes appearing later in the stream. 
   
       metaTable ::= metaHeader newline 
                     (metaData newline)+
       metaHeader ::= '## META'
   
   Rows in the 
   metadata table can refer to other items in the metadata table, 
   but not to items in the array table or attribute tables.
   
       metaData ::= identifier ',' metaItem newline
       metaItem ::= packageOrMember | class | union | intersection
       packageOrMember ::=
   
   <!-- TODO string and other fundemental types in the metadata table -->
   
   
   ### Array table

   If there are `Array`s in the stream then an array table follows the 
   metadata table.
   
       arrayTable ::= arrayClassHeader newline
                      arrayColumnHeader newline
                      (arrayData newline)*
       arrayClassHeader ::= '# ' identifier newline
       arrayColumnHeader ::= '# =id,<Element>,...'
   
   The array table is distinguished from attribute tables by the fact that 
   the `identifier` in the `arrayClassHeader` will point to the meta data 
   item for the class `ceylon.language::Array`.
   
   Unlike attribute tables, the number of columns in the array table varies 
   from row to row (depending on how many elements there are in that array). 
   
       arrayData :== arrayId ',' arrayTypeArgument (',' arrayElement)*
       arrayId ::= identifier
       arrayTypeArgument ::= identifier
       arrayElement ::= value

   The `arrayId` identifiers the array instance within the scope of 
   the serialized object graph. 
   The `arrayTypeArgument` identifies the a 
   type in the meta data table which is the element type of the array.
   
   The `arrayElement`s are the elements of the array, refered to either 
   via reference to instances in the array or attribute tables 
   or inline. 
   
   ### Attribute tables

   There is a separate attribute table for each class 
   (including super classes) 
   for which there are serialized instances.
   
       attributeTable ::= attributeClassHeader newline 
                          attributeColumnHeader newline 
                          (attributeData newline)+
       attributeClassHeader ::= '# ' '@ '? attributeClass ('extends' attributeSuperclass)? newline
       attributeClass ::= identifier
       attributeSuperclass ::= identifier
       
   The presence of an `@` indicates the class was `abstract` at the time of 
   serialization. 
   The `attributeClass` is an identifier that points to a 
   metadata item for a class *declaration*. 
   The  `attributeSuperclass` is an identifier that points to a 
   metadata item for a class *model*, and therefore includes 
   information about the type arguments to the superclass.
       
       attributeColumnHeader ::= '# =id' 
                         (',' attributeTypeParameter)* 
                         (',' attributeName)*
       attributeTypeParameter ::= '<' uident '>'
       attributeName ::= lident
   
   The `attributeColumnHeader` describes columns that will appear in the 
   `attributeData`. There is a column for each type parameter and 
   stateful attribute, referred to by unqualified name.
   
       attributeData ::= instanceId 
                         (',' attributeTypeArgument?)* 
                         (',' attributeValue)*
       attributeTypeArgument ::= identifier
       attributeValue ::= value
   
   The `attributeTypeArgument` is an identifier pointing to a metadata item 
   for a type. Note, however, that `attributeTypeArgument` will be 
   omitted when the instantiated class of the instance is not the same as the 
   class of the attribute table (i.e. when this attribute table is for a 
   super class of the instance). This is because the type argument is supplied 
   via the 'extends' clause of the subclass in this case.
   
   The `attributeValue` is the value of the attribute, refered to either 
   via reference to an instance in the array or attribute tables 
   or inline.
   
   ### Inheritance
   
   Consider:
   
       class Top() {}
       class Sub() extends Top() {}
       
   The serialized state for an instance of `Sub` will be appear as a 
   row in each of two tables (the table for `Top` and the table for `Sub`). 
   The rows will have the same `instanceId`. 
   During deserialization the instantiated type of the instance will be most 
   derived class in which the instance appears.
   
   ### Top level objects
   
   References to top level `object`s 
   (e.g. true, false, null, empty, larger etc) are serialized as a metadata 
   item to the corresponding `ValueDeclaration` which is 
   evaluated upon deserialization. This has two important consequences:
    
   * When an instance is added for serialization, and the instances reachable 
     from it are added implicitly, the graph walking stops at
     `object` declarations.
   * It follows that an `object` declaration with mutable 
     state won't have that mutable state serialized.
"""
shared package com.github.tombentley.tabular;
