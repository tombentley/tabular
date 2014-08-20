"""An example serialization library.
   
   ## Identity
   
   Each object instance is automatically allocated an integer id
   (unique within the scope of the serialization context).
   
   As far as this library is concerned, the following are value types
   (which are therefore persisted exactly once):
   
   * `String`, `Character`, `Integer`, `Byte`, `Float`
   * `Array`, `Sequence`
   
   References to top level `object`s 
   (e.g. true, false, null, larger, empty) are persisted as references 
   and resolved against those objects upon deserialization.
   
   All remaining instances must be `Identifiable` and will be serialized 
   according to that identity (so two distinct but equal instances will 
   be serialized as two instances). 
   
   ## Format
   
   A tabular format is used. There is a table for each 
   `ClassDeclaration` which holds the state for instances of that class.
   For demonstration purposes, tables get written to a `String` 
   in a line oriented format.
   Within the output, a table starts with two "header" lines, which start 
   with a hash (#). All lines following the header lines are rows, which 
   start with a number (the id of the instance whose state is in that row).
   This means that within a table all the rows should start with a different id.
   
   **Very roughly** this is the grammar we're talking about
   
       output       ::= table*
       table        ::= header row*
       header       ::= nameHeader columnHeader
       
       nameHeader   ::= hash qualifiedClassName ("extends" qualifiedClassName)? nl
       qualifiedClassName ::= ident ("." ident) "::" ident
       columnHeader ::= hash "<id> ("," columnName)* nl
       columnName   ::= ident
       hash         ::= "#"
       nl           ::= "\n" | "\r" 
       
       row          ::= integer (",", atom)* nl
       atom         ::= numberOrId,string,boolean,null,character
       numberOrId   ::= ("+" | "-") ? digits ("." digits)
       string       ::= "\"" anything "\""
       boolean      ::= "true" | "false"
       null         ::= "null"
       character    ::= "'" anything "'"
       
   In the case that a row contains an integer value it's ambiguous 
   (within the context of the stream) whether that's an integer literal or a 
   reference to another instance.
"""
shared package com.github.tombentley.tabular;
