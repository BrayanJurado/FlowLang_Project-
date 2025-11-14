#lang eopl

#|
-------------------------------------------------------------------------------
                           FLOWLANG PROJECT
-------------------------------------------------------------------------------
Brayan Camilo Urrea Jurado
urrea.brayan@correounivalle.edu.co
Código: 2410023

Nicolas Enrique Granada
granada.nicolas@correounivalle.edu.co
Código: 2310107

Enlace al repositorio: https://github.com/BrayanJurado/FlowLang_Project-.git

;;;;;;;;;;;;;;;;;;;; GRAMATICA ;;;;;;;;;;;;;;;;;;;;

<program> ::= <expression>

<expression> ::= <number>
              |  <string-lit>
              |  <identifier> {"." <identifier>}*
              |  "true" | "false" | "null" | "this"
              |  "var" {<identifier> "=" <expression>}+, "in" <expression>
              |  "const" {<identifier> "=" <expression>}+, "in" <expression>
              |  "set" <identifier> "=" <expression>
              |  "complejo" "(" <expression> "," <expression> ")"
              |  <primitive> "(" {<expression>}*, ")"
              |  "if" <expression> "then" <expression> "else" <expression> "end"
              |  "switch" <expression> {"case" <expression> ":" <expression>}* 
                 "default" ":" <expression> "end"
              |  "while" <expression> "do" <expression> "done"
              |  "for" <identifier> "in" <expression> "do" <expression> "done"
              |  "func" "(" {<identifier>}*, ")" <expression>
              |  "(" <expression> {<expression>}* ")"
              |  "letrec" {<identifier> "(" {<identifier>}*, ")" "=" <expression>}+
                 "in" <expression>
              |  "begin" <expression> {";" <expression>}* "end"
              |  "prototipo" <identifier> "=" <expression> "in" <expression>
              |  "[" {<expression>}*, "]"
              |  "{" {<identifier> ":" <expression>}+, "}"

<primitive> ::= "+" | "-" | "*" | "/" | "%" | "add1" | "sub1" | "zero?"
             |  "<" | ">" | "<=" | ">=" | "==" | "<>"
             |  "and" | "or" | "not"
             |  "longitud" | "concatenar"
             |  "vacio" | "vacio?" | "crear-lista" | "lista?" 
             |  "cabeza" | "cola" | "append" | "ref-list" | "set-list"
             |  "crear-diccionario" | "diccionario?" | "ref-diccionario" 
             |  "set-diccionario" | "claves" | "valores"
             |  "clone" | "print" | "real" | "imag"
             |  "get-field" | "set-field"

|#

;;;;;;;;;;;;;;;;;;;; ESPECIFICACIÓN LÉXICA Y GRAMATICAL ;;;;;;;;;;;;;;;;;;;;

(define the-lexical-spec
  '((whitespace (whitespace) skip)
    (comment ("%" (arbno (not #\newline))) skip)
    (identifier
      (letter (arbno (or letter digit "_" "-" "?")))
      symbol)
    (number (digit (arbno digit)) number)
    (number ("-" digit (arbno digit)) number)
    (number (digit (arbno digit) "." digit (arbno digit)) number)
    (number ("-" digit (arbno digit) "." digit (arbno digit)) number)
    (string-lit ("\"" (arbno (not #\")) "\"") string)))

(define the-grammar
  '((program (expression) a-program)
    
    ;; DECLARACIONES integradas como expresiones
    (expression ("var" (separated-list identifier "=" expression ",") "in" expression) var-decl-exp)
    (expression ("const" (separated-list identifier "=" expression ",") "in" expression) const-decl-exp)
    (expression ("prototipo" identifier "=" expression "in" expression) proto-decl-exp)
    (expression ("set" identifier "=" expression) assign-exp)
    
    ;; EXPRESIONES
    (expression (number) lit-exp)
    (expression (string-lit) string-exp)
    (expression (identifier (arbno "." identifier)) id-exp)
    (expression ("true") true-exp)
    (expression ("false") false-exp)
    (expression ("null") null-exp)
    (expression ("this") this-exp)
    
    ;; Números complejos
    (expression ("complejo" "(" expression "," expression ")") complex-exp)
    
    ;; Primitivas
    (expression
      (primitive "(" (separated-list expression ",") ")")
      primapp-exp)
    
    ;; Control de flujo
    (expression
      ("if" expression "then" expression "else" expression "end")
      if-exp)
    (expression
      ("switch" expression (arbno "case" expression ":" expression) "default" ":" expression "end")
      switch-exp)
    
    ;; Iteración
    (expression
      ("while" expression "do" expression "done")
      while-exp)
    (expression
      ("for" identifier "in" expression "do" expression "done")
      for-exp)
    
    ;; Funciones
    (expression
      ("func" "(" (separated-list identifier ",") ")" expression)
      func-exp)
    (expression
      ("(" expression (arbno expression) ")")
      app-exp)
    (expression
      ("letrec" (arbno identifier "(" (separated-list identifier ",") ")" "=" expression)
       "in" expression)
      letrec-exp)
    
    ;; Secuenciación
    (expression
      ("begin" expression (arbno ";" expression) "end")
      begin-exp)
    
    ;; PRIMITIVAS
    (primitive ("+") add-prim)
    (primitive ("-") subtract-prim)
    (primitive ("*") mult-prim)
    (primitive ("/") div-prim)
    (primitive ("%") mod-prim)
    (primitive ("add1") incr-prim)
    (primitive ("sub1") decr-prim)
    (primitive ("zero?") zero-test-prim)
    (primitive ("<") less-prim)
    (primitive (">") greater-prim)
    (primitive ("<=") lesseq-prim)
    (primitive (">=") greatereq-prim)
    (primitive ("==") equal-prim)
    (primitive ("<>") notequal-prim)
    (primitive ("and") and-prim)
    (primitive ("or") or-prim)
    (primitive ("not") not-prim)
    (primitive ("longitud") length-prim)
    (primitive ("concatenar") concat-prim)
    (primitive ("vacio") empty-list-prim)
    (primitive ("vacio?") empty?-prim)
    (primitive ("crear-lista") cons-prim)
    (primitive ("lista?") list?-prim)
    (primitive ("cabeza") car-prim)
    (primitive ("cola") cdr-prim)
    (primitive ("append") append-prim)
    (primitive ("ref-list") ref-list-prim)
    (primitive ("set-list") set-list-prim)
    (primitive ("crear-diccionario") create-dict-prim)
    (primitive ("diccionario?") dict?-prim)
    (primitive ("ref-diccionario") ref-dict-prim)
    (primitive ("set-diccionario") set-dict-prim)
    (primitive ("claves") keys-prim)
    (primitive ("valores") values-prim)
    (primitive ("clone") clone-prim)
    (primitive ("print") print-prim)
    (primitive ("real") real-prim)
    (primitive ("imag") imag-prim)
    (primitive ("get-field") get-field-prim)
    (primitive ("set-field") set-field-prim)
    
    ;; Listas y diccionarios literales
    (expression ("[" (separated-list expression ",") "]") list-literal-exp)
    (expression ("{" (separated-list identifier ":" expression ",") "}") dict-literal-exp)
    ))

(sllgen:make-define-datatypes the-lexical-spec the-grammar)

(define scan&parse
  (sllgen:make-string-parser the-lexical-spec the-grammar))


