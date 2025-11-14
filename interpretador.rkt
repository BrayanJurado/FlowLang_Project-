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

;;;;;;;;;;;;;;;;;;;; VALORES EXPRESADOS ;;;;;;;;;;;;;;;;;;;;

(define-datatype expval expval?
  (num-val (num number?))
  (complex-val (real number?) (imag number?))
  (bool-val (bool boolean?))
  (string-val (str string?))
  (null-val)
  (list-val (lst list?))
  (proto-val (fields list?) (parent expval?))
  (proc-val (proc procval?)))

;; Conversión a valor de verdad
(define truthy?
  (lambda (val)
    (cases expval val
      (bool-val (b) b)
      (num-val (n) (not (zero? n)))
      (string-val (s) (not (string=? s "")))
      (null-val () #f)
      (else #t))))

;; Extracción de valores
(define expval->num
  (lambda (val)
    (cases expval val
      (num-val (n) n)
      (complex-val (r i) r)
      (else (eopl:error 'expval->num "Not a number: ~s" val)))))

(define expval->complex
  (lambda (val)
    (cases expval val
      (complex-val (r i) (cons r i))
      (num-val (n) (cons n 0))
      (else (eopl:error 'expval->complex "Not a complex: ~s" val)))))

(define expval->string
  (lambda (val)
    (cases expval val
      (string-val (s) s)
      (else (eopl:error 'expval->string "Not a string: ~s" val)))))

(define expval->list
  (lambda (val)
    (cases expval val
      (list-val (lst) lst)
      (else (eopl:error 'expval->list "Not a list: ~s" val)))))

(define expval->proto
  (lambda (val)
    (cases expval val
      (proto-val (fields parent) (cons fields parent))
      (else (eopl:error 'expval->proto "Not a prototype: ~s" val)))))

;;;;;;;;;;;;;;;;;;;; PROCEDIMIENTOS ;;;;;;;;;;;;;;;;;;;;

(define-datatype procval procval?
  (closure
    (ids (list-of symbol?))
    (body expression?)
    (saved-env environment?)))

(define apply-procval
  (lambda (proc args this-binding)
    (cases procval proc
      (closure (ids body saved-env)
        (if (not (= (length ids) (length args)))
            (eopl:error 'apply-procval "Wrong number of arguments")
            (let* ((new-env (extend-env ids args saved-env))
                   (new-env (if (null-val? this-binding)
                                new-env
                                (extend-env '(this) (list this-binding) new-env))))
              (eval-expression body new-env)))))))

;;;;;;;;;;;;;;;;;;;; REFERENCIAS ;;;;;;;;;;;;;;;;;;;;

(define-datatype reference reference?
  (a-ref (position integer?) (vec vector?))
  (const-ref (value expval?)))

(define deref
  (lambda (ref)
    (cases reference ref
      (a-ref (pos vec) (vector-ref vec pos))
      (const-ref (val) val))))

(define setref!
  (lambda (ref val)
    (cases reference ref
      (a-ref (pos vec) (vector-set! vec pos val))
      (const-ref (v) (eopl:error 'setref! "Cannot modify constant")))))

;;;;;;;;;;;;;;;;;;;; AMBIENTES ;;;;;;;;;;;;;;;;;;;;

(define-datatype environment environment?
  (empty-env-record)
  (extended-env-record
    (syms (list-of symbol?))
    (vec vector?)
    (env environment?))
  (extended-const-env-record
    (syms (list-of symbol?))
    (vals (list-of expval?))
    (env environment?)))

(define empty-env
  (lambda () (empty-env-record)))

(define extend-env
  (lambda (syms vals env)
    (extended-env-record syms (list->vector vals) env)))

(define extend-const-env
  (lambda (syms vals env)
    (extended-const-env-record syms vals env)))

(define extend-env-recursively
  (lambda (proc-names idss bodies env)
    (let ((len (length proc-names)))
      (let ((vec (make-vector len)))
        (let ((new-env (extended-env-record proc-names vec env)))
          (for-each
            (lambda (pos ids body)
              (vector-set! vec pos (closure ids body new-env)))
            (iota len) idss bodies)
          new-env)))))

(define apply-env-ref
  (lambda (env sym)
    (cases environment env
      (empty-env-record ()
        (eopl:error 'apply-env-ref "Unbound variable: ~s" sym))
      (extended-env-record (syms vec e)
        (let ((pos (list-find-position sym syms)))
          (if (number? pos)
              (a-ref pos vec)
              (apply-env-ref e sym))))
      (extended-const-env-record (syms vals e)
        (let ((pos (list-find-position sym syms)))
          (if (number? pos)
              (const-ref (list-ref vals pos))
              (apply-env-ref e sym)))))))

(define apply-env
  (lambda (env sym)
    (deref (apply-env-ref env sym))))

(define list-find-position
  (lambda (sym los)
    (let loop ((los los) (pos 0))
      (cond
        ((null? los) #f)
        ((eqv? sym (car los)) pos)
        (else (loop (cdr los) (+ pos 1)))))))

(define iota
  (lambda (end)
    (let loop ((next 0))
      (if (>= next end) '()
        (cons next (loop (+ 1 next)))))))