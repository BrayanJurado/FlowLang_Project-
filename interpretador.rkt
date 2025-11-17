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
              |  "func" "(" {<identifier>}*, ")#" <expression>
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
    (primitive ("mod") mod-prim)
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

;;;;;;;;;;;;;;;;;;;; EVALUADOR ;;;;;;;;;;;;;;;;;;;;

(define eval-program
  (lambda (pgm)
    (cases program pgm
      (a-program (exp)
        (eval-expression exp (init-env))))))

(define init-env
  (lambda ()
    (empty-env)))

(define eval-expression
  (lambda (exp env)
    (cases expression exp
      ;; Literales
      (lit-exp (n) (num-val n))
      (string-exp (s) (string-val (substring s 1 (- (string-length s) 1))))
      (true-exp () (bool-val #t))
      (false-exp () (bool-val #f))
      (null-exp () (null-val))
      (this-exp () (apply-env env 'this))
      
      ;; Números complejos
      (complex-exp (real-exp imag-exp)
        (complex-val (expval->num (eval-expression real-exp env))
                     (expval->num (eval-expression imag-exp env))))
      
      ;; Variables y acceso a campos 
      (id-exp (id chain)
        (if (null? chain)
            ;; Sin cadena: es solo una variable
            (apply-env env id)
            ;; Con cadena: es acceso a campo(s)
            (let ((obj (apply-env env id)))
              (let loop ((obj obj) (fields chain))
                (if (null? fields)
                    obj
                    (loop (proto-get-field obj (car fields))
                          (cdr fields)))))))
      
      ;; Declaraciones
      (var-decl-exp (ids exps body)
        (let ((vals (map (lambda (e) (eval-expression e env)) exps)))
          (eval-expression body (extend-env ids vals env))))
      
      (const-decl-exp (ids exps body)
        (let ((vals (map (lambda (e) (eval-expression e env)) exps)))
          (eval-expression body (extend-const-env ids vals env))))
      
      (proto-decl-exp (id exp body)
        (let ((val (eval-expression exp env)))
          (eval-expression body (extend-env (list id) (list val) env))))
      
      ;; Asignación
      (assign-exp (id exp)
        (let ((val (eval-expression exp env)))
          (setref! (apply-env-ref env id) val)
          val))
      
      ;; Aplicación de primitivas
      (primapp-exp (prim rands)
        (let ((args (map (lambda (e) (eval-expression e env)) rands)))
          (apply-primitive prim args env)))
      
      ;; Control de flujo
      (if-exp (test conseq alt)
        (if (truthy? (eval-expression test env))
            (eval-expression conseq env)
            (eval-expression alt env)))
      
      (switch-exp (test cases values default)
        (let ((test-val (eval-expression test env)))
          (let loop ((cases cases) (values values))
            (if (null? cases)
                (eval-expression default env)
                (if (equal-vals? test-val (eval-expression (car cases) env))
                    (eval-expression (car values) env)
                    (loop (cdr cases) (cdr values)))))))
      
      ;; Iteración
      (while-exp (test body)
        (let loop ()
          (if (truthy? (eval-expression test env))
              (begin
                (eval-expression body env)
                (loop))
              (null-val))))
      
      (for-exp (var lst-exp body)
        (let ((lst (expval->list (eval-expression lst-exp env))))
          (let loop ((items lst))
            (if (null? items)
                (null-val)
                (let ((new-env (extend-env (list var) (list (car items)) env)))
                  (eval-expression body new-env)
                  (loop (cdr items)))))))
      
      ;; Funciones
      (func-exp (ids body)
        (proc-val (closure ids body env)))
      
      (app-exp (rator rands)
        (let ((proc (eval-expression rator env))
              (args (map (lambda (e) (eval-expression e env)) rands)))
          (cases expval proc
            (proc-val (p) (apply-procval p args (null-val)))
            (else (eopl:error 'eval-expression 
                    "Attempt to apply non-procedure ~s" proc)))))
      
      (letrec-exp (proc-names idss bodies letrec-body)
        (eval-expression letrec-body
          (extend-env-recursively proc-names idss bodies env)))
      
      ;; Secuenciación
      (begin-exp (first rest)
        (let loop ((result (eval-expression first env))
                   (exps rest))
          (if (null? exps)
              result
              (loop (eval-expression (car exps) env) (cdr exps)))))
      
      ;; Literales
      (list-literal-exp (exps)
        (list-val (map (lambda (e) (eval-expression e env)) exps)))
      
      (dict-literal-exp (keys vals)
        (let ((key-strs (map symbol->string keys))
              (val-expvals (map (lambda (e) (eval-expression e env)) vals)))
          (proto-val (map cons key-strs val-expvals) (null-val))))
      )))

;;;;;;;;;;;;;;;;;;;; OPERACIONES CON PROTOTIPOS ;;;;;;;;;;;;;;;;;;;;

(define proto-get-field
  (lambda (obj field-sym)
    (let ((field-str (symbol->string field-sym)))
      (cases expval obj
        (proto-val (fields parent)
          (let ((binding (assoc field-str fields)))
            (if binding
                (cdr binding)
                (if (null-val? parent)
                    (null-val)
                    (proto-get-field parent field-sym)))))
        (else (eopl:error 'proto-get-field "Not a prototype: ~s" obj))))))

(define proto-set-field
  (lambda (obj field-sym val)
    (let ((field-str (symbol->string field-sym)))
      (cases expval obj
        (proto-val (fields parent)
          (let ((binding (assoc field-str fields)))
            (if binding
                ;; Reemplazar el binding existente
                (proto-val (map (lambda (p)
                                  (if (string=? (car p) field-str)
                                      (cons field-str val)
                                      p))
                                fields)
                          parent)
                ;; Agregar nuevo campo
                (proto-val (cons (cons field-str val) fields) parent))))
        (else (eopl:error 'proto-set-field "Not a prototype: ~s" obj))))))

;;;;;;;;;;;;;;;;;;;; APLICACIÓN DE PRIMITIVAS ;;;;;;;;;;;;;;;;;;;;

(define apply-primitive
  (lambda (prim args env)
    (cases primitive prim
      ;; Aritméticas básicas
      (add-prim ()
        (let ((v1 (car args)) (v2 (cadr args)))
          (cases expval v1
            (complex-val (r1 i1)
              (let ((c2 (expval->complex v2)))
                (complex-val (+ r1 (car c2)) (+ i1 (cdr c2)))))
            (else (num-val (+ (expval->num v1) (expval->num v2)))))))
      
      (subtract-prim ()
        (let ((v1 (car args)) (v2 (cadr args)))
          (cases expval v1
            (complex-val (r1 i1)
              (let ((c2 (expval->complex v2)))
                (complex-val (- r1 (car c2)) (- i1 (cdr c2)))))
            (else (num-val (- (expval->num v1) (expval->num v2)))))))
      
      (mult-prim ()
        (let ((v1 (car args)) (v2 (cadr args)))
          (cases expval v1
            (complex-val (r1 i1)
              (let ((c2 (expval->complex v2)))
                (let ((r2 (car c2)) (i2 (cdr c2)))
                  (complex-val (- (* r1 r2) (* i1 i2))
                              (+ (* r1 i2) (* i1 r2))))))
            (else (num-val (* (expval->num v1) (expval->num v2)))))))
      
      (div-prim ()
        (let ((v1 (car args)) (v2 (cadr args)))
          (cases expval v1
            (complex-val (r1 i1)
              (let ((c2 (expval->complex v2)))
                (let ((r2 (car c2)) (i2 (cdr c2)))
                  (let ((denom (+ (* r2 r2) (* i2 i2))))
                    (complex-val (/ (+ (* r1 r2) (* i1 i2)) denom)
                                (/ (- (* i1 r2) (* r1 i2)) denom))))))
            (else
              (let ((n2 (expval->num v2)))
                (if (zero? n2)
                    (eopl:error 'div "Division by zero")
                    (num-val (/ (expval->num v1) n2))))))))
      
      (mod-prim () 
  (let ((v1 (expval->num (car args))) 
        (v2 (expval->num (cadr args))))
    (if (zero? v2)
        (eopl:error 'mod "Modulo by zero")
        (num-val 
          (if (and (integer? v1) (integer? v2))
              (remainder v1 v2)                    ; Para enteros
              (- v1 (* v2 (truncate (/ v1 v2))))))))); Para flotantes
      
      (incr-prim () (num-val (+ (expval->num (car args)) 1)))
      (decr-prim () (num-val (- (expval->num (car args)) 1)))
      (zero-test-prim () (bool-val (zero? (expval->num (car args)))))
      
      ;; Comparaciones
      (less-prim () (bool-val (< (expval->num (car args)) (expval->num (cadr args)))))
      (greater-prim () (bool-val (> (expval->num (car args)) (expval->num (cadr args)))))
      (lesseq-prim () (bool-val (<= (expval->num (car args)) (expval->num (cadr args)))))
      (greatereq-prim () (bool-val (>= (expval->num (car args)) (expval->num (cadr args)))))
      (equal-prim () (bool-val (equal-vals? (car args) (cadr args))))
      (notequal-prim () (bool-val (not (equal-vals? (car args) (cadr args)))))
      
      ;; Booleanas
      (and-prim () (bool-val (and (truthy? (car args)) (truthy? (cadr args)))))
      (or-prim () (bool-val (or (truthy? (car args)) (truthy? (cadr args)))))
      (not-prim () (bool-val (not (truthy? (car args)))))
      
      ;; Cadenas
      (length-prim () (num-val (string-length (expval->string (car args)))))
      (concat-prim () (string-val (string-append (expval->string (car args))
                                                  (expval->string (cadr args)))))
      
      ;; Listas
      (empty-list-prim () (list-val '()))
      (empty?-prim () (bool-val (null? (expval->list (car args)))))
      (cons-prim () (list-val (cons (car args) (expval->list (cadr args)))))
      (list?-prim ()
        (cases expval (car args)
          (list-val (lst) (bool-val #t))
          (else (bool-val #f))))
      (car-prim ()
        (let ((lst (expval->list (car args))))
          (if (null? lst)
              (eopl:error 'car "Empty list")
              (car lst))))
      (cdr-prim ()
        (let ((lst (expval->list (car args))))
          (if (null? lst)
              (eopl:error 'cdr "Empty list")
              (list-val (cdr lst)))))
      (append-prim () (list-val (append (expval->list (car args))
                                        (expval->list (cadr args)))))
      (ref-list-prim ()
        (let ((lst (expval->list (car args)))
              (idx (expval->num (cadr args))))
          (list-ref lst idx)))
      (set-list-prim ()
        (let ((lst (expval->list (car args)))
              (idx (expval->num (cadr args)))
              (val (caddr args)))
          (list-val (list-set lst idx val))))
      
      ;; Diccionarios 
      (create-dict-prim ()
        (let loop ((items args) (dict '()))
          (if (null? items)
              (proto-val dict (null-val))
              (let ((key (expval->string (car items)))
                    (val (cadr items)))
                (loop (cddr items) (cons (cons key val) dict))))))
      (dict?-prim ()
        (cases expval (car args)
          (proto-val (d p) (bool-val #t))
          (else (bool-val #f))))
      (ref-dict-prim ()
        (let ((obj (car args))
              (key (expval->string (cadr args))))
          (cases expval obj
            (proto-val (fields parent)
              (let ((binding (assoc key fields)))
                (if binding
                    (cdr binding)
                    (if (null-val? parent)
                        (null-val)
                        (ref-dict-prim (list parent (cadr args)))))))
            (else (null-val)))))
      (set-dict-prim ()
        (let ((obj (car args))
              (key (expval->string (cadr args)))
              (val (caddr args)))
          (cases expval obj
            (proto-val (fields parent)
              (let ((binding (assoc key fields)))
                (if binding
                    ;; Reemplazar binding existente
                    (proto-val (map (lambda (p)
                                      (if (string=? (car p) key)
                                          (cons key val)
                                          p))
                                    fields)
                              parent)
                    ;; Agregar nuevo campo
                    (proto-val (cons (cons key val) fields) parent))))
            (else (eopl:error 'set-dict "Not a dictionary")))))
      (keys-prim ()
        (cases expval (car args)
          (proto-val (fields parent)
            (list-val (map (lambda (p) (string-val (car p))) fields)))
          (else (list-val '()))))
      (values-prim ()
        (cases expval (car args)
          (proto-val (fields parent)
            (list-val (map cdr fields)))
          (else (list-val '()))))
      
      ;; Prototipos
      (clone-prim ()
        (let ((obj (car args)))
          (cases expval obj
            (proto-val (fields parent)
              ;; Crear nuevo prototipo con el objeto actual como padre
              (proto-val '() obj))
            (else (eopl:error 'clone "Cannot clone non-prototype")))))
      
      ;; Números complejos
      (real-prim ()
        (cases expval (car args)
          (complex-val (r i) (num-val r))
          (num-val (n) (num-val n))
          (else (eopl:error 'real "Not a number"))))
      
      (imag-prim ()
        (cases expval (car args)
          (complex-val (r i) (num-val i))
          (num-val (n) (num-val 0))
          (else (eopl:error 'imag "Not a number"))))
      
      ;; Print
      (print-prim ()
        (begin
          (display (expval->printable (car args)))
          (newline)
          (null-val)))
      
      ;; Acceso y asignación de campos
      (get-field-prim ()
        (let ((obj (car args))
              (field-name (expval->string (cadr args))))
          (proto-get-field obj (string->symbol field-name))))
      
      (set-field-prim ()
        (let ((obj (car args))
              (field-name (expval->string (cadr args)))
              (val (caddr args)))
          (proto-set-field obj (string->symbol field-name) val)))
      )))

;;;;;;;;;;;;;;;;;;;; FUNCIONES AUXILIARES ;;;;;;;;;;;;;;;;;;;;

(define equal-vals?
  (lambda (v1 v2)
    (cases expval v1
      (num-val (n1)
        (cases expval v2
          (num-val (n2) (= n1 n2))
          (else #f)))
      (complex-val (r1 i1)
        (cases expval v2
          (complex-val (r2 i2) (and (= r1 r2) (= i1 i2)))
          (else #f)))
      (bool-val (b1)
        (cases expval v2
          (bool-val (b2) (eqv? b1 b2))
          (else #f)))
      (string-val (s1)
        (cases expval v2
          (string-val (s2) (string=? s1 s2))
          (else #f)))
      (null-val ()
        (cases expval v2
          (null-val () #t)
          (else #f)))
      (else #f))))

(define list-set
  (lambda (lst idx val)
    (if (zero? idx)
        (cons val (cdr lst))
        (cons (car lst) (list-set (cdr lst) (- idx 1) val)))))

(define null-val?
  (lambda (val)
    (cases expval val
      (null-val () #t)
      (else #f))))

(define expval->printable
  (lambda (val)
    (cases expval val
      (num-val (n) n)
      (complex-val (r i) 
        (if (zero? i)
            r
            (string-append (number->string r) "+" (number->string i) "i")))
      (bool-val (b) (if b "true" "false"))
      (string-val (s) s)
      (null-val () "null")
      (list-val (lst) (list->printable lst))
      (proto-val (fields parent) (proto->printable fields))
      (proc-val (p) "#<procedure>"))))

(define list->printable
  (lambda (lst)
    (string-append "["
                   (if (null? lst)
                       ""
                       (string-append
                        (expval->printable (car lst))
                        (apply string-append
                               (map (lambda (v)
                                      (string-append ", " (expval->printable v)))
                                    (cdr lst)))))
                   "]")))

(define proto->printable
  (lambda (fields)
    (string-append "{"
                   (if (null? fields)
                       ""
                       (string-append
                        (car (car fields)) ": " (expval->printable (cdr (car fields)))
                        (apply string-append
                               (map (lambda (p)
                                      (string-append ", " (car p) ": " (expval->printable (cdr p))))
                                    (cdr fields)))))
                   "}")))

;;;;;;;;;;;;;;;;;;;; INTÉRPRETE INTERACTIVO ;;;;;;;;;;;;;;;;;;;;

(define run
  (lambda (string)
    (eval-program (scan&parse string))))

(define read-eval-print
  (sllgen:make-rep-loop "-->" eval-program
                        (sllgen:make-stream-parser the-lexical-spec the-grammar)))

;; Iniciar REPL
(read-eval-print)

#|
============================================
               SUSTENTACIÓN
============================================

-----------------------------------------------------------------
PREGUNTA 1 - Todos los valores denotados en UNA lista
-----------------------------------------------------------------
Demuestra: enteros, flotantes, complejos, nulos, cadenas,
booleanos, procedimientos, listas, diccionarios, prototipos

[
  42,
  3.14,
  complejo(2, 5),
  null,
  "Hola FlowLang",
  true,
  false,
  func(x) +(x, 1),
  [1, 2, 3],
  {nombre: "Ana", edad: 25}
]

Salida esperada:
> #(struct:list-val (#(struct:num-val 42) #(struct:num-val 3.14) #(struct:complex-val 2 5) #(struct:null-val) #(struct:string-val "Hola FlowLang") #(struct:bool-val #t) #(struct:bool-val #f)
  #(struct:proc-val #(struct:closure (x) #(struct:primapp-exp #(struct:add-prim) (#(struct:id-exp x ()) #(struct:lit-exp 1))) #(struct:empty-env-record))) #(struct:list-val (#(struct:num-val 1) #(struct:num-val 2) #(struct:num-val 3)))
  #(struct:proto-val (("nombre" . #(struct:string-val "Ana")) ("edad" . #(struct:num-val 25))) #(struct:null-val))))

-----------------------------------------------------------------
PREGUNTA 2: Variables mutables (set)
-----------------------------------------------------------------
Demuestra modificación de variable con set

var X = 100 in
begin
  print(X);
  set X = 999;
  print(X)
end

Salida esperada:
> 100
  999
  #(struct:null-val)

-----------------------------------------------------------------
PREGUNTA 3: Constantes (variables inmutables)
-----------------------------------------------------------------

- Programa 3a: Crear constante y retornar su valor

const PI = 3.14159 in print(PI)

Salida esperada:
> 3.14159
  #(struct:null-val)


- Programa 3b: Intentar modificar constante (debe dar ERROR)

const MAX = 100 in
begin
  print(MAX);
  set MAX = 200    
end

Salida esperada:
> Cannot modify constant

-----------------------------------------------------------------
PREGUNTA 4: Primitivas aritméticas 
-----------------------------------------------------------------

var a = 10,
    b = 3,
    c = 10.5,
    d = 3.2,
    z1 = complejo(3, 4),
    z2 = complejo(1, 2)
in
begin
  print(+(a, b));
  print(-(a, b));
  print(*(a, b));
  print(mod(a, b));
  print(/(a, b));
  print(add1(a));
  print(sub1(a));
  
  print(+(c, d));
  print(-(c, d));
  print(*(c, d));
  print(mod(c, d));
  print(/(c, d));
  print(add1(c));
  print(sub1(c));
  
  print(+(z1, z2));
  print(-(z1, z2));
  print(*(z1, z2));
  print(/(z1, z2))
end
13
7
30
1
10/3
11
9
13.7
7.3
33.6
0.8999999999999986
3.28125
11.5
9.5
4+6i
2+2i
-5+10i
11/5+-2/5i
#(struct:null-val)

-----------------------------------------------------------------
PREGUNTA 5: Primitivas booleanas 
-----------------------------------------------------------------

var x = 5,
    y = 10,
    z = 5.5,
    w = 10.8,
    verdad = true,
    falso = false
in
begin
  print(<(x, y));
  print(>(x, y));
  print(<=(x, 5));
  print(>=(y, 10));
  print(==(x, 5));
  print(<>(x, y));
  
  print(<(z, w));
  print(>(z, w));
  print(<=(z, 5.5));
  
  print(and(verdad, falso));
  print(or(verdad, falso));
  print(not(verdad))
end

Salida esperada:
> true
  false
  true
  true 
  true 
  true 
  true
  false
  true
  false
  true
  false
  #(struct:null-val)

-----------------------------------------------------------------
PREGUNTA 6: Primitivas de cadenas - (longitud, concatenar)
-----------------------------------------------------------------

var texto1 = "Hola",
    texto2 = " Mundo"
in
begin
  print(longitud(texto1));             
  print(concatenar(texto1, texto2))     
end

Salida esperada:
> 4
  Hola Mundo
  #(struct:null-val)

-----------------------------------------------------------------
PREGUNTA 7: Paso por valor y por referencia - X
-----------------------------------------------------------------

var X = [1, 2, 3],
    Y = 100,
    Z = {a: 10, b: 20},
    W = "texto"
in
letrec
  F1(a) = set-list(a, 0, 999),
  F2(b) = begin set b = 888; b end,
  F3(c) = set-diccionario(c, "a", 777),
  F4(d) = begin set d = "nuevo"; d end
in
begin
  set X = (F1 X);
  (F2 Y);
  set Z = (F3 Z);
  (F4 W);
  
  begin
    print(X);
    print(Y);
    print(Z);
    print(W);
    [X, Y, Z, W]
  end
end

Salida esperada (DEBE DAR):
> [999, 2, 3]
  100
  {a: 777, b: 20}
  texto

-----------------------------------------------------------------
PREGUNTA 8: Registro de factoriales - X
-----------------------------------------------------------------
letrec
  factorial(n) = if <=(n, 1)
                 then 1
                 else *(n, (factorial sub1(n)))
                 end,
  
  factoriales_lista(lst) = if vacio?(lst)
                           then vacio()
                           else crear-lista(
                                  (factorial cabeza(lst)),
                                  (factoriales_lista cola(lst))
                                )
                           end,
  
  registroFactorial(lista) = crear-diccionario(
                               "valores", lista,
                               "factoriales", (factoriales_lista lista)
                             )
in
var input = [1, 2, 3, 4, 7, 9] in
begin
  var resultado = (registroFactorial input) in
  begin
    print(ref-diccionario(resultado, "valores"));
    print(ref-diccionario(resultado, "factoriales"));
    print(resultado)
  end
end

Salida esperada:
> Debe dar un diccionario con valores y sus factoriales

-----------------------------------------------------------------
PREGUNTA 9: Implementación de la función map - ESTA DANDO ERRORES
-----------------------------------------------------------------

letrec
  map(lista, funcion) = if vacio?(lista)
                        then vacio()
                        else crear-lista(
                               (funcion cabeza(lista)),
                               (map cola(lista) funcion)
                             )
                        end,
  
  doble(x) = *(x, 2),
  
  cuadrado(x) = *(x, x)
in
var numeros = [1, 2, 3, 4, 5] in
begin
  print((map numeros doble));
  print((map numeros cuadrado))
end

Salida esperada:
> DEBE DAR: [2, 4, 6, 8, 10]
            [1, 4, 9, 16, 25]