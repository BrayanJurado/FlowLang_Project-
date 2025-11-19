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

;;;;;;;;;;;;;;;;;;;; GRAMATICA  ;;;;;;;;;;;;;;;;;;;;

<program> ::= <expression>

<expression> ::= <number>
              |  <string-lit>
              |  <identifier> {"." <identifier>}*
              |  "true" | "false" | "null" | "this"
              |  "var" {<identifier> "=" <expression>}+ "in" <expression>
              |  "const" {<identifier> "=" <expression>}+ "in" <expression>
              |  "set" <identifier> "=" <expression>
              |  "complejo" "(" <expression> "," <expression> ")"
              |  <primitive> "(" (separated-list <expression> ",") ")"
              |  "if" <expression> "then" <expression> "else" <expression> "end"
              |  "switch" <expression> (arbno "case" <expression> ":" <expression>) 
                 "default" ":" <expression> "end"
              |  "while" <expression> "do" <expression> "done"
              |  "for" <identifier> "in" <expression> "do" <expression> "done"
              |  "func" "(" (separated-list <identifier> ",") ")" <expression>
              |  "(" <expression> (arbno <expression>) ")"
              |  "letrec" (separated-list <identifier> "(" (separated-list <identifier> ",") ")" "=" <expression> ";")
                 "in" <expression>
              |  "begin" <expression> (arbno ";" <expression>) "end"
              |  "prototipo" <identifier> "=" <expression> "in" <expression>
              |  "[" (separated-list <expression> ",") "]"
              |  "call-method" "(" <expression> "," <expression> (arbno "," <expression>) ")"

<primitive> ::= "+" | "-" | "*" | "/" | "mod" | "add1" | "sub1" | "zero?"
              |  "<" | ">" | "<=" | ">=" | "==" | "<>"
              |  "and" | "or" | "not"
              |  "longitud" | "concatenar"
              |  "vacio" | "vacio?" | "crear-lista" | "lista?" 
              |  "cabeza" | "cola" | "append" | "ref-list" | "set-list"
              |   "crear-diccionario" | "diccionario?" | "ref-diccionario" 
              |  "set-diccionario" | "claves" | "valores"
              |  "clone" | "print" | "real" | "imag"
              |  "get-field"

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
      ("letrec" (separated-list identifier "(" (separated-list identifier ",") ")" "=" expression ";")
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
    (primitive ("call-method") call-method-prim)

    ;; Listas y diccionarios literales
    (expression ("[" (separated-list expression ",") "]") list-literal-exp)
    ;;(expression ("{" (separated-list identifier ":" expression ",") "}") dict-literal-exp)
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
  (list-val (vec vector?))
  (proto-val (dict-vec vector?))
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
      (list-val (vec) vec)
      (else (eopl:error 'expval->list "Not a list: ~s" val)))))

(define expval->dict
  (lambda (val)
    (cases expval val
      (proto-val (dict-vec) dict-vec)
      (else (eopl:error 'expval->dict "Not a dict: ~s" val)))))

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
              (vector-set! vec pos (proc-val (closure ids body new-env))))
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
            (apply-env env id)
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
        (let ((lst-val (eval-expression lst-exp env)))
          (cases expval lst-val
            (list-val (vec)
              (let ((len (vector-length vec)))
                (let loop ((i 0))
                  (if (< i len)
                      (let ((new-env (extend-env (list var) (list (vector-ref vec i)) env)))
                        (eval-expression body new-env)
                        (loop (+ i 1)))
                      (null-val)))))
            (else (eopl:error 'for-exp "Not a list")))))

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
        (let ((vals (map (lambda (e) (eval-expression e env)) exps)))
          (list-val (list->vector vals)))))))
      
   

;;;;;;;;;;;;;;;;;;;; OPERACIONES CON PROTOTIPOS ;;;;;;;;;;;;;;;;;;;;

(define proto-get-field
  (lambda (obj field-sym)
    (let ((field-str (symbol->string field-sym)))
      (cases expval obj
        (proto-val (dict-vec)
          (let ((fields (vector-ref dict-vec 0)))
            (let ((binding (assoc field-str fields)))
              (if binding
                  (cdr binding)
                  (null-val)))))
        (else (eopl:error 'proto-get-field "Not a prototype: ~s" obj))))))

(define proto-set-field
  (lambda (obj field-sym val)
    (let ((field-str (symbol->string field-sym)))
      (cases expval obj
        (proto-val (dict-vec)
          (let ((fields (vector-ref dict-vec 0)))
            (let ((binding (assoc field-str fields)))
              (if binding
                  (vector-set! dict-vec 0
                    (map (lambda (p)
                           (if (string=? (car p) field-str)
                               (cons field-str val)
                               p))
                         fields))
                  (vector-set! dict-vec 0 (cons (cons field-str val) fields)))))
          obj)
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
                    (remainder v1 v2)
                    (- v1 (* v2 (truncate (/ v1 v2)))))))))
      
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

      ;; Listas - MUTABLES
      (empty-list-prim () (list-val (make-vector 0)))
      (empty?-prim () 
        (cases expval (car args)
          (list-val (vec) (bool-val (zero? (vector-length vec))))
          (else (bool-val #f))))
      (cons-prim () 
        (let ((item (car args)))
          (cases expval (cadr args)
            (list-val (vec)
              (let* ((len (vector-length vec))
                     (new-vec (make-vector (+ len 1))))
                (vector-set! new-vec 0 item)
                (let loop ((i 0))
                  (if (< i len)
                      (begin
                        (vector-set! new-vec (+ i 1) (vector-ref vec i))
                        (loop (+ i 1)))
                      (null-val)))
                (list-val new-vec)))
            (else (eopl:error 'cons "Second argument must be a list")))))
      (list?-prim ()
        (cases expval (car args)
          (list-val (vec) (bool-val #t))
          (else (bool-val #f))))
      (car-prim ()
        (cases expval (car args)
          (list-val (vec)
            (if (zero? (vector-length vec))
                (eopl:error 'car "Empty list")
                (vector-ref vec 0)))
          (else (eopl:error 'car "Not a list"))))
      (cdr-prim ()
        (cases expval (car args)
          (list-val (vec)
            (let ((len (vector-length vec)))
              (if (zero? len)
                  (eopl:error 'cdr "Empty list")
                  (let ((new-vec (make-vector (- len 1))))
                    (let loop ((i 0))
                      (if (< i (- len 1))
                          (begin
                            (vector-set! new-vec i (vector-ref vec (+ i 1)))
                            (loop (+ i 1)))
                          (null-val)))
                    (list-val new-vec)))))
          (else (eopl:error 'cdr "Not a list"))))
      (append-prim ()
        (cases expval (car args)
          (list-val (vec1)
            (cases expval (cadr args)
              (list-val (vec2)
                (let* ((len1 (vector-length vec1))
                       (len2 (vector-length vec2))
                       (new-vec (make-vector (+ len1 len2))))
                  (let loop ((i 0))
                    (if (< i len1)
                        (begin
                          (vector-set! new-vec i (vector-ref vec1 i))
                          (loop (+ i 1)))
                        (null-val)))
                  (let loop ((i 0))
                    (if (< i len2)
                        (begin
                          (vector-set! new-vec (+ len1 i) (vector-ref vec2 i))
                          (loop (+ i 1)))
                        (null-val)))
                  (list-val new-vec)))
              (else (eopl:error 'append "Second argument must be a list"))))
          (else (eopl:error 'append "First argument must be a list"))))
      (ref-list-prim ()
        (cases expval (car args)
          (list-val (vec)
            (let ((idx (expval->num (cadr args))))
              (if (and (>= idx 0) (< idx (vector-length vec)))
                  (vector-ref vec idx)
                  (eopl:error 'ref-list "Index out of bounds"))))
          (else (eopl:error 'ref-list "Not a list"))))
      (set-list-prim ()
        (cases expval (car args)
          (list-val (vec)
            (let ((idx (expval->num (cadr args)))
                  (val (caddr args)))
              (if (and (>= idx 0) (< idx (vector-length vec)))
                  (begin
                    (vector-set! vec idx val)
                    (list-val vec))
                  (eopl:error 'set-list "Index out of bounds"))))
          (else (eopl:error 'set-list "Not a list"))))

      ;; Diccionarios - MUTABLES
      (create-dict-prim ()
        (let loop ((items args) (dict '()))
          (if (null? items)
              (let ((dict-vec (make-vector 1)))
                (vector-set! dict-vec 0 dict)
                (proto-val dict-vec))
              (let ((key (expval->string (car items)))
                    (val (cadr items)))
                (loop (cddr items) (cons (cons key val) dict))))))
      (dict?-prim ()
        (cases expval (car args)
          (proto-val (d) (bool-val #t))
          (else (bool-val #f))))
      (ref-dict-prim ()
        (cases expval (car args)
          (proto-val (dict-vec)
            (let ((key (expval->string (cadr args)))
                  (fields (vector-ref dict-vec 0)))
              (let ((binding (assoc key fields)))
                (if binding
                    (cdr binding)
                    (null-val)))))
          (else (eopl:error 'ref-dict "Not a dictionary"))))
      (set-dict-prim ()
        (cases expval (car args)
          (proto-val (dict-vec)
            (let ((key (expval->string (cadr args)))
                  (val (caddr args))
                  (fields (vector-ref dict-vec 0)))
              (let ((binding (assoc key fields)))
                (if binding
                    (vector-set! dict-vec 0
                      (map (lambda (p)
                             (if (string=? (car p) key)
                                 (cons key val)
                                 p))
                           fields))
                    (vector-set! dict-vec 0 (cons (cons key val) fields))))
              (proto-val dict-vec)))
          (else (eopl:error 'set-dict "Not a dictionary"))))
      (keys-prim ()
        (cases expval (car args)
          (proto-val (dict-vec)
            (let ((fields (vector-ref dict-vec 0)))
              (list-val (list->vector (map (lambda (p) (string-val (car p))) fields)))))
          (else (list-val (make-vector 0)))))
      (values-prim ()
        (cases expval (car args)
          (proto-val (dict-vec)
            (let ((fields (vector-ref dict-vec 0)))
              (list-val (list->vector (map cdr fields)))))
          (else (list-val (make-vector 0)))))

      ;; Prototipos
      (clone-prim ()
        (cases expval (car args)
          (proto-val (dict-vec)
            (let ((new-vec (make-vector 1)))
              (vector-set! new-vec 0 (vector-ref dict-vec 0))
              (proto-val new-vec)))
          (else (eopl:error 'clone "Cannot clone non-prototype"))))

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
      
      (call-method-prim ()
  (let ((obj (car args))
        (method-name (expval->string (cadr args)))
        (method-args (cddr args)))
    (let ((method (proto-get-field obj (string->symbol method-name))))
      (cases expval method
        (proc-val (proc) 
          ;; Pasamos obj COMO 'this'
          (apply-procval proc method-args obj))
        (else (eopl:error 'call-method "Not a procedure: ~s" method))))))
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
      (list-val (vec1)
        (cases expval v2
          (list-val (vec2) 
            (and (= (vector-length vec1) (vector-length vec2))
                 (let loop ((i 0))
                   (or (>= i (vector-length vec1))
                       (and (equal-vals? (vector-ref vec1 i) (vector-ref vec2 i))
                            (loop (+ i 1)))))))
          (else #f)))
      (proto-val (dict-vec1)
        (cases expval v2
          (proto-val (dict-vec2)
            (let ((fields1 (vector-ref dict-vec1 0))
                  (fields2 (vector-ref dict-vec2 0)))
              (and (= (length fields1) (length fields2))
                   (let loop ((fs1 fields1) (fs2 fields2))
                     (or (null? fs1)
                         (and (string=? (car (car fs1)) (car (car fs2)))
                              (equal-vals? (cdr (car fs1)) (cdr (car fs2)))
                              (loop (cdr fs1) (cdr fs2))))))))
          (else #f)))
      (else #f))))

(define null-val?
  (lambda (val)
    (cases expval val
      (null-val () #t)
      (else #f))))

(define expval->printable
  (lambda (val)
    (cases expval val
      (num-val (n) (number->string n))
      (complex-val (r i) 
        (if (zero? i)
            (number->string r)
            (string-append (number->string r) "+" (number->string i) "i")))
      (bool-val (b) (if b "true" "false"))
      (string-val (s) s)
      (null-val () "null")
      (list-val (vec) 
        (let ((lst (vector->list vec)))
          (string-append "["
                         (if (null? lst)
                             ""
                             (let ((first (expval->printable (car lst))))
                               (string-append first
                                 (apply string-append
                                   (map (lambda (v)
                                          (string-append ", " (expval->printable v)))
                                        (cdr lst))))))
                         "]")))
      (proto-val (dict-vec)
        (let ((fields (vector-ref dict-vec 0)))
          (string-append "{"
                         (if (null? fields)
                             ""
                             (let ((first-pair (car fields)))
                               (string-append (car first-pair) ": " (expval->printable (cdr first-pair))
                                 (apply string-append
                                   (map (lambda (p)
                                          (string-append ", " (car p) ": " (expval->printable (cdr p))))
                                        (cdr fields))))))
                         "}")))
      (proc-val (p) "#<procedure>"))))

;;;;;;;;;;;;;;;;;;;; INTÉRPRETE INTERACTIVO ;;;;;;;;;;;;;;;;;;;;

(define run
  (lambda (string)
    (eval-program (scan&parse string))))

(define read-eval-print
  (sllgen:make-rep-loop "-->" 
    (lambda (pgm) 
      (let ((result (eval-program pgm)))
        (display (expval->printable result))
        (newline)))
    (sllgen:make-stream-parser the-lexical-spec the-grammar)))

;; Iniciar REPL
(read-eval-print)


#|
============================================
               SUSTENTACIÓN
============================================

-----------------------------------------------------------------
PREGUNTA 1 - Todos los valores denotados en una lista
-----------------------------------------------------------------
Demuestra: enteros, flotantes, complejos, nulos, cadenas,
booleanos, procedimientos, listas, diccionarios, prototipos

var entero = 42,
    flotante = 3.14,
    complejo_num = complejo(2, 5),
    nulo = null,
    cadena = "Hola FlowLang",
    verdadero = true,
    falso = false,
    procedimiento = func(x) +(x, 1),
    lista = [1, 2, 3],
    diccionario = crear-diccionario("nombre", "Ana", "edad", 25)
in
[entero, flotante, complejo_num, nulo, cadena, verdadero, falso, procedimiento, lista, diccionario]

Salida esperada:
> [42, 3.14, 2+5i, null, Hola FlowLang, true, false, #<procedure>, [1, 2, 3], {edad: 25, nombre: Ana}]

NOTA: En nuestra implementación, los proto-val se crean con crear-diccionario, por lo que:
crear-diccionario("nombre", "Ana", "edad", 25) representa un prototipo, cumpliendo con el item j. ✓

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
  null
  #<void>

-----------------------------------------------------------------
PREGUNTA 3: Constantes (variables inmutables)
-----------------------------------------------------------------

- Programa 3a: Crear constante y retornar su valor

const PI = 3.14159 in print(PI)

Salida esperada:
> 3.14159
  null
  #<void>


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

Salida esperada:
> 13
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
  null 
  #<void>

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
  null
  #<void>

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
  null
  #<void>

-----------------------------------------------------------------
PREGUNTA 7: Paso por valor y por referencia 
-----------------------------------------------------------------

var X = [1, 2, 3],
    Y = 100,
    Z = crear-diccionario("a", 10, "b", 20),
    W = "hello"
in
letrec 
    F1(a) = 
        set-list(a, 0, 999);

    F2(b) =
        begin
            set b = 888;
            0
        end;

    F3(c) =
        set-diccionario(c, "a", 777);

    F4(d) =
        begin
            set d = "nuevo";
            0
        end
in
begin
    (F1 X);
    (F2 Y);
    (F3 Z);
    (F4 W);

    print(X);
    print(Y);
    print(Z);
    print(W);

    [X, Y, Z, W]
end

Salida esperada:
> [999, 2, 3]
  100
  {b: 20, a: 777}
  hello
  [[999, 2, 3], 100, {b: 20, a: 777}, hello] 
  #<void>

Análisis:
[999, 2, 3]      ← X CAMBIÓ (paso por referencia) ✓
100              ← Y NO CAMBIÓ (paso por valor) ✓
{a: 777, b: 20}  ← Z CAMBIÓ (paso por referencia) ✓
hello            ← W NO CAMBIÓ (paso por valor) ✓

-----------------------------------------------------------------
PREGUNTA 8: Registro de factoriales 
-----------------------------------------------------------------
letrec
    fact(n) = 
        if <(n, 2) 
        then 
            1 
        else 
            *(n, (fact -(n, 1)))
        end;

    mapFactorial(lista) = 
        if vacio?(lista) 
        then 
            vacio() 
        else 
            crear-lista(
                (fact cabeza(lista)), 
                (mapFactorial cola(lista))
            )
        end;

    registroFactorial(lista) = 
        crear-diccionario(
            "valores",     lista,
            "factoriales", (mapFactorial lista)
        )
in
(registroFactorial [1, 2, 3, 4, 7, 9])

Salida esperada:
> {factoriales: [1, 2, 6, 24, 5040, 362880], valores: [1, 2, 3, 4, 7, 9]}
  #<void>

-----------------------------------------------------------------
PREGUNTA 9: Implementación de la función map 
-----------------------------------------------------------------

letrec map(f, lista) = if vacio?(lista) then vacio() else crear-lista((f cabeza(lista)), (map f cola(lista))) end
in
letrec duplicar(x) = *(x, 2)
in
letrec cuadrado(x) = *(x, x)
in
letrec a_string(x) = concatenar(concatenar("Num: ", 
                          if ==(x, 1) then "1"
                          else if ==(x, 2) then "2"
                          else if ==(x, 3) then "3"
                          else if ==(x, 4) then "4"
                          else "5"
                          end end end end), "")
in
var lista_original = [1, 2, 3, 4, 5]
in
begin
  print("Lista original:");
  print(lista_original);
  
  print("Map - duplicar:");
  var lista_duplicada = (map duplicar lista_original) in
  begin
    print(lista_duplicada);
    
    print("Map - cuadrado:");
    var lista_cuadrados = (map cuadrado lista_original) in
    begin
      print(lista_cuadrados);
      
      print("Map - a_string:");
      var lista_strings = (map a_string lista_original) in
      begin
        print(lista_strings);
        lista_duplicada  

      end
    end
  end
end

Salida esperada:
> Lista original:
  [1, 2, 3, 4, 5]
  Map - duplicar:
  [2, 4, 6, 8, 10]
  Map - cuadrado:
  [1, 4, 9, 16, 25]
  Map - a_string:
  [Num: 1, Num: 2, Num: 3, Num: 4, Num: 5]
  [2, 4, 6, 8, 10]
  #<void>


-----------------------------------------------------------------
PREGUNTA 10: Ciclos 
-----------------------------------------------------------------

- 10.a: Ciclo FOR

var lista_original = [1, 2, 3, 4, 5],
    lista_reciprocos = vacio()
in
begin
  for x in lista_original do
    begin
      var reciproco = /(1, x) in
      begin
        print(concatenar("Original: ", 
          if ==(x, 1) then "1" 
          else if ==(x, 2) then "2"
          else if ==(x, 3) then "3"
          else if ==(x, 4) then "4"
          else "5"
          end end end end));
        print(concatenar("Reciproco: ", 
          if ==(x, 1) then "1.0"
          else if ==(x, 2) then "0.5" 
          else if ==(x, 3) then "0.333"
          else if ==(x, 4) then "0.25"
          else "0.2"
          end end end end));
        set lista_reciprocos = append(lista_reciprocos, [reciproco])
      end
    end
  done;
  print("Lista de reciprocos construida:");
  print(lista_reciprocos);
  lista_reciprocos
end

Salida esperada:
> Original: 1
  Reciproco: 1.0
  Original: 2
  Reciproco: 0.5
  Original: 3
  Reciproco: 0.333
  Original: 4
  Reciproco: 0.25
  Original: 5
  Reciproco: 0.2
  Lista de reciprocos construida:
  [1, 1/2, 1/3, 1/4, 1/5]
  [1, 1/2, 1/3, 1/4, 1/5]
  #<void>

- 10.b: Ciclo WHILE 

letrec esPar?(n) = ==(mod(n, 2), 0)
in
var i = 1,
    resultados = vacio()
in
begin
  while <=(i, 5) do
    begin
      var es_par = (esPar? i) in
      begin
        print(concatenar("i = ", 
          if ==(i, 1) then "1"
          else if ==(i, 2) then "2"
          else if ==(i, 3) then "3"
          else if ==(i, 4) then "4"
          else "5"
          end end end end));
        print(concatenar("esPar?(i) = ", 
          if es_par then "true" else "false" end));
        set resultados = append(resultados, [es_par]);
        set i = add1(i)
      end
    end
  done;
  print("Lista de resultados esPar?:");
  print(resultados);
  resultados
end

Salida esperada:
> i = 1
  esPar?(i) = false
  i = 2
  esPar?(i) = true
  i = 3
  esPar?(i) = false
  i = 4
  esPar?(i) = true
  i = 5
  esPar?(i) = false
  Lista de resultados esPar?:
  [false, true, false, true, false]
  [false, true, false, true, false]
  #<void>

-----------------------------------------------------------------
PREGUNTA 11: Prototipos 
-----------------------------------------------------------------

prototipo Vehiculo = crear-diccionario("Marca", "Sin marca", "Modelo", "Sin modelo") in
begin
  set-diccionario(Vehiculo, "setMarca", 
    func(nuevaMarca) 
      begin
        set-diccionario(this, "Marca", nuevaMarca);
        this
      end
  );
  
  set-diccionario(Vehiculo, "getMarca",
    func() ref-diccionario(this, "Marca")
  );
  
  set-diccionario(Vehiculo, "setModelo",
    func(nuevoModelo)
      begin
        set-diccionario(this, "Modelo", nuevoModelo);
        this
      end
  );
  
  set-diccionario(Vehiculo, "getModelo",
    func() ref-diccionario(this, "Modelo")
  );
  
  set-diccionario(Vehiculo, "describir",
    func()
      concatenar(
        concatenar("Vehiculo: ", ref-diccionario(this, "Marca")),
        concatenar(" - Modelo: ", ref-diccionario(this, "Modelo"))
      )
  );
  
  prototipo Moto = clone(Vehiculo) in
  begin
    set-diccionario(Moto, "Cilindrada", "0");
    
    set-diccionario(Moto, "setCilindrada",
      func(nuevaCilindrada)
        begin
          set-diccionario(this, "Cilindrada", nuevaCilindrada);
          this
        end
    );
    
    set-diccionario(Moto, "getCilindrada",
      func() ref-diccionario(this, "Cilindrada")
    );
    
    set-diccionario(Moto, "describir",
      func()
        concatenar(
          concatenar(
            concatenar("Moto: ", ref-diccionario(this, "Marca")),
            concatenar(" - ", ref-diccionario(this, "Modelo"))
          ),
          concatenar(" - ", concatenar(ref-diccionario(this, "Cilindrada"), "cc"))
        )
    );
    
    prototipo moto1 = clone(Moto) in
    begin
      call-method(moto1, "setMarca", "Yamaha");
      call-method(moto1, "setModelo", "YZF-R1");
      call-method(moto1, "setCilindrada", "998");
      
      prototipo moto2 = clone(Moto) in
      begin
        call-method(moto2, "setMarca", "Honda");
        call-method(moto2, "setModelo", "CB500F");
        call-method(moto2, "setCilindrada", "471");
        
        prototipo moto3 = clone(Moto) in
        begin
          call-method(moto3, "setMarca", "Kawasaki");
          call-method(moto3, "setModelo", "Ninja 400");
          call-method(moto3, "setCilindrada", "399");
          
          begin
            print("====================================================");
            print("   DEMOSTRACION: HERENCIA CON PROTOTIPOS");
            print("   Vehiculo -> Moto -> moto1, moto2, moto3");
            print("====================================================");
            print("");
            
            print("--- INFORMACION DE LAS 3 MOTOS ---");
            print(call-method(moto1, "describir"));
            print(call-method(moto2, "describir"));
            print(call-method(moto3, "describir"));
            print("");
            
            print("--- PRUEBA DE GETTERS ---");
            print(concatenar("Marca de moto1 (heredado): ", 
                            call-method(moto1, "getMarca")));
            print(concatenar("Modelo de moto2 (heredado): ",
                            call-method(moto2, "getModelo")));
            print(concatenar("Cilindrada de moto3 (propio): ",
                            call-method(moto3, "getCilindrada")));
            print("");
            
            print("--- PRUEBA DE SETTERS (Modificando atributos) ---");
            print("Cambiando marca de moto1 a 'Yamaha Racing'...");
            call-method(moto1, "setMarca", "Yamaha Racing");
            
            print("Cambiando cilindrada de moto3 a 450cc...");
            call-method(moto3, "setCilindrada", "450");
            
            print("Nuevos valores:");
            print(call-method(moto1, "describir"));
            print(call-method(moto3, "describir"));
            print("");
            
            print("--- VERIFICACION DE HERENCIA ---");
            print("Moto1 tiene setMarca heredado de Vehiculo? Si");
            print("Moto1 tiene setCilindrada propio de Moto? Si");
            print("Moto1 sobrescribio el metodo describir? Si");
            print("");
            
            print("--- COMPARACION: Vehiculo base vs Moto heredada ---");
            prototipo vehiculoBase = clone(Vehiculo) in
            begin
              call-method(vehiculoBase, "setMarca", "Ford");
              call-method(vehiculoBase, "setModelo", "Mustang");
              print(concatenar("Vehiculo base: ", 
                              call-method(vehiculoBase, "describir")));
              print(concatenar("Moto (heredada): ",
                              call-method(moto1, "describir")));
              print("");
              
              print("====================================================");
              print("   CONCLUSION: Herencia exitosa demostrada");
              print("   - 3 motos creadas con diferentes atributos");
              print("   - Getters y setters funcionando correctamente");
              print("   - Metodos heredados de Vehiculo operativos");
              print("   - Atributo Cilindrada exclusivo de Moto");
              print("   - 'this' vinculado automaticamente en metodos");
              print("   - Usa palabra clave 'prototipo' correctamente");
              print("====================================================");
              
              moto1
            end
          end
        end
      end
    end
  end
end

Salida esperada:
====================================================
   DEMOSTRACION: HERENCIA CON PROTOTIPOS
   Vehiculo -> Moto -> moto1, moto2, moto3
====================================================

--- INFORMACION DE LAS 3 MOTOS ---
Moto: Yamaha - YZF-R1 - 998cc
Moto: Honda - CB500F - 471cc
Moto: Kawasaki - Ninja 400 - 399cc

--- PRUEBA DE GETTERS ---
Marca de moto1 (heredado): Yamaha
Modelo de moto2 (heredado): CB500F
Cilindrada de moto3 (propio): 399

--- PRUEBA DE SETTERS (Modificando atributos) ---
Cambiando marca de moto1 a 'Yamaha Racing'...
Cambiando cilindrada de moto3 a 450cc...
Nuevos valores:
Moto: Yamaha Racing - YZF-R1 - 998cc
Moto: Kawasaki - Ninja 400 - 450cc

--- VERIFICACION DE HERENCIA ---
Moto1 tiene setMarca heredado de Vehiculo? Si
Moto1 tiene setCilindrada propio de Moto? Si
Moto1 sobrescribio el metodo describir? Si

--- COMPARACION: Vehiculo base vs Moto heredada ---
Vehiculo base: Vehiculo: Ford - Modelo: Mustang
Moto (heredada): Moto: Yamaha Racing - YZF-R1 - 998cc

====================================================
   CONCLUSION: Herencia exitosa demostrada
   - 3 motos creadas con diferentes atributos
   - Getters y setters funcionando correctamente
   - Metodos heredados de Vehiculo operativos
   - Atributo Cilindrada exclusivo de Moto
   - 'this' vinculado automaticamente en metodos
   - Usa palabra clave 'prototipo' correctamente
====================================================
{getCilindrada: #<procedure>, setCilindrada: #<procedure>, Cilindrada: 998, describir: #<procedure>, getModelo: #<procedure>, setModelo: #<procedure>, getMarca: #<procedure>, setMarca: #<procedure>, Modelo: YZF-R1, Marca: Yamaha Racing}
#<void>

|#