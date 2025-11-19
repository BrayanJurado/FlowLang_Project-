# FlowLang - Lenguaje de Programación Imperativo

[![Racket](https://img.shields.io/badge/Racket-EOPL-blue.svg)](https://racket-lang.org/)


## 👥 Equipo de trabajo

| Nombre | Código | Email | GitHub |
|--------|------|-------|--------|
| Brayan Camilo Urrea Jurado |  2410023 | urrea.brayan@correounivalle.edu.co | [@BrayanJurado](https://github.com/BrayanJurado) |
| Nicolás Enrique Granada Fernandez | 2310107 | granada.nicolas@correounivalle.edu.co | [@NicolasGranada](https://github.com/nicolasgranada) |


**Universidad del Valle**   
**Fundamentos de Interpretación y compilación de lenguajes de programación**   

---

## 🎯 Descripción del Proyecto

****FlowLang** es un lenguaje de programación imperativo con tipos dinámicos. El lenguaje combina características de programación funcional, imperativa y orientada a prototipos.**

---

## ✨ Características

### Tipos de Datos

- **Números**: Enteros, flotantes y complejos
- **Cadenas**: Con soporte para concatenación y longitud
- **Booleanos**: `true` y `false` con evaluación dinámica
- **Nulos**: `null` para valores ausentes
- **Listas**: Estructuras enlazadas mutables
- **Diccionarios**: Pares clave-valor mutables 
- **Prototipos**: Sistema de objetos con herencia por clonación
- **Funciones**: Procedimientos de primera clase con closures

### Variables y Constantes

```scheme
var x = 10 in ...        % Variable mutable
const PI = 3.14 in ...   % Constante inmutable
set x = 20               % Asignación
```

### Operaciones

**Aritméticas**: `+`, `-`, `*`, `/`, `%`, `add1`, `sub1`  
**Comparación**: `<`, `>`, `<=`, `>=`, `==`, `<>`  
**Lógicas**: `and`, `or`, `not`  
**Cadenas**: `longitud`, `concatenar`  
**Listas**: `vacio`, `vacio?`, `crear-lista`, `cabeza`, `cola`, `append`, `ref-list`, `set-list`  
**Diccionarios**: `crear-diccionario`, `ref-diccionario`, `set-diccionario`, `claves`, `valores`

### Control de Flujo

```scheme
% Condicional
if condicion then expresion else expresion end

% Switch
switch valor
  case 1: expresion1
  case 2: expresion2
  default: expresion_default
end

% Iteración
while condicion do expresion done
for x in lista do expresion done
```

### Funciones

```scheme
% Definición
func(x, y) +(x, y)

% Recursión
letrec factorial(n) = if <=(n, 1) then 1 else *(n, (factorial sub1(n))) end
in (factorial 5)
```

### Prototipos

```scheme
% Declaración
prototipo Vehiculo = crear-diccionario("Marca", "Generica", "Modelo", "Base") in ...

% Clonación y herencia
prototipo Moto = clone(Vehiculo) in
call-method(Moto, "setCilindrada", "500")

% Acceso a métodos
call-method(moto1, "getMarca")
```

---

## 📐 Gramática Formal

### Especificación Léxica

```scheme
(define the-lexical-spec
  '((whitespace (whitespace) skip)
    (comment ("%" (arbno (not #\newline))) skip)
    (identifier (letter (arbno (or letter digit "_" "-" "?"))) symbol)
    (number (digit (arbno digit)) number)
    (number ("-" digit (arbno digit)) number)
    (number (digit (arbno digit) "." digit (arbno digit)) number)
    (number ("-" digit (arbno digit) "." digit (arbno digit)) number)
    (string-lit ("\"" (arbno (not #\")) "\"") string)))
```

### Gramática BNF

```bnf
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
             |  "crear-diccionario" | "diccionario?" | "ref-diccionario" 
             |  "set-diccionario" | "claves" | "valores"
             |  "clone" | "print" | "real" | "imag"
             |  "get-field"
```

---

## 💡 Ejemplos de Uso

### Ejemplo 1: Literales y Valores Básicos

```scheme
;; Números enteros
(scan&parse "42")
;; →  #(struct:a-program #(struct:lit-exp 42))

;; Números flotantes  
(scan&parse "3.14")
;; → #(struct:a-program #(struct:lit-exp 3.14))

;; Cadenas
(scan&parse "\"Hola Mundo\"")
;; → #(struct:a-program #(struct:string-exp "\"Hola Mundo\""))

;; Booleanos
(scan&parse "true")
;; → #(struct:a-program #(struct:true-exp))
(scan&parse "false")  
;; → #(struct:a-program #(struct:false-exp))

;; Nulo
(scan&parse "null")
;; → #(struct:a-program #(struct:null-exp))
```

### Ejemplo 2: Variables y Constantes

```scheme
;; Declaración de variables
(scan&parse "var x = 10 in x")
;; → #(struct:a-program #(struct:var-decl-exp (x) (#(struct:lit-exp 10)) #(struct:id-exp x ())))

;; Múltiples variables
(scan&parse "var x = 1, y = 2 in +(x, y)")
;; → #(struct:a-program #(struct:var-decl-exp (x y) (#(struct:lit-exp 1) #(struct:lit-exp 2)) #(struct:primapp-exp #(struct:add-prim) (#(struct:id-exp x ()) #(struct:id-exp y ())))))

;; Constantes
(scan&parse "const PI = 3.14159 in PI")
;; → #(struct:a-program #(struct:const-decl-exp (PI) (#(struct:lit-exp 3.14159)) #(struct:id-exp PI ())))

;; Asignación
(scan&parse "set x = 25")
;; → #(struct:a-program #(struct:assign-exp x #(struct:lit-exp 25)))
```

### Ejemplo 3: Expresiones Aritméticas 

```scheme
;; Operaciones básicas
(scan&parse "+(10, 5)")
;; → #(struct:a-program #(struct:primapp-exp #(struct:add-prim) (#(struct:lit-exp 10) #(struct:lit-exp 5))))

(scan&parse "-(15, 3)")
;; → #(struct:a-program #(struct:primapp-exp #(struct:subtract-prim) (#(struct:lit-exp 15) #(struct:lit-exp 3))))

(scan&parse "*(4, 5)")
;; → #(struct:a-program #(struct:primapp-exp #(struct:mult-prim) (#(struct:lit-exp 4) #(struct:lit-exp 5))))

(scan&parse "/(20, 4)")
;; → #(struct:a-program #(struct:primapp-exp #(struct:div-prim) (#(struct:lit-exp 20) #(struct:lit-exp 4))))

;; Operaciones adicionales
(scan&parse "mod(10, 3)")
;; → #(struct:a-program #(struct:primapp-exp #(struct:mod-prim) (#(struct:lit-exp 10) #(struct:lit-exp 3))))

(scan&parse "add1(5)")
;; → #(struct:a-program #(struct:primapp-exp #(struct:incr-prim) (#(struct:lit-exp 5))))

(scan&parse "sub1(8)")
;; → #(struct:a-program #(struct:primapp-exp #(struct:decr-prim) (#(struct:lit-exp 8))))

;; Números complejos
(scan&parse "complejo(3, 4)")
;; → #(struct:a-program #(struct:complex-exp #(struct:lit-exp 3) #(struct:lit-exp 4)))
```

### Ejemplo 4: Primitivas Booleanas y de Comparación

```scheme
;; Operadores de comparación
(scan&parse "<(5, 10)")
;; → #(struct:a-program #(struct:primapp-exp #(struct:less-prim) (#(struct:lit-exp 5) #(struct:lit-exp 10))))

(scan&parse ">(15, 10)")
;; → #(struct:a-program #(struct:primapp-exp #(struct:greater-prim) (#(struct:lit-exp 15) #(struct:lit-exp 10))))

(scan&parse "<=(x, 100)")
;; → #(struct:a-program #(struct:primapp-exp #(struct:lesseq-prim) (#(struct:id-exp x ()) #(struct:lit-exp 100))))

(scan&parse ">=(y, 0)")
;; → #(struct:a-program #(struct:primapp-exp #(struct:greatereq-prim) (#(struct:id-exp y ()) #(struct:lit-exp 0))))

(scan&parse "==(a, b)")
;; → #(struct:a-program #(struct:primapp-exp #(struct:equal-prim) (#(struct:id-exp a ()) #(struct:id-exp b ()))))

(scan&parse "<>(x, y)")
;; → #(struct:a-program #(struct:primapp-exp #(struct:notequal-prim) (#(struct:id-exp x ()) #(struct:id-exp y ()))))

;; Operadores lógicos
(scan&parse "and(>(x, 0), <(x, 10))")
;; → #(struct:a-program
;;    #(struct:primapp-exp #(struct:and-prim) (#(struct:primapp-exp
;;        #(struct:greater-prim) (#(struct:id-exp x ()) #(struct:lit-exp 0))) #(struct:primapp-exp
;;        #(struct:less-prim) (#(struct:id-exp x ()) #(struct:lit-exp 10))))))

(scan&parse "or(==(y, 0), ==(y, 1))")
;; → #(struct:a-program #(struct:primapp-exp #(struct:or-prim)
;;    (#(struct:primapp-exp #(struct:equal-prim) (#(struct:id-exp y ()) #(struct:lit-exp 0)))
;;        #(struct:primapp-exp #(struct:equal-prim) (#(struct:id-exp y ()) #(struct:lit-exp 1))))))

(scan&parse "not(False)")
;; → #(struct:a-program #(struct:primapp-exp #(struct:not-prim) (#(struct:id-exp False ()))))

;; Pruebas de cero
(scan&parse "zero?(0)")
;; → #(struct:a-program #(struct:primapp-exp #(struct:zero-test-prim) (#(struct:lit-exp 0))))
```

### Ejemplo 5: Estructuras de Control

```scheme
;; Condicional IF
(scan&parse "if >(x, 10) then \"mayor\" else \"menor\" end")
;; → #(struct:a-program #(struct:if-exp #(struct:primapp-exp #(struct:greater-prim) (#(struct:id-exp x ()) #(struct:lit-exp 10))) #(struct:string-exp "\"mayor\"") #(struct:string-exp "\"menor\"")))

;; Switch
(scan&parse "switch dia case 1: \"Lunes\" case 2: \"Martes\" default: \"Otro\" end")
;; → #(struct:a-program #(struct:switch-exp #(struct:id-exp dia ()) (#(struct:lit-exp 1) #(struct:lit-exp 2)) (#(struct:string-exp "\"Lunes\"") #(struct:string-exp "\"Martes\"")) #(struct:string-exp "\"Otro\"")))

;; While
(scan&parse "while <(i, 5) do set i = add1(i) done")
;; → #(struct:a-program #(struct:while-exp #(struct:primapp-exp #(struct:less-prim) (#(struct:id-exp i ()) #(struct:lit-exp 5))) #(struct:assign-exp i #(struct:primapp-exp #(struct:incr-prim) (#(struct:id-exp i ()))))))

;; For
(scan&parse "for x in lista do print(x) done")
;; → #(struct:a-program #(struct:for-exp x #(struct:id-exp lista ()) #(struct:primapp-exp #(struct:print-prim) (#(struct:id-exp x ())))))
```

### Ejemplo 6: Funciones y Procedimientos

```scheme
;; Función anónima
(scan&parse "func(x, y) +(x, y)")
;; → #(struct:a-program #(struct:func-exp (x y) #(struct:primapp-exp #(struct:add-prim) (#(struct:id-exp x ()) #(struct:id-exp y ())))))

;; Aplicación de función
(scan&parse "(f 10 20)")
;; → #(struct:a-program #(struct:app-exp #(struct:id-exp f ()) (#(struct:lit-exp 10) #(struct:lit-exp 20))))

;; Recursión con letrec
(scan&parse "letrec factorial(n) = if ==(n, 0) then 1 else *(n, (factorial -(n, 1))) end in (factorial 5)")
;; → #(struct:a-program
;;     #(struct:letrec-exp
        (factorial)
        ((n))
        (#(struct:if-exp
          #(struct:primapp-exp #(struct:equal-prim) (#(struct:id-exp n ()) #(struct:lit-exp 0)))
          #(struct:lit-exp 1)
          #(struct:primapp-exp #(struct:mult-prim) (#(struct:id-exp n ()) #(struct:app-exp #(struct:id-exp factorial ()) (#(struct:primapp-exp #(struct:subtract-prim) (#(struct:id-exp n ()) #(struct:lit-exp 1)))))))))
        #(struct:app-exp #(struct:id-exp factorial ()) (#(struct:lit-exp 5)))))
```

### Ejemplo 7: Primitivas de Cadenas

```scheme
;; Longitud de cadena
(scan&parse "longitud(\"Hola\")")
;; → #(struct:a-program #(struct:primapp-exp #(struct:length-prim) (#(struct:string-exp "\"Hola\""))))

;; Concatenación
(scan&parse "concatenar(\"Hola\", \" Mundo\")")
;; → #(struct:a-program #(struct:primapp-exp #(struct:concat-prim) (#(struct:string-exp "\"Hola\"") #(struct:string-exp "\" Mundo\""))))
```

### Ejemplo 8: Listas
```scheme
;; Lista literal
(scan&parse "[1, 2, 3, 4, 5]")
;; → #(struct:a-program #(struct:list-literal-exp (#(struct:lit-exp 1) #(struct:lit-exp 2) #(struct:lit-exp 3) #(struct:lit-exp 4) #(struct:lit-exp 5))))

;; Operaciones con listas
(scan&parse "crear-lista(1, vacio())")
;; → #(struct:a-program #(struct:primapp-exp #(struct:cons-prim) (#(struct:lit-exp 1) #(struct:primapp-exp #(struct:empty-list-prim) ()))))

(scan&parse "cabeza(lista)")
;; → #(struct:a-program #(struct:primapp-exp #(struct:car-prim) (#(struct:id-exp lista ()))))

(scan&parse "cola(lista)")
;; → #(struct:a-program #(struct:primapp-exp #(struct:cdr-prim) (#(struct:id-exp lista ()))))

(scan&parse "ref-list(lista, 2)")
;; → #(struct:a-program #(struct:primapp-exp #(struct:ref-list-prim) (#(struct:id-exp lista ()) #(struct:lit-exp 2))))

;; Verificación de listas
(scan&parse "vacio?(lista)")
;; → #(struct:a-program #(struct:primapp-exp #(struct:empty?-prim) (#(struct:id-exp lista ()))))

(scan&parse "lista?(objeto)")
;; → #(struct:a-program #(struct:primapp-exp #(struct:list?-prim) (#(struct:id-exp objeto ()))))
```

### Ejemplo 9: Diccionarios y Prototipos
```scheme
;; Creación de diccionario
(scan&parse "crear-diccionario(\"nombre\", \"Ana\", \"edad\", 25)")
;; → #(struct:a-program #(struct:primapp-exp #(struct:create-dict-prim) (#(struct:string-exp "\"nombre\"") #(struct:string-exp "\"Ana\"") #(struct:string-exp "\"edad\"") #(struct:lit-exp 25))))

;; Acceso a campos
(scan&parse "ref-diccionario(persona, \"edad\")")
;; → #(struct:a-program #(struct:primapp-exp #(struct:ref-dict-prim) (#(struct:id-exp persona ()) #(struct:string-exp "\"edad\""))))

;; Verificación de diccionarios
(scan&parse "diccionario?(objeto)")
;; → #(struct:a-program #(struct:primapp-exp #(struct:dict?-prim) (#(struct:id-exp objeto ()))))

;; Prototipos
(scan&parse "prototipo Vehiculo = crear-diccionario(\"marca\", \"Generica\") in Vehiculo")
;; → #(struct:a-program #(struct:proto-decl-exp Vehiculo #(struct:primapp-exp #(struct:create-dict-prim) (#(struct:string-exp "\"marca\"") #(struct:string-exp "\"Generica\""))) #(struct:id-exp Vehiculo ())))

;; Clonación
(scan&parse "clone(objeto)")
;; → #(struct:a-program #(struct:primapp-exp #(struct:clone-prim) (#(struct:id-exp objeto ()))))

;; Llamada a métodos
(scan&parse "call-method(objeto, \"metodo\", param1, param2)")
;; → #(struct:a-program #(struct:primapp-exp #(struct:call-method-prim) (#(struct:id-exp objeto ()) #(struct:string-exp "\"metodo\"") #(struct:id-exp param1 ()) #(struct:id-exp param2 ()))))
```

### Ejemplo 10: Secuenciación y Expresiones Compuestas
```scheme
;; Begin para múltiples expresiones
(scan&parse "begin print(\"Hola\"); set x = 10; x end")
;; → #(struct:a-program #(struct:begin-exp #(struct:primapp-exp #(struct:print-prim) (#(struct:string-exp "\"Hola\""))) (#(struct:assign-exp x #(struct:lit-exp 10)) #(struct:id-exp x ()))))

;; Expresiones anidadas
(scan&parse "+(*(2, 3), /(10, 2))")
;; → #(struct:a-program #(struct:primapp-exp #(struct:add-prim) (#(struct:primapp-exp #(struct:mult-prim) (#(struct:lit-exp 2) #(struct:lit-exp 3))) #(struct:primapp-exp #(struct:div-prim) (#(struct:lit-exp 10) #(struct:lit-exp 2))))))
```

---

## 🚀 Instalación y Ejecución

### Requisitos Previos

- **DrRacket** versión 8.0 o superior
- Sistema operativo: Windows, macOS o Linux

### Pasos de Instalación

1. **Clonar el repositorio**
   ```bash
   git clone https://github.com/BrayanJurado/FlowLang_Project-.git
   cd FlowLang_Project-
   ```

2. **Abrir DrRacket**
   - Abrir el archivo `interpretador.rkt`

3. **Ejecutar el intérprete**
   - Presionar el botón **Run** (o F5)
   - El REPL se iniciará con el prompt `-->`





