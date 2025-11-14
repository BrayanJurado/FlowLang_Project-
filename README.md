# FlowLang - Lenguaje de Programación Imperativo

[![Racket](https://img.shields.io/badge/Racket-EOPL-blue.svg)](https://racket-lang.org/)


## 👥 Equipo de trabajo

| Nombre | Código | Email | GitHub |
|--------|------|-------|--------|
| Brayan Camilo Urrea Jurado |  2410023 | urrea.brayan@correounivalle.edu.co | [@BrayanJurado](https://github.com/BrayannJurado) |
| Nicolás Enrique Granada Fernandez | 2310107 | granada.nicolas@correounivalle.edu.co | [@NicolasGranada](https://github.com/nicolasgranada) |


**Universidad del Valle**   
**Fundamentos de Lenguajes de Programación y Compilación LP**   

---

## 🎯 Descripción del Proyecto

**FlowLang** es un lenguaje de programación imperativo con tipos dinámicos. El lenguaje combina características de programación funcional, imperativa y orientada a prototipos.

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
prototipo persona = {nombre: "Ana", edad: 25} in ...

% Clonación
var copia = clone(persona) in ...

% Acceso a campos
persona.nombre
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
```

---

## 💡 Ejemplos de Uso

### Ejemplo 1: Variables y Operaciones Básicas

```scheme
% Demostración de scan&parse
(scan&parse "var x = 10, y = 20 in +(x, y)")

% Ejecución
var x = 10, y = 20 in +(x, y)
% Resultado: 30
```

### Ejemplo 2: Funciones y Recursión

```scheme
% Scan&parse de función factorial
(scan&parse "letrec factorial(n) = if <=(n, 1) then 1 else *(n, (factorial sub1(n))) end in (factorial 5)")

% Ejecución
letrec factorial(n) = if <=(n, 1) 
                      then 1 
                      else *(n, (factorial sub1(n))) 
                      end 
in (factorial 5)
% Resultado: 120
```

### Ejemplo 3: Listas

```scheme
% Scan&parse de operaciones con listas
(scan&parse "var lista = crear-lista(1, crear-lista(2, vacio())) in cabeza(lista)")

% Ejecución
var lista = crear-lista(1, crear-lista(2, crear-lista(3, vacio()))) 
in begin
     print(cabeza(lista));
     print(cola(lista));
     lista
   end
% Resultado: 
% 1
% [2, 3]
% [1, 2, 3]
```

### Ejemplo 4: Diccionarios

```scheme
% Scan&parse de diccionario
(scan&parse "var dict = crear-diccionario(\"nombre\", \"Ana\", \"edad\", 25) in ref-diccionario(dict, \"nombre\")")

% Ejecución
var persona = crear-diccionario("nombre", "Ana", "edad", 25) 
in begin
     print(ref-diccionario(persona, "nombre"));
     var nueva = set-diccionario(persona, "edad", 26) in
     print(ref-diccionario(nueva, "edad"))
   end
% Resultado:
% Ana
% 26
```

### Ejemplo 5: Control de Flujo - IF

```scheme
% Scan&parse de condicional
(scan&parse "var x = 15 in if >(x, 10) then \"Mayor\" else \"Menor\" end")

% Ejecución
var edad = 18 in 
if >=(edad, 18) 
then "Mayor de edad" 
else "Menor de edad" 
end
% Resultado: "Mayor de edad"
```

### Ejemplo 6: Control de Flujo - SWITCH

```scheme
% Scan&parse de switch
(scan&parse "var dia = 3 in switch dia case 1: \"Lunes\" case 2: \"Martes\" case 3: \"Miércoles\" default: \"Otro\" end")

% Ejecución
var color = "rojo" in
switch color
  case "rojo": "Detener"
  case "amarillo": "Precaución"
  case "verde": "Avanzar"
  default: "Color desconocido"
end
% Resultado: "Detener"
```

### Ejemplo 7: Ciclo WHILE

```scheme
% Scan&parse de while
(scan&parse "var i = 0 in while <(i, 5) do begin print(i); set i = add1(i) end done")

% Ejecución
var contador = 0 in
while <(contador, 3) do
  begin
    print(contador);
    set contador = add1(contador)
  end
done
% Resultado: 
% 0
% 1
% 2
```

### Ejemplo 8: Ciclo FOR

```scheme
% Scan&parse de for
(scan&parse "var nums = [1, 2, 3] in for x in nums do print(x) done")

% Ejecución
var numeros = [1, 2, 3, 4, 5] in
for num in numeros do
  print(*(num, 2))
done
% Resultado:
% 2
% 4
% 6
% 8
% 10
```

### Ejemplo 9: Prototipos

```scheme
% Scan&parse de prototipo
(scan&parse "prototipo persona = {nombre: \"Ana\", edad: 25} in persona.nombre")

% Ejecución
prototipo vehiculo = {tipo: "Carro", modelo: "Sedan"} in
var carro = clone(vehiculo) in
begin
  print(carro.tipo);
  var actualizado = set-field(carro, "modelo", "SUV") in
  print(actualizado.modelo)
end
% Resultado:
% Carro
% SUV
```

### Ejemplo 10: Números Complejos

```scheme
% Scan&parse de complejos
(scan&parse "var z1 = complejo(3, 4), z2 = complejo(1, 2) in +(z1, z2)")

% Ejecución
var z1 = complejo(3, 4),
    z2 = complejo(1, 2)
in begin
     print(+(z1, z2));
     print(*(z1, z2))
   end
% Resultado:
% 4+6i
% -5+10i
```

### Ejemplo 11: Constantes

```scheme
% Scan&parse de constante
(scan&parse "const PI = 3.14159 in *(PI, 2)")

% Ejecución - Correcto
const MAX_USUARIOS = 100 in print(MAX_USUARIOS)
% Resultado: 100

% Ejecución - Error
const PI = 3.14 in set PI = 3.14159
% Error: "Cannot modify constant"
```

### Ejemplo 12: Closures

```scheme
% Scan&parse de closure
(scan&parse "var f = func(x) func(y) +(x, y) in ((f 10) 5)")

% Ejecución
var suma_parcial = func(x) func(y) +(x, y) in
var suma_10 = (suma_parcial 10) in
(suma_10 5)
% Resultado: 15
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





