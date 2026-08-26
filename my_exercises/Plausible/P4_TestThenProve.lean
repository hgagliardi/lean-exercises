/-
Plausible P4 — El flujo real: testear ANTES de demostrar
Preparación pasantía AWS. Día 9 del plan.
-/
import Plausible

/-!
# P4. Testear primero, demostrar después

Este archivo es el flujo de trabajo completo, y es el hábito que te
conviene llevar a la pasantía:

  1. Escribís la implementación.
  2. Escribís la especificación.
  3. La testeás con `plausible`  ← 10 segundos
  4. Recién ahí la demostrás     ← 2 horas

El paso 3 es barato y te dice si el paso 4 vale la pena. Además, y esto
es lo importante: te obliga a descubrir que tu especificación estaba
INCOMPLETA antes de gastar las 2 horas.

Usamos insertion sort porque es corto y las pruebas salen a mano.
La misma receta aplica a MergeSort (Week06).

## 1. La implementación
-/

/-- Inserta `a` en una lista ya ordenada. -/
def ins (a : Nat) : List Nat → List Nat
  | [] => [a]
  | b :: l => if a ≤ b then a :: b :: l else b :: ins a l

/-- Insertion sort. -/
def isort : List Nat → List Nat
  | [] => []
  | a :: l => ins a (isort l)

#eval isort [5, 2, 9, 1, 2]     -- [1, 2, 2, 5, 9]

/-!
## 2. La especificación (primer intento)
-/

def sorted : List Nat → Bool
  | [] => true
  | [_] => true
  | a :: b :: l => a ≤ b && sorted (b :: l)

/-!
## 3. Testeamos ANTES de demostrar
-/

example (xs : List Nat) : sorted (isort xs) = true := by plausible

/-!
## 4. Por qué `sorted` NO alcanza como especificación

Acá está la lección. `insBug` tiene un bug: al insertar en la posición
correcta, PISA el elemento que estaba ahí en vez de conservarlo.
-/

def insBug (a : Nat) : List Nat → List Nat
  | [] => [a]
  | b :: l => if a ≤ b then a :: l else b :: insBug a l   -- BUG: se come `b`

def isortBug : List Nat → List Nat
  | [] => []
  | a :: l => insBug a (isortBug l)

#eval isortBug [5, 2, 9, 1, 2]   -- pierde elementos

-- ...y sin embargo:
example (xs : List Nat) : sorted (isortBug xs) = true := by plausible

/-!
`plausible` no encuentra contraejemplo. La función está claramente rota
y pasa el test. ¿Por qué? Porque `sorted` es una especificación
INCOMPLETA: `fun _ => []` también la cumple.

Una especificación de ordenamiento necesita DOS mitades:
  (a) el resultado está ordenado
  (b) el resultado es una permutación de la entrada

Nos faltaba (b). Vamos a formularla contando ocurrencias.
-/

def count (x : Nat) : List Nat → Nat
  | [] => 0
  | a :: l => (if a = x then 1 else 0) + count x l

/-- La mitad que faltaba: se preservan las multiplicidades. -/
example (x : Nat) (xs : List Nat) : count x (isort xs) = count x xs := by plausible

/-!
Y ahora sí, el bug cae. Descomentá y vas a ver algo como:

    Found a counter-example!
    x := 15
    xs := [16, 1, 14, 17, 19, 5, 1, 18, 15, 11]
    issue: 0 = 1 does not hold
    (0 shrinks)

Fijate en `(0 shrinks)`: el contraejemplo NO se minimizó, te lo tira con
10 elementos. Compará con el ejemplo de P1, que shrinkeaba 9 veces hasta
`[0]` vs `[1]`. Ese contraste es material del ejercicio 2.4: el shrinking
depende de la instancia `Shrinkable`, y cuando no funciona bien te toca
depurar un contraejemplo enorme a mano.
-/

-- example (x : Nat) (xs : List Nat) : count x (isortBug xs) = count x xs := by plausible

/-!
## 5. Ahora sí, a demostrar

Tenemos evidencia de que las dos propiedades valen. Recién ahora invertimos
el tiempo. Tácticas que vas a necesitar: `induction`, `simp [ins, isort]`,
`split` (para los `if`), `omega`.
-/

/-! ### Parte A: el resultado está ordenado -/

-- Lema auxiliar: insertar en una lista ordenada la deja ordenada.
theorem sorted_ins (a : Nat) (l : List Nat) (h : sorted l = true) :
    sorted (ins a l) = true := by
  sorry

theorem sorted_isort (l : List Nat) : sorted (isort l) = true := by
  sorry

/-! ### Parte B: es una permutación -/

theorem count_ins (x a : Nat) (l : List Nat) :
    count x (ins a l) = (if a = x then 1 else 0) + count x l := by
  sorry

theorem count_isort (x : Nat) (l : List Nat) :
    count x (isort l) = count x l := by
  sorry

/-! ### Parte C: la especificación completa, en un solo teorema -/

theorem isort_correct (l : List Nat) :
    sorted (isort l) = true ∧ ∀ x, count x (isort l) = count x l := by
  sorry

/-!
## Ejercicios

### 4.1 — Testear antes de cada `sorry`
Antes de atacar cada teorema de arriba, escribí el `example` correspondiente
con `by plausible` y confirmá que no hay contraejemplo. Es el hábito completo.

### 4.2 — Un lema falso
El siguiente lema PARECE razonable y es FALSO. Encontrá el contraejemplo
con `plausible` (dejalo en un comentario) y explicá en una línea por qué falla.
-/

-- example (a : Nat) (l : List Nat) : ins a l = a :: l := by plausible

/-!
### 4.3 — Longitud
Enunciá y demostrá `length_isort : (isort l).length = l.length`.
Testeala primero. ¿La cumple `isortBug`? Testealo — la respuesta te dice
si `length` sirve como sustituto de la propiedad de permutación.

### 4.4 — Idempotencia
Testeá `isort (isort l) = isort l`. Después demostrala.
Pista: te va a servir un lema del estilo "si `l` está ordenada, `isort l = l`".

### 4.5 — Llevarlo a MergeSort (Week06)
Abrí `my_exercises/Week06/Sheet1.lean`. Antes de resolver cada `sorry`,
escribí la versión ejecutable de la propiedad y pasale `plausible`.
Vas a necesitar que las definiciones sean computables y las propiedades
decidibles (`Bool` en vez de `Prop`) — esa traducción es parte del ejercicio.

### 4.6 — Estabilidad
Un sort es *estable* si no reordena elementos iguales. Con `Nat` no se nota.
Cambiá a `List (Nat × Nat)` ordenando por la primera componente, formulá
estabilidad como propiedad testeable, y verificá si `isort` es estable.

## Para llevarte

1. Una especificación que `fun _ => []` cumple no es una especificación.
   `plausible` te lo muestra en 10 segundos; una demostración te lo esconde
   durante dos horas.
2. Ordenar necesita SIEMPRE las dos mitades: ordenado + permutación.
3. El costo de testear es tan bajo que no hay excusa para no hacerlo antes
   de cada `sorry`.
-/
