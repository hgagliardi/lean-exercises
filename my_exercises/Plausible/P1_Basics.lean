/-
Plausible P1 — Fundamentos de property-based testing en Lean
Preparación pasantía AWS. Día 3 del plan.
-/
import Plausible

/-!
# P1. Property-based testing con Plausible

`plausible` es el QuickCheck de Lean. NO demuestra nada: genera valores
aleatorios, evalúa la propiedad, y si falla te devuelve un contraejemplo
*minimizado* (shrinking).

Regla mental: `plausible` responde "¿es plausible que esto sea cierto?".
Si dice que sí, todavía tenés que demostrarlo. Si dice que no, te acabás
de ahorrar una hora.

## 1. Ver qué valores genera: `#sample`
-/

#sample Nat
#sample List Nat
#sample (Nat × Int)

-- Ejercicio 1.1: samplear una lista de pares. ¿Qué tamaños ves?
-- (descomentá y mirá la salida en el InfoView)
-- #sample List (Nat × Bool)

/-!
## 2. La táctica `plausible`

Sobre una propiedad VERDADERA no encuentra contraejemplo. Fijate en el
InfoView: dice "Unable to find a counter-example" y además emite un
warning `declaration uses 'sorry'`.

ESE WARNING ES EL PUNTO. `plausible` deja un hueco en la prueba.
-/

example (xs : List Nat) : xs.reverse.reverse = xs := by plausible

example (n m : Nat) : n + m = m + n := by plausible

/-!
## 3. Sobre una propiedad FALSA

Lo siguiente NO compila a propósito: `plausible` reporta el contraejemplo
como *error*. Descomentalo y leé la salida.

Deberías ver algo como:
  Found a counter-example!
  xs := [0]
  ys := [1]
  issue: [1, 0] = [0, 1] does not hold
  (9 shrinks)

"9 shrinks" = encontró un contraejemplo grande y lo redujo 9 veces hasta
el mínimo. El shrinking es lo que hace usable a esta herramienta.
-/

-- example (xs ys : List Nat) : (xs ++ ys).reverse = xs.reverse ++ ys.reverse := by plausible

/-!
## 4. Configuración

Campos reales de `Plausible.Configuration`:
  numInst        (default 100)  — cuántos casos generar
  maxSize        (default 100)  — tamaño máximo de los valores
  numRetries     (default 10)
  traceDiscarded (default false) — mostrar casos descartados por precondición
  traceSuccesses (default false) — mostrar los casos que pasaron
  traceShrink    (default false) — mostrar el proceso de minimización
-/

example (n : Nat) : n + 0 = n := by
  plausible (config := { numInst := 500, maxSize := 200 })

-- Ejercicio 1.2: corré esto con traceSuccesses := true y mirá qué valores probó.
example (n : Nat) : n * 1 = n := by
  plausible (config := { numInst := 10 })

/-!
## 5. Precondiciones (hipótesis)

Cuando la propiedad tiene hipótesis, Plausible genera valores y DESCARTA
los que no las cumplen. Si descarta demasiados, el test es inútil aunque
diga "no counter-example": puede que apenas haya probado 3 casos reales.

Activá `traceDiscarded := true` para ver cuántos tira. En el ejemplo de abajo
vas a ver el warning: "Gave up after failing to generate values that fulfill
the preconditions 11 times." — es exactamente el problema descrito.
-/

example (n : Nat) (h : 10 < n) : 5 < n := by plausible

/-!
## Ejercicios

Reemplazá cada `sorry` por `by plausible` (o por `by plausible (config := ...)`).
Para las que sean FALSAS, anotá el contraejemplo en un comentario y dejá el
`sorry`: el archivo tiene que seguir compilando.
-/

-- Ejercicio 1.3: ¿verdadera o falsa?
example (xs : List Nat) : xs.length = xs.reverse.length := sorry

-- Ejercicio 1.4: ¿verdadera o falsa?
example (xs ys : List Nat) : (xs ++ ys).length = xs.length + ys.length := sorry

-- Ejercicio 1.5: ojo con esta. Contraejemplo esperado: n := 0
example (n : Nat) : 0 < n := sorry

-- Ejercicio 1.6: resta truncada en ℕ
example (n m : Nat) : n - m + m = n := sorry

-- Ejercicio 1.7: esta necesita muchos casos para fallar. Probá numInst := 1000.
example (n : Nat) : n < 200 := sorry

-- Ejercicio 1.8: filter y length
example (xs : List Nat) : (xs.filter (· > 3)).length ≤ xs.length := sorry

/-!
## Para llevarte

1. `plausible` NUNCA cierra un goal de verdad — deja `sorry`.
2. Usalo ANTES de invertir tiempo demostrando.
3. Si la propiedad tiene hipótesis fuertes, revisá `traceDiscarded`.
4. El shrinking es lo que convierte un contraejemplo de 200 elementos en
   uno de 1 elemento que podés entender.

Siguiente: P2_Generators.lean — generar valores de TUS propios tipos.
-/
