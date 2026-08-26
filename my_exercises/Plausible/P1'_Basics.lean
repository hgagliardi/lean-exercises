/-
Plausible P1' — SOLUCIONES de P1_Basics.lean
No abrir hasta haber intentado 15 minutos por ejercicio.
-/
import Plausible

/-!
# Soluciones P1

Las propiedades FALSAS quedan con `sorry` a propósito: si les ponés
`by plausible` el archivo no compila (el contraejemplo es un *error*).
El contraejemplo anotado en el comentario es la salida real de Plausible
en esta máquina.
-/

-- Ejercicio 1.1 — samplear una lista de pares
#sample List (Nat × Bool)
-- Observación: los tamaños crecen con el índice del sample. Plausible
-- arranca con valores chicos y va aumentando el `size` — por eso los
-- primeros samples suelen ser `[]` o listas de 1 elemento.

-- Ejercicio 1.2 — ver los casos que pasaron
example (n : Nat) : n * 1 = n := by
  plausible (config := { numInst := 10, traceSuccesses := true })

-- Ejercicio 1.3 — VERDADERA
example (xs : List Nat) : xs.length = xs.reverse.length := by plausible

-- Ejercicio 1.4 — VERDADERA
example (xs ys : List Nat) : (xs ++ ys).length = xs.length + ys.length := by plausible

-- Ejercicio 1.5 — FALSA
--   Found a counter-example!
--   n := 0
--   issue: 0 < 0 does not hold
example (n : Nat) : 0 < n := sorry

-- Ejercicio 1.6 — FALSA. La resta en ℕ es truncada: 0 - 1 = 0, no -1.
--   Found a counter-example!
--   n := 0, m := 1
--   issue: 1 = 0 does not hold
-- El enunciado verdadero necesita la hipótesis `m ≤ n`:
example (n m : Nat) (h : m ≤ n) : n - m + m = n := by plausible
-- (y sin la hipótesis, es falsa:)
example (n m : Nat) : n - m + m = n := sorry

-- Ejercicio 1.7 — FALSA, pero hay que buscarla.
-- Con la config por defecto (maxSize := 100) NUNCA falla: Plausible no
-- genera naturales mayores a 100. Hay que subir `maxSize`, no `numInst`.
-- Ésta es la trampa del ejercicio.
--   con { numInst := 1000, maxSize := 500 }:
--   Found a counter-example!
--   n := 204
--   issue: 204 < 200 does not hold
example (n : Nat) : n < 200 := sorry

-- Ejercicio 1.8 — VERDADERA
example (xs : List Nat) : (xs.filter (· > 3)).length ≤ xs.length := by plausible

/-!
## Lo que había que sacar de acá

* 1.5 / 1.6: los contraejemplos de ℕ casi siempre son `0`. La resta truncada
  y el `0 <` son las dos trampas clásicas.
* 1.7: `numInst` y `maxSize` controlan cosas DISTINTAS. Más casos no ayuda
  si todos los casos son chicos. Cuando un test "pasa" siempre, sospechá
  del rango de generación antes que de la propiedad.
-/
