/-
Plausible P2' — SOLUCIONES de P2_Generators.lean
Archivo autocontenido: redefine los tipos para poder correrlo solo.
-/
import Plausible

open Plausible

/-! ### 2.1 — Enumerado con pesos

`Gen.oneOf` elige entre GENERADORES, no entre valores. Repetir un generador
en el array es lo que le da más peso. Acá `spade` sale 2/5 de las veces
en vez de 1/4.
-/

inductive Suit where
  | spade | heart | diamond | club
  deriving Repr, DecidableEq

instance : Shrinkable Suit := {}

instance : SampleableExt Suit :=
  SampleableExt.mkSelfContained <|
    Gen.oneOf #[pure .spade, pure .spade, pure .heart, pure .diamond, pure .club] (by decide)

#sample Suit

/-! ### 2.2 — Listas no vacías

La clave: no generar `List Nat` y descartar la vacía. Se genera el head
por separado, así el invariante vale por construcción.
-/

structure NonEmptyList where
  head : Nat
  tail : List Nat
  deriving Repr

instance : Shrinkable NonEmptyList where
  -- achicamos por la cola; el head no se puede sacar sin romper el invariante
  shrink l :=
    match l.tail with
    | [] => []
    | _ :: t => [{ head := l.head, tail := t }]

instance : SampleableExt NonEmptyList :=
  SampleableExt.mkSelfContained do
    let h ← Gen.chooseNat
    let t ← Gen.listOf Gen.chooseNat
    return { head := h, tail := t }

#sample NonEmptyList

example (l : NonEmptyList) : (l.head :: l.tail) ≠ [] := by plausible

/-! ### 2.3 — Listas ordenadas (el ejercicio importante)

Estrategia: generar una lista de SALTOS `[d₀, d₁, d₂, ...]` y acumular.
Como cada salto es ≥ 0, las sumas parciales son no decrecientes.
El resultado está ordenado por construcción — cero descartes.
-/

structure SortedList where
  val : List Nat
  deriving Repr

def SortedList.isSorted : List Nat → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => a ≤ b && SortedList.isSorted (b :: rest)

/-- Sumas parciales: convierte saltos en una lista no decreciente. -/
def prefixSums (acc : Nat) : List Nat → List Nat
  | [] => []
  | d :: ds => (acc + d) :: prefixSums (acc + d) ds

#eval prefixSums 0 [3, 0, 5, 2]     -- [3, 3, 8, 10]

instance : Shrinkable SortedList where
  -- sacar el último elemento preserva el orden; sacar del medio también,
  -- pero dropLast alcanza y es más simple
  shrink l :=
    match l.val with
    | [] => []
    | _ => [{ val := l.val.dropLast }]

instance : SampleableExt SortedList :=
  SampleableExt.mkSelfContained do
    let deltas ← Gen.listOf Gen.chooseNat
    return { val := prefixSums 0 deltas }

#sample SortedList

-- El test que valida EL GENERADOR, no la propiedad.
example (l : SortedList) : SortedList.isSorted l.val = true := by plausible

/-! ### 2.4 — Shrinking a mano

El shrinker de abajo devuelve, además de los subárboles, el mismo árbol
con todos los valores reducidos a la mitad. Eso hace que un contraejemplo
con `node leaf 8173 leaf` colapse a `node leaf 0 leaf` en pocos pasos.
-/

inductive Tree where
  | leaf : Tree
  | node : Tree → Nat → Tree → Tree
  deriving Repr

def Tree.size : Tree → Nat
  | .leaf => 0
  | .node l _ r => 1 + l.size + r.size

def Tree.depth : Tree → Nat
  | .leaf => 0
  | .node l _ r => 1 + max l.depth r.depth

/-- Divide todos los valores del árbol por 2. -/
def Tree.halve : Tree → Tree
  | .leaf => .leaf
  | .node l v r => .node l.halve (v / 2) r.halve

def genTree : Nat → Gen Tree
  | 0 => return .leaf
  | fuel + 1 => do
    let stop ← Gen.chooseNatLt 0 3 (by decide)
    if stop.val = 0 then
      return .leaf
    else
      let l ← genTree fuel
      let v ← Gen.chooseNat
      let r ← genTree fuel
      return .node l v r

instance : Shrinkable Tree where
  shrink
    | .leaf => []
    | .node l v r =>
        -- subárboles (estructuralmente más chicos) + valores a la mitad
        let smaller := [l, r]
        if v = 0 then smaller
        else smaller ++ [Tree.node l (v / 2) r, (Tree.node l v r).halve]

instance : SampleableExt Tree :=
  SampleableExt.mkSelfContained do
    let fuel ← Gen.getSize
    genTree (min fuel 4)

example (t : Tree) : t.depth ≤ t.size := by plausible

/-!
## Lo que había que sacar de acá

* 2.1 `Gen.oneOf` elige entre generadores → repetir uno = ponderarlo.
* 2.2/2.3 el patrón central: **generar cumpliendo el invariante**, nunca
  generar-y-filtrar. Con filtrado, Plausible se rinde (`Gave up after
  failing to generate values that fulfill the preconditions`).
* 2.3 el truco de los saltos acumulados es reutilizable para cualquier
  estructura monótona: timestamps, rangos de IP, versiones.
* 2.4 un `Shrinkable` que solo achica la ESTRUCTURA deja los VALORES
  enormes. Un buen shrinker ataca las dos dimensiones.
-/
