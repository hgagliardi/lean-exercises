/-
Plausible P2 — Generadores para tipos propios
Preparación pasantía AWS. Día 3 del plan.
-/
import Plausible

open Plausible

/-!
# P2. `Gen`, `Shrinkable` y `SampleableExt`

En P1 testeamos propiedades sobre `Nat` y `List Nat`, que ya traen
generadores. Acá aprendemos a generar valores de NUESTROS tipos.
Esto es lo que vas a hacer en la pasantía: los datos reales nunca son
`Nat`, son structs y árboles con invariantes.

Tres piezas:

* `Gen α`          — mónada de generación aleatoria. `Gen α ≈ Size → Rand α`.
* `Shrinkable α`   — dado un valor que falla, devuelve versiones "más chicas"
                     para probar. Sin esto tenés contraejemplos ilegibles.
* `SampleableExt α`— junta las dos y le dice a `plausible` cómo tratar el tipo.

## 1. Combinadores de `Gen` (los reales, verificados)

  Gen.chooseAny α          -- cualquier valor (necesita `Random Id α`)
  Gen.choose α lo hi h     -- en el rango [lo, hi], con prueba `lo ≤ hi`
  Gen.chooseNat            -- entre 0 y el size actual
  Gen.chooseNatLt lo hi h  -- en [lo, hi)
  Gen.elements xs h        -- uno de la lista, con prueba `0 < xs.length`
  Gen.oneOf gens h         -- elige uno de varios GENERADORES
  Gen.listOf g             -- lista de largo aleatorio
  Gen.arrayOf g            -- idem para Array
  Gen.prodOf g1 g2         -- par
  Gen.permutationOf xs     -- permutación de xs (¡devuelve la prueba `xs ~ ys`!)
  Gen.getSize              -- leer el parámetro de tamaño
  Gen.resize f g           -- correr g con el tamaño transformado por f

## 2. Un tipo enumerado
-/

inductive Color where
  | red | green | blue
  deriving Repr, DecidableEq

-- Sin shrinking: un enumerado no tiene "versión más chica" natural.
instance : Shrinkable Color := {}

instance : SampleableExt Color :=
  SampleableExt.mkSelfContained (Gen.elements [.red, .green, .blue] (by decide))

#sample Color

-- Ahora `plausible` sabe generar Color:
example (c : Color) : c = .red ∨ c = .green ∨ c = .blue := by plausible

/-!
## 3. Un tipo con invariante: pares ordenados

Acá está la gracia. Queremos generar SOLO pares `(a, b)` con `a ≤ b`.
Mala idea: generar cualquier par y descartar los que no cumplen
(eso es lo que pasaba en P1 con `10 < n`: Plausible se rinde).
Buena idea: generar `a`, y después generar `b` a partir de `a`.
-/

structure OrderedPair where
  lo : Nat
  hi : Nat
  h : lo ≤ hi
  deriving Repr

instance : Shrinkable OrderedPair where
  shrink p :=
    -- achicamos manteniendo el invariante: bajamos `hi` hacia `lo`
    if h : p.lo ≤ p.hi / 2 then [⟨p.lo, p.hi / 2, h⟩] else []

instance : SampleableExt OrderedPair :=
  SampleableExt.mkSelfContained do
    let a ← Gen.chooseNat
    let d ← Gen.chooseNat
    return ⟨a, a + d, Nat.le_add_right a d⟩

#sample OrderedPair

example (p : OrderedPair) : p.lo ≤ p.hi := by plausible

/-!
## 4. Un tipo recursivo: árboles binarios

Un generador recursivo necesita COMBUSTIBLE (`fuel`), si no diverge.
El patrón estándar: recursión sobre un `Nat` que baja, usando el `size`
de Plausible como combustible inicial.
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

def genTree : Nat → Gen Tree
  | 0 => return .leaf
  | fuel + 1 => do
    -- 1 de cada 3 veces cortamos temprano, para no generar siempre el árbol máximo
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
    | .node l _ r => [l, r]   -- un subárbol siempre es más chico

instance : SampleableExt Tree :=
  SampleableExt.mkSelfContained do
    let fuel ← Gen.getSize
    genTree (min fuel 5)

#sample Tree

-- Propiedad verdadera sobre árboles generados:
example (t : Tree) : t.depth ≤ t.size := by plausible

/-!
## Ejercicios

### 2.1 — Enumerado con pesos
Definí `Suit` (♠♥♦♣) y su instancia. Después usá `Gen.oneOf` para que
`spade` salga el doble de seguido que los otros.
Pista: `Gen.oneOf #[g1, g2, g3] (by decide)` elige entre GENERADORES,
así que podés repetir uno.
-/

inductive Suit where
  | spade | heart | diamond | club
  deriving Repr, DecidableEq

instance : Shrinkable Suit := {}

instance : SampleableExt Suit := sorry

/-!
### 2.2 — Listas no vacías
Definí un generador de `List Nat` que nunca produzca la lista vacía.
Pista: generá un elemento y una lista, y concatenalos.
-/

structure NonEmptyList where
  head : Nat
  tail : List Nat
  deriving Repr

instance : Shrinkable NonEmptyList := sorry

instance : SampleableExt NonEmptyList := sorry

-- Y después testeá que efectivamente nunca es vacía:
-- example (l : NonEmptyList) : (l.head :: l.tail) ≠ [] := by plausible

/-!
### 2.3 — Listas ORDENADAS
Este es el ejercicio importante. Generá `List Nat` ya ordenada de forma
ascendente, SIN descartar candidatos.
Pista: generá una lista cualquiera de "saltos" `[d₀, d₁, d₂, ...]` y
construí `[d₀, d₀+d₁, d₀+d₁+d₂, ...]` con `List.scanl`.
-/

structure SortedList where
  val : List Nat
  deriving Repr

def SortedList.isSorted : List Nat → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => a ≤ b && SortedList.isSorted (b :: rest)

instance : Shrinkable SortedList := sorry

instance : SampleableExt SortedList := sorry

-- El test que valida TU GENERADOR (no la propiedad): si esto falla,
-- tu generador está mal, no el teorema.
-- example (l : SortedList) : SortedList.isSorted l.val = true := by plausible

/-!
### 2.4 — Shrinking a mano
El `Shrinkable Tree` de arriba solo devuelve subárboles. Mejoralo para que
también devuelva el mismo árbol con los valores `Nat` reducidos a la mitad.
Compará la calidad de los contraejemplos antes y después con
`traceShrink := true`.
-/

/-!
## Para llevarte

1. Generá valores que YA cumplan el invariante; no generes y descartes.
2. `Shrinkable` es lo que separa un contraejemplo útil de uno ilegible.
3. Todo generador recursivo necesita combustible.
4. SIEMPRE testeá tu generador con una propiedad trivial (como 2.3) antes
   de confiar en él. Un generador roto que solo produce `[]` pasa todos
   los tests del mundo.

Siguiente: P3_LambdaTerms.lean — generar términos lambda BIEN TIPADOS.
-/
