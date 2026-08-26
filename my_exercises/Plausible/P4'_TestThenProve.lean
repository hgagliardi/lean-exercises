/-
Plausible P4' — SOLUCIONES de P4_TestThenProve.lean
Todas las demostraciones de este archivo compilan sin `sorry`.
-/
import Plausible

def ins (a : Nat) : List Nat → List Nat
  | [] => [a]
  | b :: l => if a ≤ b then a :: b :: l else b :: ins a l

def isort : List Nat → List Nat
  | [] => []
  | a :: l => ins a (isort l)

def sorted : List Nat → Bool
  | [] => true
  | [_] => true
  | a :: b :: l => a ≤ b && sorted (b :: l)

def count (x : Nat) : List Nat → Nat
  | [] => 0
  | a :: l => (if a = x then 1 else 0) + count x l

/-! ## Parte A: el resultado está ordenado

El problema: en el caso `¬(a ≤ b)`, `ins a (b :: l) = b :: ins a l`, y para
concluir `sorted (b :: ins a l)` hace falta saber CUÁL ES LA CABEZA de
`ins a l`. La hipótesis inductiva "está ordenada" no alcanza.

La técnica: **fortalecer la hipótesis inductiva**. Se demuestra a la vez
que el resultado está ordenado Y que su cabeza es o bien `a`, o bien la
cabeza original. Es el mismo truco que vas a usar en MergeSort (Week06).
-/

theorem sorted_tail {b : Nat} {l : List Nat} (h : sorted (b :: l) = true) :
    sorted l = true := by
  cases l with
  | nil => simp [sorted]
  | cons c l' => simp [sorted] at h; simp [h.2]

theorem sorted_cons_of (b : Nat) (m : List Nat) (hm : sorted m = true)
    (hhead : ∀ c, m.head? = some c → b ≤ c) : sorted (b :: m) = true := by
  cases m with
  | nil => simp [sorted]
  | cons c m' =>
    have hbc : b ≤ c := hhead c rfl
    simp [sorted, hbc, hm]

/-- La hipótesis inductiva fortalecida. -/
theorem ins_spec : ∀ (l : List Nat) (a : Nat), sorted l = true →
    sorted (ins a l) = true ∧ ((ins a l).head? = some a ∨ (ins a l).head? = l.head?) := by
  intro l
  induction l with
  | nil => intro a _; simp [ins, sorted]
  | cons b l' ih =>
    intro a h
    by_cases hab : a ≤ b
    · simp [ins, hab, sorted, h]
    · have hsl' : sorted l' = true := sorted_tail h
      obtain ⟨ihs, ihh⟩ := ih a hsl'
      have hba : b ≤ a := by omega
      refine ⟨?_, ?_⟩
      · simp only [ins, hab, if_false]
        refine sorted_cons_of b (ins a l') ihs ?_
        intro c hc
        rcases ihh with hh | hh
        · rw [hh] at hc; simp at hc; omega
        · rw [hh] at hc
          cases l' with
          | nil => simp at hc
          | cons d l'' =>
            simp at hc
            subst hc
            simp [sorted] at h
            exact h.1
      · right; simp [ins, hab]

theorem sorted_ins (a : Nat) (l : List Nat) (h : sorted l = true) :
    sorted (ins a l) = true := (ins_spec l a h).1

theorem sorted_isort (l : List Nat) : sorted (isort l) = true := by
  induction l with
  | nil => simp [isort, sorted]
  | cons a l' ih => exact sorted_ins a (isort l') ih

/-! ## Parte B: es una permutación

Mucho más fácil: `count` conmuta con todo y `omega` cierra la aritmética.
-/

theorem count_ins (x a : Nat) (l : List Nat) :
    count x (ins a l) = (if a = x then 1 else 0) + count x l := by
  induction l with
  | nil => simp [ins, count]
  | cons b l' ih =>
    by_cases hab : a ≤ b
    · simp [ins, hab, count]
    · simp only [ins, hab, if_false, count, ih]
      omega

theorem count_isort (x : Nat) (l : List Nat) : count x (isort l) = count x l := by
  induction l with
  | nil => simp [isort]
  | cons a l' ih => simp [isort, count_ins, count, ih]

/-! ## Parte C: la especificación completa -/

theorem isort_correct (l : List Nat) :
    sorted (isort l) = true ∧ ∀ x, count x (isort l) = count x l :=
  ⟨sorted_isort l, fun x => count_isort x l⟩

/-! ## 4.2 — El lema falso

    example (a : Nat) (l : List Nat) : ins a l = a :: l

Salida real de `plausible`:

    Found a counter-example!
    a := 4
    l := [1, 1, 4, 5, 6, 1]
    issue: [1, 1, 4, 4, 5, 6, 1] = [4, 1, 1, 4, 5, 6, 1] does not hold
    (0 shrinks)

Por qué falla: `ins` pone `a` en su LUGAR, no al principio. Solo coincide
con `a :: l` cuando `a` ya es menor o igual que la cabeza de `l`. El
enunciado verdadero es `ins_of_sorted_le` de más abajo, y necesita esa
hipótesis.
-/

/-! ## 4.3 — Longitud -/

theorem length_ins (a : Nat) (l : List Nat) : (ins a l).length = l.length + 1 := by
  induction l with
  | nil => simp [ins]
  | cons b l' ih => by_cases hab : a ≤ b <;> simp [ins, hab, ih]

theorem length_isort (l : List Nat) : (isort l).length = l.length := by
  induction l with
  | nil => simp [isort]
  | cons a l' ih => simp [isort, length_ins, ih]

/-!
### ¿`length` sirve como sustituto de la propiedad de permutación?

Sobre `isortBug` (el que se come elementos), `plausible` da:

    example (xs : List Nat) : (isortBug xs).length = xs.length := by plausible
    Found a counter-example!
    xs := [0, 0]
    issue: 1 = 2 does not hold
    (5 shrinks)

Así que SÍ caza este bug, y encima con un contraejemplo mínimo precioso
(`[0, 0]`, 5 shrinks) — mucho mejor que el que daba `count`.

Pero NO es un sustituto en general. `fun l => List.replicate l.length 0`
tiene la longitud correcta, devuelve algo ordenado, y es un sort
completamente roto. `length` es una condición necesaria, no suficiente;
`count` sí es suficiente.

Moraleja doble: una propiedad más débil puede dar contraejemplos mucho
más legibles, así que sirve para DEPURAR — pero la que tenés que
demostrar es la fuerte.
-/

/-! ## 4.4 — Idempotencia -/

theorem ins_of_sorted_le (a : Nat) (l : List Nat) (h : sorted (a :: l) = true) :
    ins a l = a :: l := by
  cases l with
  | nil => simp [ins]
  | cons b l' => simp [sorted] at h; simp [ins, h.1]

theorem isort_of_sorted (l : List Nat) (h : sorted l = true) : isort l = l := by
  induction l with
  | nil => simp [isort]
  | cons a l' ih =>
    have hs : sorted l' = true := sorted_tail h
    simp [isort, ih hs, ins_of_sorted_le a l' h]

theorem isort_idem (l : List Nat) : isort (isort l) = isort l :=
  isort_of_sorted (isort l) (sorted_isort l)

/-! ## 4.6 — Estabilidad

Formulación testeable: un sort es estable si, al filtrar por una clave,
el orden de los elementos con esa clave es el mismo antes y después.
-/

def insP (a : Nat × Nat) : List (Nat × Nat) → List (Nat × Nat)
  | [] => [a]
  | b :: l => if a.1 ≤ b.1 then a :: b :: l else b :: insP a l

def isortP : List (Nat × Nat) → List (Nat × Nat)
  | [] => []
  | a :: l => insP a (isortP l)

def stableOn (k : Nat) (xs : List (Nat × Nat)) : Bool :=
  (isortP xs).filter (·.1 == k) == xs.filter (·.1 == k)

example (k : Nat) (xs : List (Nat × Nat)) : stableOn k xs = true := by
  plausible (config := { numInst := 500 })

/-!
Resultado: sin contraejemplo en 500 casos. **Insertion sort es estable.**

El detalle fino de por qué: `isort (a :: l) = ins a (isort l)` ordena
primero la COLA y después inserta la cabeza. Y `ins` usa `a.1 ≤ b.1`
(con el `≤`, no el `<`), así que ante un empate el elemento nuevo — que
venía ANTES en la lista original — queda adelante. Correcto.

Cambiá `≤` por `<` en `insP` y volvé a correr: `plausible` te debería
encontrar el contraejemplo de estabilidad. Ese es el ejercicio real,
porque es un cambio de un carácter que ningún test de "está ordenado"
puede detectar.
-/

/-!
## Lo que había que sacar de acá

1. **Fortalecer la hipótesis inductiva** es la técnica central de toda la
   Parte A, y es la misma que necesita MergeSort en Week06. Si la IH no
   te alcanza, no busques otra táctica: buscá un enunciado más fuerte.
2. La mitad "es una permutación" es la difícil de ACORDARSE y la fácil de
   demostrar. La mitad "está ordenada" es al revés.
3. Propiedades débiles (`length`) dan mejores contraejemplos que las
   fuertes (`count`). Usá las débiles para depurar, demostrá las fuertes.
4. La estabilidad depende de un `≤` contra un `<`. Un carácter. Ninguna
   demostración de sortedness lo detecta, y `plausible` sí.
-/
