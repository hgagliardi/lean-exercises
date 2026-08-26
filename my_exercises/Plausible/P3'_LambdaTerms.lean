/-
Plausible P3' — SOLUCIONES de P3_LambdaTerms.lean
Archivo autocontenido. Todos los números de este archivo son mediciones
reales corridas en esta máquina, no estimaciones.
-/
import Plausible

open Plausible

/-! ## Setup (igual que P3) -/

inductive Ty where
  | base : Ty
  | arrow : Ty → Ty → Ty
  deriving Repr, DecidableEq, BEq

inductive Term where
  | var : Nat → Term
  | lam : Ty → Term → Term
  | app : Term → Term → Term
  deriving Repr, DecidableEq, BEq

def infer (ctx : List Ty) : Term → Option Ty
  | .var n => ctx[n]?
  | .lam a body =>
      match infer (a :: ctx) body with
      | some b => some (.arrow a b)
      | none => none
  | .app f x =>
      match infer ctx f, infer ctx x with
      | some (.arrow a b), some a' => if a = a' then some b else none
      | _, _ => none

def inferBuggy (ctx : List Ty) : Term → Option Ty
  | .var n => ctx[n]?
  | .lam a body =>
      match inferBuggy (a :: ctx) body with
      | some b => some (.arrow a b)
      | none => none
  | .app f x =>
      match inferBuggy ctx f, inferBuggy ctx x with
      | some (.arrow _ b), some _ => some b
      | _, _ => none

def genTy : Nat → Gen Ty
  | 0 => return .base
  | fuel + 1 => do
    let c ← Gen.chooseNatLt 0 3 (by decide)
    if c.val = 0 then return .base
    else return .arrow (← genTy fuel) (← genTy fuel)

def varsOfType (ctx : List Ty) (ty : Ty) : List Term :=
  let rec go : List Ty → Nat → List Term
    | [], _ => []
    | t :: ts, i => if t = ty then .var i :: go ts (i + 1) else go ts (i + 1)
  go ctx 0

def pickVar (ctx : List Ty) (ty : Ty) : Gen (Option Term) :=
  match varsOfType ctx ty with
  | [] => return none
  | v :: vs => do return some (← Gen.elements (v :: vs) (by simp))

/-- El generador base de P3: solo variables y lambdas. -/
def genTerm (ctx : List Ty) (ty : Ty) : Nat → Gen (Option Term)
  | 0 => pickVar ctx ty
  | fuel + 1 => do
    let choice ← Gen.chooseNatLt 0 2 (by decide)
    match ty with
    | .arrow a b =>
        if choice.val = 0 then
          match ← pickVar ctx ty with
          | some v => return some v
          | none =>
              match ← genTerm (a :: ctx) b fuel with
              | some body => return some (.lam a body)
              | none => return none
        else
          match ← genTerm (a :: ctx) b fuel with
          | some body => return some (.lam a body)
          | none => return none
    | .base => pickVar ctx ty

/-! ## 3.1 — La regla de aplicación

### Primer intento (genTerm2): la versión obvia, y ES PEOR

Para generar `x : ty` por aplicación: inventar `a`, generar `f : a → ty`,
generar `x : a`, devolver `.app f x`. Si algo falla, caer a `pickVar`.
-/

def genTerm2 (ctx : List Ty) (ty : Ty) : Nat → Gen (Option Term)
  | 0 => pickVar ctx ty
  | fuel + 1 => do
    let choice ← Gen.chooseNatLt 0 3 (by decide)
    if choice.val = 0 then
      match ← pickVar ctx ty with
      | some v => return some v
      | none => genTerm2 ctx ty fuel
    else if choice.val = 1 then
      match ty with
      | .arrow a b =>
          match ← genTerm2 (a :: ctx) b fuel with
          | some body => return some (.lam a body)
          | none => pickVar ctx ty
      | .base => genTerm2 ctx ty fuel
    else
      let a ← genTy (min fuel 2)
      match ← genTerm2 ctx (.arrow a ty) fuel with
      | none => pickVar ctx ty
      | some f =>
        match ← genTerm2 ctx a fuel with
        | none => pickVar ctx ty
        | some x => return some (.app f x)

/-!
### Segundo intento (genTerm3): fallback al generador que SÍ funciona

Dos cambios, los dos importantes:

1. Cuando la rama de aplicación falla, no cae a `pickVar` (que en contexto
   vacío devuelve `none` casi siempre) sino a `genTerm`, que sabe construir
   lambdas. **Nunca hagas fallback a algo más débil que lo que ya tenías.**
2. El tipo del argumento `a` se genera con combustible 1, no 2. Un tipo de
   argumento grande es casi imposible de habitar.
-/

def genTerm3 (ctx : List Ty) (ty : Ty) : Nat → Gen (Option Term)
  | 0 => genTerm ctx ty 0
  | fuel + 1 => do
    let choice ← Gen.chooseNatLt 0 3 (by decide)
    if choice.val = 0 then
      genTerm ctx ty (fuel + 1)
    else
      let a ← genTy (min fuel 1)
      match ← genTerm3 ctx (.arrow a ty) fuel with
      | none => genTerm ctx ty (fuel + 1)
      | some f =>
        match ← genTerm3 ctx a fuel with
        | none => genTerm ctx ty (fuel + 1)
        | some x => return some (.app f x)

/-! ## 3.2 — Medir la tasa de éxito

Ésta es la parte del ejercicio que más importa, y la que da el resultado
sorprendente.
-/

def successRate (gen : Ty → Nat → Gen (Option Term)) (n fuel : Nat) :
    BaseIO (Nat × Nat) := do
  let mut nones := 0
  for _ in [0:n] do
    let r ← Gen.run (do let ty ← genTy fuel; gen ty fuel) 10
    if r.isNone then nones := nones + 1
  return (nones, n)   -- (cuántos fallaron, de cuántos)

def hasApp : Term → Bool
  | .var _ => false
  | .lam _ b => hasApp b
  | .app _ _ => true

def appRate (n fuel : Nat) : BaseIO (Nat × Nat) := do
  let mut apps := 0
  let mut oks := 0
  for _ in [0:n] do
    let r ← Gen.run (do let ty ← genTy fuel; genTerm3 [] ty fuel) 10
    match r with
    | some t => oks := oks + 1; if hasApp t then apps := apps + 1
    | none => pure ()
  return (apps, oks)   -- (cuántos tienen aplicación, de los que salieron)

-- Rangos medidos en 4 corridas independientes en esta máquina:
#eval successRate (fun ty f => genTerm [] ty f) 300 4    -- 156-177 / 300 → 52-59% falla
#eval successRate (fun ty f => genTerm2 [] ty f) 300 4   -- 262-276 / 300 → 87-92% falla (!)
#eval successRate (fun ty f => genTerm3 [] ty f) 300 4   -- 159-179 / 300 → 53-60% falla
#eval appRate 300 4                                       -- 31-44 de ~135 → 23-33% con aplicación

/-!
### El resultado

    genTerm  (solo var+lam)        52-59% de `none`
    genTerm2 (app, fallback malo)  87-92% de `none`   ← desastre
    genTerm3 (app, fallback bueno) 53-60% de `none`

Dos conclusiones, y la segunda es la que no esperaba:

**1. `genTerm2` es un desastre.** Agregar la regla de aplicación de la
forma obvia llevó la tasa de fallo de ~55% a ~90%. Un generador que
devuelve `none` el 90% de las veces está testeando 30 casos de cada 300,
y `plausible` te va a decir igual "Unable to find a counter-example" —
con toda confianza y sin haber probado casi nada.

**2. `genTerm3` NO es más exitoso que `genTerm`.** Ambos rondan el 55%.
Lo que arregla el fallback no es la tasa de éxito, es evitar la
degradación. Y la ganancia real está en otro lado: `appRate` dice que
23-33% de los términos que produce `genTerm3` contienen una aplicación,
contra 0% en `genTerm`.

O sea: la métrica correcta no era la tasa de éxito. Era la COBERTURA.
`genTerm` tenía 55% de éxito generando exclusivamente lambdas anidadas
sin una sola aplicación — perfecto según la tasa de éxito, inútil para
testear cualquier cosa relacionada con aplicar funciones.

Esto es exactamente lo que denuncia el paper de Pałka. Si estás testeando
un optimizador de aplicaciones, un generador con 100% de éxito que nunca
genera una aplicación te da una suite verde que no ejecuta el código que
te interesa.

**Medí siempre la cobertura de tu generador. Un test verde sobre un
generador degenerado es peor que no tener test.**
-/

/-! ## La propiedad central, con el generador bueno -/

structure Candidate where
  ty : Ty
  tm : Option Term
  deriving Repr

def Candidate.ok (c : Candidate) : Bool :=
  match c.tm with
  | none => true
  | some t => infer [] t == some c.ty

instance : Shrinkable Candidate where
  shrink c :=
    match c.tm with
    | some (.lam _ _) => [{ c with tm := none }]
    | some (.app f _) => [{ c with tm := some f }, { c with tm := none }]
    | _ => []

instance : SampleableExt Candidate :=
  SampleableExt.mkSelfContained do
    let size ← Gen.getSize
    let fuel := min size 4
    let ty ← genTy fuel
    let tm ← genTerm3 [] ty fuel
    return { ty := ty, tm := tm }

example (c : Candidate) : c.ok = true := by plausible

/-! ## 3.3 — Cazar el bug de `inferBuggy`

`Candidate.ok` no lo detecta nunca, porque el generador dirigido produce
SOLO términos bien tipados, y sobre esos los dos checkers coinciden.
El bug es de PERMISIVIDAD: acepta cosas que debería rechazar. Para verlo
hacen falta términos mal tipados, o sea un generador CRUDO.
-/

def genRaw : Nat → Gen Term
  | 0 => do
      let n ← Gen.chooseNatLt 0 3 (by decide)
      return .var n.val
  | fuel + 1 => do
    let c ← Gen.chooseNatLt 0 3 (by decide)
    if c.val = 0 then
      let n ← Gen.chooseNatLt 0 3 (by decide)
      return .var n.val
    else if c.val = 1 then
      return .lam (← genTy 1) (← genRaw fuel)
    else
      return .app (← genRaw fuel) (← genRaw fuel)

structure RawTerm where
  tm : Term
  deriving Repr

instance : Shrinkable RawTerm where
  shrink r :=
    match r.tm with
    | .var _ => []
    | .lam _ b => [{ tm := b }]
    | .app f x => [{ tm := f }, { tm := x }]

instance : SampleableExt RawTerm :=
  SampleableExt.mkSelfContained do
    let s ← Gen.getSize
    return { tm := ← genRaw (min s 4) }

/-- Si el checker con bug acepta un término, el correcto también debería. -/
def RawTerm.soundness (r : RawTerm) : Bool :=
  !(inferBuggy [] r.tm).isSome || (infer [] r.tm).isSome

/-!
Descomentá para ver el bug. Salida real:

    Found a counter-example!
    r := { tm := Term.lam (Ty.arrow base base)
             (Term.app
               (Term.lam base (Term.lam (Ty.arrow base base) (Term.var 2)))
               (Term.lam (Ty.arrow base base) (Term.lam (Ty.arrow base base) (Term.var 1)))) }
    issue: false does not hold
    (0 shrinks)
-/

-- example (r : RawTerm) : r.soundness = true := by plausible (config := { numInst := 500 })

/-!
**La lección de 3.3**: no existe "el" generador. El dirigido por tipos
encuentra bugs de MISCOMPILACIÓN (el optimizador rompe un programa válido);
el crudo encuentra bugs de PERMISIVIDAD (el checker acepta basura).
Necesitás los dos, y saber cuál corresponde a cada propiedad.
-/

/-! ## 3.4 — Sustitución y preservación de tipos

Acá es donde `plausible` se paga solo. La sustitución con índices de
de Bruijn requiere *shifting*, y equivocarse es la norma, no la excepción.
-/

/-- Sube en `d` los índices libres (los ≥ cutoff). -/
def shift (d cutoff : Nat) : Term → Term
  | .var n => if n < cutoff then .var n else .var (n + d)
  | .lam a b => .lam a (shift d (cutoff + 1) b)
  | .app f x => .app (shift d cutoff f) (shift d cutoff x)

/-- Sustituye la variable `j` por `s`. Los índices mayores a `j` BAJAN uno,
    porque la lambda que los ligaba desaparece al reducir. -/
def subst (j : Nat) (s : Term) : Term → Term
  | .var n => if n = j then s else if j < n then .var (n - 1) else .var n
  | .lam a b => .lam a (subst (j + 1) (shift 1 0 s) b)
  | .app f x => .app (subst j s f) (subst j s x)

/-- Un paso de beta-reducción. -/
def step : Term → Option Term
  | .app (.lam _ b) v => some (subst 0 v b)
  | .app f x =>
      match step f with
      | some f' => some (.app f' x)
      | none =>
          match step x with
          | some x' => some (.app f x')
          | none => none
  | .lam a b =>
      match step b with
      | some b' => some (.lam a b')
      | none => none
  | .var _ => none

/-- PRESERVACIÓN: reducir no cambia el tipo. -/
def Candidate.preservation (c : Candidate) : Bool :=
  match c.tm with
  | none => true
  | some t =>
    match infer [] t with
    | none => true
    | some ty =>
      match step t with
      | none => true
      | some t' => infer [] t' == some ty

example (c : Candidate) : c.preservation = true := by
  plausible (config := { numInst := 500 })

/-!
Verificado: sin contraejemplo en 500 casos.

Probá a romperlo a propósito para ver el valor de la herramienta:

* en `subst`, cambiá `if j < n then .var (n - 1)` por `.var n`
  (olvidarse de bajar los índices libres)
* en `subst`, sacá el `shift 1 0 s` al entrar a la lambda
  (el error clásico: captura de variables)

Los dos son bugs sutiles que a ojo no se ven, y `plausible` te los tira
en menos de un segundo. Este es el argumento entero del property-based
testing sobre lenguajes.

**Ojo con la vacuidad**: `preservation` devuelve `true` cuando `step t`
es `none`, o sea cuando el término no tiene redexes. Si tu generador
produce pocos términos con aplicaciones (recordá: 23-33%), la mayoría de los
casos pasan por vacuidad. Un buen ejercicio de cierre: escribí una versión
de `preservation` que cuente cuántos casos fueron NO vacíos.
-/
