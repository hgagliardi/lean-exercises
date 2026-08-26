/-
Plausible P3 — Generación de términos lambda BIEN TIPADOS
Preparación pasantía AWS. Día 7 del plan.

Basado en: Pałka, Claessen, Russo, Hughes,
"Testing an Optimising Compiler by Generating Random Lambda Terms" (AST 2011).
-/
import Plausible

open Plausible

/-!
# P3. Términos lambda bien tipados

La idea del paper: para encontrar bugs en un compilador no alcanza con
generar programas al azar — casi todos son basura que ni siquiera tipa,
y el compilador los rechaza antes de llegar al optimizador. Hay que generar
programas que YA estén bien tipados, y para eso se genera *dirigido por el
tipo*: primero elegís el tipo que querés, y después construís un término
de ese tipo.

Este es el ejercicio más transferible a la pasantía. Es exactamente la
técnica que se usa para testear specs estructuradas (specimen, políticas
IAM, configuraciones de red).

## 1. El lenguaje: lambda simplemente tipado, índices de de Bruijn

Sin nombres de variables: `var 0` es la lambda más cercana, `var 1` la
siguiente, etc. Evita todo el problema de captura de nombres.
-/

inductive Ty where
  | base : Ty
  | arrow : Ty → Ty → Ty
  deriving Repr, DecidableEq, BEq

inductive Term where
  | var : Nat → Term
  | lam : Ty → Term → Term
  | app : Term → Term → Term
  deriving Repr, DecidableEq, BEq

/-- El type checker. `none` = el término no tipa en ese contexto. -/
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

-- La identidad en `base`: λ(x : base). x
#eval infer [] (.lam .base (.var 0))          -- some (base → base)
-- Un término mal tipado: aplicar algo de tipo base
#eval infer [] (.app (.var 0) (.var 0))       -- none

/-!
## 2. Generador de tipos

Igual que el árbol de P2: recursión con combustible.
-/

def genTy : Nat → Gen Ty
  | 0 => return .base
  | fuel + 1 => do
    let c ← Gen.chooseNatLt 0 3 (by decide)
    if c.val = 0 then
      return .base
    else
      return .arrow (← genTy fuel) (← genTy fuel)

/-!
## 3. Generación DIRIGIDA POR EL TIPO

`varsOfType ctx ty` = todas las variables del contexto que tienen tipo `ty`.
Esta es la pieza que hace que el término salga bien tipado por construcción.
-/

def varsOfType (ctx : List Ty) (ty : Ty) : List Term :=
  let rec go : List Ty → Nat → List Term
    | [], _ => []
    | t :: ts, i => if t = ty then .var i :: go ts (i + 1) else go ts (i + 1)
  go ctx 0

#eval varsOfType [.base, .arrow .base .base, .base] .base   -- [var 0, var 2]

/-- Elige una variable del contexto que tenga el tipo pedido, si existe. -/
def pickVar (ctx : List Ty) (ty : Ty) : Gen (Option Term) :=
  match h : varsOfType ctx ty with
  | [] => return none
  | v :: vs => do return some (← Gen.elements (v :: vs) (by simp))

/-!
`genTerm ctx ty fuel` intenta construir un término de tipo `ty` en el
contexto `ctx`. Devuelve `none` si no encuentra ninguno.

Por ahora sabe hacer dos cosas:
  * usar una variable del contexto que ya tenga el tipo `ty`
  * si `ty = a → b`, meter una lambda y generar el cuerpo de tipo `b`
    en el contexto extendido `a :: ctx`

Le FALTA la regla de aplicación. Ese es el ejercicio 3.1.
-/

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

/-!
## 4. El test que valida el GENERADOR

Este es el patrón clave, y lo que más te va a servir: antes de usar el
generador para buscar bugs en otra cosa, testeás que el generador cumple
su propia especificación.

Especificación: *todo término que genero, tipa con el tipo que pedí*.
-/

structure Candidate where
  ty : Ty
  tm : Option Term
  deriving Repr

/-- `true` si el candidato es vacío, o si el término tipa con el tipo pedido. -/
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
    let tm ← genTerm [] ty fuel
    return { ty := ty, tm := tm }

#sample Candidate

-- LA PROPIEDAD CENTRAL: el generador nunca produce un término mal tipado.
example (c : Candidate) : c.ok = true := by plausible

/-!
## 5. Encontrar un bug con esto

Abajo hay un type checker CON UN BUG (`inferBuggy`): en la regla de
aplicación no chequea que el tipo del argumento coincida con el dominio
de la función. Un checker así acepta programas que se rompen en runtime.

Fijate que `plausible` NO lo detecta con la propiedad de arriba —
porque `inferBuggy` es más permisivo, no más restrictivo. Hay que
elegir la propiedad correcta. Ese es el ejercicio 3.3.
-/

def inferBuggy (ctx : List Ty) : Term → Option Ty
  | .var n => ctx[n]?
  | .lam a body =>
      match inferBuggy (a :: ctx) body with
      | some b => some (.arrow a b)
      | none => none
  | .app f x =>
      match inferBuggy ctx f, inferBuggy ctx x with
      | some (.arrow _ b), some _ => some b   -- BUG: no compara `a` con `a'`
      | _, _ => none

/-!
## Ejercicios

### 3.1 — Agregar la regla de aplicación (EL EJERCICIO PRINCIPAL)

Extendé `genTerm` para que también pueda generar `.app f x`.
Para construir un término de tipo `b` por aplicación necesitás:
  1. inventar un tipo de argumento `a` (usá `genTy` con poco combustible)
  2. generar `f : a → b`
  3. generar `x : a`
  4. devolver `.app f x`

Ojo con dos cosas:
  * si `a` es muy grande, casi nunca vas a poder generar un `x : a` y te
    va a dar `none` todo el tiempo. Mantené el combustible de `a` chico.
  * el combustible tiene que BAJAR en las dos llamadas recursivas.

Escribilo como `genTerm2` y volvé a correr la propiedad central.
-/

def genTerm2 (ctx : List Ty) (ty : Ty) : Nat → Gen (Option Term) := sorry

/-!
### 3.2 — Medir la tasa de éxito
Escribí un `#eval` que genere 100 candidatos y cuente cuántos dieron `none`.
Pista: `Gen.run g size : BaseIO α`, y `#eval` corre `BaseIO`.
No asumas que agregar la aplicación mejora el número: medilo. En esta
máquina, la versión obvia de 3.1 lo EMPEORA de ~55% a ~90% de `none`.
Averiguá por qué y arreglalo.

Y después medí una segunda cosa: de los términos que sí salen, ¿qué
porcentaje contiene realmente una aplicación? Esa es la métrica que
importa de verdad, y no es la misma que la tasa de éxito.
-/

-- #eval do ...

/-!
### 3.3 — Cazar el bug de `inferBuggy`
La propiedad `c.ok = true` no lo detecta. Encontrá una propiedad que sí.
Pista: pensá en qué hace `inferBuggy` que `infer` no hace. Necesitás
generar términos POSIBLEMENTE MAL TIPADOS (un generador distinto, sin
dirección por tipos) y comparar los dos checkers:

    todo término que `inferBuggy` acepta, ¿lo acepta también `infer`?

Vas a necesitar un `SampleableExt Term` "crudo", que genere términos al
azar sin cuidar los tipos. Ese contraste — generador dirigido vs. generador
crudo — es la lección central del paper de Pałka.
-/

/-!
### 3.4 — Sustitución y preservación de tipos
Definí la sustitución `subst : Term → Nat → Term → Term` y un paso de
beta-reducción `step : Term → Option Term`. Después testeá PRESERVACIÓN:

    si `infer [] t = some ty` y `step t = some t'`, entonces `infer [] t' = some ty`

Esta propiedad es el corazón de la seguridad de tipos, y es notoriamente
fácil de romper al implementar sustitución con índices de de Bruijn
(el famoso "shifting"). `plausible` te va a encontrar el error en segundos.
-/

/-!
## Para llevarte

1. Generación dirigida por el tipo: elegís el tipo primero, el término después.
   El resultado es correcto POR CONSTRUCCIÓN, no por filtrado.
2. Siempre medí la tasa de `none` de tu generador. Es la métrica que dice
   si tu test realmente está testeando algo.
3. Para cazar un bug de PERMISIVIDAD necesitás un generador crudo, no uno
   dirigido. Distintos bugs necesitan distintos generadores.

Siguiente: P4_TestThenProve.lean — el flujo completo, testear antes de demostrar.
-/
