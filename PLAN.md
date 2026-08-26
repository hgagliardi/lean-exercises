# Plan acelerado — Lean + Plausible en 12 días

**Objetivo**: llegar a la pasantía en AWS (arranca ~2026-09-07) con Lean como
lenguaje de programación y property-based testing sólidos.
**Fecha de inicio**: 2026-08-26.

## Criterio de corte

El curso FAA2025 completo son ~10 semanas (~226 `sorry`). Este plan cubre ~75
más 4 hojas nuevas de Plausible.

- **Adentro**: Semanas 1, 2, 4, 5, 6, 8 + `my_exercises/Plausible/`
- **Afuera**: Semana 3 (salvo `Sheet0.lean`, que se lee), Semanas 7, 9, 10,
  los Problem Sets salvo el 04, y los `Exercise.lean` de W01–W02.

Razón: lo que AWS nombró (Plausible, specimen, el paper de Pałka) es
generación de datos estructurados y bien tipados. Grafos y BFS no transfieren.

## Cómo trabajar

- Resolvés en `my_exercises/`. Los archivos **con apóstrofe son las soluciones**
  (`Sheet1.lean` → `Sheet1'.lean`). Igual en Plausible (`P1_Basics.lean` → `P1'_Basics.lean`).
- **Timebox de 15 min por `sorry`.** Si no sale: abrís la solución, la leés,
  la cerrás, la reescribís de memoria. El atasco es el único enemigo real.
- `exact?` / `apply?` / `observe h : P` sin culpa: buscan en Mathlib por vos.
- **`plausible` antes de demostrar**, desde el día 3 en adelante.

## Calendario

| Día | Fecha | Trabajo | ~sorries | ✓ |
|-----|-------|---------|----------|---|
| 1  | 08-26 | Week01 Sheets 1→2→3. Lógica proposicional. | 15 | ☐ |
| 2  | 08-27 | Week02 Sheets 0→1→2 (∀/∃, `use`, `obtain`, `rw`). Leer Week03 `Sheet0.lean` sin resolver. | 14 | ☐ |
| 3  | 08-28 | **Plausible P1** (`#sample`, táctica, shrinking) + **P2** (`Shrinkable`, `SampleableExt`). | — | ☐ |
| 4  | 08-29 | Week04 Sheets 1+2 — inducción funcional, terminación. | ~8 | ☐ |
| 5  | 08-30 | Week04 Sheet3 + Problem Set 04. **El día más denso.** | ~12 | ☐ |
| 6  | 08-31 | Week05 Sheets 0→1→2 — predicados inductivos, soundness/completeness. | 15 | ☐ |
| 7  | 09-01 | **Plausible P3** — términos lambda bien tipados. El ejercicio clave. | — | ☐ |
| 8  | 09-02 | Week06 `API.lean` + Sheets 1+2 — MergeSort, invariantes de merge. | ~8 | ☐ |
| 9  | 09-03 | Week06 Sheet3 + **Plausible P4** — testear antes de demostrar. ✂ Sheet3 si vas justo. | ~4 | ☐ |
| 10 | 09-04 | Week08 `API.lean` + Sheet1 — mónada `TimeM`, corrección vs. costo. | ~12 | ☐ |
| 11 | 09-05 | Leer, no codear: paper de Pałka + repo **specimen**. Anotar qué generaría Plausible para sus specs. | — | ☐ |
| 12 | 09-06 | Buffer. Si sobra: paper de Millstein (OOPSLA'25) + mini-proyecto propio. | — | ☐ |

## Las hojas de Plausible

En `my_exercises/Plausible/`. Todas compilan; los números son mediciones reales.

| Archivo | Qué enseña |
|---------|------------|
| `P1_Basics.lean` | `#sample`, táctica `plausible`, config, leer el shrinking. La trampa `numInst` vs `maxSize`. |
| `P2_Generators.lean` | `Gen`, `Shrinkable`, `SampleableExt`. Generar cumpliendo el invariante en vez de generar-y-filtrar. |
| `P3_LambdaTerms.lean` | Generación dirigida por tipos (paper de Pałka). Medir cobertura, no solo tasa de éxito. |
| `P4_TestThenProve.lean` | El flujo completo. Por qué "está ordenado" no es una especificación. |

## Bibliografía de la pasantía

- Plausible — https://github.com/leanprover-community/plausible
- specimen — https://github.com/strata-org/specimen
- Millstein et al., OOPSLA'25 — https://web.cs.ucla.edu/~todd/research/pub.php?id=oopsla25a
- Pałka, Claessen, Russo, Hughes, *Testing an Optimising Compiler by Generating
  Random Lambda Terms* (AST 2011) — la base conceptual de `P3`.

## Notas de entorno

- Toolchain fijo: `leanprover/lean4:v4.22.0-rc3`. Lean no es retrocompatible.
- Plausible ya viene instalado como dependencia transitiva de Mathlib
  (`.lake/packages/plausible`). Alcanza con `import Plausible`.
- **`import Mathlib.Tactic` puede tirar segfault en esta máquina por RAM**
  (15 GB totales, ~7 libres). Si pasa, importá módulos específicos
  (`import Mathlib.Data.List.Basic`). Las 8 hojas de Plausible solo
  necesitan `import Plausible`, así que compilan siempre.
- Compilar una hoja desde la raíz del repo: `lake env lean my_exercises/Plausible/P1_Basics.lean`
