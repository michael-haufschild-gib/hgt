# Observer-jet formation decomposition and sharp properness — Lean formalization

- **Source:** `docs/drafts/pipeline/3-formalized/universal-law-field/topologically-admitted-formation-mechanics/observer-jet-formation-decomposition-clock-order-properness-and-rh-source-reduction-law.md`
- **ID:** ULF-TAFM-23
- **Status:** `[FORMALIZED] [UNCONDITIONAL] [AXIOM-CLEAN] [NOT RH]`
- **Modules:**
  - `GaloisForLFunctions.RHTower.Suzuki.SuzukiObserverJetFormation`
  - `GaloisForLFunctions.RHTower.Suzuki.SuzukiObserverJetFormationCompletion`

## Exact finite decomposition

Existing module `SuzukiObserverJetFormation.lean` proves mass/drift cancellation, terminal
second-history closure, coordinate reconstruction, Green identity `(OJ.9)`, literal weighted
curvature bound `(OJ.20)`, source landing `(OJ.29)`, source estimate `(OJ.30)`, and exact
implication `(OJ.31) → RH`.

Completion module adds:

- complete affine-gauge classification by equality of discrete curvature;
- explicit unit quadrupoles, zero mass/drift, and exact curvature response;
- injectivity of mass/drift/history coordinates through every finite cutoff;
- exact finite-coordinate coefficientwise response classification.

## Sharp completion and norm

`ObserverJetSecondFormationCompletion` is exactly `ℓ¹(Fin 2 ⊕ ℕ)`, carrying mass, drift, and
second-history coordinates in one sum norm. Finite coordinate singles have dense span.

`observerJetSecondFormationExtends_iff` proves continuous extension iff curvature is uniformly
bounded. `norm_observerJetCompletionResponseCLM` proves the exact norm

`max |λ 0| (max |(λ 1 - λ 0)| (sSup (Set.range fun j => |Δ² λ j|)))`.

No product max norm or inflated continuity constant replaces paper's `F²` sum norm.

## Literal clock and arithmetic source

New literal theorems prove first differences unbounded along square indices, uniform curvature
bound `13/4`, minimal additive order two, convergence of completed-source zeroth jets to zero, and
the normalized source estimate exactly as `(OJ.30)`.

`suzukiObserverJetFormationCompletion_unconditional` is closed theorem-family certificate. It
records `(OJ.31) → RH` as exact reduction only. `(OJ.31)` itself remains open; no hypothesis was
hidden, asserted, or discharged by claiming RH.

## Verification

Direct foreground elaboration passed with `lake env lean`. Targeted leaf build
`GaloisForLFunctions.RHTower.Suzuki.SuzukiObserverJetFormationCompletion` passed `12879/12879`; no
umbrella build was run. Eight capstone axiom audits report only `propext`, `Classical.choice`, and
`Quot.sound`. Module is wired into `RHTower` and `HTGeometry.UniversalLawField`.

Global `scripts/formal_tools.py lint` recognized this module as reachable but currently fails on
unrelated concurrently owned unwired modules; it reported no forbidden declaration in either
observer-jet module.
