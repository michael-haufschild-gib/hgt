# congruence-order-trace-kahler-exterior-square-nonmetricity-law — LEAN COMPLETE

Card in stage 3 with companion; EVERY boxed equation is an unconditional Lean theorem, including
`(26j1)`–`(26j3)`.  `lake build GaloisForLFunctions.HTGeometry` green.
Seven modules under `HTGeometry/ConstraintRelativity/`, all wired:

1. `CongruenceOrderExteriorSquare.lean` (1557 lines — do NOT grow) — (3), (15),
   `kaehlerModelEquiv`, **(5)** `kaehlerCongruenceEquiv`.
2. `CongruenceOrderTraceDual.lean` — (9), **(4)**, **(26k)**.
3. `CongruenceOrderHorizon.lean` — **(7)**, **(27)/(28)**, **(6)**; `aMul`, `prodFibreEquiv`,
   `piFibreEquiv`, `sqFibreEquiv`, `quotientScalarsEquiv`, `exteriorSquareModel`.
4. `CongruenceOrderSoldering.lean` — A-module layer, **(26b)**, **(26e)**, **(26g)**.
5. `CongruenceOrderResidueHom.lean` — **(26f)**.
6. `CongruenceOrderKaehlerDifferent.lean` — **(26l)**; zeroth Fitting ideal built from scratch.
7. `CongruenceOrderFirstOrder.lean` — `residueEquiv` (`A/𝔪 ≅ R/(a)`), **(26j1)**
   (`maximalIdealSq_smul_kaehler`, `maximalIdealSq_smul_traceDefect`), **(26j2)**
   (`headReduction`, `headReduction_eq_zero`), `kaehlerHeadEquiv` (`Ω/𝔪Ω ≅ (A/𝔪)^m`),
   `traceDefectHeadEquiv'` (`L/𝔪L ≅ k^m`), `homHeadEquiv`, **(26j3)**
   `solderingObstructionEquiv` (`𝒩₀ ≅ Mat_{m×m}(k)`), `headMap_eq_zero_of_lifts`.

## Downstream: soldering card's concrete sharp model is now formalized
`source-soldering-transport-defect-cocycle-and-law-symbol-formalized.md` had admitted that its
"Concrete sharp model" was not formalized; its Scope now points at module 7.  What is still NOT
done there: identifying that instance with the abstract `lawObstruction` of
`SolderingTransportSymbol.lean`, which needs `[Field k] [Algebra k A]` — a COEFFICIENT FIELD,
i.e. the card's own `R = ℂ[[a]]`.  State it with `Algebra k R` + `k → R/(a)` bijective if attempted.

## Lean traps added this round
- `smul_single` in `CongruenceOrderExteriorSquare.lean` was marked `private` by tooling —
  re-prove the one-liner inline instead of editing that file.
- `zero_smul` on `Ω[A⁄R]` / `traceDefect` needs BOTH the ring AND the element explicit; `simp`
  cannot close `0 • x = 0` there.
- `IsScalarTower.algebraMap_smul A r` rewrites `algebraMap r • x → r • x` (use FORWARD).
- `Ideal.quotientEquivAlgOfEq` / `quotientKerAlgEquivOfSurjective` need `a`, `m` pinned or the
  `Ideal.IsTwoSided` search gets stuck on metavariables.
- `LinearEquiv.piCongrRight` fails to synthesize `∀ i, Module R (ψ i)` for CONSTANT families here;
  a hand-rolled `piMapEquiv` (postcompose a linear equiv on a function space) works.
- Bridging `M ⧸ (I • ⊤ : Submodule A M)` to `M ⧸ (aMul a M : Submodule R M)` by an A-equiv then
  `restrictScalars` causes an `isDefEq` TIMEOUT.  Instead prove
  `(I • ⊤).restrictScalars R = aMul a M` and use `Submodule.quotEquivOfEq` over R directly.
- `abbrev`, not `def`, for a quotient type you want instances on (`solderingObstructionSpace`).
- A concurrent session edits this tree; `lake build` can fail transiently on their half-written
  modules — re-run before believing a failure.
