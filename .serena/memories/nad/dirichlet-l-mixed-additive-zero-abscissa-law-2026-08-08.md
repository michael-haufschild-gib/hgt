# Card `dirichlet-l-mixed-additive-zero-abscissa-law` — CLOSED, stage 3 (2026-08-08)

Now `docs/drafts/pipeline/3-formalized/dirichlet-l-mixed-additive-zero-abscissa-law.md`.

## Card prose was stale — most of it was already built

The log said "`Theta_chi`, classical twisted Littlewood theorem, and exact limsup identity `(D3)`
remain paper-level".  All three already existed:

* `RHTower/DirichletZeroAbscissa.zeroAbscissa χ` = `Θ_χ`, with `half_le_zeroAbscissa`,
  `zeroAbscissa_le_one`, `exists_zero_lt_re`, `LFunction_ne_zero_of_zeroAbscissa_lt`.
* `RHTower/TwistedMertensLittlewood.twistedMertensSubpowerBound_zeroAbscissa` = `(D7)`,
  unconditional.
* `RHTower/TwistedMertensLittlewood.limsup_mertens_eq_zeroAbscissa` = **`(D3)`**, unconditional.

**Always grep the tree for the card's named objects before planning work.**

## What this cycle added — `RHTower/TwistedOrderLawExact.lean`

* `frequently_rpow_le_twistedMertensEvenConvolution` — `(D4a)`, unconditional Ω₊:
  `C_{χ,k}(N) ≥ (N+1)^{3k-1-ε}` infinitely often.  Route: negate, absorb with
  `HTGeometry.exists_global_subpower_of_eventually_le`, then
  `not_mertensSubpower_of_LFunction_eq_zero` at a zero supplied by `exists_zero_lt_re`.
* `DirichletGRH χ` predicate; `gammaFactor_ne_zero_of_re_pos`;
  `completedLFunction_eq_zero_of_LFunction_eq_zero`;
  **`LFunction_eq_zero_conj_one_sub`** — the reflection `ρ ↦ conj (1 - ρ)` on zeros of `L(·,χ)`,
  got by composing `hprim.completedLFunction_one_sub` (which lands on `χ⁻¹`) with
  `DirichletCompletedLConjugate.conj_completedLFunction` (which brings it back to `χ`);
* `zeroAbscissa_eq_half_iff_dirichletGRH` and **`dirichletGRH_iff_limsup_mertens_eq`** = `(D4)`.

## Pattern worth reusing

For any "zero abscissa = 1/2 ↔ RH-type hypothesis" statement, the `←` direction needs a reflection
that stays with the *same* L-function.  For `ζ` that is `completedRiemannZeta_one_sub` alone; for a
Dirichlet `χ` the functional equation moves to `χ⁻¹`, so it must be composed with conjugation
symmetry.  Both are now packaged: `RHTower.riemannZeta_one_sub_eq_zero_of_mem_openStrip` and
`RHTower.LFunction_eq_zero_conj_one_sub`.

## Repo note

`RHTower/Sieve/MertensDefectTail.lean` (committed by a concurrent agent in `3db338baa`) references
an undefined `invLogVar` and breaks the `GaloisForLFunctions.RHTower` umbrella build.  Not from this
work; every module of this card builds cleanly on its own.
