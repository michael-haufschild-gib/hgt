# Attempt 13: producer verdict — deviation moment + symmetry insufficiency (Lean-proved)

Two modules (both wired, umbrella green 18904 jobs, all key theorems
`[propext, Classical.choice, Quot.sound]`):

## `GaussHodgeWeilDeviationMoment.lean` — the exact quantity arithmetic must control
- `xi_zeroCopy_eq_zero q : xi (q.1 : ℂ) = 0` (copy → actual xi zero; new reusable bridge).
- `xiSpectralPoint_im q : (α_q).im = 1/2 − re(ρ)`; `abs_xiSpectralPoint_im_lt_half` (strip).
- `xiWeilOddPart_eq_deviation_mul_dslope`: odd part at α = i·Im(α)·dslope F (conj α) α —
  deviation × symmetric divided difference, all F, no hypotheses.
- **Deviation moment identity** `xiWeilPolarization_re_eq_deviation_moment`:
  Re W(F,F) = Σ'‖evenPart F(α_q)‖² − Σ' (Im α_q)²·‖dslope F (conj α_q) α_q‖², i.e. the
  Weil-positivity defect = second moment of zero deviations (β−1/2)² weighted by |ΔF|².
- `xiWeilPolarization_re_ge_strip_bound`: Re W ≥ Σ‖even‖² − (1/4)Σ‖ΔF‖² (needs Summable ΔF²).
- `riemannHypothesis_iff_deviation_moment_eq_zero`.

## `GaussHodgeWeilSymmetryInsufficiency.lean` — the source cannot be symmetry
- `finiteWeilForm S F G` (Weil form of any finite divisor).
- `exists_entire_finiteWeilForm_neg`: finite conj-stable S with off-line point ⇒ entire
  polynomial F with (finiteWeilForm S F F).re = −2 < 0. Witness: kill-product over
  S∖{a, conj a} times the linear interpolant hitting 1/−1 at the pair.
- `weilPositivity_not_symmetry_consequence`: explicit comparison function
  (z²−a²)(z²−ā²)-form, a = 1 + i/4 — even, conjugation-real, all zeros in |Im| < 1/2, off-line
  quadruple, entire negative-diagonal test on its divisor. Formal Davenport–Heilbronn lesson:
  ANY producer of the RH positivity must consume the Euler product; FE + reality + strip are
  jointly insufficient. Concept-level [BRIDGE]/[REDISCOVERED]; formal content corpus-new.

## Final open core (post-attempt-13)
An arithmetic (Euler-product-derived) inequality Σ m(ρ)(β−1/2)²·|ΔF(ρ)|² ≤ Σ‖even part‖² for
entire square-summable tests — with formal proof that nothing weaker than arithmetic suffices,
and (attempt 12) that entire tests are the whole battlefield.

## Lean traps (2026-08 mathlib)
`tsum_le_tsum` → `Summable.tsum_le_tsum` (SummationFilter refactor); `Differentiable.finsetProd`
gives Pi-product form (convert with Finset.prod_apply); `differentiable_id'` removed;
`Differentiable.add_const` positional elaboration fails on `fun z => z + c` (use
`differentiable_id.add (differentiable_const _)`); `push_neg` deprecated (lint-fatal).
