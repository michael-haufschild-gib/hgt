# Attempt 12: entire detection — RH ⟺ Weil positivity on entire tests (Lean-proved)

Module: `formal/GaloisForLFunctions/RHTower/GaussHodgeWeilEntireDetection.lean` (wired, RHTower
umbrella green 18899 jobs, all 5 theorems `[propext, Classical.choice, Quot.sound]`).

## The finding
Asked for an exogenous reason the odd ℓ² sector is null (i.e. a producer for Weil positivity),
the honest verdict: none exists short of RH. The executed best shot minimizes the producer's
burden instead: the rough (indicator) test class that all previous converses used adds NOTHING.

- `exists_entire_divisorOdd_unit_test`: at any divisor copy with non-real spectral point there
  is an ENTIRE, square-summable, divisor-odd test with value 1 there. Construction:
  F = c⁻¹·chain_α − d⁻¹·chain_conjα where chain = `xiThetaDividedChain` terminal divided
  quotient (multiplicity-exact). Uses NO simplicity and NO conjugation symmetry of XiC.
- `riemannHypothesis_iff_xiWeilPolarization_nonneg_entire`: **RH ⟺ 0 ≤ Re W(F,F) for every
  entire square-summable F** — strict sharpening of `riemannHypothesis_iff_xiWeilPolarization_nonneg`.
- `riemannHypothesis_iff_forall_entire_divisorOdd_eval_eq_zero`, 
  `riemannHypothesis_iff_polarization_parityFlip_invariant_entire`: same restriction for the
  attempt-11 fundamental-symmetry criteria.

## Producer statement now minimal
An unconditional positivity source for Re W(F,F) on ENTIRE square-summable tests closes RH.
This is exactly the class where explicit-formula / compressed-trace / CC-compression producers
live; nothing about non-analytic tests is ever needed.

## Reuse notes
- `XiHedenmalmMultiplicityChain.lean` owns the full divided-chain apparatus:
  `xiThetaDividedChain_local_order` (vanishing below multiplicity + nonzero terminal value +
  GLOBAL factorization XiC z = (z−α)^m·chain z), `_analyticAt`, `_nonzero_at_multiplicity`,
  jets ↔ multiplicity. Never re-derive multiplicity machinery.
- Converse skeleton: `riemannHypothesis_of_xiSpectralPoint_real` + by_cases hreal + 
  `Complex.conj_eq_iff_re` — cleaner than ¬RH-extraction via riemannHypothesis_iff_xi_zero_re_eq_half.
- mathlib `IsolatedZeros`: `eq_pow_order_mul_iterate_dslope` is a GLOBAL identity;
  `iterate_dslope_fslope_ne_zero`; `HasFPowerSeriesAt.locally_zero_iff`.
- `push_neg` is deprecated (lint-fatal warning); use `simp only [..., not_or]` or `push Not`.
