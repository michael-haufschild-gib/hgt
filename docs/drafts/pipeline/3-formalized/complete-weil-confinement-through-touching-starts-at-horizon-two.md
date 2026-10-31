# Explicit conductor confinement through touching

- **ID:** complete-weil-confinement-through-touching-starts-at-horizon-two
- **Stage:** 3-formalized
- **Statement:** Every nonpositive unit packet of the actual complete Weil matrix
  has one finite Ramanujan conductor cutoff valid for all `N≥2` and `0<c≤1`.
  The cutoff satisfies `R≤exp(D(C+1))`, where `C` is the proved defect ceiling
  and `D>0` depends only on the prescribed error.

## Proof

Write `q=completeWeilPoleShift φ 1<1` and `λ=2/(1−q)`.
The exact prime identity bounds prime energy plus the full defect by
`(log N+log 4+4)‖x‖²`. The center uses at most `(1+q)/2` of that defect.
The self term has its endpoint floor, the cross form costs at most `4C‖x‖²`,
and both poles cost at most `2|P|‖x‖²`.

The literal boundary correction has form bound
`D log(N+1)/N ‖x‖²≤D‖x‖²`. Thus the complete energy is at least
`a‖x‖²+(1−q)D_prime/2`, where

`a=self(1)−γ−log 4−4−exp(1/2)/2−q((1+λ)ψ+15)−4C−2|P|−D`.

A nonpositive unit packet has prime defect at most
`max(0,−2a/(1−q))`. The proved exponential conductor confinement theorem
then supplies the same finite approximation cutoff at every stated horizon.

## Lean

`CriticalArithmeticCorrelationTheory/TheCompleteWeilReserveHasAnExplicitTouchingHorizon.lean`:
`exists_fullWeilNonRatioMatrix_explicit_form_bound`,
`exists_fullWeilNonRatioMatrix_explicit_action_bound`,
`exists_completeWeil_primeDefect_reserve_explicit_through_touching`, and
`exists_negative_completeWeil_conductor_cutoff_explicit_through_touching`.
Direct Lean check passed. Both capstone transitive axiom audits contain only
`propext`, `Classical.choice`, and `Quot.sound`.
