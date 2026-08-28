# HB division-free cross-pair response compensator

Status: formalized
Route: HB
Started: 2026-08-28
Completed: 2026-08-28

## Conjecture HC19

Let `F_n(q)` be literal unit unsquared BM source amplitude times its complementary exponent.
Define the reflected cross-pair response correction

`K_n(q) = (2q-1) F_n(reflect q)`.

Then the composite response charge is

`H_n(q) = (2q-1) F_n(q) F_n(reflect q)`,

so functional-equation involution makes `H_n(reflect q) = -H_n(q)` without division. Prove that
`K_n` and `H_n` vanish exactly on the critical wall, while corrected reflection current cancels
unconditionally at every Xi copy. Off wall this must be nontrivial cancellation of nonzero charges
even though HC18 canonical optical power remains strictly positive.

## Result

HC19 holds. Lean proves exact factorization of the corrected charge, its critical-wall zero
classification, and its reflection-odd law. Consequently, the corrected reflection current
vanishes at every Xi copy with no premise.

For every tilted Xi copy, the same theorem package proves simultaneously:

- cross-pair charge is nonzero;
- corrected reflection current is zero;
- canonical Peierls--Darboux optical power is strictly positive.

Thus this is genuine cancellation of two nonzero reflected charges, not a zero-source or
zero-observable degeneration.

## Main Lean theorems

- `d4BMXiSecondHarmonicBareResponseFactor_eq_zero_iff`
- `d4BMXiSecondHarmonicCrossPairResponseCorrection_eq_zero_iff`
- `d4BMXiSecondHarmonicCrossPairResponseCharge_eq`
- `d4BMXiSecondHarmonicCrossPairResponseCharge_eq_zero_iff`
- `d4BMXiSecondHarmonicCrossPairResponseCharge_reflection_odd`
- `forall_d4BMXiSecondHarmonicCrossPairResponseCorrectedReflectionCurrent_eq_zero`
- `d4BMXiSecondHarmonicCrossPairCancellation_nontrivial_of_tilt`

Module:
`formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMCrossPairResponseCompensator.lean`

## New knowledge

Removing division and source-wall singularities does not restore RH force to response-corrected
reflection currents. The explicit polynomial cross-pair correction is regular at the wall, has the
same exact wall zero locus as the physical source, and cancels all Xi fibres unconditionally.

The sharp surviving gate is therefore structural, not merely regularity: a viable HB proof must
derive response source-independence, reflection locality, or a literal left-QNM/action incidence
that excludes source-matched reflected factors. HC18 optical positivity supplies an independent
certificate that HC19 cancellation remains physically nontrivial off wall.

## Literature audit through 2026-08-28

Primary literature supplies conserved Kerr reflection currents and QNM bilinear forms, nonlinear
second-order Teukolsky sources, absorption-induced mode excitation, and Peierls/covariant phase
space. Search found no Xi-divisor response charge, no division-free reflected-source cross-pair
compensator, and no theorem combining unconditional current cancellation with strictly positive
off-wall optical power:

- Green et al., *Conserved currents for Kerr and orthogonality of quasinormal modes*,
  https://arxiv.org/abs/2210.15935
- Spiers--Pound--Moxon, *Second-order Teukolsky formalism in Kerr spacetime: formulation and
  nonlinear source*, https://arxiv.org/abs/2305.19332
- Sberna et al., *Nonlinear effects in the black hole ringdown: absorption-induced mode
  excitation*, https://arxiv.org/abs/2112.11168
- Khavkine, *Covariant phase space, constraints, gauge and the Peierls formula*,
  https://arxiv.org/abs/1402.1282

Novelty claim is the exact compensator/factorization/classification and strengthened regularity
no-go, not the underlying classical perturbation frameworks.

## Verification

- Direct: `lake env lean GaloisForLFunctions/RHTower/ThetaCuspHawkingBMCrossPairResponseCompensator.lean`
- Target audit: `lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCrossPairResponseCompensator`
- Build result: success, 11913 jobs after shared dependency replay
- `#print axioms` on seven endpoints: `[propext, Classical.choice, Quot.sound]` only
- Forbidden-token and diff-whitespace scans: clean
- Umbrella import added to `formal/GaloisForLFunctions/RHTower.lean`; no umbrella build run
- Global lint reports only unrelated umbrella reachability failures; this module is reachable and
  has no lint finding

## Remaining HB burden

Classify source-independent response corrections exactly, then derive such a nonzero correction
from the literal left-QNM/action problem. HC19 proves algebraic regularity alone cannot distinguish
physical response from a source-matched compensator.
