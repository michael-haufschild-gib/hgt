# HB third-order cokernel quantitative trichotomy

## Status

Paper proof and Lean formalization complete, 2026-08-28. Promoted to stage 3. Frontier map is read-only and remains untouched.

## Route

HB, specifically missing gauge-fixed third-order `++-` Einstein--Teukolsky producer forced by AIME/BM incidence.

## Corpus basis

- `d4EinsteinThirdOrderPlusPlusMinusSource_chargeSplit` identifies three non-AIME channels: charge-orthogonal stationary cascade, second-harmonic cascade, and direct third variation.
- `d4EinsteinThirdOrder_nonAIMEProjection_eq_neg_AIME_of_unitBMTarget_of_criticalLine` fixes their aggregate resonant projection exactly to the negative AIME numerator under critical-line unit BM incidence.
- `d4EinsteinThirdOrder_unitBMTarget_of_criticalLine_forces_nonexact_channel` proves only a qualitative nonexact-channel trichotomy.
- Corpus search found no quantitative lower bound, sharp constant, or norm-bearing cokernel trichotomy for these actual channels.

## HC45 conjecture

If three complex resonant projections sum to `-AIME`, triangle inequality forces total channel norm at least `‖AIME‖`; hence at least one channel has norm at least `‖AIME‖ / 3`. The constant `1/3` is sharp, attained when all three channels equal `-AIME/3`.

Applied to actual third-order Einstein source under critical-line unit BM incidence and nonzero absorbed seed, at least one of the three non-AIME channels simultaneously:

- carries resonant norm at least one-third of exact AIME norm; and
- represents a nonzero cokernel class, because every linearized-operator-exact channel is annihilated by the left resonant state.

## Positive survivor

Missing HB source is not merely nonexact somewhere. Its three-channel decomposition obeys a sharp quantitative budget: literal dynamics must place at least one-third of exact AIME resonant norm into one physical non-AIME channel. This supplies a falsifiable lower bound for any future gauge-fixed third-order computation and closes qualitative-to-quantitative proof burden.

## Bounded novelty audit

Search date: 2026-08-28. Primary sources checked: Sberna et al. AIME (`arXiv:2112.11168`), Spiers--Pound--Moxon second-order Teukolsky nonlinear source (`arXiv:2305.19332`), Green--Hollands--Sberna--Toomani--Zimmerman conserved QNM projections (`arXiv:2210.15935`), and Ma--Yang quadratic QNM excitation (`arXiv:2401.15516`). They establish third-order AIME, nonlinear Teukolsky source machinery, resonant projection, and quadratic excitation, respectively. Bounded search found no exact three-channel AIME cancellation budget, sharp `1/3` bound, or quantitative cokernel trichotomy. This is a bounded no-match finding, not exhaustive literature-wide novelty claim.

## Conjecture loop

- HC45-A: abstract three-channel norm budget — proved in Lean.
- HC45-B: sharp `1/3` pigeonhole bound — proved in Lean.
- HC45-C: sharpness witness — proved in Lean.
- HC45-D: actual Einstein-channel quantitative nonexact trichotomy — proved in Lean.

## Lean artifact

`GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMThirdOrderCokernelQuantitativeTrichotomy`

Main results:

- three-channel aggregate norm budget;
- one-third pigeonhole lower bound;
- aligned equal-channel witness proving sharpness;
- actual BM/AIME non-AIME source norm budget;
- quantitative disjunction pairing one-third lower bound with nonexactness of selected physical channel.

All declarations are closed Lean proofs. No new axioms, `sorry`, `admit`, `opaque`, or `unsafe` declarations are introduced.

## Verification audit

- `lake env lean GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspHawkingBMThirdOrderCokernelQuantitativeTrichotomy.lean`: passed.
- `lake build GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMThirdOrderCokernelQuantitativeTrichotomy`: passed, 12,749 jobs.
- `#print axioms` for all five public theorems: only `propext`, `Classical.choice`, and `Quot.sound`.
- Module wired into `GaloisForLFunctions.RHTower` umbrella; no umbrella build was run.
- Formal lint contains no HC45 error. Global lint remains red only on unrelated pre-existing or concurrently added unreachable owned modules.
