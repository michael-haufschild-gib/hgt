# HB/AIME field-redefinition orbit-minimax coercivity

## Status

Paper proof and Lean formalization complete, 2026-08-28. Promoted to stage 3. Frontier map is read-only and remains untouched.

## Route

HB with AIME input. Extract exact, coordinate-invariant size of third-order Birmingham--Mokhtari cokernel burden after HC47 proved individual cascade/direct projections are field-redefinition dependent.

## Corpus basis

- `D4ThirdOrderProjectionTriple.total` is invariant under every affine redistribution `(a,b,c) ↦ (a-δ,b-ε,c+δ+ε)`.
- `d4ThirdOrderProjectionPeak_ge_oneThird` and `d4ThirdOrderProjectionPeak_eq_oneThird_iff` classify sharp orbit minimax representative.
- `d4EinsteinThirdOrder_nonAIMEProjection_eq_neg_AIME_of_unitBMTarget_of_criticalLine` identifies actual total non-AIME projection with negative AIME numerator.
- `d4FundamentalQNMCrossBranchAIMENumerator` factors as seed amplitude times its squared norm times chiral mass jet.
- `d4FundamentalQNMCrossBranchChiralMassJetNumerator_shadow` and `_xi_ne_zero` give optical-shadow invariance and nonvanishing on every Xi descendant.
- Mandatory corpus search found no exact AIME norm formula, seed-normalized orbit coercivity invariant, or physical minimax variational theorem.

## Failed/pivoted conjecture

HC47-0 sought a preferred physical equality of named channels. It failed: quadratic perturbation-coordinate changes move amplitude between cascade and direct channels. HC48 therefore measures the entire redistribution orbit, not any chosen channel.

## HC48 conjecture

Define orbit-minimax cost of a projection triple by `‖total‖/3`. Then:

1. it is exactly invariant under every redistribution;
2. it is the sharp lower bound of peak channel norm across the orbit, attained uniquely by equipartition;
3. on the actual critical-line unit-BM matching locus it equals one third of AIME numerator norm;
4. AIME numerator norm is exactly `‖amplitude‖^3 · ‖massJet(z)‖`;
5. dividing physical orbit-minimax cost by nonzero seed cubic norm leaves the positive optical-shadow-invariant kernel `‖massJet(xiSpectralPoint q)‖/3`.

This converts a coordinate-dependent trichotomy into a gauge-invariant exact coercivity coefficient.

## Bounded novelty audit

Search date: 2026-08-28. Primary-source search covered AIME (`arXiv:2112.11168`), conserved QNM projections (`arXiv:2210.15935`), nonlinear Teukolsky sources (`arXiv:2305.19332`), field-redefinition invariance in gravity (`arXiv:1309.5945`), and nonlinear QNM excitation beyond GR (`arXiv:2404.11110`). Bounded search found no exact three-channel orbit-minimax AIME coercivity, cubic seed-normalized obstruction coefficient, or optical-shadow invariance theorem of this form. This is a bounded no-match result, not an exhaustive literature-wide novelty claim.

## Conjecture loop

- HC48-A: abstract orbit cost is invariant and has exact variational characterization — proved in Lean.
- HC48-B: actual BM/AIME total realizes this cost — proved in Lean.
- HC48-C: exact cubic norm factorization — proved in Lean.
- HC48-D: normalized kernel is positive at every Xi descendant and optical-shadow invariant — proved in Lean.
- HC48-E: kernel has closed spectral formula `4 / ‖Q(z)+2‖` — discovered during proof and proved in Lean.
- HC48-F: every equal-total physical representative obeys the exact cubic lower bound, with one unique optimizer — proved in Lean.

## Positive survivor

Named stationary/second-harmonic/direct projections are coordinate artifacts, but their redistribution orbit has exact coercive size. On critical-line unit-BM matching locus, every coordinate representative has peak norm at least

`‖amplitude‖³ · 4 / ‖d4ThetaTeukolskyAngularQ (xiSpectralPoint q) + 2‖`.

Unique minimizer is equal-channel orbit representative. For nonzero seed this cost is strictly positive, so no quadratic field redefinition can dilute all three resonant channels below that amount. Dividing by seed cubic norm exposes a positive optical-shadow-invariant spectral kernel.

## Lean artifact

`GaloisForLFunctions.RHTower.ThetaCuspHawkingAIMEFieldRedefinitionOrbitMinimaxCoercivity`

All declarations are closed Lean proofs. No new axioms, `sorry`, `admit`, `opaque`, or `unsafe` declarations are introduced.

## Verification audit

- `lake env lean GaloisForLFunctions/RHTower/ThetaCuspHawkingAIMEFieldRedefinitionOrbitMinimaxCoercivity.lean`: passed.
- `lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingAIMEFieldRedefinitionOrbitMinimaxCoercivity`: passed, 12,753 jobs.
- `#print axioms` for all fourteen public theorems: only `propext`, `Classical.choice`, and `Quot.sound`.
- Module wired into `GaloisForLFunctions.RHTower` umbrella; no umbrella build was run.
- Formal lint contains no HC48 error. Global lint remains red only on unrelated unreachable owned modules.
