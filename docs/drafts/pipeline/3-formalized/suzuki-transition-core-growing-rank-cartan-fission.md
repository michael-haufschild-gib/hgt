# Suzuki transition-core growing-rank Cartan fission

- **ID:** SP-E-GROWING-RANK-CARTAN-FISSION
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Corpus-first audit of `SUZUKI-FE-REFLECTED-WALL-WARD-ASSEMBLY`, exact reporter-secant transition localization, fixed-scale dressed-core no-go, fixed positive-channel rank escape, and nonabelian Cartan cubic completion
- **Statement:** Fissioning every positive Suzuki transition pair into its own determinant-one rank-two Stokes block preserves the literal ordered prime-pair coefficients exactly, while the completed nonlinear observable differs from the divergent transition core by a uniformly bounded nonnegative cubic mass.

## Goal

Test the growing-channel-rank survivor left jointly by the fixed-scale Suzuki no-go and positive-channel rank-escape theorem. Required construction had to preserve both ordered source labels and the literal reporter-secant coefficient, absorb the nonsummable linear transition core before scalarization, and avoid replacing it by a bounded fixed scalar correction.

This closes two shared gates simultaneously:

1. coefficient- and two-label-faithful nonabelian occurrence of the exact Route-P/Suzuki Cauchy transition core;
2. uniform control of the nonlinear Cartan Taylor error despite cofinal divergence of the linear mass.

It does not prove RH. Remaining gate is source-natural completed Gamma/polar rectangular admission of this signed growing-rank carrier with uniformly lower-semibounded Xi-selected residual.

## Gates

- [x] 0 → 1  in-progress: corpus-derived, source-labelled, surviving architecture identified
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean module `SuzukiTransitionCoreGrowingRankCartanFission`, direct check, leaf build, and axiom audit pass
- [ ] 3 → 4  publication-ready: standalone paper and external novelty review

## Conjecture loop

### Failed conjecture classes found before conjecturing

Corpus search ruled out reflection-invariant odd-target reconstruction, Gaussian projective descent, centered-integral descent as an upstream law, fixed source-scale dressed budgets, fixed actual-head CCM compensation, and every uniformly bounded fixed-rank positive Suzuki resolution. These failures force conservation/renormalization before invariant scalarization and leave growing channel rank as one exact surviving class.

### Surviving conjecture

For every retained ordered transition pair `ij`, set

`x(N,ij) = suzukiNaturalApertureCauchyPairTerm N ij / 2`

and attach the existing determinant-one Stokes block with amplitude `sqrt x`. Then

`2 * Σ x = suzukiNaturalApertureTransitionCoreCauchyEnergy N`

exactly. Adding the quadratic counterterm to twice the block log gives

`completed N = transitionCore N + 2 * Σ R₃(x(N,ij))`.

On every positive-core pair, reporter-secant Gram is at most two, hence

`0 ≤ x(N,ij) ≤ w_i w_j`, where `w_n = Λ(n)/√n`.

The corpus logarithmic Dirichlet majorant gives `Σ w_n³ < ∞`; therefore

`0 ≤ Σ R₃(x(N,ij)) ≤ (Σ_{2≤n≤N} w_n³)² / 3`

uniformly in `N`.

### Hostile audit

The completed observable still tends to positive infinity on aperture `8n`, while its difference from the literal transition core is uniformly bounded. Thus construction demonstrably does not smuggle in forbidden fixed bounded correction or erase PNT-scale mass. Its rank grows with retained ordered source pairs, exactly as forced by prior corpus rank escape.

## Lean certificate

Module: `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiTransitionCoreGrowingRankCartanFission.lean`

Key theorems:

- `summable_criticalMellinAtomWeight_cube`
- `det_suzukiTransitionCoreStokesFissionCell`
- `suzukiTransitionCoreStokesLinearMass_two_mul_eq`
- `suzukiTransitionCoreCompletedStokesFissionObservable_eq`
- `exists_uniform_bound_suzukiTransitionCoreStokesCubicRemainderMass`
- `exists_uniform_bound_abs_suzukiTransitionCoreCompletedStokesFissionObservable_sub_core`
- `tendsto_suzukiTransitionCoreCompletedStokesFissionObservable_eight_mul_atTop`

## Exact open producer

Construct an unconditional completed-source law before Xi selection that admits ordered fission blocks and the continuum/Gamma leg into one signed Krein or rectangular carrier, proves its selected residual uniformly lower-semibounded, and preserves:

- both ordered prime labels;
- reporter-secant coefficient and divisor multiplicity;
- four reflection orientations;
- signed atomic--continuous relative mass before Hahn--Jordan separation.

Merely bounding the cubic fission remainder is insufficient: linear transition mass still escapes. Admission law must make the corresponding continuum/Gamma action co-diverge and cancel or order that mass before scalar domination.

## Verification

- `lake env lean GaloisForLFunctions/RHTower/Suzuki/SuzukiTransitionCoreGrowingRankCartanFission.lean` — pass.
- `lake build GaloisForLFunctions.RHTower.Suzuki.SuzukiTransitionCoreGrowingRankCartanFission` — pass (`[11954/11954]` target complete; dependency replay only as required for missing oleans).
- `#print axioms` on summability, exact mass, uniform-excess, and cofinal-escape theorems — only `propext`, `Classical.choice`, `Quot.sound`.
- Wired into `GaloisForLFunctions/RHTower.lean`; umbrella build intentionally not run.

## Log

- 2026-08-31 — corpus-first route/no-go audit isolated growing-rank pairwise fission.
- 2026-08-31 — conjecture survived hostile coefficient, sign, scaling, and summability checks; paper proof and unconditional Lean formalization completed.
