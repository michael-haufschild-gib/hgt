# NB/BD raw Möbius critical-tail no-go (2026-08-27)

## Result
Unconditional Lean closure of the literal raw Möbius Báez--Duarte full-error and canonical complementary-tail decay route.

Module: `formal/GaloisForLFunctions/RHTower/BaezDuarteMobiusCriticalTailObstruction.lean`
Card: `docs/drafts/pipeline/5-failed/baez-duarte-raw-mobius-critical-tail-no-go.md`
Umbrella import: `formal/GaloisForLFunctions/RHTower.lean`.

## Dependency-closed theorem chain
1. Exact inverse Abel: `M(N) = N * H_N - sum_{n<N} H_n`.
2. `N * H_N^2 -> 0` implies `sqrt N * H_N -> 0`, then weighted Cesaro gives `M(N)/sqrt N -> 0`.
3. Exact Abel estimate gives critical Möbius--Laplace profile `exp(-y/2) * F(exp(-y)) -> 0`.
4. A generic sharp Abel final-value lemma sends a vanishing logarithmic profile to vanishing normalized radial Mellin tail; head/log chart also vanishes.
5. Profile decay implies half-decay and RH. An unconditional nontrivial zero is thus on the critical line.
6. Denominator-free Mellin--zeta identity forces radial boundary value `Gamma rho * (rho - 1) != 0`, contradiction.

## Main unconditional endpoints
- `not_tendsto_nat_mul_deningerHarmonicPartial_sq_zero`
- `not_tendsto_bdMobiusFullErrorEnergy_zero`
- `not_tendsto_bdMobiusComplementaryTailErrorEnergy_zero`

## Positive survivor
Each nonnegative quantity has one fixed positive lower floor attained cofinally often:
- `frequent_harmonic_energy_floor`
- `frequent_bdMobiusFullErrorEnergy_floor`
- `frequent_bdMobiusComplementaryTailErrorEnergy_floor`

## Verification
- Direct `lake env lean`: PASS.
- Exact module `lake build GaloisForLFunctions.RHTower.BaezDuarteMobiusCriticalTailObstruction`: PASS (10003/10003).
- Axiom audit: only `propext`, `Classical.choice`, `Quot.sound`.
- Targeted `git diff --check`: PASS.
- Global lint currently fails only on unrelated concurrent unreachable modules in `RHTower.Sieve` and `HTGeometry`; new module is wired/reachable.

## Novelty
Do not claim broad literature novelty for raw natural approximant failure: Báez-Duarte/Auil and later work already show failures of natural Beurling sequences; Gallardo-Gutiérrez--Seco 2025 use a corrected terminal harmonic term. Exact denominator-free critical-zero residue proof and fixed cofinal floor for this corpus canonical complementary tail were not found in audited sources, so treat as candidate corpus/formal novelty pending expert review.

## Coordination
User declared `rh-current-frontier-map.md` read-only. This work did not edit it. Concurrent workspace changes currently modify that file; preserve them and do not revert.