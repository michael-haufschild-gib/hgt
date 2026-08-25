# Xi Noether–concentration quantization

- **ID:** RH-NCQ
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** corpus synthesis: Route R completion core + prime–Archimedean conjugate-pair concentration
- **Statement:** For every off-line Xi divisor copy and every relative probe scale `0 < λ < 1`, absolute source Noether charge times conjugate-pair quadratic concentration energy equals `multiplicity · π λ² / (2(1-λ²))`, independent of zero height and horizontal displacement.

## Goal

Falsify or prove that source completion charge and analytic concentration are quantitatively the same defect, not merely RH-equivalent predicates.

## Gates

- [x] 0 → 1 in-progress: exact unconditional statement; source fixed before divisor specialization; direct formula attack
- [x] 1 → 2 fully-proven: dependency-closed paper proof
- [x] 2 → 3 formalized: exact Lean theorem, targeted build, axiom audit
- [ ] 3 → 4 publication-ready: not claimed; parent analytic identity is elementary

## Audit and hostile verdict

- `[CORPUS]` `abs_routeRPrimeGammaXiNoetherOrientationCharge_eq` gives `|Qρ| = (mρ/2)bρ`.
- `[CORPUS]` `integral_sq_lineConjugateCauchyConcentrationProfile` gives `E(b,y) = πy²/(b(b²-y²))`.
- `[CORPUS]` searches found no theorem combining these invariants.
- `[LITERATURE]` Poisson kernels and spectral/operator RH frameworks exist; targeted current search found no source-Noether/concentration calibration for Xi zeros.
- `[BRIDGE]` Verdict: analytically routine after both corpus constructions, but non-vacuous quantitative cross-route law; no RH or novelty claim.

## Paper proof

Let `bρ` be completion-core radius and `mρ` divisor multiplicity. Off-linearity gives `bρ > 0`. Put `y = λbρ`; then `0 < y < bρ`. Exact concentration law yields
`E(bρ,λbρ) = πλ²/(bρ(1-λ²))`. Exact Noether calibration gives
`|Qρ| = (mρ/2)bρ`. Multiplication and cancellation of `bρ ≠ 0` give
`|Qρ|E(bρ,λbρ) = mρπλ²/(2(1-λ²))`. No other hypothesis is used.

## Log

- 2026-08-25 — `[LEAN-PROVED]` as `abs_routeRPrimeGammaXiNoetherOrientationCharge_mul_concentrationEnergy_eq`; direct compile and targeted build pass; axioms `[propext, Classical.choice, Quot.sound]`. Static lint reports only unrelated pre-existing umbrella reachability failures.
