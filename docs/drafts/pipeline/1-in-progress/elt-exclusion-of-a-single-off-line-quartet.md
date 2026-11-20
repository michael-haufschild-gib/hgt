# Exclusion of a single off-line quartet of the Riemann zeta function

- **ID:** elt-exclusion-of-a-single-off-line-quartet
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** docs/reports/review-2011/obstacles-summary.md §2.4 (Problem O8)
- **Statement:** For every $\rho_0 \in \mathbb{C}$, the Riemann zeta function does not satisfy `HasSingleOffLineQuartet ρ₀`: $\zeta(s)$ cannot have $\{ \rho \in Z(\zeta) : \operatorname{Re}\rho \neq 1/2 \} = \{\rho_0, \bar{\rho}_0, 1-\rho_0, 1-\bar{\rho}_0\}$ with $\operatorname{Re}\rho_0 > 1/2$.

## Goal
Resolve §2.4 unconditionally (`∀ ρ₀ : ℂ, ¬ HasSingleOffLineQuartet ρ₀`) and formalize its equivalence-discharged corollaries:
1. `ThreeProbeAmplificationLaw` and the $m=4$ Gershgorin probe upgrade (`ThePrimeDisplacementIndexAmplificationPayoff.lean`).
2. `TwoIntervalRadialExclusionLaw` (`TheOrdinaryPrimeRadiusDetectsExactlyOneOffLineQuartet.lean`).
3. Equivalence of the $(2,3,6)$ ordinary-prime dilation recurrence bounds with `RiemannHypothesis` (`MixingTwoPrimeDilationsRemovesQuartetAliasing.lean` / `ThePrimeDisplacementIndexAmplificationPayoff.lean`).
4. Exclusion of the two-wave proper-power discrepancy regime (`TwoProperPowerWavesCharacterizeASingleQuartet.lean`).
5. Collapse of `riemannHypothesis_or_quartet_or_double_neutral_prime_excursions` to `RiemannHypothesis` or double-neutral opposite exponential prime excursions (`OppositeExcursionsOfTheThirdConfinedPrimeWave.lean`).
6. Collapse of the off-line count dichotomy to `RiemannHypothesis ∨ 4 ≤ (rightZeros zetaZeroConfig).encard`.

## Gates
- [x] 0 → 1  in-progress: well-posed, twin firewall audited (`EulerSymmetric` quartet models, `coshModel` FE models, prime-2 Schur twins, $\{0,1\}$-coprime step imitators).
- [ ] 1 → 2  fully-proven: complete dependency-closed paper proof with zero open core.
- [ ] 2 → 3  formalized: unconditional Lean theorems in `formal/GaloisForLFunctions/ExceptionalLayerTheory/`, `#print axioms` clean, wired into `ExceptionalLayerTheory.lean`.

## Twin calibration constraints
Any valid refutation of `HasSingleOffLineQuartet ρ₀` must simultaneously use what separates $\zeta$ from all four twin families:
1. Unit Dirichlet coefficients $a_n \equiv 1$ on $\mathbb{N}_{\ge 1}$ (fails on `EulerSymmetric` and prime-2 Schur twins).
2. Euler product over primes (fails on `coshModel` and Hurwitz/Epstein combinations).
3. Functional equation with $\Gamma_{\mathbb{R}}(s) = \pi^{-s/2}\Gamma(s/2)$ and global polynomial vertical growth / Lindelöf on $\operatorname{Re}s = 1/2$ (fails on `EulerSymmetric` and `{0,1}` step imitators).
4. Finiteness/uniqueness of the off-line quartet $\{ \rho_0, \bar{\rho}_0, 1-\rho_0, 1-\bar{\rho}_0 \}$ with $|\operatorname{Im}\rho_0| > 67 > 0$ and quotient $\Xi_\flat \in \mathcal{LP}$.
