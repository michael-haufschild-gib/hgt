# Exclusion of a single off-line quartet of the Riemann zeta function

- **ID:** elt-exclusion-of-a-single-off-line-quartet
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** docs/reports/review-2011/obstacles-summary.md §2.4 (Problem O8)
- **Statement:** For every $\rho_0 \in \mathbb{C}$, the Riemann zeta function does not satisfy `HasSingleOffLineQuartet ρ₀`: $\zeta(s)$ cannot have $\{\rho \in Z(\zeta) : \operatorname{Re}\rho \neq 1/2\} = \{\rho_0, \bar{\rho}_0, 1-\rho_0, 1-\bar{\rho}_0\}$ with $\operatorname{Re}\rho_0 > 1/2$.

## Goal
Resolve §2.4 unconditionally (`∀ ρ₀ : ℂ, ¬ HasSingleOffLineQuartet ρ₀`) and formalize its equivalence-discharged corollaries:
1. `ThreeProbeAmplificationLaw` and the $m=4$ Gershgorin probe upgrade (`ThePrimeDisplacementIndexAmplificationPayoff.lean`).
2. `TwoIntervalRadialExclusionLaw` (`TheOrdinaryPrimeRadiusDetectsExactlyOneOffLineQuartet.lean`).
3. Equivalence of the $(2,3,6)$ ordinary-prime dilation recurrence bounds with `RiemannHypothesis` (`MixingTwoPrimeDilationsRemovesQuartetAliasing.lean` / `ThePrimeDisplacementIndexAmplificationPayoff.lean`).
4. Exclusion of the two-wave proper-power discrepancy regime (`TwoProperPowerWavesCharacterizeASingleQuartet.lean`).
5. Collapse of `riemannHypothesis_or_quartet_or_double_neutral_prime_excursions` to `RiemannHypothesis` or double-neutral opposite exponential prime excursions (`OppositeExcursionsOfTheThirdConfinedPrimeWave.lean`).
6. Collapse of the off-line count dichotomy to `RiemannHypothesis ∨ 4 ≤ (rightZeros zetaZeroConfig).encard`.

## Gates
- [x] 0 → 1  in-progress: well-posed; countermodel firewall established.
- [ ] 1 → 2  fully-proven: complete dependency-closed paper proof with zero open core.
- [ ] 2 → 3  formalized: unconditional Lean theorems in `formal/GaloisForLFunctions/ExceptionalLayerTheory/`, `#print axioms` clean, wired into `ExceptionalLayerTheory.lean`.

## Countermodel boundaries (necessary ingredients)
Any valid proof of `∀ ρ₀ : ℂ, ¬ HasSingleOffLineQuartet ρ₀` must fail on all models realizing a lone quartet:
1. **Completed functional-equation & heat models (`coshModel`, pre-last-collision heat states $H_{\Lambda-\varepsilon}$):** satisfy $\xi_{\mathrm{model}}(1-s)=\xi_{\mathrm{model}}(s)$, Fourier kernel $\tilde{\Phi}(u) > 0$, full Lindelöf, quotient $\Xi_\flat \in \mathcal{LP}$, and a lone off-line quartet, lacking only discrete unit Dirichlet coefficients $a_n \equiv 1$ and an Euler product.
2. **Two-sided rational-prime edits (`ANonRealPairAloneOnTopOfATwoSidedEdit`, random $\{0,1,2\}$-prime edits):** under RH for $\zeta$, realize Euler products $\prod_p (1-p^{-s})^{-w(p)}$ ($w(p) \in \{0,1,2\}$) with unique right zeros $\{\rho_0, \bar{\rho}_0\}$, $|\theta_{\mathrm{edit}}(x) - x + 2\operatorname{Re}(x^{\rho_0}/\rho_0)| \le C\sqrt{x}\log^2 x$, and pointwise Lindelöf on $\operatorname{Re}s > 1/2$, lacking only $a_n \equiv 1$ ($w(p) \equiv 1$) and continuation across $\operatorname{Re}s = 1/2$.
3. **Schur local-gate twins and finite-field fake rational zeta functions:** preserve the functional equation and positive Euler-logarithm structure, lacking either $a_n \equiv 1$ together with non-periodicity of off-line zeros in $\mathbb{C}$ (`Prime-p Schur`) or an underlying additive ring with $\Gamma_{\mathbb{R}}$ completion (`Z_fake(T)`).

## Open mathematical gap (`[OPEN CORE]`)
Construct an unconditional arithmetic producer valid for every $\beta_0 = \operatorname{Re}\rho_0 \in (1/2, 20999/24000]$ and $|\operatorname{Im}\rho_0| > 67$ that couples unit integer counting $a_n \equiv 1$ ($\sum_{d \mid n} \Lambda(d) = \log n$), the rational-prime Euler product $w(p) \equiv 1$, and the $\Gamma_{\mathbb{R}}$ functional equation to contradict $\psi(x) - x = -2m\operatorname{Re}(x^{\rho_0}/\rho_0) + O(\sqrt{x}\log^2 x)$ (equivalently, construct three signed prime-supported negative probes of `atomGram` with `distinctProbeEnergy < 3/2` from one negative two-prime difference witness).
- Linear and bilinear meromorphic, sieve, and spectral identities hold identically at $\zeta(\rho_0) = 0$.
- Vertical $T \to \infty$ mean-value and universality methods have zero density sensitivity to $O(1)$ off-line zeros, while Kronecker alignment of $\pi(X)$ primes forces $\log\tau \asymp X$ where conditional $|\log\zeta(\sigma+i\tau)| \ll (\log\tau)^{2-2\sigma}/\log\log\tau$ absorbs $X^{\beta_0-\sigma}$.
- Existing unconditional strip producers (`MetaplecticMobiusDescent`: $\Theta \le 20999/24000$; factorwise Gauss barrier $\ge 3/5$) have fixed exponent floors strictly above $1/2$ and cannot exclude $\beta_0 \in (1/2, 3/5]$.
