# Unconditional Decision of the Asymptotic Abscissa Law

- **ID:** aal-horocycle-functional-equation-decision
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** docs/reports/review-0711/aal.md
- **Statement:** `RHTower.AsymptoticAbscissaLaw` ($\Theta_\infty = \Theta$) holds unconditionally for the Riemann zeta function $\zeta(s)$.

## Goal
Establish a dependency-closed unconditional proof of `RHTower.AsymptoticAbscissaLaw` and formalize both the decision and its unconditional collapse corollaries (`riemannHypothesis_tfae_of_asymptoticAbscissaLaw`, `zetaAsymptoticAbscissa = zetaZeroAbscissa`, `¬ PrimeErrorIsFiniteOscillation`, `oddBoundStateSpace` dichotomy, global abscissa/rate collapses) in Lean 4.

## Gates
- [x] 0 → 1  in-progress: internal corpus frontier, 5-way countermodel discriminator filter, and external SOTA audited
- [ ] 1 → 2  fully-proven: quantifier-exact, dependency-closed paper proof with zero `[OPEN CORE]`
- [ ] 2 → 3  formalized: unconditional Lean 4 theorem and corollaries checked with `lake --old env lean`, `#print axioms` clean, wired into umbrellas

## Approach
Eliminate a hypothetical finite separated top layer $F_+ = \{\rho : \xi(\rho) = 0,\ \operatorname{Re}\rho > \theta\}$ ($\frac{1}{2} \le \theta < \Theta = \beta_*$) by combining:
1. Exact unit-coefficient integer structure $a(n) \equiv 1$ ($N(x) = \lfloor x \rfloor$) and the Riemann functional equation $\xi(s) = \xi(1 - s)$ (via modular/horocycle geometry on $SL_2(\mathbb{Z})\backslash\mathbb{H}$ or coupled additive-multiplicative representations), simultaneously failing on `AnIntegerNormBeurlingOneOff`, `RationalPrimeOneOff`, `ABoundedCountWithANewZero`, and `SymmetricRationalZeroRelocation`.
2. High-height zero-free strip $\operatorname{Re} s > \theta$, $|t| \ge T_0$ and sub-polynomial vertical growth of $1/\zeta(s)$ on $\operatorname{Re} s \ge \theta + \delta$.

## Log
- 2026-11-08 — created in 1-in-progress
