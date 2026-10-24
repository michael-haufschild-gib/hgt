# Sharp even nonnegative heat-root barrier

- **ID:** sharp-even-heat-root-barrier
- **Stage:** 0-backlog
- **Type:** CONJECTURE (symbolic mechanism; dependency audit pending)
- **Source:** Arithmetic Local Divisor Geometry; universal finite-degree root obstruction
- **Statement:** The sharp positive-root barrier for an even nonnegative polynomial of degree `2d` whose forward heat has nonnegative coefficients is the largest zero of the probabilists' Hermite polynomial `He_(2d−1)`, in Gaussian units. Equality should force a shifted `He_(2d)` extremizer.

## Existing input and scope

`RHTower/XiWardGlobalCapAndFiniteHeadArithmetic` proves heat inversion and the universal obstruction `4λ deg P≤δ²`, using positivity of the inverse-heat Hermite weights. Do not repackage that theorem. The proposed refinement uses the additional double-root condition forced by real-axis nonnegativity, identifies the exact finite-degree boundary, and classifies equality. It does not produce arithmetic positivity for the actual Xi head.

## Proposed precise result

Let `d≥2`, `λ>0`, and let `h_d` be the largest real zero of `He_(2d−1)`. If `P` is a nonzero even real polynomial of degree `2d`, `P(x)≥0` for all real `x`, and every coefficient of `E_(λ/2)P` is nonnegative, then every positive root `δ` of `P` obeys

`δ≤sqrt(λ) h_d`.

At equality, conjecturally

`P(X)=c λ^d [He_(2d)(X/sqrt(λ))−He_(2d)(h_d)]`, `c>0`.

This polynomial should attain the boundary: its heat is `c[X^(2d)−λ^d He_(2d)(h_d)]`, with two nonnegative coefficients.

## Proof mechanism to audit

1. Evenness survives heat and its inverse, and the leading coefficient survives. Write `Q=E_(λ/2)P` in even monomials with nonnegative coefficients.
2. A real zero of a globally nonnegative polynomial is a stationary point. Its inverse-heat derivative is a nonnegative combination of odd Hermite polynomials. Beyond `h_d`, every summand is positive by strict interlacing of Hermite roots, contradicting `P'(δ)=0`.
3. At `h_d`, all lower odd Hermite polynomials remain positive, while the highest one vanishes. Thus every nonconstant coefficient of `Q` below degree `2d` must vanish. The root equation fixes the constant coefficient.
4. To certify the proposed extremizer globally, use the Hermite ODE. For `H=He_n`, the Sonin quantity `H²+(H')²/n` has derivative `2x(H')²/n`, hence critical-value magnitudes increase along the positive axis. Interlacing makes the outermost critical point of `He_(2d)` its most negative minimum. Evenness gives the same minimum on the negative axis.
5. Audit the exact root asymptotic before any asymptotic optimality claim. If `h_d²/(2d)→4`, then the existing universal constant `4` is asymptotically sharp even in this nonnegative even class; the finite-degree improvement and equality rigidity are the positive survivor.

## Gates

- [ ] Corpus and primary-literature novelty audit.
- [ ] Verify interlacing, ODE, global-minimum and equality arguments without extra premises.
- [ ] Dependency-closed paper proof, including normalization and `d=2` boundary case.
- [ ] Lean formalization in the programme folder and transitive axiom audit.

No numerical experiments or source-sign hypotheses are allowed. Do not promote the conjecture on the strength of a plausible Hermite picture.
