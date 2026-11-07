# Metaplectic conversion of Möbius coefficients

- **ID:** metaplectic-mobius-descent
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Statement:** Sextic Poisson transformation converts ideal Möbius coefficients over the Eisenstein integers into cubic theta coefficients; a second transformation may close a contracting mean-square descent.

## Target

Prove an unconditional source estimate beyond absolute convergence. The candidate external estimate is
`Σ_{0<N(u)≤D^(1+θ)} |Σ_n μ_K(n)(u/n)_6 W(N(n)/D)|² ≪ D^(2+θ+ε)`
for every fixed `θ, ε > 0` and smooth compactly supported `W`. Sixth-power rows then give the `11/12` exponent. This is an external claim, not a theorem established in this corpus.

## Arithmetic mechanism to audit

1. Normalized cubic Gauss sums satisfy `γ₂(n)³ = μ_K(n) α(n)` on squarefree primary elements.
2. Hasse–Davenport converts `μ_K(n) γ₋₁(n)` to cubic theta coefficients, up to a fixed ray-class factor.
3. Theta completion adds cube indices. Möbius inversion removes them.
4. Two Poisson transformations, with a positive enlargement between them, produce a smaller row range. Regrouping divisor terms before absolute values forces `f′ | k′`.
5. Required transfer bounds must control transformed weights uniformly; scale contraction alone proves no estimate.

## Status and sources

No dependency-closed paper proof or local Lean theorem yet. Corpus searches for the sextic/cubic mechanism found no matching source estimate. External endpoints and their transitive analytic dependencies require audit before reuse.

- [OpenAI, The Quasi-Riemann Hypothesis, §§4–7 and Appendix A](https://github.com/openai/math/blob/main/preprints/The-Quasi-Riemann-Hypothesis-October-5-2026/paper2.pdf).
- [Kontorovich development](https://github.com/AlexKontorovich/quasi-rh): `ElevenTwelfths.Unconditional.riemannZeta_ne_zero_of_re_gt_elevenTwelfths` is an advertised unconditional endpoint; not locally checked.
- [Rubinstein's guide](https://www.math.uwaterloo.ca/~mrubinst/quasi_rh_notes/zeta_11_12_guide.pdf), §8, explicitly separates transfer estimates from the final induction.
