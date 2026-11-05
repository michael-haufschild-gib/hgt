# All-rank first-atom center tails

- **Stage:** 2-fully-proven
- **Type:** THEOREM ON PAPER; Lean incomplete
- **Wall:** Σ6
- **Statement:** For every finite `N` and `r≥0`, the matrix with entries
  `∫_(s>r) Re((-i)^(j+k)) ∂ₜ^(j+k)[φ(s/2+t)φ(s/2−t)]|ₜ₌₀ ds`,
  where `φ(x)=thetaCuspSourceTerm x 1`, is positive definite.

## All-frequency square mechanism

Write `K(u)=K_(iτ)(2u)`, `J_p(q)=∫_q^∞ u^p K(u)du`, and
`L(x)=x|K_(1/2+iτ/2)(x)|²`. The order recurrence and conjugation give
`z' = −(1/2+iτ/2)z/x − conjugate(z)`, hence

`L' = −2x Re(z²)`, `L'+2L = 4x(Im z)² ≥ 0`, `|L'| ≤ 2L`.

Moreover `L(x)>0` for `x>0`: the corpus theorem
`HTGeometry.re_eq_zero_of_modifiedBesselKOrder_eq_zero` excludes zeros
at nonzero real order.

The determinant-two substitution in the product of the two whole-line
Schläfli integrals gives

`K_α(x)K_β(x) = ∫_ℝ exp((α+β)t) K_(α−β)(2x cosh t)dt`.

Set `α=1/2+iτ/2`, `β=conjugate(α)`. Evenness replaces `exp t` by
`cosh t`; then `w=x sinh t` gives

`L(x)=∫_ℝ K_(iτ)(2√(x²+w²))dw`.

Integrating at `x=√(q²+v²)` and using plane polar coordinates yields

`J_1(q)=(1/π)∫_0^∞ L(√(q²+v²))dv > 0`.

For `u≥q>0`, the radius increase
`√(u²+v²)−√(q²+v²)` lies in `[0,u−q]`. The square reserve therefore
gives `J_1(u)≥exp(−2(u−q))J_1(q)` directly under the integral.
Differentiating this inequality at `u=q` gives `J_1'+2J_1≥0`.
For `p≥1`, integration by parts gives

`J_p(q)=q^(p−1)J_1(q)+(p−1)∫_q^∞u^(p−2)J_1(u)du >0`,

`J_p'(q)=q^(p−1)J_1'(q)`, so `J_p'+2J_p≥0`. Consequently
`J_p(u)≥exp(−2(u−q))J_p(q)` for `u≥q`, and

`J_(p+2)(q)=q²J_p(q)+2∫_q^∞uJ_p(u)du`
`≥(q²+q+1/2)J_p(q)`.

## Literal first-atom tail

For `q=πexp r`, put `H_r(t)=∫_r^∞φ(s/2+t)φ(s/2−t)ds`.
The source normalization gives

`H_r(t)=4/√π ∫_q^∞u^(3/2)(4u²+9−12u cosh(2t))exp(−2u cosh(2t))du`.

With Fourier convention `Hhat(ξ)=∫ H(t)exp(iξt)dt`,
`Hhat_r(2τ)=4F(q,τ)/√π`, where

`F=4J_(7/2)−6J_(3/2)−6q^(5/2)K(q)`
` =4J_(7/2)−6J_(3/2)+6qJ_(3/2)'`
` ≥4(q²−2q−1)J_(3/2)>0` for `q>1+√2`.

Physical `r≥0` has `q≥π>3`, so this covers every center and frequency.
Fourier inversion identifies each signed derivative with the corresponding
moment of this strictly positive density. The finite quadratic form is
an integral of a nonzero polynomial squared against that density, hence
strictly positive at every finite rank.

All exchanges in the paper argument have absolute majorants: for fixed
order, `|K_ν(x)|≤C_ν exp(−x)` on `x≥1`; the determinant-two product
inherits integrability from the two Schläfli factors. The polar integrand
is bounded by a radial exponential. The square-tail comparison uses
pointwise order and needs no differentiation under that integral.
Derivatives of `H_r` have polynomial
hyperbolic factors against `exp(−2q cosh(2t))`, so `H_r` is Schwartz;
its Fourier transform has every polynomial moment. The same majorants
justify differentiation of the literal center integral.

**Lean remaining:** square derivative; product and radial identities;
weighted-tail comparison; literal Fourier/moment bridge and strict matrix
positivity. No all-rank Lean theorem is claimed yet.

The complete theta sum additionally needs unequal atom pairs and its
infinite remainder controlled uniformly in rank. This first-atom theorem
does not close that separate assertion.
