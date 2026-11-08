# Positive annihilator division forces coefficient oscillation

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Obstacles:** B13, B112.
- **Object:** For a nonnegative two-prime polynomial `P(X,Y)` with constant coefficient one, define the canonical formal coefficients `b_(a,b)` by
  `Σ b_(a,b) X^a Y^b = 1/((1−X)(1−Y)P(X,Y))`.
  These are the two-prime lattice coefficients of the formal quotient `ζ/P`.
- **Statement sought:** If `P(2^(−ρ),3^(−ρ))=0`, `β=Re ρ>0`, then for every `0≤α<β` and `C>0` there are lattice indices with
  `b_(a,b)>C exp(α(a log 2+b log 3))`, and indices with
  `b_(a,b)<−C exp(α(a log 2+b log 3))`.
  In particular, infinitely many negative coefficients are unavoidable; neither sign admits a smaller exponential envelope.
- **Mechanism:** Positive convolution with `P` equals the constant coefficient array one. A lower envelope `b_d≥−C exp(αL_d)` forces an upper envelope via the recurrence, and an upper envelope forces a lower one. Either one-sided envelope therefore gives absolute convergence in `Re s>α` on the sparse two-prime semigroup. Evaluating the convolution identity there would make `P` zero-free, contradicting the prescribed zero.
- **Positive survivor:** Quantitative two-sided coefficient growth at every exponent below a right-hand zero, beyond merely excluding a nonnegative quotient.
- **Novelty:** Corpus searches found annihilator existence, mass costs, positivity firewalls and reciprocal-coefficient excursion laws. `StableDirichletPolynomialPutnam` excludes containment of stable critical zero sets using Herglotz rigidity; `ZetaZerosLeeYangPutnam` excludes Lee–Yang divisibility using Hamburger rigidity. Neither supplies the two-sided coefficient-growth theorem for arbitrary positive annihilators.

## Paper proof

Map `P` to real coefficients and form its inverse in the two-variable formal power-series ring; constant coefficient one makes this inverse valid. Multiply by the series whose every coefficient is one. The resulting canonical series `B` satisfies `P B = Σ_d X^d`, hence
`b_d + Σ_{0≠e≤d} c_e b_(d−e) = 1`.

Put `W_d=exp(αL_d)≥1` and `A=Σ_e c_e`. Nonnegative frequencies give `W_(d−e)≤W_d`. If `b_d≥−C W_d` everywhere, the recurrence gives `b_d≤(1+CA)W_d`; if `b_d≤C W_d` everywhere, it gives `b_d≥−CA W_d`. Thus either one-sided envelope implies `|b_d|≤K W_d` for some finite `K`.

At a zero `ρ` with `Re ρ>α`, the weighted terms are bounded by `K exp(−(Re ρ−α)L_d)`, a product of two summable geometric sequences. Absolute convergence permits multiplying by the finite polynomial and regrouping by additive antidiagonals. Consequently
`P(ρ) Σ_d b_d exp(−ρL_d) = 1/((1−2^(−ρ))(1−3^(−ρ)))`.
The left side vanishes; the right side is nonzero because `Re ρ>0`. Both one-sided envelopes are impossible. Replacing `C` by a bound for any prescribed finite set forces excursions outside that set, so both signs occur infinitely often.

The same evaluation argument gives an endpoint refinement: `Σ_d |b_d| exp(−(Re ρ)L_d)` diverges. If this sum converged, the convolution identity would remain evaluable at `ρ` itself. This is part of the same contribution, not a separate result count.

Lean formalization pending; uncounted.
