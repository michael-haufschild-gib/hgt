# Polynomial return bounds from the proved logarithmic-form estimate

- **ID:** SPL-polynomial-return-profile-rate
- **Stage:** 0-backlog
- **Type:** CANDIDATE THEOREM
- **Corpus input:** `RHTower/Matveev/EffectiveBaker.lean`,
  `GaloisForLFunctions.RHTower.Matveev.effectiveBakerBound_holds`.

For `α=log 3/log 4`, seek constants `A>0` and integer `D≥1` such that
all precision parameters `Q≥2` admit a discrete half-turn within `1/Q`
by index `A Q^D`. The existing elementary bound is exponential in `Q`.
A matching polynomial exclusion, with a possibly different exponent,
should follow from the same logarithmic-form bound.

The corpus theorem gives `|u log 2+v log 3|≥c(2+|u|+|v|)^{-C}` for
nonzero integer coefficients. Restricting to a Dirichlet return
`|qα−m|<1/Q`, `q≤Q`, bounds its winding by `0≤m≤q` and its nonzero
step below by a fixed inverse power of `Q`. Multiplying that step to a
half-turn gives a polynomial index bound. The odd coefficient `2ℓ+1`
likewise supplies a polynomial lower separation for half-turns.

Combined with the proved profile modulus and finite pairing inequality,
this should replace the iterated-logarithmic average rate by a positive
power rate, with constants depending only on the fixed scales two and
three. The elementary explicit-constant estimates remain distinct results.

The source statement and proof were inspected. Its olean exists; do not
rebuild it. A fresh transitive axiom audit and Lean specializations remain
required. No many-prime uniform exponent or pointwise count bound is claimed.
