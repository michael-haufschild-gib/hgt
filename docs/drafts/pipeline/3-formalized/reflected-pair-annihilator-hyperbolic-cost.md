# Sharp mass cost of a reflected pair

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Obstacles:** B13, B112; positive annihilation of a reflected pair.
- **Statement:** For a normalized positive two-prime Dirichlet polynomial supported at nonconstant logarithmic frequencies in `[a,B]`, `0<a<B`, simultaneous zeros at `σ±δ+iγ`, `δ>0`, force the central tail mass to satisfy
  `H(σ) ≥ sinh(δ(B+a)/2)/sinh(δ(B-a)/2)`.
- **Sharpness:** Positive trinomials supported at frequencies `a` and `B`, with opposite phases, attain the bound when `a=log 2` and `B` is a positive even multiple of `a`.
- **Mechanism:** Combine the two zero identities using `sinh(δ((B+a)/2-L))`. Its absolute value is at most `sinh(δ(B-a)/2)` on the support.
- **Boundary limits:** As `δ→0`, the cost approaches `(B+a)/(B-a)`; as `B→∞`, it approaches `exp(δa)`. Both limits are formalized.
- **Corpus audit:** Existing `TheUnitMassBoundaryOfPositiveAnnihilators` handles coalesced double zeros. `TheWeightedSpectrumOfAReflectedPair` concerns a different `L²` quadratic form, not annihilator mass. No paired annihilator bound found.
- **Extremizer:** With `u=δa`, `v=δB`, use coefficients `A=sinh(v)/sinh(v-u)` and `C=sinh(u)/sinh(v-u)` in `1+A X+C X^(B/a)`, where `X=2^(σ-s)` and `B/a` is even. Both coefficients are positive; the two zeros share height `π/log 2`.
- **Exact excess:** The bound equals `exp(δa)+2sinh(δa)/(exp(δ(B-a))-1)`. For `a=log 2`, every pair has `H>exp(δa)`, but for each `ε>0` an explicit positive polynomial has `H<exp(δa)+ε`.

## Proof

Write `v_j=c_j exp(-L_j(σ+iγ))`. The two zeros give `Σ exp(∓δL_j)v_j=-1`. For `c=(B+a)/2`, their weighted difference gives
`Σ sinh(δ(c-L_j))v_j=-sinh(δc)`.
The test's modulus on `[a,B]` is bounded by `sinh(δ(B-a)/2)`. Triangle inequality proves the bound.

For the extremizer, `X=-exp(∓u)` at the two prescribed points and its even power is `exp(∓v)`. Both zero equations follow from
`sinh(v)exp(±u)-sinh(u)exp(±v)=sinh(v-u)`.
Its central mass is `(sinh v+sinh u)/sinh(v-u)`, equal to the bound by the addition formulas.

The exact excess is positive. To make it smaller than `ε`, choose the even bandwidth large enough and use `exp(t)-1≥t`. Thus the strict floor is the infimum, not a minimum.

## Lean and audit

Module: `ArithmeticPositiveDuality/TheHyperbolicCostOfReflectedZeroPairs.lean`.

- `reflected_pair_hyperbolic_moment`, `reflected_pair_forces_hyperbolic_mass`: exact moment and universal bound.
- `reflectedPairAnnihilator_zeros`, `reflectedPairAnnihilator_mass`, `exists_sharp_reflected_pair_annihilator`: explicit positive extremizers at every even prime-two bandwidth.
- `reflected_pair_mass_gt_single_root_floor`, `exists_reflected_pair_mass_near_single_root_floor`: strict floor and arbitrarily small excess.
- `tendsto_reflected_pair_cost_at_zero`, `tendsto_reflected_pair_cost_atTop`: the two boundary limits.

Direct `lake --old env lean GaloisForLFunctions/ArithmeticPositiveDuality/TheHyperbolicCostOfReflectedZeroPairs.lean` passed without warnings. All nine audited declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`. Umbrella import added.

## Gain and limit

Reflection has an exact finite-bandwidth penalty, but forces no uniform positive excess above the one-root floor. The positive survivor is the sharp bandwidth law with explicit extremizers and an unattained infimum. This extends the coalesced double-zero boundary to distinct reflected zeros.

The infimum ranges over heights; the marked ordinate is not asserted to be a zeta ordinate. The cost at an arbitrary fixed height remains a separate problem. No independent arithmetic upper bound is supplied; B13 and B112 remain open. Counted as one contribution, including its extremizers and limit laws.
