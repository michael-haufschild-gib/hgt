# Multiplicity costs Chebyshev mass at bounded frequency

- **Stage:** 3-formalized
- **Obstacles:** B13; positive annihilation of finite exceptional layers.
- **Statement:** If a normalized positive two-prime Dirichlet polynomial has a zero of order at least `r+1` and all nonconstant logarithmic frequencies lie in `[a,B]`, where `a=log 2<B`, its tail mass `H` at that zero satisfies
  `H ≥ |T_r((B+a)/(B-a))|` and `(B-a)(H-1) ≥ 2ar²`.
- **Intrinsic form:** For `r≥1`, `H>1` and an actual supported monomial has logarithmic frequency at least `a+2ar²/(H-1)`; no bandwidth premise is required.
- **New content sought:** Replace the existing double-zero span bound by an all-multiplicity law. Arbitrary multiplicity near unit mass remains possible only with growing frequency span; no multiplicity bound for ζ is assumed.
- **Corpus baseline:** `TheUnitMassBoundaryOfPositiveAnnihilators.double_zero_forces_frequency_span_cost`; `ArbitraryMultiplicityNearUnitAnnihilatorMass.exists_arbitrary_multiplicity_near_unit_mass`. Searches found no all-multiplicity span bound.

## Argument

Write the tail at the zero as `Σ v_j=-1`. Vanishing derivatives give `Σ L_j^k v_j=0` for `1≤k≤r`. Consequently every degree-`r` polynomial `q` satisfies `Σ q(L_j)v_j=-q(0)`. Choose `q(L)=T_r((B+a-2L)/(B-a))`; its absolute value on the frequency interval is at most one. The triangle inequality gives the claimed cost.

For `x≥1`, the recurrence `T_(n+2)=2xT_(n+1)-T_n` gives
`T_(n+1)-T_n≥(2n+1)(x-1)` and `T_n≥1+n²(x-1)` simultaneously by induction.
Substitution yields the quadratic bound. At a multiple zero, the existing strict unit-mass boundary gives `H>1`; apply the bound at the largest supported frequency to obtain the intrinsic form.

## Lean and audit

Module: `ArithmeticPositiveDuality/TheChebyshevCostOfAnnihilatorMultiplicity.lean`.

- `polynomial_frequency_moment_eq_zero`: polynomial moment cancellation from analytic multiplicity.
- `multiplicity_forces_chebyshev_mass`: the all-multiplicity Chebyshev bound.
- `multiplicity_forces_quadratic_frequency_cost`: `(B-a)(H-1)≥2ar²`.
- `multiplicity_forces_large_frequency`: an actual supported frequency exceeds `a+2ar²/(H-1)`.

Direct `lake --old env lean GaloisForLFunctions/ArithmeticPositiveDuality/TheChebyshevCostOfAnnihilatorMultiplicity.lean` passed without warnings. All four declarations have only `propext`, `Classical.choice`, and `Quot.sound` as transitive axioms. Imported by `ArithmeticPositiveDuality.lean`.

## Gain and limit

The previous exact span cost covered only double zeros. The new law controls every multiplicity, with a quadratic necessary frequency scale near unit mass. These are universal inequalities for positive annihilators; no unproved arithmetic input is assumed. They do not bound ζ multiplicities or exclude a finite exceptional layer. Sharpness beyond double zeros remains a separate question. Counted as one contribution, including all its corollaries.
