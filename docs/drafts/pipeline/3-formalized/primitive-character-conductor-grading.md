# Primitive character windows are graded by conductor

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Wall:** Σ1j, different primitive moduli

For primitive characters `ψ₁,ψ₂` of distinct positive moduli `q₁,q₂`,
every common period `M`, complex coefficients `c₁,c₂`, and frequency `k`,

`crossPower (Re(c₁ψ₁)) (Re(c₂ψ₂)) M k = 0`.

For `q₁,q₂>1` and a common spatial profile, the complete tilted-spline
Weil cross term tends to zero at second order on every positive canonical
critical curve. The capstone supplies the literal spline's regular tail,
Fourier decay, and critical schedule; no analytic source input remains
as a premise. The spatial profile is any `C²` function supported in
`[−A,0]`, with `A≥0`.

## Proof

Lifting a `q`-periodic twist to period `M=dq` gives coefficient zero
unless `d|k`; at `k=dj` it gives `d` times the period-`q` coefficient.
Partition a full period into `d` blocks and sum the resulting geometric
progression to obtain this identity exactly.

The primitive Gauss-sum formula makes the period-`q` coefficient vanish
unless `gcd(j,q)=1`. Every nonzero lifted coefficient therefore satisfies
`M/gcd(M,k)=q`. A frequency cannot have two distinct reduced denominators,
so the two coefficients have zero product at every frequency. The exact
critical-curve polarization formula then has a zero spectral sum.

Namespace `GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations`:

- `twistCoeff_mul_period`
- `coprime_of_twistCoeff_charTwist_ne_zero`
- `reduced_denominator_of_charTwist_ne_zero`
- `crossPower_charTwist_distinct_conductors`
- `cross_layer_charTwist_distinct_conductors`
- `cross_layer_charTwist_distinct_conductors_tilted`

Module: `ArithmeticHodgeTheoryOfDegenerations/PrimitiveCharacterConductorGrading.lean`.
Axiom audit uses only `propext`, `Classical.choice`, and `Quot.sound`.

Together with the same-modulus parity theorem, this gives conductor and
parity grading. Moving frequencies remain open.
