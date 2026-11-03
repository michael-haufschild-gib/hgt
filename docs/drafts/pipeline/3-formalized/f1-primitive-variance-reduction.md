# Primitive variance retains the first odd moment

- **ID:** F1-PVR
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [Joint first-fold payment](../1-in-progress/f1-joint-cubic-prime-payment.md)
- **Statement:** Primitive mass and the sinh pole leave one explicit first-moment charge
  in a lower bound for the complete odd unit-window Weil form.

For a real odd C² function `F` supported in `[-1/2,1/2]`, put
`E=∫F²`, `m=∫xF`, `H(x)=∫_{−1}ˣF`, `C(t)=∫F(x)F(x+t)dx`,
`L=∫₀¹(E−C(t))/t dt` and `w=log2/√2`. Then

`∫H²−m²≤E/(4π²)`,

`Q(F)≥L−(γ+logπ+log2+1/192+1/(96π²)+97/483840)E
 −(39/64)m²−2wC(log2)`.

## Proof

Oddness gives `∫F=0`. Thus `H` vanishes at and beyond both unit endpoints and
`H'=F`. Integration by parts gives `∫H=−m`. Periodic Wirtinger on this unit
interval therefore gives `∫H²−m²≤E/(4π²)`.

On `|x|≤1/2`, the proved sinh remainder bound is
`(2sinh(x/2)−x)²≤x⁶/540`. Its squared integral is at most
`1/(540·448)=1/241920`. Cauchy–Schwarz gives
`(sinhPairing(F)−m)²≤E/241920`. Completing the square
`[96(sinhPairing(F)−m)−m]²≥0` gives
`sinhPairing(F)²/2≤(97/192)m²+(97/483840)E`.

The audited Gamma reserve gives `Q≥P+E/64`. Substitute the exact identity
`∫₀¹t(E−C(t))dt=E/2+∫H²` into `P`, then use the preceding two inequalities.
The mass coefficient is `1/48−1/64+1/(96π²)+97/483840`; the moment coefficient
is `1/24+1/16+97/192=39/64`. The signed prime correlation is retained exactly.

## Lean

Source: `WTZ.ThePrimitiveVarianceRetainsTheOddMoment`:
`unit_odd_primitive_variance_le`, `unit_sinhPairing_sub_position_square_le`,
`weilQuad_ge_logarithmic_first_moment`. Individual `lake --old env lean` audit passes;
transitive axioms are exactly `propext`, `Classical.choice`, `Quot.sound`.
The variance and sinh remainder estimates require only continuity and unit support
(with oddness for the primitive). No positivity input is assumed.
The sufficient two-moment regional sign is
[refuted](../5-failed/f1-primitive-variance-joint-payment.md). Complete odd unit-window
positivity remains open; the [stronger Gamma reserve](f1-higher-gamma-reserve.md)
retains additional positive terms.
