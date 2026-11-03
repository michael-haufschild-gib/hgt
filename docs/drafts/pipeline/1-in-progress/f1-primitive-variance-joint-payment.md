# Primitive variance and the two-moment first-fold payment

- **ID:** F1-PV
- **Stage:** 1-in-progress
- **Type:** REFUTED TARGET; positive survivor under audit
- **Source:** [Joint first-fold payment](f1-joint-cubic-prime-payment.md)
- **Refuted statement:** The explicit two-moment form below is nonnegative for every real odd C²
  function `G` supported in `[-1,1]`.
- **Obstruction:** A [smooth quadratic-cutoff approximation](f1-quadratic-cutoff-reserve-test.md)
  has `P(F)+E/64<0`, hence `D(G)<0`. Its individual Lean and standard-only axiom audits pass.
  Retirement awaits the stronger Gamma reserve's positive-survivor audit.

Put `d=2log2`, `w=log2/√2`, `W(u)=−½log(1−u²)`, `P₃(u)=(5u³−3u)/2`, and

`c=γ+logπ+1/192+1/(96π²)+97/483840`,
`A(u)=137/60−c+W(u)`, `β=77/20+39/256`.

The proposed joint payment is

`∫₀¹A G²+w∫_{d−1}¹G(u)G(d−u)du
 −β(∫₀¹uG)²−(63/20)(∫₀¹P₃G)² ≥ 0`.

## Paper reduction

For `F(x)=G(2x)`, put `E=∫F²`, `m=∫xF`, `H(x)=∫_{−1}ˣF`.
The primitive has equal zero endpoint values on the unit interval and `∫H=−m`.
Periodic Wirtinger therefore retains its mean:

`∫H²−m²≤E/(4π²)`.

Unlike a uniform primitive-mass estimate, this places the entire remaining charge on
the same first odd moment. The existing squared sinh remainder bound gives
`|sinhPairing F−m|²≤E/241920`. Young's inequality with parameter `1/96` yields

`½(sinhPairing F)²≤(97/192)m²+(97/483840)E`.

Substitution in the exact primitive expression for `P` gives

`P+E/64 ≥ L−(c+log2)E−(39/64)m²−2w C(log2)`.

The regional/exterior identity, scaling and fifth harmonic gap give
`L=J(G)/4+log2 E+∫₀¹WG²`, `m=½∫₀¹uG`, and
`J(G)/4≥(137/60)E−(77/20)(∫₀¹uG)²−(63/20)(∫₀¹P₃G)²`.
This gives the audited reduction `D(G)≤P(F)+E/64≤Q(F)`. Its sign would give the
missing floor `P≥−E/64`, hence complete odd unit-window positivity.

## The refuted joint sign

On the reflection strip, multiplication and reflection have paired matrix
`[[A(u),w],[w,A(d−u)]]`; off the strip the coefficient is `A(u)`.
The [joint low-moment payment](../3-formalized/f1-joint-low-moment-chord-payment.md) proves
`D(G)+(3203/1280)(∫₀¹uG)²≥∫₀¹G²/1000`: a polynomial comparison has spectral bounds
`19/50≤B₀≤37/20`, and its inverse chord pays the full `P₃` charge together with `3/2`
of the first charge. The remaining first-moment debit and its coupling are open.
The [same linear chord cannot pay the full first charge](../5-failed/f1-linear-inverse-chord-full-payment.md),
even if the third charge is omitted.

The [positive inverse](../3-formalized/f1-positive-first-moment-inverse.md) gives the exact
first-moment solution `q₁`: off the strip `q₁=u/A(u)`; on it,
`q₁(u)=[A(v)u−wv]/[A(u)A(v)−w²]`, `v=d−u`. The numerator is at least `7451/60000`.
Thus `q₁>0`, and `q₁<u/A` on the open strip.

The global sign `D≥0` is false. Seeking sufficient inverse-matrix estimates for this
sign cannot close the first fold. The complete form retains the exact local Gamma
remainder and exterior reserve; these terms remain available for a replacement
joint payment.

## Source status

- `HTGeometry.wirtinger_intervalIntegral` in `CirclePoincareWirtinger`: checked source statement;
  supplies the periodic variance inequality.
- WTZ `unit_odd_sinhPairing_eq_primitive_cosh`, `unit_odd_position_eq_primitive_integral`,
  and `unit_sinh_linear_residual_square_le`: individually audited inputs.
- LST `RegionalLogarithmicGap`: audited fifth-harmonic gap and projection mechanism.
- The [primitive variance and joint Gamma/pole reduction](../3-formalized/f1-primitive-variance-reduction.md)
  pass individual Lean and standard-only transitive axiom audits. They establish
  the lower bound `Q≥L−(c+log2)E−(39/64)m²−2wC(log2)` for every odd C² unit test.
- The [exact exterior and two-moment assembly](../3-formalized/f1-regional-exterior-identity.md)
  prove `D(G)≤P(F)+E/64≤Q(F)` in Lean, with standard-only transitive axioms.
- WTZ `firstFoldTwoMomentForm_add_reduced_first_moment_ge_mass` and
  `weilQuad_add_reduced_first_moment_ge_mass` prove the reduced first-moment-charged
  coercivity bounds with standard-only transitive axioms.
- The explicit polynomial and logarithmic first-moment inverses, their positivity and local
  upper bounds pass individual Lean and standard-only transitive axiom audits.
- The displayed joint sign is refuted by `exists_odd_unit_firstFoldTwoMoment_neg`; no positivity premise is added.
