# Primitive variance and the two-moment first-fold payment

- **ID:** F1-PV
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** [Joint first-fold payment](f1-joint-cubic-prime-payment.md)
- **Statement:** The explicit two-moment form below is nonnegative for every real odd C²
  function `G` supported in `[-1,1]`.

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

## Actual remaining inequality

On the reflection strip, multiplication and reflection have paired matrix
`[[A(u),w],[w,A(d−u)]]`; off the strip the coefficient is `A(u)`.
The [third-moment payment](../3-formalized/f1-first-moment-complete-payment.md) proves
`D(G)+β(∫₀¹uG)²≥∫₀¹G²/1000`: a polynomial comparison has spectral bounds
`19/50≤B≤37/20`, and its inverse chord pays the full `P₃` charge.
Only the first-moment debit remains. Its coupling to the positive complement must still
be controlled; positivity on the first-moment kernel does not establish this conjecture.

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
- WTZ `firstFoldTwoMomentForm_add_first_moment_ge_mass` and
  `weilQuad_add_first_moment_ge_mass` prove the first-moment-charged coercivity bounds
  with standard-only transitive axioms.
- The displayed joint sign remains unproved; no positivity premise has been added.
