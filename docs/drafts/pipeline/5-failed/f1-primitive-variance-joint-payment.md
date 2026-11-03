# Primitive variance and the two-moment first-fold payment

- **ID:** F1-PV
- **Stage:** 5-failed
- **Type:** REFUTED CONJECTURE; Lean counterexample and positive reserve
- **Source:** [Joint first-fold payment](../1-in-progress/f1-joint-cubic-prime-payment.md)
- **Refuted statement:** The explicit two-moment form below is nonnegative for every real odd C²
  function `G` supported in `[-1,1]`.
- **Obstruction:** A smooth quadratic-cutoff approximation has `P(F)+E/64<0`, hence
  `D(G)<0`. Complete Weil positivity remains open.

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
This gives the audited reduction `D(G)≤P(F)+E/64≤Q(F)`. The sufficient signs
`D≥0` and `P≥−E/64` are both false.

## The refuted joint sign

On the reflection strip, multiplication and reflection have paired matrix
`[[A(u),w],[w,A(d−u)]]`; off the strip the coefficient is `A(u)`.
The [joint low-moment payment](../3-formalized/f1-joint-low-moment-chord-payment.md) proves
`D(G)+(3203/1280)(∫₀¹uG)²≥∫₀¹G²/1000`: a polynomial comparison has spectral bounds
`19/50≤B₀≤37/20`, and its inverse chord pays the full `P₃` charge together with `3/2`
of the first charge. The remaining debit cannot be paid within `D` for all tests.
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

## Exact counterexample

Let `F(x)=2x(1−4x²)²` for `|x|≤1/2`, zero outside. Its mass and position moment are
`E=128/3465`, `m=4/105`. For `0≤t≤1`, its correlation is

`C(t)=128/3465−(256/315)t²+(128/21)t⁴−(128/15)t⁵
 +(512/105)t⁷−(128/63)t⁹+(256/693)t¹¹`.

Centering the overlap at `−t/2` reduces the correlation to the integral of
`(z²−t²)[z⁴−2(1+t²)z²+(1−t²)²]²` on `0≤z≤1−t`. Integration gives

`L=∫₀¹(E−C)/t=128/315−32/21+128/75−512/735+128/567−256/7623`,
`M₁=∫₀¹t(E−C)=64/315−64/63+128/105−512/945+128/693−256/9009`.

Put `l=693147180/10⁹`, `h=693147181/10⁹`. Evaluate positive powers in `C` at `l`
and negative powers at `h`, obtaining `c₋≤C(log2)`. Since `c₋<0` and
`0≤log2/√2≤4902/10000`, the prime contribution is at most `−2(4902/10000)c₋`.
The sign of `F` gives `sinhPairing F≥m>0`. Also

`γ+logπ+log2 ≥ c₀=577215/10⁶+1098612/10⁶+1−3/(314159/10⁵)+l`.

Consequently the exact retained form satisfies

`P(F)+E/64 ≤ L−c₀E−M₁/24−m²/16−m²/2−2(4902/10000)c₋+E/64 < 0`.

The final inequality is rational and kernel-checked. For C² transfer, multiply the
support-preserving smooth quintic approximants by `(1−4x²)/(1−2x²)`. This ratio is
smooth on the unit interval, lies in `[0,1]`, and has Lipschitz constant `8` there.
The product vanishes locally outside the interval, including at the ratio's poles.
The resulting odd C² family has the same support, size at most `1`, Lipschitz constant
`32`, and pointwise limit `F`. The increment bound `Eₙ−Cₙ(t)≤32²t²` dominates the
logarithmic lag integrand. Dominated convergence transfers the strict sign.

`TheUniformGammaReserveHasANegativeDirection` proves the exact data and raw sign;
`TheRetainedGammaFormIsContinuous` proves retained-form continuity;
`TheUniformGammaReserveCannotPayTheFirstFold` proves
`exists_odd_unit_reservedGamma_neg` and `exists_odd_unit_firstFoldTwoMoment_neg`.
Their individual Lean checks and transitive-axiom audits use only
`[propext, Classical.choice, Quot.sound]`.

## No-go closure

- **Killing theorem:** A real odd C² unit-window test has `P+E/64<0` and `D<0`.
- **Positive survivor:** The [higher Gamma reserve](../3-formalized/f1-higher-gamma-reserve.md)
  gives `Q≥P+(193/10000)E+M₃/960+M₄/192` and
  `Q≥P+(193/10000+17/23040)E+(13/3840)m²`. It repairs the same smooth direction:
  some odd C² unit-window test has `P+E/64<0<Q`.
- **New insight:** The local Gamma remainder supplies higher lag energy and a first-moment
  credit; replacing it by a mass reserve loses terms needed by the failed comparison.
- **Status:** Both universal replacement bounds have dependency-closed paper proofs and
  Lean proofs in `TheGammaRemainderRetainsHigherLags`. The same-test repair is
  `exists_odd_unit_reservedGamma_neg_weil_pos` in
  `TheHigherGammaReserveRepairsTheQuadraticCutoff`. Individual Lean checks pass;
  transitive axioms are `[propext, Classical.choice, Quot.sound]` only.
