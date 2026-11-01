# Rational scattering reality has a sharp degree budget

- **ID:** RIT-RATIONAL-SCATTERING-REALITY
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `docs/reports/review-3110/argon.md`, §2.2.

## Statements

Put `C(t)=3/16+t²/4+it/4`. For a reduced rational function `R=P/Q`, with monic
`Q`, count only real `t` for which `Q(C(t))≠0`.

1. `R(C(t))` is real for infinitely many such `t` iff `R` is a real constant.
2. Otherwise the number of exact real matches is at most `2(deg P+deg Q)`.
3. The bound four for linear numerator and denominator is attained by
   `R(z)=i(z−3/2)/(z−1/2)`. Its real matches satisfy
   `t²=7/4` or `t²=15/4`; its denominator never vanishes on this parabola.
4. Above every prescribed height, a genuine critical-line zeta zero is a pole of
   the normalized modular scattering coefficient where `R` is regular and nonreal,
   unless `R` is a real constant.

## Paper proof

Set `A=P∘C`, `B=Q∘C`, and conjugate polynomial coefficients with a bar.
Infinite reality forces the polynomial identity `ĀB=AB̄`. Composition preserves
coprimeness, so `B | B̄`. The degrees are equal. Since `Q` is monic and `C` has
real leading coefficient `1/4`, the leading coefficient of `B` is real and
nonzero. Therefore `B=B̄`.

Thus `Q(C(t))` is real for every real `t`. The existing polynomial reality
classifier forces `Q` to be constant; monicity gives `Q=1`. The same classifier
then makes `P` a real constant. Real constants give the converse.

For a fraction other than a real constant, `D=ĀB−AB̄` is nonzero: otherwise
all real parameters except the finitely many denominator roots would be real
matches, contradicting statement 1. Every regular real match gives a distinct
complex root of `D`, and

```
deg D ≤ deg A+deg B = 2(deg P+deg Q).
```

For the explicit linear fractional example, reality is the circle equation
`(Re C(t)−1)²+(Im C(t))²=1/4`. After substitution this becomes
`(4t²−7)(4t²−15)=0`, giving four distinct real parameters.

The finite real-match set and finite denominator-zero set are bounded above.
The unconditional Hardy theorem supplies critical-line zeta zeros beyond both
sets and any prescribed height. The existing scattering noncancellation theorem
makes those actual zeros genuine poles, proving statement 4.

## Exact obstruction and positive survivor

- **Obstruction:** no fixed nonconstant rational scalar change of the native Casimir
  can place infinitely many critical-line energies on the real axis.
- **Positive survivor:** a finite exact-real interpolation bound, sharp already for
  linear fractional transforms.
- **Scope:** this does not exclude rational approximations with increasing degree,
  approximate reality, or Padé approximations of transfer operators. The corpus's
  entire Casimir transform remains a valid scalar escape; spectral occurrence remains
  a separate missing theorem.
- **Scientific status:** extends the corpus polynomial classifier; external novelty
  unassessed. No RH claim.

## Validation

- [x] Lean classification, degree bound, sharp four-point example, and actual-pole corollary.
- [x] Transitive axiom audits: only `propext`, `Classical.choice`, `Quot.sound`.
- [x] Umbrella import.
- [x] Final direct production-file check.

Lean: `RenormalizedIntersectionTheory/ScatteringRationalReality.lean`.
Public declarations: `infinite_realLocus_iff`, `ncard_realLocus_le`,
`sharpMobius_realLocus_ncard`, `exists_critical_pole_regular_nonreal_above`.
