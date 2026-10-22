# Gamma reflected-intensity exact-collapse universality law

## Status

Fully proven on paper; Lean 4 formalization in progress.

## Theorem-first source

- `gammaOppositeShiftIntensityMero_eq_reflectionProduct_div`: reflected intensity is the quotient
  of two thermal reflection products.
- `differentialAlgebraicOver_gammaReflectionProductMero_iff_integerWeight`: one reflection
  product is DA exactly on its half-integral weight lattice.
- `gammaReflectionProductMero_div_add_nat`: integer translation of weight changes a reflection
  product by an explicit nonzero DA gauge.
- `gammaReflectionProductMero_eq_gauge_mul_reducedVeneziano`: Euler reflection reduces a thermal
  product to a DA gauge times one translated Gamma ratio.
- `differentiallyAlgebraicOver_reducedVenezianoAmplitudeMero_iff_integerShift`: a translated
  Gamma ratio is DA exactly on one integer orbit.
- `hypertranscendentalOver_gammaFintypeOrbitProductMero`: an exposed nonzero Gamma-orbit charge
  forces HT.
- `hypertranscendentalOver_pow_of_pos`: a positive power of an HT scalar remains HT.

The corpus proves only that a nonnegative integer difference of the two weights is sufficient for
intensity collapse.  It does not classify the full collapse locus or expose the second component
coming from simultaneous thermal exceptional weights.

## Universal law

For arbitrary complex shifts `a,b`, the reflected-frequency intensity of the opposite-orientation
Gamma clock is differentially algebraic exactly when either

1. `b-a` is an integer, or
2. both `1-2a` and `1-2b` are integers.

On the complement of this union the intensity is hypertranscendental.  Thus the collapse locus is
the union of a relative translation-orbit diagonal and the product of the two absolute thermal
half-lattices; integer separation alone is not the universal boundary.

## Paper proof

Write `R(h)=Gamma(z+h)Gamma(h-z)`.  Existing reflection identities give

`I(a,b)=R(a)/R(b)`

and, up to a nonzero DA gauge,

`I(a,b)=Gamma(z+a) Gamma(z+1-b) /
  (Gamma(z+1-a) Gamma(z+b))`.

If `b-a` is integral, `R(a)/R(b)` is a DA shift gauge; both signs follow by inversion.  If both
`1-2a` and `1-2b` are integral, each `R` is DA, so their quotient is DA.

Conversely assume neither collapse mechanism holds.  If exactly one weight lies on the thermal
half-lattice, one of `R(a),R(b)` is nonzero DA and the other HT, so their quotient is HT.  If
neither weight is exceptional and `a+b` is nonintegral, the charge at `a` in the four-factor
normal form is separated from `1-b`, `1-a`, and `b`; the exposed-orbit theorem forces HT.  If
neither weight is exceptional and `a+b` is integral, translate `b` to `1-a`.  The remaining core
is, up to a nonzero DA gauge,

`(Gamma(z+a)/Gamma(z+1-a))^2`.

Its ratio is HT because `1-2a` is nonintegral, and its square remains HT.  Multiplication by the
integer-translation gauge preserves HT.  These cases exhaust the complement.

No numerical computation is used; proof is symbolic because task forbids computations.

## Lean formalization

Planned module:
`GaloisForLFunctions.HTGeometry.GammaReflectedIntensityExactCollapseUniversalityLaw`.

## Novelty audit

Pending literature audit after Lean formalization. Corpus audit is negative.
