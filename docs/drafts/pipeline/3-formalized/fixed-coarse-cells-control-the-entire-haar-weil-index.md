# Fixed coarse cells control the entire Haar Weil index

- **ID:** fixed-coarse-cells-control-the-entire-haar-weil-index
- **Stage:** 3-formalized
- **Statement:** A universal finite detail head `A` bounds the negative
  dimension of the actual full Weil form by `R+A` whenever coarse coefficients
  occupy the first `R` cells. Detail coefficients and their upper horizon are
  unrestricted. Every prime power, Gamma term, coarse interaction and full
  polar term is included.

## Proof

The proved Haar-tail theorem gives one `A` for which every balanced detail
profile with its first `A` coefficients zero has full Weil energy at least
its nonnegative square mass, independently of its upper horizon.

On any finite family of complete profiles, record the `R` coarse coefficients
and the first `A` detail coefficients. A vector in the kernel has zero coarse
profile; its complete profile is precisely a high Haar tail. The original
full Weil form is therefore nonnegative on this kernel, without estimating
or dropping any cross term. Restriction of the `R+A` readouts to a negative
subspace is injective, giving the stated dimension bound.

## Scope

The coarse cell cutoff is fixed; the bound grows linearly with it. This does
not give a uniform bound when the coarse cutoff tends to infinity.

## Verification

`ArithmeticIndexDescent/FixedCoarseCellsControlTheEntireWeilIndex.lean`:
`exists_uniform_fixedCoarse_fullWeil_negative_dimension` passed a direct
`lake --old env lean` check. Its transitive axioms are exactly `propext`,
`Classical.choice`, and `Quot.sound`.
