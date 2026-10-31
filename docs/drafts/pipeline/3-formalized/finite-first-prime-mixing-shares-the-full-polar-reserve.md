# Finite first-prime mixing shares the full polar reserve

- **ID:** finite-first-prime-mixing-shares-the-full-polar-reserve
- **Stage:** 3-formalized
- **Statement:** For each fixed finite prime set, its first-power coarse/detail
  mixing can be added to the full nonfirst source while retaining any fraction
  below one of the original complete-profile Gamma energy, after one finite
  detail head. Both original polar moments remain exact.

## Proof

At integer lag `m≥2`, the established mixed-tail bound is
`|B_m(d_tail,q)|≤[4Λ(m)/√m] Γ(F)/cellGammaWeight(A)`.
Sum over the finite prime set, retaining the original untruncated `F`.
Since the cell weight dominates `log A`, one head makes this sum at most
`εΓ(F)/2`.

The full Haar diagonal and all mixed exponents at least two already differ
from `Γ(F)+P(F)` by at most `εΓ(F)/2` beyond one head. Take the larger
head and add the absolute errors. Thus the augmented source differs from
`Γ(F)+P(F)` by at most `εΓ(F)`. Expanding
`P(F)=2coshHalfMoment(F)²−2sinhHalfMoment(F)²` gives the retained reserve.
First powers occur only in the new finite sum; higher mixed powers occur
only in the existing nonfirst source.

The joint source is nonnegative when this finite detail head and the original
sinh moment vanish. Restricting these `A+1` linear readouts to any negative
subspace is injective, so its dimension is at most `A+1`, uniformly in cell
horizon and in the original finite profile family.

## Scope

The prime set is fixed; the cell horizon and signed coefficient vectors are
arbitrary. Coarse signed source terms are not included in this payment.

## Verification

`ArithmeticIndexDescent/FiniteFirstPrimeMixingSharesTheFullPolarReserve.lean`:
`exists_finiteFirstPrime_fullPolar_completeGamma_reserve` and
`exists_uniform_finiteFirstPrime_fullPolar_negative_dimension`.
Direct `lake --old env lean` check passed. Capstone transitive axioms:
`propext`, `Classical.choice`, `Quot.sound`. Umbrella wired.
