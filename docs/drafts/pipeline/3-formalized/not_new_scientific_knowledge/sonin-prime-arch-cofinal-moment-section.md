# Sonin--prime-arch cofinal moment section

- **ID:** `sonin-prime-arch-cofinal-moment-section`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Scientific status:** not new scientific knowledge
- **Lean file:** `formal/GaloisForLFunctions/RHTower/SoninPrimeArchCofinalMomentSection.lean`
- **Statement:** Static closure of every finite prime--Gamma moment block along the positive Sonin
  moment curve is equivalent to the existence of one positive aperture sequence converging to the
  entire moment germ; either form implies RH.

## Goal

Replace unrelated per-polynomial or per-cutoff schedules by one coherent cofinal source section.
The premise is a value relation between the explicit all-prime Sonin residual energy and the fixed
continued prime--Gamma germ; it contains no Xi divisor, zero-location sign, real-rootedness, or
limiting positive Xi measure.

## Growing-block condition

Choose

```text
cutoff  : Nat -> Nat,
aperture : Nat -> Real,
error    : Nat -> Real
```

such that

```text
cutoff j -> infinity,
aperture j > 0,
error j >= 0 and error j -> 0,
norm (SoninMoment(aperture j,r) - PrimeArchMoment(r)) <= error j
  whenever r < cutoff j.
```

For each fixed `r`, cofinality eventually places `r` inside the block, while the common error
tends to zero.  Hence the same aperture sequence converges in every fixed moment coordinate.
Reusing that sequence at every finite cutoff supplies the already formalized simultaneous
finite-moment coupling, which transfers positive Sonin Hankel values to the prime--Gamma source
and yields RH.

Conversely, the earlier static finite-block closure condition already supplies such a coherent
section.  At stage `j`, choose from closure one positive aperture whose first `j + 1` moments are
within `1 / (j + 1)` in the product metric.  Coordinate projection contracts distance, so these
choices form a growing-block approximation and converge in every fixed moment.  A single-moment
section also returns every finite block to the same closure.  Thus no compatibility axiom between
the finite closures is needed:

```text
all finite prime--Gamma blocks lie in the corresponding Sonin curve closures
  <-> one positive aperture sequence converges in every moment coordinate.
```

The formal chain is

```text
one growing-block Sonin/prime--Gamma approximation
  -> one aperture sequence converging in every moment
  -> compatible finite Sonin moment coupling
  -> prime--Gamma integer-polynomial Hankel positivity
  -> RH.
```

The card does not prove the finite-block closure itself.  It proves that this one static
source-value relation automatically creates the coherent sequence, cutoff, and vanishing error.

## Principal declarations

- `SoninPrimeArchSingleMomentCoupling`
- `SoninPrimeArchCofinalBlockApproximation`
- `soninPrimeArchSingleMomentCoupling_of_cofinalBlockApproximation`
- `soninPrimeArchFiniteMomentCoupling_of_singleMomentCoupling`
- `exists_soninPrimeArchCofinalBlockApproximation_of_finiteMomentClosure`
- `soninPrimeArchFiniteMomentClosure_iff_exists_singleMomentCoupling`
- `riemannHypothesis_of_soninPrimeArchSingleMomentCoupling`
- `riemannHypothesis_of_soninPrimeArchCofinalBlockApproximation`

## Gates

- [x] 0 -> 1  coherent source-only condition isolated
- [x] 1 -> 2  complete proof
- [x] 2 -> 3  formalized in Lean with no new axioms
- [ ] 3 -> 4  publication-ready treatment not warranted for this interface theorem
