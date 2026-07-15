# Xi positive-paired diagonal is the prime--Gamma moment-germ sector

- **ID:** `xi-positive-paired-diagonal-moment-germ-core`
- **Stage:** 3-formalized
- **Type:** exact source value relation / paper-to-Lean bridge
- **Status:** `[PROVED] [FORMALIZED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Lean:** `formal/GaloisForLFunctions/RHTower/XiPositivePairedDiagonalSectorCollapse.lean`

## Statement

For every centered source point `z` with nonzero imaginary part,

```text
ccmPositivePairedReducedKernel z z
  = 2 * (z.re / z.im) *
      (continuedPrimeArchReciprocalSquareTrace z).im.       (1)
```

In the upper half-plane this gives the exact sign equivalence

```text
0 <= ccmPositivePairedReducedKernel z z
  <->
0 <= z.re * (continuedPrimeArchReciprocalSquareTrace z).im. (2)
```

Away from the center, normalized odd division identifies the same reciprocal-square trace with
the determinate analytic prime--archimedean moment germ:

```text
continuedPrimeArchReciprocalSquareTrace z
  = normalizedPrimeArchMomentGerm z.                       (3)
```

Consequently `(1)` also has the moment-germ form

```text
ccmPositivePairedReducedKernel z z
  = 2 * (z.re / z.im) * (normalizedPrimeArchMomentGerm z).im. (4)
```

For every exact quartet-admissible radius `R`, the same module now formalizes

```text
exterior paired diagonal nonnegative beyond R
  <-> RH
  <-> every finite reduced source matrix is positive semidefinite. (5)
```

At `R=218/25` the radius premise is already discharged.  The remaining source problem is therefore
not a matrix-positivity problem and not a comparison between two unrelated transforms.  It is the
exterior upper-half-plane sign of the imaginary part of one explicit analytic moment germ.  The
module closes the exterior local-pole contradiction and the return implication from RH; it does
not prove the prime--Gamma source sign.

## Lean declarations

- `continuedPrimeArchReciprocalSquareTrace_eq_normalizedPrimeArchMomentGerm`;
- `ccmPositivePairedReducedKernel_self_eq_reciprocalSquareSector`;
- `ccmPositivePairedReducedKernel_self_nonneg_iff_re_mul_reciprocalSquare_im_nonneg`;
- `ccmPositivePairedReducedKernel_self_eq_momentGermSector`;
- `exists_xiReciprocalSquareUpperSector_neg_near_of_zero`;
- `exists_ccmPositivePairedReducedKernel_self_neg_above_of_zero`;
- `continuedPrimeArchPositiveExteriorPairedDiagonalNonnegative_iff_riemannHypothesis`;
- `continuedPrimeArchPositiveExteriorPairedDiagonalNonnegative_twoHundredEighteen_twentyFifths_iff_rh`;
- `continuedPrimeArchPositiveExteriorPairedDiagonalNonnegative_iff_reducedSourcePassivity`.

## Verification

The exact leaf check

```text
lake env lean GaloisForLFunctions/RHTower/XiPositivePairedDiagonalSectorCollapse.lean
```

passes on the pinned Lean toolchain.  The required parent build exposed and the same run repaired
two elaboration defects in `HTGeometry/HilbertSchmidtOperator.lean`: the separability class needed
its namespace qualification, and the orthonormal norm-square arithmetic needed exact numeral
normalization.

## Gates

- [x] diagonal/reciprocal-square identity formalized
- [x] upper-half-plane sign equivalence formalized
- [x] reciprocal-square/moment-germ identity formalized
- [x] exterior-preserving local pole witness formalized
- [x] exact exterior diagonal criterion formalized at general and rational radii
- [x] scalar diagonal / finite-matrix collapse formalized through RH
- [x] exact leaf build passes
- [ ] exterior source sign for the moment germ
- [ ] RH
