# Xi--Hurwitz orientation exterior continued-Cauchy closure

- **ID:** `xi-hurwitz-orientation-exterior-cauchy-closure`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean), `[BRIDGE]`
- **Scientific status:** `[PROVED] [NO NOVELTY CLAIM]`
- **Statement:** For every exact off-line-quartet accretive radius `R`, the canonical
  Xi--Hurwitz orientation vector belongs to the Hilbert closure of the continued prime--Gamma
  Cauchy source vectors whose poles satisfy `R < |re z|`.  Positivity of the explicit finite
  continued-source divided-difference energies on this exterior family implies RH.

## The closure reduction

Let

```text
E_R = span_C { CauchyLp(z) : z is in the two-sided continued source domain,
                              R < |re z| }.
```

If `XiOffLineQuartetAccretiveBand R`, Lean proves

```text
v_Xi in closure(E_R).
```

This is unconditional.  On a critical-line divisor fiber the signed Hurwitz orientation
coefficient is zero.  On an off-critical fiber `rho`, the exact quartet budget gives

```text
R + 1/2 < |im rho| = |re alpha_rho|.
```

The normalized Cauchy pole exhaustion is taken horizontally with displacement at most `1/4`.
Every approximating pole therefore remains in `R < |re z|`, including on the negative-frequency
side.  Summing the resulting closed-subspace membership over exact analytic-multiplicity fibers
places the complete orientation vector in `closure(E_R)`.

At the discharged rational radius this reads

```text
v_Xi in closure span {
  CauchyLp(z) : z is in the continued source domain and 218/25 < |re z|
}.
```

Thus all central Cauchy generators are unnecessary for the remaining orientation proof.

## Exterior source-value criterion

For a finite pairwise conjugate-separated exterior packet `(c_i,z_i)`, define

```text
K(z,w) =
  (continuedPrimeArchSourceRelativeTrace(conj w)
    - continuedPrimeArchSourceRelativeTrace(z)) / (z - conj w),

Q_source(c,z) = re sum_i sum_j c_i conj(c_j) K(z_i,z_j).
```

The module proves that exterior perturbations can remove every conjugate collision while staying
outside the central band, and that their exact source energies converge to the unconditional Weil
Hilbert value.  Consequently

```text
[Q_source(c,z) >= 0 for every finite separated exterior packet]
  -> [the Weil Hilbert form is nonnegative on E_R]
  -> [the Weil Hilbert form is nonnegative at v_Xi]
  -> RH.
```

Conversely RH makes the Weil reflection the identity on the whole `ell^2` divisor carrier, so it
supplies every exterior source inequality.  Hence, for every exact quartet-admissible radius,

```text
XiExteriorContinuedCauchySourcePassivity R <-> RH.
```

In particular,

```text
XiExteriorContinuedCauchySourcePassivity (218/25) <-> RH.
```

## What changed in the open problem

The previous source-core target quantified over the entire regular centered strip.  It can now be
replaced by the strictly smaller, concrete target:

```text
Prove positivity of every finite continued prime--Gamma divided-difference matrix
using only pairwise separated poles with 218/25 < |re z|.
```

No estimate or positivity theorem is needed for central poles.  The remaining problem is still
RH-strength: the formalization does not prove the exterior source sign.  In particular, pointwise
anti-Herglotz sign is not enough for arbitrary finite matrices, and mixed exterior correlations
remain the hard source-side content.

## Lean certificate

Module:

`formal/GaloisForLFunctions/RHTower/XiHurwitzOrientationExteriorCauchyClosure.lean`

Principal declarations:

- `RHTower.xiWeilFiberIndicatorLp_mem_exteriorContinuedCauchyHilbertSubspace`
- `RHTower.xiHurwitzOrientationFiberCoefficient_eq_zero_of_re_eq_half`
- `RHTower.xiHurwitzOrientationVector_mem_exteriorContinuedCauchyHilbertSubspace`
- `RHTower.exists_pairwiseConjSeparatedExteriorContinuedSourceEnergy_tendsto`
- `RHTower.exteriorContinuedCauchyCore_nonnegative_of_sourcePassivity`
- `RHTower.riemannHypothesis_of_exteriorContinuedCauchySourcePassivity`
- `RHTower.exteriorContinuedCauchySourcePassivity_iff_riemannHypothesis`
- `RHTower.exteriorContinuedCauchySourcePassivity_twoHundredEighteen_twentyFifths_iff_rh`

The module is imported by `formal/GaloisForLFunctions/RHTower.lean`.  Its exact target build and
direct module check pass.  Axiom inspection of the closure, source transfer, and terminal
equivalence reports only `propext`, `Classical.choice`, and `Quot.sound`.

## Gates

- [x] mathematical proof complete
- [x] Lean formalization complete
- [x] exact target build
- [x] RHTower umbrella import
- [x] axiom audit
- [ ] exterior prime--Gamma source passivity; this is the remaining RH-strength theorem
