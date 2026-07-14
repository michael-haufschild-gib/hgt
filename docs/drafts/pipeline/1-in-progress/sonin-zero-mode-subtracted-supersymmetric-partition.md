# Sonin zero-mode-subtracted supersymmetric partition

- **ID:** `sonin-zero-mode-subtracted-supersymmetric-partition`
- **Stage:** 1-in-progress
- **Type:** exact physics value relation / corpus strengthening
- **Scientific status:** source-derived and source-formalized; novelty not claimed
- **Lean targets:** `formal/GaloisForLFunctions/HTGeometry/TwoProjectionSupersymmetry.lean`,
  `formal/GaloisForLFunctions/RHTower/SoninTimeBandHilbertSchmidt.lean`

## Claim

Let `P,R` be orthogonal projections and let `Z` be an orthogonal projection annihilated on both
sides by `P,R`.  Put

```text
A = P-R,
C = Z-(1-P-R).
```

Then the zero-mode-subtracted two-projection superalgebra is

```text
A^2 + C^2 = 1-Z,
AC + CA = 0.
```

Consequently every state obeys the exact active-space energy partition

```text
||(P-R) psi||^2 + ||C psi||^2 = ||(1-Z) psi||^2.
```

This is a static constraint law.  It removes the joint zero-mode sector rather than introducing
a dynamical supersymmetric flow.

## Sonin specialization

Take `P,R` to be the physical- and Fourier-forbidden projections, and `Z` to be the actual
projection onto their common kernel, `centralSoninProjection a`.  The corrected partner `C` is
definitionally `centralSoninProjectionCorrection a`.  Hence

```text
||(P-R) psi||^2
  + ||centralSoninProjectionCorrection a psi||^2
= ||(1-centralSoninProjection a) psi||^2.
```

Two quantitative consequences are now exposed in the RHTower surface:

```text
||centralSoninProjectionCorrection a|| <= 1,
||centralSoninDilationCornerResidual a p hp|| <= 4.
```

The first is not obtained by a triangle estimate on the three projection terms.  The second uses
the exact residual linearization, the new correction contraction, the already-sharp formal-
complement contraction, and `||U_p+U_p^{-1}|| <= 2`.  It is uniform in the dilation scale.

The Hilbert--Schmidt value admits a second, trace-safe decomposition.  Put

```text
D = (1-R)(1-P)-Z.
```

Then `C = RP-D`, the two terms are Hilbert--Schmidt orthogonal, and therefore

```text
||C||_HS^2 = ||RP||_HS^2 + ||D||_HS^2.
```

This deliberately does not take `tr(C)`: the correction is currently known Hilbert--Schmidt,
not trace class.  The split rewrites the existing residual estimate as

```text
||centralSoninDilationCornerResidual(a,p)||_HS^2
  <= 16 (||RP||_HS^2 + ||D||_HS^2).
```

The first term is the ordinary finite time--band overlap.  The second is now the single explicit
exterior-overlap value that must be paired or estimated before the classical Shannon-number trace
can yield a fully explicit aperture law.

## Open value comparison

`[BRIDGE] [OPEN CORE]` For `a>0`, prove the two remaining exact values in the concrete central
Fourier model:

```text
||centralSoninExteriorOverlap(a)||_HS^2 = ||RP||_HS^2,
||RP||_HS^2 = |[-a,a]|^2 = 4 a^2.
```

The first is the generic-sector pairing from two-projection supersymmetry after the common range
and common kernel are removed; the corpus already proves the common range is zero by bounded-
support Fourier uncertainty and defines `Z` as the common-kernel projection.  The second is the
Shannon-number trace for the localization operator with Fourier phase `exp(-2*pi*i*x*y)`.  Together
they would give

```text
||centralSoninProjectionCorrection(a)||_HS^2 = 8 a^2,
||centralSoninDilationCornerResidual(a,p)||_HS^2 <= 128 a^2.
```

These displayed aperture laws are targets, not current Lean theorems.  The remaining work is an
exact partial-isometry/trace pairing followed by the measure-theoretic kernel trace, not a
positivity argument or numerical estimate.  For the localization normalization and trace value,
see *Sharp estimates for eigenvalues of localization operators with applications to area laws*,
arXiv:2603.23832, https://arxiv.org/abs/2603.23832.

## Corpus value

1. The correction energy is no longer an opaque Hilbert--Schmidt error: it is exactly the portion
   of active Sonin energy not carried by the physical/Fourier projection mismatch.
2. A norm premise for the actual correction is discharged without a cutoff-size constant.
3. The conservation law is reusable in `HTGeometry` for any two quantum constraints with a
   specified common zero-mode projector.
4. The contraction is propagated into the concrete Sonin dilation-residual theorem surface.
5. No RH conclusion follows from this identity alone; the live source-norm comparison remains
   open.
6. The Hilbert--Schmidt split replaces the correction norm in the prime-power residual bound by
   two positive time--frequency overlap energies and exposes the exact missing comparison.
7. The same replacement is propagated into the semilocal geometric trace-response bound, so the
   obstruction and source-comparison surfaces now use the identical two-channel energy.

## Physics provenance

Avron--Seiler--Simon introduced the supersymmetric treatment of pairs of Fermi projections in
quantum charge deficiency and transport.  In that machinery the projection difference and its
anticommuting partner form the two supercharge coordinates.  Simon later gave a direct account of
the same two-projection supersymmetry.  The present `Z`-subtracted identity is the exact algebraic
specialization obtained by removing the common-kernel zero mode and identifying the surviving
partner with the existing Sonin correction.

Primary sources:

- J. E. Avron, R. Seiler, B. Simon, *Charge Deficiency, Charge Transport and Comparison of
  Dimensions*, Communications in Mathematical Physics 159 (1994), 399--422,
  https://math.caltech.edu/SimonPapers/228.pdf.
- J. Avron, R. Seiler, B. Simon, *The Index of a Pair of Projections*, Journal of Functional
  Analysis 120 (1994), 220--237, https://doi.org/10.1006/jfan.1994.1031.
- B. Simon, *Unitaries Permuting Two Orthogonal Projections*, arXiv:1703.05437,
  https://arxiv.org/abs/1703.05437.

## Formal surface

- `twoProjection_difference_sq_add_corrected_complement_sq`
- `twoProjection_difference_anticommutes_corrected_complement`
- `norm_twoProjection_difference_sq_add_corrected_complement_sq`
- `norm_centralSoninProjectionDifference_sq_add_correction_sq`
- `norm_centralSoninProjectionCorrection_le_one`
- `norm_centralSoninDilationCornerResidual_le_four`
- `twoProjectionExteriorOverlap`
- `twoProjectionExteriorOverlap_isHilbertSchmidt`
- `hsInner_twoProjection_overlap_exterior_eq_zero`
- `hsNormSq_twoProjection_correctedComplement_eq_overlap_add_exterior`
- `centralSoninExteriorOverlap`
- `centralSoninExteriorOverlap_isHilbertSchmidt`
- `hsNormSq_centralSoninProjectionCorrection_eq_timeBand_add_exterior`
- `centralSoninDilationCornerResidual_hsNormSq_le_timeBand_add_exterior`
- `norm_soninSemilocalGeometricTraceResponse_le_timeBand_add_exterior`

## Verification boundary

The declarations are source-formalized but intentionally uncompiled.  No Lean invocation, build,
lint, axiom check, numerical script, or experimental computation was run, in accordance with the
active no-build/no-computation constraint.  Promotion to Stage 3 requires later targeted checking.
