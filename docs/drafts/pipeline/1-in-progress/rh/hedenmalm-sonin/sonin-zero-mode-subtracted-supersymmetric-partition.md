# Sonin zero-mode-subtracted supersymmetric partition

- **ID:** `sonin-zero-mode-subtracted-supersymmetric-partition`
- **Stage:** 1-in-progress
- **Type:** exact physics value relation / corpus strengthening
- **Scientific status:** source-derived and source-formalized; novelty not claimed
- **Verification status:** source-only by explicit instruction; no Lean process or build run
- **Lean targets:** `formal/GaloisForLFunctions/HTGeometry/HilbertSchmidtOperator.lean`,
  `formal/GaloisForLFunctions/HTGeometry/L2PairingEnergy.lean`,
  `formal/GaloisForLFunctions/HTGeometry/TwoProjectionSupersymmetry.lean`,
  `formal/GaloisForLFunctions/HTGeometry/TwoProjectionHilbertSchmidtEnergy.lean`,
  `formal/GaloisForLFunctions/RHTower/SoninTimeBandHilbertSchmidt.lean`,
  `formal/GaloisForLFunctions/RHTower/SoninProlateCommutatorEnergy.lean`, and
  `formal/GaloisForLFunctions/RHTower/SoninSemilocalTraceObstruction.lean`

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

The first term is the ordinary finite time--band overlap.  The exterior term is no longer a
single opaque value.  Orient the two projections so that `P` is the Fourier cutoff and `R` the
physical cutoff, and put

```text
H_in  = PRP,
K     = (1-P)RP,
H_out = (1-P)(1-R)(1-P)-Z.
```

Here `H_in` is definitionally the existing Sonin alternating/prolate block and `K` is the
existing prolate transition corner.  The supersymmetric sector decompositions are

```text
||RP||_HS^2 = ||H_in||_HS^2 + ||K||_HS^2,
||D||_HS^2  = ||H_out||_HS^2 + ||K||_HS^2,
||C||_HS^2  = ||H_in||_HS^2 + ||H_out||_HS^2 + 2||K||_HS^2.
```

They are trace-safe Pythagorean identities.  The factorization is also exact:

```text
K†K = H_in-H_in^2,
KK† = H_out-H_out^2,
tr(H_in-H_in^2) = tr(H_out-H_out^2) = ||K||_HS^2.
```

Only products of Hilbert--Schmidt operators are traced.  In the existing free-fermion surface,
`||K||_HS^2` is the local number variance and half the physical/Fourier commutator energy.

## Value comparison

`[BRIDGE]` For `a>0`, the supersymmetric factor equality and the original overlap comparison are
now source-formalized without an additional hypothesis:

```text
||H_out(a)||_HS^2 = ||H_in(a)||_HS^2,
||D(a)||_HS^2 = ||RP(a)||_HS^2,
||C(a)||_HS^2 = 2 ||RP(a)||_HS^2.
```

The same transition value occurs in the decompositions of `D` and `RP` and cancels.  The needed
terminal trace decay is also closed on both sides.  The interior block already has a compact
strict-contraction theorem.  For the exterior block the new exact structural identity is

```text
H_out = Q T_out Q,
T_out = P_(Fourier-complement) P_(physical-complement) P_(Fourier-complement),
Q = 1-Z.
```

Equivalently, `H_out = T_out-Z`.  Every eigenvalue-one vector of `T_out` lies in the common
complementary carrier `range(Z)`, while `Q` removes that entire carrier.  Since `H_out` is
Hilbert--Schmidt, it is compact; it is also positive and contractive as the `Q`-compression of the
positive alternating block.  The reusable compact-positive-contraction spectral lemma therefore
gives `||H_out||<1`.  This discharges the former exterior strictness hypothesis rather than merely
renaming it.

`[BRIDGE]` The one-step Witten cancellation is extended algebraically to every power
difference

```text
tr(H_in^n-H_in^(n+1)) = tr(H_out^n-H_out^(n+1)),
```

using the exact intertwining `H_out^n K = K H_in^n` and Hilbert--Schmidt cyclicity.  Trace
linearity on the power products and the finite telescope are also formalized, giving

```text
tr(H_in^2)-tr(H_out^2)
  = tr(H_in^(n+2))-tr(H_out^(n+2))
```

for every `n`.  Both terminal power traces now tend to zero by the generic Hilbert--Schmidt strict-
contraction trace-decay theorem.  Hence their constant difference is zero and the displayed
factor equality follows.

`[BRIDGE]` The independent Shannon time--band area law is now source-formalized for the
localization operator with Fourier phase `exp(-2*pi*i*x*y)`:

```text
||RP||_HS^2 = |[-a,a]|^2 = 4 a^2.
```

It is obtained from three reusable facts rather than a spectral estimate: an orthonormal family
in a separable Hilbert space has countable index, Parseval commutes the resulting basis sum with
the kernel integral, and the complex bilinear `L²` functional `v ↦ ∫ u v` is exactly the Riesz
functional represented by `star u`.  Since the Fourier phase has unit modulus, its kernel energy
is the rectangle area.  The central rectangle has side lengths `2a` and `2a`, giving source
theorems

```text
||centralSoninProjectionCorrection(a)||_HS^2 = 8 a^2,
||centralSoninDilationCornerResidual(a,p)||_HS^2 <= 128 a^2.
```

The same substitution is propagated to the logarithmically weighted prime-power residual and
the semilocal response bound.  No numerical estimate or spectral asymptotic is used.  For the
localization normalization and trace value,
see *Sharp estimates for eigenvalues of localization operators with applications to area laws*,
arXiv:2603.23832, https://arxiv.org/abs/2603.23832.

The same area is now exposed in the operator-trace coordinate used by localization theory:

```text
Re Tr(soninAlternatingBlock physicalForbidden fourierForbidden) = 4 a^2.
```

Generically, `re_opTrace_twoProjectionInteriorCompression_eq_hsNormSq_overlap` proves
`Re Tr(PRP)=||RP||_HS^2` for orthogonal projections whenever the overlap is Hilbert--Schmidt.
The central theorem `re_opTrace_centralProlateBlock_eq_four_mul_sq` therefore gives the exact
Landau--Pollak/Shannon effective dimension of the actual prolate block already used by the Sonin
resolvent.  Downstream trace arguments no longer have to reconstruct this value through the
overlap operator or a singular-value sum.

## Corpus value

1. The correction energy is no longer an opaque Hilbert--Schmidt error: it is exactly the portion
   of active Sonin energy not carried by the physical/Fourier projection mismatch.
2. A norm premise for the actual correction is discharged without a cutoff-size constant.
3. The conservation law is reusable in `HTGeometry` for any two quantum constraints with a
   specified common zero-mode projector.
4. The contraction is propagated into the concrete Sonin dilation-residual theorem surface.
5. No RH conclusion follows from this identity alone; the live RH source comparison remains open.
6. The Hilbert--Schmidt split replaces the correction norm in the prime-power residual bound by
   two positive time--frequency overlap energies.
7. The same replacement is propagated into the semilocal geometric trace-response bound, so the
   obstruction and source-comparison surfaces now use the identical two-channel energy.
8. The former exterior-overlap unknown is split into an exterior positive compression plus the
   existing prolate transition value; no new analytic hypothesis is introduced.
9. The correction, dilation-residual, and semilocal-response surfaces now accept the three-channel
   compressed-Hamiltonian partition directly.
10. The overlap equality is reduced to equality of two positive compression energies; the
    already-formalized number-variance term cancels exactly.
11. Every consecutive interior/exterior power-difference trace is formally equal by the
    transition intertwining and Hilbert--Schmidt cyclicity, and their individual trace difference
    is formally constant from degree two onward.
12. The exterior compression is the complementary alternating block with its complete
    eigenvalue-one carrier subtracted; the existing compact-positive strictness mechanism
    therefore closes exterior terminal decay.
13. The overlap equality, correction-energy doubling, residual estimate, weighted prime-power
    estimate, and semilocal response bound are propagated as unconditional source theorems.
14. The Fourier-kernel Shannon trace `||RP||_HS^2=4a^2` is now source-formalized and propagated;
    no supersymmetric comparison or aperture-value hypothesis remains on this route.
15. The complete all-prime weighted residual energy is bounded by `128a^2` times the existing
    summable Euler-coefficient energy, so the assembled kernel now has a scalar aperture majorant.
16. The prolate energy, number variance, and cutoff-commutator surfaces now satisfy the exact
    finite-aperture budgets `E_prolate+Var=4a^2` and `2E_prolate+E_commutator=8a^2`.
17. The actual prolate compression has the exact trace `4a^2`, not merely an overlap-energy
    representation of that value.

## Physics provenance

Avron--Seiler--Simon introduced the supersymmetric treatment of pairs of Fermi projections in
quantum charge deficiency and transport.  In that machinery the projection difference and its
anticommuting partner form the two supercharge coordinates.  Simon later gave a direct account of
the same two-projection supersymmetry.  The present `Z`-subtracted identity is the exact algebraic
specialization obtained by removing the common-kernel zero mode and identifying the surviving
partner with the existing Sonin correction.  The further factorizations `K†K` and `KK†` are the
partner-Hamiltonian mechanism of supersymmetric quantum mechanics; trace cyclicity is the finite
supertrace cancellation used here.

Primary sources:

- J. E. Avron, R. Seiler, B. Simon, *Charge Deficiency, Charge Transport and Comparison of
  Dimensions*, Communications in Mathematical Physics 159 (1994), 399--422,
  https://math.caltech.edu/SimonPapers/228.pdf.
- J. Avron, R. Seiler, B. Simon, *The Index of a Pair of Projections*, Journal of Functional
  Analysis 120 (1994), 220--237, https://doi.org/10.1006/jfan.1994.1031.
- B. Simon, *Unitaries Permuting Two Orthogonal Projections*, arXiv:1703.05437,
  https://arxiv.org/abs/1703.05437.
- E. Witten, *Dynamical Breaking of Supersymmetry*, Nuclear Physics B 188 (1981), 513--554,
  https://doi.org/10.1016/0550-3213(81)90006-7.

## Formal surface

- `Orthonormal.countable_index`
- `HTGeometry.norm_l2_sq_eq_integral_norm_sq`
- `HTGeometry.complexMulBilinear_lpPairing_eq_toDual_star`
- `HTGeometry.norm_complexMulBilinear_lpPairing`
- `hsNormSq_kernelOperator_eq_norm_sq`
- `fullFourierFunctionalContinuous_eq_toDual`
- `norm_fullFourierFunctionalField_sq`
- `hsNormSq_fullToRestrictedTimeBandFourier_eq_rectangleArea`
- `hsNormSq_fullTimeBandFourier_eq_rectangleArea`
- `hsNormSq_cutoffFourierCutoff_eq_rectangleArea`
- `hsNormSq_centralTimeBandOverlap_eq_four_mul_sq`
- `hsNormSq_centralSoninExteriorOverlap_eq_four_mul_sq`
- `hsNormSq_centralSoninProjectionCorrection_eq_eight_mul_sq`
- `centralSoninDilationCornerResidual_hsNormSq_le_128_mul_sq`
- `centralSoninWeightedPrimePowerResidual_hsNormSq_le_128_mul_sq`
- `tsum_centralSoninWeightedPrimePowerResidual_hsNormSq_le_area`
- `norm_soninSemilocalGeometricTraceResponse_le_area`
- `hsNormSq_centralProlateBlock_add_transition_eq_four_mul_sq`
- `hsNormSq_centralProlateBlock_add_re_opTrace_impurity_eq_four_mul_sq`
- `two_mul_hsNormSq_centralProlateBlock_add_commutator_eq_eight_mul_sq`
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
- `twoProjectionInteriorCompression`
- `twoProjectionTransition`
- `twoProjectionExteriorCompression`
- `twoProjectionExteriorCompression_mul_zeroMode_eq_zero`
- `zeroMode_mul_twoProjectionExteriorCompression_eq_zero`
- `adjoint_twoProjectionTransition_mul_self_eq_interiorCompression_sub_sq`
- `twoProjectionTransition_mul_adjoint_eq_exteriorCompression_sub_sq`
- `opTrace_twoProjectionInteriorCompression_impurity_eq_exteriorCompression_impurity`
- `twoProjectionExteriorCompression_mul_transition_eq_transition_mul_interiorCompression`
- `twoProjectionExteriorCompression_pow_mul_transition_eq_transition_mul_interiorCompression_pow`
- `twoProjectionInteriorCompression_powerDifference_eq_power_mul_adjointTransition_mul_transition`
- `twoProjectionExteriorCompression_powerDifference_eq_power_mul_transition_mul_adjointTransition`
- `opTrace_twoProjectionInteriorCompression_powerDifference_eq_exteriorCompression_powerDifference`
- `opTrace_pow_add_two_sub_pow_add_three_of_isHilbertSchmidt`
- `opTrace_twoProjectionInteriorCompression_sq_sub_exteriorCompression_sq_eq_power_sub_power`
- `hsNormSq_twoProjection_overlap_eq_interiorCompression_add_transition`
- `hsNormSq_twoProjectionExteriorOverlap_eq_exteriorCompression_add_transition`
- `hsNormSq_twoProjection_overlap_add_exteriorCompression_eq_exteriorOverlap_add_interiorCompression`
- `hsNormSq_twoProjection_correctedComplement_eq_compressions_add_two_mul_transition`
- `centralSoninExteriorOverlap`
- `centralSoninExteriorOverlap_isHilbertSchmidt`
- `centralSoninExteriorCompression`
- `centralSoninExteriorCompression_eq_complementaryAlternatingBlock_sub_carrier`
- `centralSoninExteriorCompression_isHilbertSchmidt`
- `mem_inf_of_soninAlternatingBlock_apply_eq_self`
- `norm_lt_one_of_compact_of_symmetric_of_nonnegative_of_not_eigenvalue_one`
- `norm_centralSoninExteriorCompression_lt_one`
- `hsNormSq_centralSoninProjectionCorrection_eq_timeBand_add_exterior`
- `hsNormSq_centralSoninProjectionCorrection_eq_compressions_add_two_mul_transition`
- `hsNormSq_centralTimeBandOverlap_eq_prolateBlock_add_transition`
- `hsNormSq_centralSoninExteriorOverlap_eq_exteriorCompression_add_transition`
- `hsNormSq_centralTimeBandOverlap_add_exteriorCompression_eq_exteriorOverlap_add_prolateBlock`
- `opTrace_centralProlateImpurity_eq_exteriorCompressionImpurity`
- `opTrace_centralProlatePowerDifference_eq_exteriorCompressionPowerDifference`
- `opTrace_centralProlate_sq_sub_exteriorCompression_sq_eq_power_sub_power`
- `tendsto_opTrace_pow_add_two_zero_of_isHilbertSchmidt_norm_lt_one`
- `tendsto_opTrace_centralSoninAlternatingBlock_pow_add_two_zero`
- `hsNormSq_centralSoninExteriorCompression_eq_prolateBlock`
- `hsNormSq_centralSoninExteriorOverlap_eq_timeBand`
- `hsNormSq_centralSoninProjectionCorrection_eq_two_mul_timeBand`
- `re_opTrace_centralExteriorCompressionImpurity_eq_transition_hsNormSq`
- `hsNormSq_centralSoninProjectionCorrection_eq_compressions_add_two_mul_re_opTrace_prolateImpurity`
- `centralSoninDilationCornerResidual_hsNormSq_le_timeBand_add_exterior`
- `centralSoninDilationCornerResidual_hsNormSq_le_compressions_add_two_mul_transition`
- `centralSoninDilationCornerResidual_hsNormSq_le_timeBand`
- `centralSoninWeightedPrimePowerResidual_hsNormSq_le_timeBand`
- `norm_soninSemilocalGeometricTraceResponse_le_timeBand_add_exterior`
- `norm_soninSemilocalGeometricTraceResponse_le_compressions_add_two_mul_transition`
- `norm_soninSemilocalGeometricTraceResponse_le_timeBand`

## Verification boundary

The declarations are source-formalized but intentionally uncompiled.  No Lean invocation, build,
lint, axiom check, numerical script, or experimental computation was run, in accordance with the
active no-build/no-computation constraint.  Promotion to Stage 3 requires later targeted checking.
