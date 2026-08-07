# Sonin aperture anomaly and principal-relative closure law — formalized

- **ID:** `sonin-aperture-area-rigidity-and-restriction-defect`
- **Stage:** 3-formalized
- **Scientific status:** `[LEAN-PROVED] [CORPUS-NEW WELD] [NOVELTY UNVERIFIED] [NOT RH]`
- **Paper proof:**
  `../../2-fully-proven/new_scientific_knowledge/sonin/sonin-aperture-area-rigidity-and-restriction-defect.md`
- **Status:** unconditional; no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe`

## Lean modules

- `formal/GaloisForLFunctions/RHTower/TraceClassCyclicity.lean`
- `formal/GaloisForLFunctions/RHTower/SoninPrincipalRelativeTraceSplitting.lean`
- `formal/GaloisForLFunctions/RHTower/SoninApertureRestrictionDefect.lean`
- `formal/GaloisForLFunctions/RHTower/SoninApertureCyclicMassConservation.lean`
- `formal/GaloisForLFunctions/RHTower/SoninApertureAreaRigidity.lean`
- `formal/GaloisForLFunctions/RHTower/SoninPrincipalRelativeApertureNoGo.lean`
- `formal/GaloisForLFunctions/RHTower/SoninApertureDefectPositivity.lean`
- `formal/GaloisForLFunctions/RHTower/SoninLayerWindowNormalForm.lean`
- `formal/GaloisForLFunctions/RHTower/SoninApertureLayerAlgebra.lean`
- `formal/GaloisForLFunctions/RHTower/SoninApertureCurvatureTrace.lean`
- `formal/GaloisForLFunctions/RHTower/SoninApertureDefectNonadditive.lean`

## Formal theorem chain

1. `SoninPrincipalRelativePresentation.toOperator_injective` proves fixed-aperture directness.
2. `finitePart_ofQuadraticCorner` gives principal logarithmic trace plus the unique ordinary
   Schatten-1 anomaly.
3. `exists_unitaryPush_centralSoninProjectionCorrection_eq_iff` classifies unitary aperture
   transport: it exists exactly for equal positive apertures.
4. `evenCentralSoninQuadraticCorner_restrictionDefect` gives the exact lost-layer restriction law.
5. `evenCentralSoninQuadraticCorner_restrictionDefect_eq_adjoint_mul` factors the diagonal defect
   as `X†X`.
6. `one_le_norm_evenSoninApertureLostTransition_sub_compact` proves sharp compact distance `>=1`
   in every strict crossing chamber.
7. `evenCentralSoninQuadraticCorner_restrictionDefect_not_isCompactOperator` proves the positive
   diagonal defect noncompact.
8. `exists_prime_restrictionDefect_not_mem_principalRelativeIdeal` proves that every strict
   positive aperture pair has a genuine prime whose restriction defect lies outside the exact
   principal-relative ideal.
9. `evenFormalSoninComplement_compress_twoPolarizationShell_principalRelativeEq` upgrades the
   shell compression from arbitrary compact error to the concrete Schatten-1 relative ideal.
10. `soninWindowState_operator_mul_principalRelativeEq` proves the full canonical zero/live
    normal-state algebra closes modulo that exact ideal.
11. `evenCentralSoninQuadraticCorner_restrictionDefect_principalRelativeEq_shell` identifies the
    noncompact defect class with the existing scale-one live shell from `r*a` to `r*b`.
12. `soninLiveWindowCyclicLogWeight_apertureLostLayer` evaluates its cyclic principal mass as
    `log b-log a`, independent of `r`.
13. `evenSoninApertureRestrictionDefect_compressed_cocycle` proves exact functorial restriction;
    `evenSoninApertureRestrictionDefect_principalRelative_cocycle` proves ordinary additivity in
    the quotient.
14. `evenSoninApertureRestrictionCurvature_memSchattenClass_one` places the complete remaining
    aperture curvature in Schatten-1.
15. `soninApertureTotalLayerWindow_operator_eq_retained_add_lost` proves exact shell conservation.
16. `soninAperture_cyclicMass_conservation` proves exact conservation of orbital mass `log r`.
17. `evenCentralSoninQuadraticCorner_restrictionDefect_isPositive` and
    `reApplyInnerSelf_restrictionDefect_nonneg` prove the diagonal defect is a positive operator,
    and `evenCentralSoninQuadraticCorner_restrictionDefect_eq_zero_iff` /
    `evenCentralSoninQuadraticCorner_compress_eq_iff` give the exactness criterion: restriction is
    exact precisely when the lost-layer transition vanishes.
18. `re_opTrace_evenSoninApertureRestrictionCurvature_eq_neg_hsNormSq` identifies the ordinary
    trace of the curvature as minus the successive-layer coupling energy, hence
    `..._nonpos` and `..._eq_zero_iff`.
19. `exists_scale_evenSoninApertureRestrictionCurvature_ne_zero` and
    `exists_scale_evenSoninApertureRestrictionDefect_ne_add` show the anomaly is real: at an actual
    dilation scale the curvature is nonzero, so the defect is genuinely non-additive.

## Verdict and survivor

The full defect is never a relative correction, but its noncompact principal class is already an
existing canonical live shell. Contrary to the previous verdict, no enlarged principal algebra is
needed for diagonal aperture restriction: the canonical normal-state algebra is closed modulo the
exact relative ideal and already has the logarithmic reader. The only remaining aperture anomaly
is the ordinary trace of an explicitly isolated Schatten-1 curvature.
The principal logarithmic aperture mass is conserved internally, so it requires no archimedean
counterterm.

This is a terminal no-go for the finite-prime principal-plus-relative-ideal cofinalization, not a
proof of RH and not a no-go for every possible enlarged principal algebra.

## Verification

- direct `lake env lean` checks passed for every module listed above;
- `#print axioms` on all 62 declarations named by the paper card returns only `propext`,
  `Classical.choice`, and `Quot.sound`;
- every module is imported by `GaloisForLFunctions.RHTower`;
- no `sorry`, `admit`, project `axiom`, `opaque`, or `unsafe` declaration is introduced.

## Remaining frontier

Compute the ordinary trace of the aperture curvature and compare it with the cutoff-dependent
Burnol conductor cocycle on the genuine semilocal graph. Exact cancellation advances to the signed
completed lower floor; mismatch gives a terminal no-go for this source class.
