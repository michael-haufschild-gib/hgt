# Sonin aperture Ward-curvature transgression

- **ID:** `sonin-aperture-ward-curvature-transgression`
- **Stage:** 3-formalized
- **Type:** FORMAL CLOSURE / SUZUKI ANTI-LOOP REDUCTION
- **Scientific status:** `[NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Status:** unconditional Lean 4 proof
- **Terminal status:** not RH, not not-RH, not a full Suzuki no-go

## Lean modules

- `formal/GaloisForLFunctions/RHTower/TraceClassCompressionCurvature.lean`
- `formal/GaloisForLFunctions/RHTower/SoninApertureCurvatureTrace.lean`
- `formal/GaloisForLFunctions/RHTower/SoninApertureWardCurvature.lean`

## Principal declarations

```text
isHilbertSchmidt_of_adjoint_mul_self_memSchattenClass_one
re_opTrace_compression_sub_self_eq_neg_hsNormSq
compression_sub_self_eq_zero_iff_boundary_zero
evenSoninApertureSuccessiveLayerTransition
evenSoninApertureSuccessiveLayerTransition_isHilbertSchmidt
re_opTrace_evenSoninApertureRestrictionCurvature_eq_neg_hsNormSq
evenSoninApertureRestrictionCurvature_eq_zero_iff_successiveLayerTransition_eq_zero
re_opTrace_evenSoninApertureRestrictionCurvature_eq_zero_iff
evenSoninApertureLayers_successive_orthogonal
evenSoninApertureSymmetricSuccessiveLayerChannel
crossBoundary_apertureLayer_symmetricSuccessive_eq_adjoint
two_mul_re_opTrace_apertureCurvature_add_WardEnergy_eq_zero
```

## Formal statement

For `0<a<b<c<r*a` and `r>1`, if

```text
Z=(Q_a-Q_b)(U_r+U_r^*)(Q_b-Q_c),
X=Z+Z^*,
Kappa=Delta_(a,c)-Delta_(a,b)-Delta_(b,c),
```

Lean proves

```text
Z is Hilbert--Schmidt,
Re Tr Kappa=-||Z||_HS^2,
Re Tr Kappa=0 iff Kappa=0 iff Z=0,
2 Re Tr Kappa+||[X,Q_a-Q_b]||_HS^2=0.
```

No hypothesis is left undisclosed and no computation is used.

## Verification

Direct module checks passed with `lake env lean`; final project audit is recorded in session
handover after the narrow `lake build` and axiom/lint checks.
