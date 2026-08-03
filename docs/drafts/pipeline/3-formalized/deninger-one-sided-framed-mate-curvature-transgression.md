# One-sided framed mate-curvature transgression — formalization certificate

- **ID:** `deninger-one-sided-framed-mate-curvature-transgression`
- **Stage:** 3, formalized in Lean 4
- **Paper proof:**
  `../2-fully-proven/new_scientific_knowledge/deninger/deninger-one-sided-framed-mate-curvature-transgression.md`
- **Lean module:**
  `GaloisForLFunctions.RHTower.DeningerOneSidedFramedMateCurvatureTransgression`
- **RH status:** not proved

## Formalized content

`DeningerOneSidedFramedMateCurvatureTransgression.lean` proves unconditionally:

- `deningerTopConormalAffineTransport_mul`: coherent scalar top-conormal
  transport is a flat affine representation;
- `deningerCoherentPowerShift_is_affineCoboundary`: every coherent monomial
  power sector has affine potential zero or one, so scalar ramified sectors
  cannot produce nonflat horizontal curvature;
- `deningerOneSidedFramedTransport_eq_diagonal_mul`: the new transport is
  literally conormal-only diagonal gain followed by affine top-conormal
  transport;
- `deningerOneSidedFramedCurvature_eq`: exact upper-triangular curvature
  \[
    F_\chi(m,n)_{01}=\chi(m)(m-1)(1-\chi(n));
  \]
- `deningerFramedCompositionCurvature_bianchi`: full nonabelian Bianchi
  identity for every natural-number-indexed matrix transport;
- `deningerHalfDensityMateGain_eq_norm_inv_sq` and
  `deningerHalfDensityMateGain_mul`: the explicit positive gain is the inverse
  squared Deninger half-density norm and is multiplicative on positive power
  degrees;
- `deningerHalfDensityMateGain_sub_inv_eq_mateCurvature` and
  `deningerOneSidedReducedCurvature_dual_sub_source`: source/dual reduced
  curvature polarization is exactly `deningerTensorSquareRadialMateCurvature`;
- `deningerOneSidedFramedCurvature_two_eq_zero_iff`: the first nontrivial
  left frame has zero curvature exactly when `Re(s)=1/2`;
- `deningerCalderonWittBaseGammaBoundaryDefectCoefficient_eq_framedCurvaturePolarization`:
  actual ordered `(2,3)` Gamma boundary at forced degree six is the existing
  positive calibration of this framed curvature polarization.

No theorem assumes a Xi zero lies on the critical line, Gamma curvature
vanishes, source annihilation, or RH.

## Verification

Direct foreground elaboration:

```text
lake env lean \
  GaloisForLFunctions/RHTower/DeningerOneSidedFramedMateCurvatureTransgression.lean
```

passes without errors or warnings.

Targeted module build only:

```text
lake build \
  GaloisForLFunctions.RHTower.DeningerOneSidedFramedMateCurvatureTransgression
```

passes. No full build was run.

Scratch `#print axioms` audit of ten headline theorems reports only:

```text
propext
Classical.choice
Quot.sound
```

The classification corollary omits `Classical.choice`. No project axiom,
`sorry`, `admit`, `opaque`, or `unsafe` declaration is used.

Module is imported by `GaloisForLFunctions.RHTower` umbrella.

## Frontier after formalization

This closes construction of first parameter-dependent nonflat horizontal
curvature in Deninger framed source and its exact scalar Gamma realization.
It does not prove curvature vanishing. Remaining theorem is
`FRAMED_MATE_CURVATURE_SINGULAR_STOKES_ANNIHILATION`: extend this rank-two
curvature to completed Xi Green common-test incidence and derive its
annihilation from a source-native singular Cartier/Stokes boundary law that
does not use Xi zero locations.

