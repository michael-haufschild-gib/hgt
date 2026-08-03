# Deninger Gamma--Green quadratic mate curvature

- **ID:** `deninger-gamma-green-quadratic-mate-curvature`
- **Status:** formalized in Lean 4; unconditional; Route L remains open
- **Paper proof:**
  `../2-fully-proven/new_scientific_knowledge/deninger/deninger-gamma-green-quadratic-mate-curvature.md`
- **Lean module:**
  `GaloisForLFunctions.RHTower.DeningerCalderonWittGammaGreenQuadraticMateCurvature`

## Formal result

The module defines normalized positive mate gauge

```text
gHat(q) = gGamma(q) / (1 + norm(bGamma(q)))
```

and scalar curvature

```text
E(q) = fracture(q)^2 * gHat(q).
```

It proves:

- `deningerCalderonWittGammaGreenMateGauge_pos`;
- `deningerCalderonWittNormalizedBaseGammaBoundaryDefectCoefficient_eq_greenFracture_mul_mateGauge`;
- `deningerCalderonWittGammaGreenMateCurvature_nonneg`;
- `deningerCalderonWittGammaGreenMateCurvature_eq_zero_iff`;
- `deningerCalderonWittGammaGreenMateCurvature_pos_iff`;
- `deningerCalderonWittAllCrossPrimeGammaAdmissionOperator_greenProvenance_apply_eq_mateCurvature`;
- `deningerCalderonWittAllCrossPrimeGammaAdmissionOperator_reflectedGaussianGreen_apply_eq_zero_iff`.

The central pointwise identity is

```text
A_Gamma (C (Green a)) q i
  = E(q) * Hodge(Riesz a)(q) * h_CW(i).
```

For the fixed reflected Gaussian, Hodge value and every packet-horizon
coordinate are nonzero.  Hence each individual coordinate of admitted
Green provenance vanishes exactly when `re rho_q = 1/2`.

## Frontier consequence

This closes reflection-parity, scalar codiagonal, positive-gauge, and
packet-coordinate cancellation as Deninger source-null-homotopy mechanisms.
Missing source comparison must construct a strict cofinal Cartier mate whose
source law kills this positive quadratic curvature.  Assuming that law is
still RH-equivalent; this module does not assume it.

## Verification

- direct `lake env lean` on module: passed;
- targeted module build: passed;
- formal lint without build: passed;
- forbidden declaration scan: passed;
- axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`;
- umbrella import:
  `GaloisForLFunctions.RHTower`.
