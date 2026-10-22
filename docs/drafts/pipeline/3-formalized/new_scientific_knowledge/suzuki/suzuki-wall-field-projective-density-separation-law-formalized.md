# Suzuki wall-field projective density separation law — formalization certificate

- **Stage:** 3-formalized
- **Paper proof:**
  `./suzuki-wall-field-projective-density-separation-law.md`
- **Lean module:**
  `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiWallFieldProjectiveDensitySeparationLaw.lean`
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [SOURCE-SPECIFIC]`
  `[CANDIDATE NEW SCIENTIFIC KNOWLEDGE] [NOVELTY UNVERIFIED] [NOT RH]`

## Formalized result

Lean proves marked affine-secant tensor and characteristic denominator are homogeneous degree two
under common source scaling, including affine homogeneous coordinate.  Common nonzero scaling
cancels exactly from normalized quotient.

For critical wall field `omega_e(t)`, same laws specialize to

```text
T(omega_e*x,...,omega_e*c)=H_e(t)*T(x,...,c),
D(omega_e*y,omega_e*Y)=H_e(t)*D(y,Y),
H_e(t)=Lambda(p^(e+1))/sqrt(p^(e+1))*exp(i*t*log(p^(e+1))).
```

Division-free Suzuki affine cross numerator therefore retains exact far-hinge density while
normalized response forgets it.  Lean also proves `omega_e(t) != 0`, discharging quotient gate.

Key declarations:

```text
suzukiProjectiveAffineSecantTensor_commonScale
suzukiProjectiveAffineSecantDenominator_commonScale
suzukiProjectiveAffineSecant_quotient_commonScale
suzukiProjectiveAffineSecantTensor_linearMap_smul
suzukiCriticalWallField_ne_zero
suzukiProjectiveAffineSecantTensor_criticalWallField_eq_farHingeDensity
suzukiProjectiveAffineSecantDenominator_criticalWallField_eq_farHingeDensity
suzukiProjectiveAffineSecant_quotient_criticalWallField
suzukiProjectiveAffineSecant_cross_criticalWallField_eq_farHingeDensity
```

## Frontier correction

One-mode resolvent completion is not canonical because actual Suzuki response is projective.
Arithmetic density must live in division-free determinant line.  Open core is actual unscaled
marked-tensor Ward compensation, not normalized quotient positivity.

## Verification

- direct source check passed:
  `lake env lean GaloisForLFunctions/RHTower/Suzuki/SuzukiWallFieldProjectiveDensitySeparationLaw.lean`;
- unconditional, no `sorry`, `admit`, project axiom, `opaque`, `unsafe`, computation, estimate, or
  RH premise;
- final targeted SOTA build passed `9457/9457`;
- axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`;
- formal lint reaches module but remains red on 22 unrelated concurrent unreachable modules.
