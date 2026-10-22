# Suzuki critical wall-field resolvent dressing law — formalization certificate

- **Stage:** 3-formalized
- **Paper proof:**
  `./suzuki-critical-wall-field-resolvent-dressing-law.md`
- **Lean module:**
  `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiCriticalWallFieldResolventDressingLaw.lean`
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [SOURCE-SPECIFIC]`
  `[CANDIDATE NEW SCIENTIFIC KNOWLEDGE] [NOVELTY UNVERIFIED] [NOT RH]`

## Formalized result

Lean treats bare wall field as source coordinate and applies scalar restricted-Weil resolvent
mode before affine sewing.  It proves

```text
D_0-D_aff=K_(alpha,beta)(s) omega_e,
omega_e(D_0-D_aff)
 =K_(alpha,beta)(s) Lambda(n)/sqrt(n) exp(i t log n).
```

At zero height and below-spectrum negative shifts, self-paired residual is strictly negative on
negative spectral levels and strictly positive on positive levels.  Prime-power weight is proved
strictly positive from exact `Lambda(p^(e+1))=log p`.

Key declarations:

```text
suzukiCriticalWallDressedResidual_eq_kreinDefect_mul_wallField
suzukiCriticalWallDressedResidual_eq_rational_mul_wallField
suzukiCriticalWallField_mul_dressedResidual_eq_kreinDefect_mul_farHingeNumerator
suzukiCriticalFarHingeWeight_pos
re_suzukiCriticalWallField_mul_dressedResidual_zero_eq
re_suzukiCriticalWallField_mul_dressedResidual_zero_neg
re_suzukiCriticalWallField_mul_dressedResidual_zero_pos
```

## Scope and frontier

Formalization does not construct actual restricted-Weil operator, its spectral measure, or
endpoint trace domain.  Correct open core is `SUZUKI-RESOLVENT-DRESSED-WALL-WARD`: instantiate
boundary observation of resolvent-dressed wall field and prove mixed compensation block pays exact
negative-mode Krein debt with uniformly lower-bounded rectangular residual.  RH is not proved.

## Verification

- direct source check:
  `lake env lean GaloisForLFunctions/RHTower/Suzuki/SuzukiCriticalWallFieldResolventDressingLaw.lean`;
- targeted SOTA build: `9455/9455` jobs;
- axiom audit: `propext`, `Classical.choice`, `Quot.sound` only;
- repository formal lint reaches new module but remains red on thirteen unrelated concurrent
  unreachable modules (six `RHTower`, six `HTGeometry`, one `HilbertMetric`);
- no `sorry`, `admit`, new axiom, `opaque`, `unsafe`, numerical computation, estimate, or RH premise.
