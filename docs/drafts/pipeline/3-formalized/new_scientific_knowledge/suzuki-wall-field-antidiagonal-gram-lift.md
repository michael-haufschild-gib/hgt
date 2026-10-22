# Suzuki wall-field anti-diagonal Gram lift — formalization certificate

- **Stage:** 3-formalized
- **Paper proof:**
  `../../2-fully-proven/new_scientific_knowledge/suzuki-wall-field-antidiagonal-gram-lift.md`
- **Lean module:**
  `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiWallFieldAntidiagonalGramLift.lean`
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [SOURCE-SPECIFIC]`
  `[CANDIDATE NEW SCIENTIFIC KNOWLEDGE] [NOVELTY UNVERIFIED] [NOT RH]`

## Formalized result

Lean defines two-height wall kernel

```text
K_e(t,u)=omega_e(t)*conj(omega_e(u))
```

and proves exact reflection, Hermitian symmetry, stationarity, positive diagonal, and far
anti-diagonal:

```text
conj(omega_e(-t))=omega_e(t),
K_e(t,u)=Lambda(n)/sqrt(n)*exp(i*(t-u)*log(n)/2),
K_e(t,t)=Lambda(n)/sqrt(n),
K_e(t,-t)=Lambda(n)/sqrt(n)*exp(i*t*log n).
```

Every finite height matrix is literally `Matrix.gram` of conjugated wall features, hence positive
semidefinite.  Far delayed-hinge atom is `-i*K_e(t,-t)/t^2`: complete phase is reflected
anti-diagonal of genuine PSD carrier, not put on positive diagonal.

Same diagonal mass supplies exact sharp marked Lorentz completion:

```text
S_(m,d)((b_e*r,b_e*s),(b_e*r,b_e*s))+d^2*(b_e*s)^2
 = Lambda(n)/sqrt(n)*(r-m*s)^2 >= 0.
```

Key declarations:

```text
star_suzukiCriticalWallFieldGramKernel_swap
star_suzukiCriticalWallField_neg
suzukiCriticalWallFieldGramKernel_eq_differenceCharacter
suzukiCriticalWallFieldGramKernel_diagonal
suzukiCriticalWallFieldGramKernel_antidiagonal
suzukiCriticalDelayedHingeJumpAtom_eq_neg_I_mul_wallKernel_antidiagonal_div
suzukiCriticalWallFieldGramMatrix_eq_gram
suzukiCriticalWallFieldGramMatrix_posSemidef
suzukiMarkedSecant_wallAmplitude_minimalRootedCompletion_eq
suzukiMarkedSecant_wallAmplitude_minimalRootedCompletion_nonneg
```

## Scientific advance and remaining wall

This discharges prior representation obstruction “complex bilinear wall square is not a norm
square”: correct, but it is FE-reflected anti-diagonal, while positive diagonal pays exact local
rooted debt.  One Hermitian block now carries both without phase loss.

`SUZUKI-FE-REFLECTED-WALL-WARD-ASSEMBLY` remains RH-bearing: compensate divergent all-prime
diagonal, assemble actual Robin/polar--Gamma/holonomy rectangular kernel before projective
division, and prove uniformly lower semibounded Ward defect.  Local Gram positivity alone is not
RH.

## Verification

- direct source check passed:
  `lake env lean GaloisForLFunctions/RHTower/Suzuki/SuzukiWallFieldAntidiagonalGramLift.lean`;
- unconditional, no `sorry`, `admit`, project axiom, `opaque`, `unsafe`, computation, estimate, or
  RH premise;
- final targeted SOTA build passed `9457/9457`;
- axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`;
- formal lint reaches module but remains red on 22 unrelated concurrent unreachable modules.
