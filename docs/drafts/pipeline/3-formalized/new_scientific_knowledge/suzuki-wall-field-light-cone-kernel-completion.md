# Suzuki wall-field light-cone kernel completion — formalization certificate

- **Stage:** 3-formalized
- **Paper proof:**
  `../../2-fully-proven/new_scientific_knowledge/suzuki-wall-field-light-cone-kernel-completion.md`
- **Lean module:**
  `formal/GaloisForLFunctions/RHTower/SuzukiWallFieldLightConeKernelCompletion.lean`
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [SOURCE-SPECIFIC]`
  `[CANDIDATE NEW SCIENTIFIC KNOWLEDGE] [NOVELTY UNVERIFIED] [NOT RH]`

## Formalized result

For critical wall field `omega_e`, Lean defines reflected amplitudes

```text
ellPlus(t) =(omega_e(t)+i*omega_e(-t))/2,
ellMinus(t)=(omega_e(t)-i*omega_e(-t))/2.
```

Their rank-one kernels obey exact two-variable identities

```text
Gram(ellPlus)-Gram(ellMinus)=F_reflected,
Gram(ellPlus)+Gram(ellMinus)=K_FE-symmetrized,
F_reflected+Gram(ellMinus)=Gram(ellPlus).
```

The two Gram legs are unique under first two equations.  With
`v_e(t)=(Re omega_e(t),Im omega_e(t))`, Lean proves source realization rather than abstract
isomorphism:

```text
R v_e(t)=-v_e(-t),
Gram(ellPlus)(t,u) =QPlus_1(v_e(t),v_e(u)),
Gram(ellMinus)(t,u)=QMinus_1(v_e(t),v_e(u)),
F_reflected(t,u)   =QFE_1(v_e(t),v_e(u)).
```

On diagonal, reflected current is `Im(omega_e(t)^2)`.  Off center, exact delayed-hinge identity is

```text
t^2*Re J_e(t)+|ellMinus(t)|^2=|ellPlus(t)|^2>=0.
```

For arbitrary finite prime-power source and height packets, both light matrices are literal Gram
matrices in finite source-coordinate Euclidean space, hence PSD, and packet completion remains
entrywise exact.

Key declarations:

```text
suzukiCriticalWallPositiveLightKernel_sub_negative_eq_reflectedCurrent
suzukiCriticalWallPositiveLightKernel_add_negative_eq_symmetrizedGram
suzukiCriticalWallReflectedCurrentKernel_add_negative_eq_positive
suzukiCriticalWallLightKernels_unique
weldFEReflectionLinear_suzukiCriticalWallPlaneVector
suzukiCriticalWallPositiveLightKernel_eq_weldPositiveLightForm
suzukiCriticalWallNegativeLightKernel_eq_weldNegativeLightForm
suzukiCriticalWallReflectedCurrentKernel_eq_weldFEKreinQ
suzukiCriticalWallReflectedCurrentKernel_diagonal
suzukiCriticalDelayedHingeJumpAtom_re_add_negativeLight_eq_positiveLight
suzukiCriticalDelayedHingeJumpAtom_re_add_negativeLight_nonneg
suzukiCriticalWallPositiveLightPacketMatrix_posSemidef
suzukiCriticalWallNegativeLightPacketMatrix_posSemidef
suzukiCriticalWallReflectedCurrentPacketMatrix_add_negative_eq_positive
```

## Scientific advance and remaining wall

Common wall scaling was already proven positivity-neutral.  This module instead performs
non-common FE/Xi-real mixing and proves exact negative completion leg is forced by same wall
source, not fitted external data.  It closes source realization of abstract light channel at every
finite aperture.

Actual RH-bearing statement is narrower and still open: prove division-free
Robin/Gamma/holonomy boundary trace supplies or dominates this forced `Gram(ellMinus)` leg, then
renormalize nonsummable cofinal light mass while retaining marked and holonomy Schur payments.
Only after that can corpus rectangular Ward lower-bound connector imply RH.

## Verification

- direct source check passed:
  `lake env lean GaloisForLFunctions/RHTower/SuzukiWallFieldLightConeKernelCompletion.lean`;
- unconditional, no `sorry`, `admit`, project axiom, `opaque`, `unsafe`, computation, estimate, or
  RH premise;
- final targeted SOTA build passed `9458/9458`;
- axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`;
- formal lint reaches module but remains red on 21 unrelated concurrent unreachable modules.
