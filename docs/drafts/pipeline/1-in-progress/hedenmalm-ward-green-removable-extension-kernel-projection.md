# Hedenmalm Ward--Green removable extension and kernel projection

- **ID:** `P-G152`
- **Stage:** `1-in-progress`
- **Type:** THEOREM (Lean) + OPEN PRODUCER
- **Status:** `[PAPER-PROVED] [LEAN-PROVED] [CORPUS-NEW CLASSIFICATION] [NOT RH]`
- **Parent:** `P-G151`
- **Target module:** `formal/GaloisForLFunctions/RHTower/HedenmalmWardGreenRemovableExtensionKernelProjection.lean`

## Goal

Determine exact information discarded by Ward Green totalization at the critical line. Replace the
vague “discontinuous index channel” wall by a source-regular term plus one explicit spectral
projection, then attack that projection rather than repeating positive-frame completions.

## Conjecture loop

1. `[CONJECTURE]` The inverse-square five-shift scalar is genuinely singular and requires an
   unbounded source coefficient.
2. `[FAILED / PIVOT]` Amplitude cancellation shows every exponential pair defect is
   `4 sinh(ka)^2`; after division by `a^2` it has a removable entire extension through `a=0`.
   The obstruction is not blow-up.
3. `[CONJECTURE]` The totalized Ward scalar equals that removable extension everywhere.
4. `[FAILED AT KERNEL]` Totalized inversion sets the scalar to zero at `a=0`, while the removable
   value is the positive quadratic jet of the five-shift defect.
5. `[PROVED]` There is an exact decomposition

   ```text
   totalizedGreenScalar(a)
     = removableSourceScalar(a) - jumpConstant * 1_{a=0},
   jumpConstant >= 1/81.
   ```

   For the critical-feature trace this becomes a regular source trace minus the critical-line
   spectral projection trace. This should classify the missing producer exactly.
6. `[PROVED]` The removable value is the limit of positive off-line quantum values, hence its
   scale-one jump satisfies `jumpConstant >= 1/81`.
7. `[PROVED]` Multiplication by the critical-feature energy and absolute Xi summation preserve the
   decomposition exactly:

   ```text
   WardGreenTrace(t)
     = RemovableTrace(t)
       - jumpConstant * CriticalLineFeatureEnergyTrace(t).
   ```

   Both terms are summable. No error or unsigned majorant remains.
8. `[PROVED]` Full feature energy splits into critical-line plus off-line energy, and

   ```text
   CriticalLineFeatureEnergyTrace(t) = FullFeatureEnergyTrace(t) <-> RH.
   ```

   Thus the missing projection is exactly RH-bearing; replacing it by full energy is circular.

## New knowledge

Ward--Green obstruction is a positive spectral-atom subtraction, not an analytic blow-up. The
regular source extension contains a nonzero quadratic jet on the Ward kernel; totalized inversion
removes exactly that jet on each critical-line copy. This reconciles P-G148's forced discontinuity
with P-G150's bounded trace and P-G151's Plancherel fracture: all three are shadows of one kernel
projection law.

Next producer must recover critical-line projection by a source boundary value/residue/index, or
construct a signed identity where that projector cancels before scalar trace. More Green
regularization, continuous-frame completion, or holomorphic diagonal majorization cannot do so.

## Lean certificate

Headline theorems:

- `continuous_fiveShiftWardGreenRemovableExtension`
- `fiveShiftEulerGammaPairedRenormalizedFeature_eq_extension_sub_kernelAtom`
- `fiveShiftWardGreenKernelJump_ge`
- `fiveShiftCriticalFeatureWardGreenCurrent_eq_removable_sub_kernelProjection`
- `fiveShiftWardGreenKernelProjectionTrace_eq_jump_mul_lineEnergy`
- `fiveShiftCriticalFeatureWardGreenTrace_eq_removable_sub_jump_mul_lineEnergy`
- `criticalLineCriticalFeatureEnergyTrace_eq_full_iff_rh`

## Anti-theatre test

- Defining a piecewise extension without proving removability/continuity is not progress.
- Restating P-G148 boundary discontinuity is not progress.
- Required new knowledge: exact analytic extension, exact positive jump, per-copy decomposition,
  summable trace decomposition, and proof that no other term is missing.

## Gates

- [x] exact exponential-pair removable quotient
- [x] continuous five-shift extension
- [x] positive jump quantum
- [x] exact scalar extension-minus-kernel-atom law
- [x] exact critical-feature trace decomposition
- [x] direct Lean check
- [x] exact module build
- [x] axiom audit (`[propext, Classical.choice, Quot.sound]` only)
- [ ] umbrella build
- [ ] source recovery/elimination of kernel projection
- [ ] unconditional RH

## Log

- 2026-08-13 -- opened after P-G151 proved complete positive-frame reconstruction loses phase.
- 2026-08-13 -- direct check, exact module build, and seven-theorem axiom audit pass.
