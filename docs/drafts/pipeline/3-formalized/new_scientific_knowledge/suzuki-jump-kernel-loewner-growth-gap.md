# Suzuki jump-kernel Loewner gap — Lean certificate

- **ID:** `suzuki-jump-kernel-loewner-growth-gap-lean`
- **Stage:** 3-formalized
- **Type:** FORMALIZED RH-FRONTIER REDUCTION
- **Scientific status:** `[LEAN-PROVED] [UNCONDITIONAL] [NOT AN RH PROOF]`
- **Paper proof:**
  `../../2-fully-proven/new_scientific_knowledge/suzuki-jump-kernel-loewner-growth-gap.md`

## Module

`formal/GaloisForLFunctions/RHTower/SuzukiJumpKernelLoewnerGap.lean`

## Certified declarations

- `suzukiScalarPickKernel_realAffineSourceFunction`: Pick kernel commutes with real affine
  extrapolation.
- `suzukiScalarPickKernel_jumpWeylCandidate`: exact multiplier/source kernel split.
- `suzukiAffineKernelGap_nonneg_iff_loewnerGrowth`: exact quadratic-form growth-versus-deficit
  equivalence.
- `suzukiAffineKernelGap_nonneg_of_loewnerGrowth`: positivity consumer.
- `suzukiAffineKernel_extrapolation_factor_gt_one`: two negative shifts extrapolate past nearer
  source.
- `suzukiAffineSewnExteriorWeylQuotient_eq_jumpWeylCandidate`: actual one-sided sewn quotient is
  abstract affine source candidate.
- `suzukiScalarPickKernel_affineSewnExteriorWeylQuotient`: actual full Pick kernel decomposition.

## Scope boundary

Lean proves all algebra without RH premise, computations, `sorry`, or new axioms.  It does not
assume or prove Loewner growth inequality.  That source-specific inequality is current RH-bearing
analytic producer.

