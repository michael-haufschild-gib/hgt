# Finite failure-kernel transversal revision, observer saturation, and cofinal barrier law — formalized

- **ID:** ULF-FKT-1
- **Stage:** 3-formalized
- **Paper:** `docs/drafts/pipeline/2-fully-proven/universal-law-field/failure-kernel-transversal-mechanics/finite-failure-kernel-transversal-revision-observer-saturation-and-cofinal-barrier-law.md`
- **Lean module:** `GaloisForLFunctions.HTGeometry.ConstitutiveFailureKernelTransversal`
- **Umbrella:** `GaloisForLFunctions.HTGeometry.UniversalLawField`
- **Status:** [LEAN-CERTIFIED] [NO SORRY] [NO PROJECT AXIOMS] [NOT RH]

## Certified declarations

- `FiniteConsequence`
- `IsFailureKernel`
- `HitsFailureKernel`
- `SuccessfulKernelRevision`
- `MinimalSuccessfulKernelRevision`
- `exists_failureKernel_subset`
- `successfulKernelRevision_iff_hits_all_failureKernels`
- `minimalSuccessfulKernelRevision_core_certificate`
- `HitsFailureFamily`
- `mapFailureKernels`
- `pullKernelRepair`
- `image_hitsFailureFamily`
- `pullKernelRepair_hitsFailureFamily`
- `FibreSaturatedRepairOn`
- `subset_pullKernelRepair_image`
- `pullKernelRepair_image_eq_iff_fibreSaturated`
- `no_finite_global_singleton_failureTransversal`
- `range_subset_of_hits_singleton_failureKernels`
- `card_ge_of_hits_initial_failureKernels`
- `singleton_not_triangle_failureTransversal`
- `triangle_failureTransversal_card_ge_two`
- `triangleFractionalRepair_pair_constraints`
- `triangleFractionalRepair_total`
- `no_swapInvariant_singleton_kernelRepair`
- `symmetricFractionalKernelRepair_swapInvariant`
- `symmetricFractionalKernelRepair_total`
- `failureKernelTransversal_mechanism_capstone`

## Exact formal content

1. Strong induction on finite bases extracts an inclusion-minimal derivation kernel from every
   entailing base.
2. A removal succeeds iff it hits every minimal failure kernel.
3. Every member of a minimal successful removal is the unique removed point in some live kernel.
4. Observer image and marked pullback transport transversals; image--pullback is exact iff the source
   repair is fibre-saturated.
5. Triangle kernels require integral repair cost at least two, while the symmetric fractional repair
   has cost `3/2`.
6. A two-point swap has no invariant singleton repair but fixes the half--half fractional repair.
7. Hitting the first `n` singleton kernels costs at least `n`; every finite removal misses a later
   singleton kernel.

## Verification

- Direct foreground elaboration:
  `lake env lean GaloisForLFunctions/HTGeometry/ConstitutiveFailureKernelTransversal.lean`
- Formal lint:
  `python3 scripts/formal_tools.py lint`
- Final umbrella audit:
  `lake build GaloisForLFunctions.HTGeometry.UniversalLawField`
- Axiom audit uses a temporary `/tmp` file and `#print axioms` for the capstones.  It reports only
  Lean/mathlib foundations (`propext`, `Classical.choice`, `Quot.sound`) and no project axiom.

## Scope

This certifies a route-independent finite revision mechanism.  It does not prove that RH route
obstructions form presentation-invariant failure kernels, construct a cross-route transversal, or
imply RH.

## Log

- 2026-08-10 -- direct elaboration and formal lint passed; module wired into umbrella.
- 2026-08-10 -- final umbrella build and axiom audit passed.
