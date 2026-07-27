# Atiyah-kernel projective finiteness universality law

## Status

Fully proven on paper; formalized in Lean 4; **verification gate passed**.

`lake build` succeeds on the module inside the `GaloisForLFunctions.HTGeometry` umbrella (which imports it), and `#print axioms` gives exactly `propext, Classical.choice, Quot.sound` for

```text
GaloisForLFunctions.HTGeometry.multiplierAtiyahKernel_orderOne_universal_or_projectivelyFinite
```


## Theorem-first source

- `multiplierAtiyahKernel_mk_mem_projectiveDirectionalFiniteLawLocus_one`:
  every nonzero multiplier Atiyah-kernel direction belongs to the order-one projective finite-law
  locus.
- `projectiveDirectionalFiniteLawLocus_finite_fin2`:
  every proper finite-law stratum in a two-dimensional projective law space is finite.

Whole-corpus search found both ingredients but no theorem closing their shared projective object.

## Universal law

For every compatible two-direction equivariant multiplier system, exactly the following forced
phase split holds:

1. the order-one finite-law locus is all of the projective line; or
2. the projectivized zero locus of the multiplier Atiyah-class map is finite.

The statement is universal in the acting group, the three coefficient fields, compatible group
actions and derivations, multiplier cocycle, and multiplier vector.

## Paper proof

Let `Z` be the projectivized multiplier Atiyah kernel and `L₁` the order-one projective finite-law
locus.  The pointwise Atiyah theorem gives `Z ⊆ L₁`: use the canonical nonzero representative of
each projective point and apply the kernel-inclusion theorem.  If `L₁` is universal, the first
alternative holds.  Otherwise the binary-projective theorem says `L₁` is finite.  Its subset `Z`
is therefore finite.

## Lean formalization

- Module:
  `GaloisForLFunctions.HTGeometry.AtiyahKernelProjectiveFinitenessUniversalityLaw`
- Theorem:
  `GaloisForLFunctions.HTGeometry.multiplierAtiyahKernel_orderOne_universal_or_projectivelyFinite`
- Exact check:
  `lake env lean GaloisForLFunctions/HTGeometry/AtiyahKernelProjectiveFinitenessUniversalityLaw.lean`
  passed on 2026-07-22.

## Novelty audit

Pending literature audit after theorem-generation phase.  Corpus audit is negative: no pre-existing
closure theorem combines the multiplier Atiyah kernel with binary projective-stratum finiteness.
