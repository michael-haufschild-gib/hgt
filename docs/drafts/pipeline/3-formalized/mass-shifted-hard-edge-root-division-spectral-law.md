# Mass-shifted hard-edge root-division spectral law

- **ID:** `mass-shifted-hard-edge-root-division-spectral-law`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** hard-edge Cauchy system `HHWB.16`--`HHWB.19`
- **Statement:** Distinct root deletions of one radical state are pairwise orthogonal; repeated
  root deletion is isotropic and, under positive semidefiniteness, enlarges the radical.

## Scientific result

For symmetric bilinear form `B`, `B`-self-adjoint coordinate `T`, and radical vector `f`, every
family

```text
(T - root i) (deleted i) = f
```

with injective root labels is pairwise `B`-orthogonal. A two-step chain at one root has isotropic
middle vector; positive semidefiniteness promotes it into `ker B`.

The literal polynomial moment specialization proves the same statements for factors
`(X-C r) * q = f`. Strict positive moment admission therefore excludes any nonzero repeated
root-deletion chain.

Applied to hard-edge `F/(u-r)`, this classifies root division as spectral information, not an
independent arithmetic source law: simple roots generate orthogonal positive descendants, while a
multiple root forces kernel enlargement.

## Lean certificate

Module: `GaloisForLFunctions.HTGeometry.NullRootDivisionSpectralLaw`

Capstones:

- `rootDeletion_orthogonal`
- `rootDeletion_pairwise_orthogonal`
- `repeatedRootDeletion_isotropic`
- `repeatedRootDeletion_mem_ker`
- `momentInner_rootDivisions_orthogonal`
- `momentInner_repeatedRootDeletion_isotropic`
- `no_repeatedRootDeletion_of_positiveMomentForm`

## Verification

- Direct `lake env lean` check: passed.
- Targeted `lake build GaloisForLFunctions.HTGeometry.NullRootDivisionSpectralLaw`: passed.
- Axiom audit: only `propext`, `Classical.choice`, `Quot.sound`.
- Forbidden declaration scan: clean.
- Umbrella: imported by `GaloisForLFunctions.HTGeometry`.

## Route consequence

Static root division cannot close §9.3's hard edge. It diagnoses simple versus multiple ground
edge kernel. Remaining live datum is cross-aperture/current-admission transport on the bounded
relative mass scale isolated by the companion in-progress card.

## Log

- 2026-08-11 — paper algebra and polynomial moment specialization proved.
- 2026-08-11 — unconditional Lean formalization, target build, and axiom audit passed.
