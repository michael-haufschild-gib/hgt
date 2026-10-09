# A universal bound for normalized disk embeddings

- **ID:** NORMALIZED-EMBEDDING-DISK-BOUND-20261009
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean verified)
- **Parent:** `../1-in-progress/normalized-embedding-local-compactness.md`.
- **Lean:** `formal/GaloisForLFunctions/HTGeometry/NormalizedEmbeddingDiskBound.lean`.

## Statement

There is C>0 such that for every R>0 and every holomorphic f on D(0,R), injective there with derivative nonzero throughout, f(0)=0 and f′(0)=1, one has |f(z)|≤CR whenever |z|≤R/2. The proof also supplies an omitted value a with |a|<2R.

## Complete paper proof

If D(0,2R) lay in the image, the existing analytic inverse g would map that disk to D(0,R). It fixes zero and has derivative one there, by differentiating f∘g=id. The installed Schwarz derivative bound instead gives |g′(0)|≤1/2. Thus there is an omitted a with |a|<2R. The checked one-center-fiber omitted-value theorem supplies universal B>1 and |f(z)−a|≤B|f(0)−a|=B|a| on the half disk. The triangle inequality gives |f(z)|≤(B+1)|a|≤2(B+1)R. Set C=2(B+1).

The proof uses the exact nonzero-derivative premise of `Bottcher.imageInv_analytic`; it does not claim that premise has been removed.

## Audit and scope

**BRIDGE.** This supplies the initial chart bound in the active exhaustion compactness argument. It does not construct an exhaustion of the actual Xi surface or prove intrinsic uniformization. External novelty remains unverified under the user's no-web restriction.

Scratch check, production leaf build, both public-declaration standard-only axiom audits, and final actual-source `lake env lean` all pass. Final source log is empty. Wired into `HTGeometry.lean`; index refresh passed. Global lint reports seven unrelated unreachable modules and no own-module or forbidden-declaration errors.

Logs: `/tmp/hgt-NormalizedEmbeddingDiskBound-build.log`, `/tmp/hgt-normalized-embedding-axioms.log`, `/tmp/hgt-normalized-embedding-final.log`, `/tmp/hgt-normalized-embedding-index.log`, `/tmp/hgt-finite-end-approximation-lint.log`.
