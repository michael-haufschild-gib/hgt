# Original characterwise core Green identity with coherent seam current

- **Stage:** 1-in-progress
- **Type:** POSITIVE ORIGINAL-SOURCE ENERGY DECOMPOSITION
- **Goal:** Derive the integrated characterwise core energy identity with its actual circular current, then attach the complete cusp form without discarding modes or boundary contributions.

## Evidence and conjecture

Revalidated both cycle47 source hashes unchanged. Previous goal turn completed29 audited positive declarations and is classified progress. Explicit OR corpus discovery for Green identity, boundary form, Dirichlet-to-Neumann, and impedance returned197 declarations in78 modules (`/tmp/selberg_core50_corpus.json`). Read the actual modular potential Green formula, original trace core/cusp energy identity, and full actual Bessel boundary-square identity. The inspected pinned-boundary inertia result suggests retaining the exact boundary quadratic form before making a positivity claim; its theta-specific hypotheses are not Maass input.

For actual upper character r, let M_r=||P_r F||² and E_r=||P_r D_x F||²+||P_r D_y F||². Positive conjecture:

`integral_core (E_r-lambda*M_r/y²) = (topCurrent_r + pairedArcCurrent_r)/2`.

Every term is an original source quantity. Upper-block translation commutes with P_r and the unitary action cancels in mass/current pairings, proving the side condition. The existing horizontal-area identity retains the curved arc term; vertical FTC retains top minus bottom. Their sum is exactly the normal-density current already bounded in cycle47. No characterwise inversion cancellation is imposed.

The original projected field retains C² regularity and the same scalar Maass potential because a fixed finite linear map commutes with both real coordinate derivatives. The norm-square Laplacian identity then gives `Delta M_r=2(E_r-lambda*M_r/y²)`. All geometric and smoothness conditions in the corpus Green lemma must be discharged from the literal source, not left as new analytic premises.

## Loop and gates

- [x] Revalidation and corpus-derived paper candidate.
- [x] Actual projected-source derivative and Laplacian identity.
- [x] Actual upper-character translation/current matching.
- [x] Integrated original core energy identity retaining full circular current.
- [x] Derive the complete cusp form and flux identity for every actual linear observation, including zero components and convergence of both series.
- [ ] Sum the actual character-coordinate cusp identities, match the unit-period top current, and test the resulting full quarter comparison.
- [ ] Scratch/source/final-module/axiom/index/wiring/lint audits and process cleanup for finished modules.

The full Selberg goal remains active. Neither the spectral quarter bound nor an assumed boundary positivity is an input.

## Positive proof loop — cycle48

**Derivative conjecture → proof.** The complete source chart is C². Composition with an actual continuous linear observation commutes with its first derivative. The same equality on a positive-height neighborhood allows a second differentiation. Applying coordinate observations to the original component equations proves the vector equation, and applying any fixed observation preserves the original scalar potential. This includes zero observations. The original projected-field norm-square Laplacian then retains both physical derivative squares. Their complete finite sum gives `Delta M_r=2(E_r-lambda*M_r/y²)`.

**Side-matching conjecture → proof.** The complete block is commutative, so its character projector commutes with every actual block unitary. Integer parameter one is the actual class of T. Original source and derivative transport under T, followed by unitarity, preserves character mass and each physical mass current. This discharges the corpus Green formula's side-matching condition from the original source.

**Core conjecture → proof.** Horizontal area integration retains the exact curved boundary contribution. Vertical integration retains top minus bottom. Reflection folds the lower current into paired points. The resulting term is exactly the literal outward normal current from cycle47, with tangent `(-x/y,-1)` and its arc-length factor. Thus

`integral_core Delta M_r = topCurrent_r + integral_0^(1/2) pairedArcCurrent_r`.

Actual C² regularity and compact-domain geometry prove integrability of the mass, Laplacian, and physical quarter form. The exact source potential gives

`coreQuarter_r = topCurrent_r/2 + (integral pairedArcCurrent_r)/2 + (lambda-1/4)*coreMass_r`.

No characterwise cancellation of the circular current is imposed.

**Cusp-strengthening conjecture → proof.** Every fixed observation of the original source is invariant under the original congruence group, remains an eigenfunction with the same eigenvalue, and decays at every integral cusp. Cusp decay follows from all finitely many original coordinate limits and continuity of the observation. Hence the observed function is zero or an actual `MaassCuspEigenform` at the unchanged level and eigenvalue. Both cases are retained. This reuses the complete proved Bessel identities on a genuine original-source observation, without inventing a new cusp condition or discarding zero projections.

The complete observed physical cusp quarter integral equals its original Bessel seam series plus its full series of nonnegative mode-square integrals. Both series are proved summable. The matching identity expresses exactly the same sum as minus original observed flux plus `(lambda-1/4)` times original observed tail mass. All integer modes remain, including the explicitly handled zero mode. The positive original-source class and these exact identities supply the next finite character-coordinate assembly.

The explicit OR follow-up for projected source, linear combination, cusp condition, and eigenfunction space returned295 declarations in196 modules (`/tmp/selberg_core50_linear_corpus.json`). Inspected the actual Maass subtype, invariant-function submodule, source scalar-trace cusp proof, and original Bessel definitions; metadata coverage does not mean every returned proof body was read.

## Current Lean outputs

- `formal/GaloisForLFunctions/RHTower/SelbergMaassCharacterDynamics.lean`:18 public declarations; original projected dynamics and physical side matching.
- `formal/GaloisForLFunctions/RHTower/SelbergMaassCharacterCoreGreen.lean`:19 public declarations; original core area/current/quarter identity and integrability.
- `formal/GaloisForLFunctions/RHTower/SelbergMaassReadoutCusp.lean`:15 public declarations; actual observed cusp sources, complete boundary-square decomposition, summability, and matching flux identity.

All three complete scratch files and exact source checks have passed. Only the Dynamics olean was emitted before final audits, as the needed dependency of the other checks. The full Selberg objective is not completed by these identities; finite assembly and the source-derived uniform quarter comparison remain in progress.
