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
- [x] Sum the actual character-coordinate cusp identities and match the unit-period top current and physical tail mass.
- [x] Prove the integrated arithmetic seam bound for the complete glued energy balance.
- [ ] Derive the required uniform bulk comparison from the actual source and arithmetic phase structure.
- [x] Scratch/source/final-module/axiom/index/wiring/lint audits and process cleanup for finished modules.

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
- `formal/GaloisForLFunctions/RHTower/SelbergMaassCharacterCuspGlue.lean`:28 public declarations; exact physical flux/mass normalization, full core–cusp gluing, original residue Fourier form, and integrated arithmetic seam control.

All four complete scratch files and exact source checks have passed. Only the Dynamics olean was emitted before final audits, as the needed dependency of the other checks. The finite assembly is complete. The source-derived uniform quarter comparison remains in progress.

## Audit certificate — 2026-09-09

Serialized final builds rebuilt only their named target: `lake build GaloisForLFunctions.RHTower.SelbergMaassCharacterDynamics` (13s), then `lake build GaloisForLFunctions.RHTower.SelbergMaassCharacterCoreGreen` (10s), then `lake build GaloisForLFunctions.RHTower.SelbergMaassReadoutCusp` (21s). All52 public declarations passed the post-build `/tmp` axiom audit with only standard `propext`, `Classical.choice`, and `Quot.sound`. No source hash changed during the audit.

All three modules are wired once into `RHTower.lean`. Exact-module search and API coverage includes all52 public declarations; the index has58 entries including three local instances and three private zero-function helpers. Index refresh and repository formal lint passed with existing large-file warnings. Every task-owned Lean/build/index/lint handle is terminal; the final process scan found no task-owned Lean/Lake worker. No build overlap, full/umbrella build, numerical experiment, commit, or push occurred.

Cycle48 artifacts: `/tmp/selberg_core50_manifest.json`, `/tmp/selberg_core50_audit.json`, `/tmp/selberg_core50_coverage.json`; complete scratch, source, final-build, axiom, index, and lint logs share that prefix. The finite assembly was subsequently completed in cycle49 below. This card remains in progress because the quantitative full quarter comparison is still required.

## Positive proof loop — cycle49

Broad explicit-OR corpus discovery for gluing, interface, transmission, current, and periodic returned9771 declarations across2366 modules (`/tmp/selberg_glue51_corpus.json`). All matching index metadata was retrieved; this is not a claim to have read every proof body. The actual congruence trace mass normalization, physical pairing integral, periodic current, and finite trace core/cusp assembly supply the concrete mechanism below.

Conjecture → proof: observing every coordinate of an actual upper-character projection preserves its full physical mass and vertical current, with `sum_q readoutFlux_q(Y)=topCurrent_r(Y)/2`. The checked proof sums literal squared coordinate masses, uses actual period-one mass transport to remove the level normalization, and differentiates that equality at positive height. The original pairing product rule gives twice the total readout flux. Differentiation of the unit-strip mass gives its literal vertical current; current periodicity then shifts the interval to the core top. Every tail is genuinely integrable by the proved zero-or-Maass observation theorem, including zero observations. The finite tail integral exchange identifies their sum with the literal physical character tail mass. Summing the complete cusp identities cancels the cutoff current and retains the curved seam. No boundary sign, spectral endpoint, or coercivity premise is introduced.

The complete flux normalization, original tail integrability/identification, cutoff cancellation, projected-vector boundary form, and exact residue-mode formula have now passed the complete scratch check. The resulting identity at height1 is

`coreQuarter_r + boundarySum_r + squareSum_r - (lambda-1/4)*(coreMass_r+tailMass_r) = integral(pairedArcCurrent_r)/2`.

Second conjecture → proof: integrate the actual phase-current inequality without losing its physical normalization. The AND corpus query for integral, square, and current returned5 declarations in4 modules; inspected `SelbergWeightedPathEnergy.integral_square_completion` and its resistance-energy proof. Square completion on the actual half-length arc gives `(integral J)^2 <= (integral J²)/2`. Combining this with the already proved `J² <= (16/3)*loss*gradient` yields `(integral J/2)^2 <= (2/3)*integral(loss*gradient)`. Hence the full glued balance has this same original arithmetic loss–gradient bound. Actual source continuity proves the needed arc integrability. Its right side is a literal boundary integral; no trace-to-area comparison or spectral quarter constant is assumed. The complete strengthening passed scratch, source, final-module, and axiom checks.

## Cycle49 audit and remaining target

`lake env lean /tmp/selberg_glue51.lean` and the exact source check passed. The serialized final command `lake build GaloisForLFunctions.RHTower.SelbergMaassCharacterCuspGlue` rebuilt only that module (6.8s). All28 public declarations passed the post-build `/tmp` axiom check, with only standard `propext`, `Classical.choice`, and `Quot.sound`. The source hash remained unchanged; its umbrella import occurs once. All28 public declarations have exact-module search and API coverage (29 index entries including the local instance). Index refresh and repository lint passed; lint reported existing large-file warnings only. Every task-owned check/build handle is terminal. No full/umbrella build, build overlap, numerical experiment, commit, or push occurred.

Artifacts: `/tmp/selberg_glue51_manifest.json`, `/tmp/selberg_glue51_audit.json`, `/tmp/selberg_glue51_coverage.json`, and the scratch/source/build/axiom/index/lint logs with that prefix. The completed module is `formal/GaloisForLFunctions/RHTower/SelbergMaassCharacterCuspGlue.lean`.

Next mathematical target: use the actual residue Fourier form and complete inversion phase/angular decomposition to compare the coherent boundary response with the positive physical bulk terms. The newly proved `2/3` controls an integrated seam response; it is not the spectral quarter constant. Keep the original core, all cusp modes, and both physical derivative energies. The uniform full-domain mass–gradient comparison, and therefore the full unconditional Selberg goal, remain unproved.
