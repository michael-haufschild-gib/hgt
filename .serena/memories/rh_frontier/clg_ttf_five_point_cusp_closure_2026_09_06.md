# CLG/TTF: actual equispaced five-point cusp closed

Extends `mem:rh_frontier/clg_ttf_global_d1_rank_three_mixture_2026_09_06`.

## Current result

`RHTower.exists_thetaCuspCenterMixedGramFiveEquispaced_posDef_punctured` in `formal/GaloisForLFunctions/RHTower/ThetaCuspCenterMixedFivePointCusp.lean` proves: for every 0<a<1/2, exists δ>0, for every h≠0 with |h|<δ, the literal center-mixed density Gram matrix on 0,h,2h,3h,4h is Matrix.PosDef. Positive-spacing corollary also supplied. Every source sign and regularity input is discharged. This closes D3 after global native D1 and strict actual rank-three mixing.

## Proof mechanism

`formal/GaloisForLFunctions/HilbertMetric/FivePointFiniteDifferenceCusp.lean` gives a generic C8 theorem. Central finite-difference basis of orders 0,1,2,3,4 separates the even 0/2/4 and odd 1/3 blocks. Exact seven stencil-moment proofs plus Taylor's theorem yield an entrywise limit. Limiting even block is Hankel(J0,J2,J4,J6,J8), odd block [[-J2,-J4],[-J4,-J6]]. Existing positivity and new D1 mixture make both strict. `GaloisForLFunctions.HTGeometry.posDef_eventually_of_tendsto` gives strict nearby normalized matrices. An exact quadratic-form congruence with an injective coordinate map returns the literal five-node matrix. Only C8 regularity needed; do not build redundant C12 or all-order smoothness for this cusp.

## Integration correction

The prior new `HedenmalmCenterMixedEighthHankelClosure` originally repeated four declarations already in `ThetaCuspCenterMixedFourPointOddParityCusp`. Removed duplicate seventh/eighth jet definitions and their HasDerivAt declarations. New mixture module now imports that existing four-point module, retains its new iteratedDeriv 7/8 identities and rank-three mixture proof. Both the corrected mixture and actual five-point capstone passed direct Lean; their combined import no longer collides. A text scan of all 31 public names across six new modules found no outside duplicates.

## Evidence

Scratch and production `lake env lean` checks pass. Only needed new oleans generated. New five-point physical capstone axiom audit: [propext, Classical.choice, Quot.sound]. No old theorem audits repeated; the new capstone covers its corrected mixture dependency. Formal lint passes; indexes refreshed; both new modules wired into area umbrellas. No umbrella/full build. An initial lint failure was an unrelated concurrently unwired MobiusDivisorAbelHomothety; its owning work wired it, then gate passed. No modification to that module by this task.

## Remaining RH chain

Completed theta source -> Xi Bezoutian -> EVERY finite two-channel Weil packet PSD -> RH. Global native D1, actual rank-three center mixing, and local equispaced rank-five cusp now closed. General configurations, higher packet ranks, actual theta-to-divisor incidence and cofinal no-escape remain. Do NOT infer all-packet positivity or RH from the cusp or from generic complete reflected-Hankel signs; corpus no-gos retain their scopes. Separate C5 fronts remain open.

Current documentation: `docs/drafts/pipeline/3-formalized/clg-ttf-five-point-cusp.md`, the two earlier D1/mixture cards, frontier map, tcd-hard-core-status, and top/D2/D3 sections of theta-center-mixed-five-point-cusp notebook updated. Universal STATUS not changed: no new route-independent rule needed.

User efficiency instructions persist: one foreground Lean process per agent, no full or umbrella builds, only necessary oleans, audit only newly created capstones, clean scratch/processes. No commit/push requested or performed. Goal remains active; RH unproved.