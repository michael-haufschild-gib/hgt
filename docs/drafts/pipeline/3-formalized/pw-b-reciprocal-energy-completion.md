# PW-B reciprocal-energy completion

- **ID:** PW-B-RECIPROCAL-ENERGY-COMPLETION
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** ../1-in-progress/rh-current-frontier-map.md · PW-B fixed-grade partner-balance edge
- **Statement:** Every inversion-closed extension of finite physical energy support contains the minimal reciprocal completion and its infinite reciprocal tail; the forced reciprocal map realizes the two Mellin-grade reflection identities globally.

## Goal

Discharge the geometric support burden exposed by the finite-energy local-reflection no-go in the PW-B chain:

`completed reciprocal-energy seam -> physical CTP reverse -> fixed-grade partner balance -> shared Deninger/FZZ equilibrium -> RH`.

## Gates

- [x] 0 → 1 in-progress: finite local no-go’s exact reciprocal-rigidity survivor identified from corpus.
- [x] 1 → 2 fully-proven: completion minimality, forced-tail, and global realization proved below.
- [x] Lean source proof: `RHTower.pwReciprocalTail_forced` and `RHTower.nonempty_PWGlobalReciprocalFEReflectionData` elaborate with `lake env lean`.
- [ ] Final artifact audit: final leaf build and `#print axioms` are deferred because Lake artifact closure is stale and expands beyond permitted audit scope.
- [ ] 3 → 4 publication-ready: support theorem only; it does not prove a physical seam or RH.

## Proof

The required finite-energy two-grade reflection fixes the local map to `x ↦ x⁻¹`. If an extension contains `(0,X)` and is closed under this map, then it contains every `y>X⁻¹`, because `y⁻¹∈(0,X)`. The explicit global datum `energyMap=weight=x⁻¹` preserves positivity and satisfies both grade-one and grade-two equations. `[PROVED HERE]`

## Consequence

- **Discharged premise:** the support geometry of any spectrally independent reciprocal completion is now exact, including a minimal completion and a constructive global model.
- **Remaining hard premise:** derive this completion as a literal Hawking closed-time-path source seam while preserving the finite-energy contact terms. The theorem does not identify a physical source extension, establish functional-equation reflection at all complex grades, or claim partner balance.
- **Status:** dependency-closed Lean source theorem in `GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspHawkingParikhWilczekReciprocalCompletion.lean`, wired into `RHTower.lean`.

## Log

- 2026-09-15 — reciprocal support-completion geometry formalized.
