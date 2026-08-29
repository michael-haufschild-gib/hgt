# Theta rank-three raw unimodality

- **ID:** S6F-RU
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** hostile S6F/TCD computation; proof must be source-pure
- **Statement:** On `0 <= x <= 137/2000`, raw reflected rank-three D1 has exactly one interior critical point, a strict maximum.

## Goal

Prove an exact one-crossing law for

```text
x ↦ thetaCuspFullSourceReflectionEighthHankelCurvature x.
```

Since raw D1 is already positive at `x=0` and native D1 is already positive at `x=137/2000`, unimodality would make the minimum occur at an endpoint and close the remaining finite S6F/TCD interval. This is a competing closure mechanism to projective-drift positivity; neither may assume computed brackets or values.

## Gates

- [x] 0 → 1 in-progress: exact source object, endpoint route, falsifiable one-crossing claim
- [ ] 1 → 2 fully-proven: source-pure one-crossing proof for raw derivative
- [ ] 2 → 3 formalized: exact derivative classifier and endpoint-minimum theorem in Lean
- [ ] 3 → 4 publication-ready: integrate with S6F/TCD cofinal landing

## Approach

Differentiate the exact raw modular closure once, obtaining the order-nine source-orbit polynomial. Search for a strictly monotone ratio or sign-changing clock whose unique crossing determines raw derivative sign. A direct proof needs only “at most one zero and positive-to-negative orientation”; it does not need the critical point's location.

## Hostile audit

- Dense computation reports one raw-derivative sign-change bracket and raw minimum at seam. This selects the conjecture but is not a proof.
- Simple raw monotone increase is incompatible with the observed endpoint-side derivative sign and should not be pursued.
- Projective normalization removes the observed raw maximum and gives a different candidate, recorded in `theta-rank-three-projective-drift.md`.
- First kill tests: certify whether raw derivative has further near-multiple zeros; derive endpoint derivative signs symbolically; test the one-crossing claim outside physical orbit and against known negative universal seam states.

## Open core

Find an exact source-derived one-crossing invariant for the raw order-nine derivative. If no such invariant exists or more than one critical point occurs, retire this card and retain projective drift as the primary finite-gate attack.

## Log

- 2026-08-29 — created after second-pass computation audit exposed raw-unimodality as a distinct endpoint proof strategy.
- 2026-08-29 — Follow-up dense scan at 2,000,001 points again found exactly one sampled raw
  derivative sign change, now bracketed by `[0.0544456495, 0.05444568375]`, and one sampled raw
  second-derivative sign change near `0.03041768`. Arb proves a positive derivative chamber before
  the candidate maximum and a negative chamber after it but does not isolate uniqueness. Raw
  monotonicity is therefore rejected; one-crossing/unimodality remains the exact source-pure target.
