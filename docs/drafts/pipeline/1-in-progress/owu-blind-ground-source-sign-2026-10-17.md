# OWU: blind odd ground source sign

- **ID:** owu-blind-ground-source-sign-2026-10-17
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** read-only OWU entry in `docs/reports/rh-current-frontier-map.md`
- **Statement:** [OPEN CORE] Derive a nonnegative blind odd ground minimum from the actual arithmetic source, using and testing the current ground-space polynomial structure without adding a sign premise.

## Goal and plan

OWU only this turn. Earlier thread attempts: XN, HF, IRK, EGC; none credited
with the user's strict significant RH-frontier advance. Full 44-route goal
remains active. Bounds, another receiver/equivalence, and merely easier
formal wrappers do not qualify.

1. Inspect current Lean declarations and corpus search for the exact blind
   constraint, corrected ground space, and canonical generator.
2. Conjecture a source mechanism; attack circularity, loss of blindness, and
   missing positivity. Keep every arithmetic term.
3. Write a dependency-closed paper proof before new Lean code.
4. Formalize only unconditional survivors; one owned Lean build at a time,
   no computations, no axioms/debt, no heartbeat increases, no full builds.
5. Final module and axiom audits, wiring, formal lint, cleanup.

## Initial evidence and question

Frontier entry states corrected odd ground transforms have the form
`P(w²) F_G(w)`, degree below ground-space dimension, with exact finite
spectral interpolation. It also states the canonical ground factor need
not be blind. Inspect the actual domain and image of this polynomial map:
dimension arguments apply only if the entire corrected ground space obeys
the blind constraint. No such claim is assumed.

## Status

- [x] OWU selected; frontier map read-only.
- [ ] Significant obstacle-removing source construction proved.
- [ ] Exact survivor formalized and verified.
- [ ] User's strict contribution criterion met.
