# IRK: charged arithmetic source and projective lift

- **ID:** irk-charged-source-projective-lift-2026-10-17
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** read-only IRK entry in `docs/reports/rh-current-frontier-map.md`
- **Statement:** [OPEN CORE] Construct a global arithmetic rotation source realization retaining the actual Xi boundary defect, with a derived integral analytic count.

## Goal

Remove a genuine source-construction obstruction in IRK. An estimate, trace coordinate receiver, or renamed RH equivalence does not qualify. This turn concerns IRK only; earlier thread attempts concerned XN and HF and were not credited as qualifying advances. The full 44-route objective remains open.

## Evidence and plan

1. Inspect current Lean source and search the corpus. No external sources or old research Markdown.
2. State and attack a precise source construction. Preserve the clock correction: the existing untwisting theorem transfers all isolated dipole charge to the removed correction.
3. Write a dependency-closed paper proof before implementing any surviving theorem.
4. Formalize without extra analytic hypotheses, axioms, computations, or heartbeat changes. Check only owned modules, one foreground Lean process at a time.
5. Audit every new public theorem's axioms, wire finished modules, run formal lint, clean owned scratch, and state the remaining gap honestly.

## Current source facts

- `PrimeRotationXiRelativeKTwo`: literal relative K2 source, exact multiplicity boundary, composition correction, and charge loss under untwisting.
- `PrimeRotationCanonicalTraceIntegrality`: integral traces of actual finite prime-Weyl matrix idempotents, without a Xi projective realization.
- `PrimeRotationXiDeterminantSource`: full source jet relation determinant has the actual Xi multiplicity and agrees with Xi in the marked tame quotient.
- `PrimeRotationXiBoundaryHomotopy`: explicit invertible boundary homotopies distinguish the two sides of the critical line; quantum transgression remains separate.
- Broad deep research returned no useful exact hit. Coverage was complete at the source inventory level, but compiler metadata was mostly pending/stale; no suggested lemma is accepted without inspecting source and checking Lean.

## Gates

- [x] Source-pure problem selected; frontier map untouched.
- [ ] Dependency-closed paper proof of a new obstacle-removing theorem.
- [ ] Formalized and audited.
- [ ] Meets user's significant-frontier-contribution criterion.

## Log

- 2026-10-17 — IRK selected. No claim that existing local boundary identities construct the missing global projective lift.
