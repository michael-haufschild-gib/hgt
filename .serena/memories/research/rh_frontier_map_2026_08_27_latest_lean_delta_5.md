# RH frontier map — 2026-08-27 Lean delta 5

Target: `docs/drafts/pipeline/1-in-progress/rh-current-frontier-map.md`.
Baseline HEAD during audit: `f715d7f3df8746d307867834b37554223e6d3e95`.
User requires Lean-only corpus search via `scripts/formal_tools.py research`, no route cards/literature, no builds, no diary/history structure, no subagents.

Ledger remains 24 live branch labels and 35 candidate interface labels. No independent route added.

Lean-derived changes folded in:
- HB: physical regular/complementary horizon incidence, rank-one Green response, and exact physical horizon selector are closed. Selector vanishes copywise iff critical line and universally iff RH. Same-frequency physical ingoing/outgoing Green equality is false on every Xi fibre. Source-scaled polarized current equals squared source amplitude times canonical current and equals AdS boundary concomitant; Peierls candidate is twice it and has exact critical-line zero locus for nonzero seed. FE reflection also cannot cancel: chi maps to -chi+i/2, exponents add to 8n+5, unscaled currents add to -(8n+5). Exact open core: prove actual augmented source Peierls incidence in one time-oriented skew propagator with conjugate-frequency endpoint/counterterm and left-QNM sewing, then pre-specialization global equality/simultaneous solvability.
- Matomäki--Teräväinen/Harman sieve: divisor Rankin/Euler bound and discarded c1 tail mean square (up to final external parameters); c2 prime-window mean square from reciprocal mass; Mertens exponential error gives 6Yδ on high (1+δ) windows; log-power schedule gives eventual 6Y(log u)^(-K) for every fixed K>=0. This is unsigned infrastructure for E/T1, not a route: no fixed E relation, signed Hall/co-moving flux, T1 Weil landing, or Xi/RH endpoint.
- Abelian zeta gas: exact Kolmogorov q-Gamma product and finite cutoff laws survive; no deterministic centered cutoff converges a.s. for 1/2<sigma<=1, and existing weak-limit no-go also applies. Ordinary centered infinite-socle completion terminal.
- Milnor K2 Bruhat pair: explicit left/right diagonal, upper, simple-Weyl actions; all left/right commutations except Weyl--Weyl. Removes local transport ambiguity only; global reciprocity and Xi occurrence remain absent.
- Terminal table updated for same-frequency/reflected-current Hawking selection, centered zeta-gas socle limit, and finite ABHN/Bruhat landing.

Validation:
- `git diff --check` clean.
- ledger 822 lines (<4000).
- live-branch table count remains 24.
- no Lean build/lint run because documentation-only task.
- concurrent user/agent edits outside target preserved. Concurrent Lean files during audit included HB Peierls landing and sieve PrimeWindowMertensMass, PrimeWindowAdicMeanSquare, PrimeWindowLogPowerSchedule.
