2026-08-17 literal-monotonicity audit and formal closure.

New module:
- formal/GaloisForLFunctions/HTGeometry/StaticLocalComplexityMonotonicityRigidityLaw.lean
- umbrella-wired in HTGeometry.lean.

Proved:
1. Empty circuit gives nested operator two-gate complexity zero at t=0 and exact return R_L.
2. Any MonotoneOn complexity history on [0,R_L] collapses identically to zero; dual for AntitoneOn.
3. Existing laboratory ramp is at least 8, and every lab time precedes R_L.
4. Therefore actual complexity strictly rises from zero at t=0 and strictly falls back to zero at R_L; full-cycle history is neither nondecreasing nor nonincreasing.
5. For s,t both in laboratory window, if t >= 1024*pi*s then actual infimal complexities satisfy C(s) <= C(t). This is actual-complexity ordering, not merely envelope ordering.

Important boundary:
- Full all-pairs monotonicity for arbitrary lab times s<=t remains open. Corpus has no cost-nonincreasing circuit comparison map and envelopes alone cannot prove nearby-time comparison.
- Do not claim global monotonicity; exact recurrence forbids it.
- Brown-Susskind second-law picture is conjectural/probabilistic, not deterministic pointwise monotonicity.

Verification:
- Targeted lake env lean and targeted lake build pass.
- Axiom audit only propext, Classical.choice, Quot.sound.
- Project lint only two unrelated pre-existing RHTower reachability errors.
- No full umbrella build run.

Cards:
- Stage3 static-local-complexity-monotonicity-rigidity-law.md
- Stage1 nested-static-local-literal-complexity-monotonicity.md remains open for all-pairs lab claim.
Paper theorem/proof/abstract/claim trace updated; PDF 22 pages compiled and affected pages visually clean.