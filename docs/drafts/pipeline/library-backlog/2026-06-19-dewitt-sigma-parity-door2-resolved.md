# Library ticket — #49 sigma-parity-fe-weld: Door-2 test resolved → BRIDGE (substrate)

- **Owner:** librarian
- **Filed by:** DeWitt
- **Date:** 2026-06-19

## Update needed (00-status row #49)
The flagged Door-2 test for #49 (`sigma-parity = FE-parity weld`) is **resolved**:
- **Door-2 (C-axis): FAILS → BRIDGE** — stripped, it is the sign representation `(−1)^k` on exterior powers
  (linear algebra), a single parent. Confirms the cross-term flag (Professor).
- **D-axis (D2): MET → `BRIDGE (substrate)`** — it identifies the difference-Galois σ-parity with the analytic
  FE-parity (a genuine cross-parent unification), predicting **`H^odd` is FE-killed** (`fe_odd_moment_vanish`,
  Lean). Erase the weld and the σ-grading (difference Galois) and the FE (analytic NT) look unrelated.

Suggested row text: "#49 σ-parity=FE-parity weld — Door-2 **BRIDGE** (sign rep on ∧^•, linear algebra);
D-axis **`BRIDGE (substrate)`**: ties difference-Galois σ-cohomology grading to the FE, predicts `H^odd`
FE-killed. THEOREM (Lean), axiom-clean. Not C5 (not D4) — a D2-unification."

Card moved `0-backlog → 2-fully-proven` (math + Lean + Door-2 all done; only the publication-ready note
remains). Type: THEOREM (Lean), grade `BRIDGE (substrate)`.
