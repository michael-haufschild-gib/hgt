# Source computability of the horizontal-collision carriers

- **ID:** hc-carrier-source-computability
- **Stage:** 1-in-progress
- **Type:** CANDIDATE (no-go)
- **Source:** docs/reports/review-3010/opus.md §3, §7
- **Statement:** A carrier computable from explicit formulas (finitely many holomorphic clocks and Weil forms) cannot
  be quantized: vanishing on all critical configurations forces vanishing on all admissible configurations.

## Goal
Decide whether the quantized horizontal-collision endpoint (RH ⇔ collision charge < 2) gives a producer route, or
reduces to a known wall. Kill: every carrier is (1) source-realizable but unquantized (Π via explicit formula),
(2) zero-indexed and non-holomorphic (zero density / spectral realization), or (3) Weil-type with a test vanishing
on the real zeros (theta completeness). Meat: one carrier that is source-computable and keeps a finite quantum.

## Gates
- [ ] 0 → 1  in-progress: well-posed, attack idea
- [ ] 1 → 2  fully-proven: complete paper proof of the no-go and its quantitative survivor
- [ ] 2 → 3  formalized: Lean theorems, file check green, standard axioms only

## Approach
1. Classify each `XiHorizontalCollision*` carrier: zero-side summand holomorphic in ρ? genuine source formula?
   quantum on the source side?
2. Paper proof: holomorphic linear and sesquilinear carriers vanishing on critical configurations vanish on all
   admissible configurations (identity theorem plus the involution ρ ↦ 1 − ρ̄); quantitative three-lines tradeoff.
3. Finite height X ≤ T^θ: prime-side statement; compare with Π.
4. Selection: Davenport–Heilbronn and Beurling zero sets.
5. 𝔽_q calibration.
6. Census salvage: depth sensitivity f(δ log X).

## Log
- 2026-10-30 — created in 1-in-progress
