# Window jump counts through `log 3` and naive heights on `ℤ[ℚ_{>0}^×]`

- **ID:** WJCH
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** docs/reports/review-0211/obstacles-summary.md §2.5.1 (Q1, steps 1–2) and §2.6.1 (B20, B32)
- **Statement:** (1) On window tests of length `A ≤ log 3` (`a = A/2 ≤ ½ log 3`), express Weil's quadratic form `Q(H)` by an identity whose terms are Lévy jump counts, jump/graph counts attached to `n = 2` (`T₂`), and manifest squares, proving `Q(H) ≥ 0`. (2) Construct for every window length `A` a count `h_A` on window tests with `h_A(H) = ½ Q(H)` up to manifest squares, equivalently a nonnegative naive height `h` on `ℤ[ℚ_{>0}^×]` within `C_x` of `τ_x(ξ ⋆ ξ′)` on every cycle.

## Goal
Resolve §2.5.1 (`A ≤ log 3` count-and-square identity and Weil positivity across the entire single-prime window) and §2.6.1 (all-window count `h_A` / naive height on `ℤ[ℚ_{>0}^×]`), and unconditionally formalize the resulting theorems and their corollaries in Lean 4.

## Gates
- [x] 0 → 1  in-progress: exact mathematical statements fixed, corpus buildings mapped
- [ ] 1 → 2  fully-proven: complete dependency-closed paper proofs
- [ ] 2 → 3  formalized: Lean 4 modules checked cleanly with `lake --old env lean`, standard axioms verified, wired into umbrella modules

## Approach
1. **Single-prime window (`A ≤ log 3`, `a = A/2 ≤ ½ log 3`):**
   - Recenter `H = e^{y/2} h` supported in `[−A, 0]` to `F(u) = H(u − A/2)` supported in `[−a, a]`, `a ≤ ½ log 3`, and split orthogonally into `F = F_even + F_odd`.
   - Only `n = 2` has a non-departing prime jump (`2a ≤ log 3 < log 4`, and at `n = 3` the shift `log 3 ≥ 2a` leaves `(−a, a)`).
   - Construct exact algebraic decompositions of `fullZeroForm F_even` and `fullZeroForm F_odd` on `[−½ log 3, ½ log 3]` into nonnegative-weight archimedean Lévy jump squares, `T₂`-graph jump/reflection squares on the strip `[log 2 − a, a]`, and manifest squares (including `+½ coshPairing(F_even)²` on the even sector and gauge-transformed jump/potential squares on both sectors).
2. **All-window counts (`h_A`) and naive heights on `ℤ[ℚ_{>0}^×]`:**
   - Use the exact `{∞, 2}` window decomposition at `A ≤ log 3` to formulate and test multi-prime (`n ≤ e^A`) count/log-count/sum-of-squares candidates against all proved obstructions (`goldenDatum`, `liouvilleTwin`, shifted pair `ζ(s−a)ζ(s+a)`, Epstein boosts, bounded-rank lattices, bidegree blindness).
