# CHMD odd cone: exact prime cross-sign split and the window identity

- **ID:** chmd-odd-prime-cross-sign-split
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** user directive 2026-10-17 (Step A, two-leg quadratic level) · STATUS MUST-1572
- **Statement:** For odd `v ≥ 0` on `[0,∞)` with compact support and `g = Θ|v|`:
  `−∫ phiDoobPrimeCross v n = 2(Λ(n)/√n)∫_0^{log n} g(s)g(log n − s) ds − 4(Λ(n)/√n)∫_0^∞ g(s)g(s+log n) ds`.
  On `supp v ⊆ (−L/2, L/2)`, `L ≤ 2 log 2`: `E(v) = Λ_∞(g) + 4·bonus(g) + B₂(g) + B₃(g)`, the last three nonnegative.

## Goal
Sharpen MUST-1562/1565 (cross terms merely dropped as `≤ 0`) to an exact identity exposing the
positive prime channels of the primes `2` and `3` on the window.

## Gates
- [x] 0 → 1, 1 → 2 (paper proof: split at `−log n`, `0`; fold by evenness)
- [x] 2 → 3: `RHTower/CHMDOddPrimeCrossSignBonusAndWindowPositivity`, `lake env lean` clean, `lake build --old` olean,
  standard axioms, wired
- [ ] 3 → 4 not pursued

## No-go closure
Not a no-go. Open: positivity of `Λ_∞(Θ|v|) + 4·bonus + B₂ + B₃` on the window `L ≤ 2 log 2` (true under RH since
odd tests are primitive; unconditional proof would need the window programme's sharp archimedean kernel analysis
with the prime channels added; crude Fourier/uncertainty bounds lose factors of order 100).

## Log
- 2026-10-17 — created in 3-formalized; STATUS MUST-1572.
