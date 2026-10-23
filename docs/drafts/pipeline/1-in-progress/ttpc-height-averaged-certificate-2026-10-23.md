# TTPC: height-averaged rank–trace certificate

- **ID:** ttpc-hac
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** formal/GaloisForLFunctions/TransThresholdPairCorrelation/README.md §7 open problems 1–3
- **Statement:** Averaging the (linear-in-`frobSq`) rank–trace seam over the window height `T` with a
  smooth weight of width `εT`, at fixed `L`, localizes the whole trans-threshold Frobenius surplus to the
  coalescent band `|log(n/m)| ≤ T^{-1+η}`; sum frequencies, far pairs and the grid end effect cost
  `o(T l³)` unconditionally, and the certified count for `[T, 2T]` loses only `O(ε)N`.

## Goal
Open problem 2's purpose (sum frequencies and far pairs paid without `O(XL)` loss, same `1/18` budget)
by a mechanism that needs no weighted Gram matrix: the seam is linear in `frobSq` (the `√frobSq` tail
term is concave, so Jensen keeps it), and the zero-side block structure is used at each fixed `T`.
Completes the reduction open problem 1 ⟸ open problem 3 with a smooth kernel `K̄_ω(θ) = ∫ω(T)∫_T^{2T}cos(τθ)`.

## Gates
- [x] 0 → 1  in-progress: well-posed, attack idea
- [ ] 1 → 2  fully-proven
- [ ] 2 → 3  formalized

## Approach
1. k-fold integration by parts: `|∫ω(T) sin(κT + c)| ≤ ‖ω^{(k)}‖₁/|κ|^k`.
2. `JmK, JpK` are sums of two such phases in `T` (for every offset `x`); split `A^±` at `|x| ≤ a`,
   Fubini on the inner box, the tail `|x| > a` costs `b‖ω‖₁∫Φ²x²/a²`.
3. Far pairs and sum frequencies: `(Σ a_n)² ≤ 9X` times the averaged kernel bound.
4. Fixed `L` across the average is required: with `L = λl(T)` the moving prime cutoff costs `X log²X`
   (pairs at the cutoff with `|θ| ≈ 1/T` see a sharp-in-`T` kernel).
5. Averaged end form; averaged seam; window-shift counting.

## Log
- 2026-10-23 — created; step 4 obstruction found (moving cutoff), fixed-`L` route chosen.
