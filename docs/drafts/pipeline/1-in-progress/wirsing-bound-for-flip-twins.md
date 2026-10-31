# Wirsing bound for prime-set flip twins

- **ID:** rit-wirsing-flip
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Programme:** RenormalizedIntersectionTheory (open topic 3: twins whose flipped and unflipped primes both have divergent reciprocal sums)
- **Statement:** Let `P` be a set of primes with relative logarithmic density `κ`:
  `|Σ_{p∈P, p≤x} log p/p − κ log x| ≤ C`. For the completely multiplicative flip `ω_P`
  (`ω(p) = −1` iff `p ∈ P`) and `L(x) = Σ_{n≤x} ω(n)/n`:
  `|L(x)| ≤ C' (log x)^{1−2κ}` for `κ < 1/2`, `|L(x)| ≤ C' log log x` for `κ = 1/2`, `|L(x)| ≤ C'` for
  `κ > 1/2`. Consequence: for `κ > 1/4`, `L(x)² = o(log x)`, so `ω_P` has margin `0` and the atomic
  Hodge index separates it from `ζ` (SMAP `not_hasHyperplaneGap_of_harmonicSum_small`).

## Goal
Close the twin class of RIT open topic 3 for every flip set of relative density `κ > 1/4`
(e.g. primes `≡ 1 mod 4`, `κ = 1/2`).

## Proof (Levin–Fainleib / Wirsing integral equation)
1. **Chebyshev identity** (`RHTower.Sieve.sum_mul_log_eq_vonMangoldt`, `f(n) = ω(n)/n`):
   `Σ_{n≤x} ω(n) log n/n = Σ_{d≤x} ω(d)Λ(d)/d · L(x/d)`.
2. **Split the weights**: `ω(d)Λ(d) = Λ(d) − 2·1_{d=p^k, p∈P, k odd}Λ(d)`. Prime powers `k ≥ 2`
   contribute `O(Σ log p/p²)·sup|L(x/d)| ≤ O(log x)` (`|L| ≤ H ≤ log x + 1`).
3. **Unflipped part**: `Σ_{d≤x} Λ(d)/d · L(x/d) = Σ_{n≤x} ω(n)/n · ψ₁(x/n)`, `ψ₁(y) = Σ_{d≤y} Λ(d)/d
   = log y + O(1)` (Mertens) `= L(x) log x − Σ_{n≤x} ω(n) log n/n + O(log x)`.
4. **Flipped part by partial summation**: with `R(y) = Σ_{p∈P,p≤y} log p/p − κ log y = O(1)`,
   `Σ_{p∈P,p≤x} (log p/p) L(x/p) = κ Σ (Abel weights) + O(sup|R| · Var L) = κ·M(x) + O(log x)`,
   `M(x) = Σ_{n≤x} L(x/n)·(log-cell weights) ≈ Σ_{m≤x} L(m)/m`.
5. **Integral equation**: `L(x) log x = (2 − 2κ) M(x) + O(log x)`, `M(x) = Σ_{m≤x} L(m)/m` (discrete form).
6. **Discrete Gronwall**: `M_N − M_{N−1} = L(N)/N`, hence `M_N = M_{N−1}(1 + a/(N log N)) + O(1/N)`,
   `a = 2 − 2κ`; `∏_{n≤N}(1 + a/(n log n)) ≍ (log N)^a` gives `|M_N| ≪ (log N)^{max(a,1)}·(log log N)^{[a=1]}`
   and `|L(N)| ≪ (log N)^{a−1}` (resp. `log log N`, `1`).
7. **RIT corollary**: `κ > 1/4` ⇒ `L(N)²/log N → 0` ⇒ `HodgeSeparates (primeSetFlip P)`.
8. **Instance**: primes `≡ 1 mod 4` from the Mertens theorem for degree-one primes of `ℚ(i)`
   (`ArtinMertens.exists_abs_degreeOneMertens_sub_log_le`), `κ = 1/2`.

## Gates
- [ ] 1 → 2  fully-proven (steps 1–7 written out with constants)
- [ ] 2 → 3  formalized

## Lean plan
Module `RenormalizedIntersectionTheory/TheWirsingBoundForFlipTwins.lean` (steps 1–7), then
`…/PrimesOneModFourAreSeparated.lean` (step 8).

## Log
- 2026-10-31 — card created; inputs located in the corpus (Chebyshev identity, Mertens with bounded
  error, Abel summation, number-field Mertens)
