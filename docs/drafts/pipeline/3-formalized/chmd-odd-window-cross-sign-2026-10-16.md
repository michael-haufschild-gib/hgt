# CHMD: sign law of the prime cross terms on the one-signed odd cone

- **ID:** chmd-odd-window-cross-sign-2026-10-16
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean), unconditional
- **Source:** continuation of chmd-single-prime-window-2026-10-16 (user pivot: fixed prime power, explicit weight)
- **Statement:** (1) odd `v ≥ 0` on `[0,∞)`, `supp v ⊆ (−L/2, L/2)`, `L ≤ 2 log n` ⟹ `phiDoobPrimeCross v n ≤ 0` pointwise. (2) `L ≤ 2 log 2` ⟹ the whole prime cross series is `≤ 0` ⟹ `Λ_∞(Θv) ≤ E(v)`. (3) `(|a|−|b|)² ≤ (a−b)²` ⟹ `jumpEnergy |f| ≤ jumpEnergy f` ⟹ `Λ_∞(|f|) ≤ Λ_∞(f)`. (4) `Λ_∞(Θ|v|) ≤ E(v)` on the cone; `Λ_∞(Θ|v|) ≥ 0 ⟹ E(v) ≥ 0`.
- **Status:** STATUS MUST-1562. One leaf (`CHMDOddWindowCrossSign`; 11 declarations), standard axioms; `lake env lean` clean; `lake build --old` green; wired.

## Gates
- [x] 0 → 1, [x] 1 → 2, [x] 2 → 3 (`tsum_cross_nonpos_of_odd_oneSigned`, `weilLevyForm_abs_le`, `levy_abs_le_sourceEnergy_of_odd_oneSigned`)
- [ ] 3 → 4

## What was learned about fixed-prime-power domination
Domination at prime power `n` (chain variance ≥ its cosh-mass share) is anticorrelation of `Θv` at
lag `log n`. On the one-signed odd cone it is automatic for every `n` with `2 log n ≥ L`: the lag
`log n` crosses the origin, so the two factors have opposite signs. On `L ≤ 2 log 2` this covers
all prime powers, including the active primes `2` and `3`; the primes only help. The arithmetic
positivity on this cone is therefore equivalent to a prime-free archimedean inequality
(`Λ_∞ ≥ 0` on nonnegative even tests of support `≤ 2 log 2`, strictly stronger than the corpus
`weilArchRe ≥ 0`, which keeps the pole mass `2C²` and is proved only up to `12/25`). The exact
form `Λ_∞(Θv) = Λ_∞(Θ|v|) + 4∫∫_{s,t>0} Θ|v|(s) Θ|v|(t) ω(s+t)` (cross-sign bonus) is the next
identity to formalize; it recovers part of the pole mass.

## Lean module (namespace `RHTower.CHMDPolar`)
`RHTower/CHMDOddWindowCrossSign.lean` — see STATUS MUST-1562 for the declaration list.
