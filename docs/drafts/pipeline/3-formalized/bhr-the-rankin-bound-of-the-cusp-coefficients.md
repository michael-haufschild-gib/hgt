# BHR — Rankin's bound for the cusp coefficients

- **ID:** bhr-cusp-rankin-bound
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** application of `bhr-smoothed-rankin-selberg-sums-with-power-saving.md`; improves the bound
  `|ρ(n)| ≪ |n|^{½}` of `bhr-the-l-functions-of-the-cusp-modes.md`.
- **Statement:** For `g ∈ S(λ)` with Whittaker coefficients `ρ(n)`, `ρ(0) = 0`, there are `C ≥ 0`, `δ > 0` with
  `|ρ(n)| ≤ C|n|^{½−δ}` for all `n ≠ 0`. In mean-square form: `|ρ(n)|² + |ρ(−n)|² ≤ C' n^{1−β}`, `β = 1/(4(N+1))`.

## Paper proof
1. *Summability.* `f(m)φ_Δ(my) ≥ 0`, and for `my ≥ e^8`, `Δ ≤ 1`: `(log my)²/(4Δ²) ≥ (log my)²/4 ≥ 2 log(my)`, so
   `φ_Δ(my) ≤ (my)^{−2}/(2√πΔ)`; `Σ f(m)m^{−2} < ∞`.
2. *Single term.* At `y = 1/n`, the `m = n` term is `f(n)G(0)/Δ = f(n)n^β/(2√π)` for `Δ = n^{−β}`.
3. *Smoothed bound.* `Σ_m f(m)φ_Δ(m/n) ≤ Ae^{Δ²}n e^{−1/n} + KΔ^{−N−1}n^{3/4} ≤ Ae·n + K n^{β(N+1)}n^{3/4}`.
4. *Division by `n^β`.* `f(n) ≤ 2√π(Ae·n^{1−β} + K n^{βN+3/4})`, and `βN + ¾ = 1 − β` for `β = 1/(4(N+1))`.
5. `|ρ(±n)|² ≤ f(n)`, square roots: `|ρ(n)| ≤ √C' |n|^{½−β/2}`.

## Lean certificate
`formal/GaloisForLFunctions/BlackHoleRingdown/TheRankinBoundOfTheCuspCoefficients.lean`, wired into
`BlackHoleRingdown.lean`, checked with `lake --old env lean`, no messages. Axioms of `rankin_bound`: `propext`,
`Classical.choice`, `Quot.sound`.

| Claim | Theorems (namespace `BlackHoleRingdown.CuspRB`) |
|---|---|
| 1 | `smTerm`, `smSum_eq_ofReal`, `smTerm_nonneg`, `summable_smTerm` |
| 2–4 | `exists_rsCoeff_le` |
| 5 | `rankin_bound` |

## Scope
No single horocyclic harmonic of a cusp ringdown mode carries a fixed fraction of the energy budget of its
frequency band: `|ρ(n)|²` is `o(n)` with a power saving, whereas equipartition alone (the mean-square law) only gives
`O(n)`. The exponent `δ` is not explicit; Ramanujan–Petersson (`δ = ½ − ε`) remains open. For Hecke eigenforms,
`ρ(n) = ρ(1)λ(n)`, this is a bound `|λ(n)| ≪ n^{½−δ}` for the Hecke eigenvalues.

## Log
- 2026-11-08 — created and formalized.
