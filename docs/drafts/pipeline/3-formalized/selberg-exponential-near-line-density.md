# Exponential near-line zero density from a two-length Barban–Vehov mollifier

- **ID:** SELBERG-EXP-NEAR-LINE
- **Stage:** 3-formalized
- **Type:** PARTIAL PRODUCER (zero-density infrastructure; routes LA, TG)
- **Parent:** `rh-goal-loop-opus-2026-09-29.md`, cycle 49 (row 48 named the obstruction)

## Target

There are `A, K > 0` such that for all large `U`, with `L = log U`, admissible heights
`T₁ ∈ (U/4, U/4+1)`, `T₂ ∈ (U/2−1, U/2)` exist with, for every `1 ≤ a ≤ (L−2)/2`,

`2π (a/L) · #{ρ : Re ρ ≥ ½ + 2a/L, T₁ ≤ Im ρ ≤ T₂} ≤ (T₂ − T₁) · A e^{−a/1200} + K L`.

The corpus rate is `r_A(a) ≍ 1/a` (`exists_selberg_nearLine_zeroDensity`); the target is the
Selberg-strength exponential rate, uniform in `a` (heights chosen once for all displacements).

## Mechanism (paper)

Barban–Vehov: `ζΨ_Z = 1 + P_Z + f_Z`, `P_Z = Σ_{n≤Z} Λ(n)/log Z · n^{−s}`, tail `f_Z` exponentially
small near the line by L² three-lines (corpus, `Z = ⌊U^{1/100}⌋`). The `1/a` rate comes only from the
head `P_Z` (mean square `≍ 1/a²` at `½ + a/L`).

Two lengths `Y < X`, mollifier `M = (log X · Ψ_X − log Y · Ψ_Y)/log(X/Y)`: coefficients `μ(n)` for
`n ≤ Y`, `μ(n) log(X/n)/log(X/Y)` for `Y < n ≤ X` (real, `|·| ≤ 1`, first `= 1`). Since
`log Z · P_Z = Σ_{n≤Z} Λ(n) n^{−s}`,

`ζM − 1 = H + g`, `H = (1/log(X/Y)) Σ_{Y<n≤X} Λ(n) n^{−s}`, `g = (log X f_X − log Y f_Y)/log(X/Y)`.

The head starts at `Y`: `∫|H|² ≤ (T + 8X(1+log X)) Y^{−2a/L} Σ_{n≤X} Λ(n)²/n / log²(X/Y)`, and with
`X = ⌊U^{1/100}⌋`, `Y = ⌊U^{1/200}⌋` this is `≪ T e^{−a/100}`. The tails need the three-lines
estimate for both lengths: the gate and the tail theorem are generalized from `⌊U^{1/100}⌋` to any
`N ∈ [U^{1/200}/2, U^{1/100}]` (only `log N ≳ L` enters the main-term constant; the right-line
tail `16/N² ≤ e^{−L/200}` gives `e^{−(a+1)/600}`). Then `∫|ζM|² ≤ (T₂−T₁)(1 + 3√η + 2η)`,
`η ≪ e^{−a/600}`, and Littlewood (corpus consumer) gives the count.

## Lean plan

1. `ZetaMollifiedWindowGateLength` — high-block window gate for every length in the range.
2. `SelbergNearLineTailLength` — three-lines tail for every length, uniform in `a`.
3. `SelbergExponentialNearLineDensity` — two-length mollifier, head mean square, density.

## Lean

- `RHTower/ZetaMollifiedWindowGateLength.lean` — `exists_highBlock_window_bound_productAFE_len`
  (gate for every length `2 ≤ N ≤ U^{1/100}`, `log U ≤ 400 log N`; constant `400 M_R/R`).
- `RHTower/SelbergNearLineTailLength.lean` — `exists_eventually_integral_hbMollifiedTail_rightShift_le_len`
  (`∫|f_N|² ≤ C e^{−(a+1)/600}(T₂−T₁+2U^{99/100})` for all `N ∈ [U^{1/200}/2, U^{1/100}]`, all
  `0 < a`, `2a+2 ≤ log U`; threshold independent of `a`, `N`).
- `RHTower/SelbergExponentialNearLineDensity.lean` — `twoLengthCoeff`, `zeta_mul_twoLength_eq`,
  `integral_normSq_twoLengthHead_rightShift_le` (`≤ 128(T₂−T₁)e^{−a/100}`),
  `integral_normSq_zetaTwoLength_rightShift_le`, `exists_selberg_exponential_nearLine_zeroDensity`.

All three: `lake env lean` clean, `lake build --old` green, axioms `[propext, Classical.choice,
Quot.sound]`, wired in `RHTower.lean` after `SelbergNearLineZeroDensity`, collision scan 0.
STATUS MUST-571.

## Reading

`N(σ; T₁, T₂) ≪ T^{1−(σ−½)/2400} log T` for `½ + 2/L ≤ σ ≤ ½ + (L−2)/L`: Selberg-type density
with exponent linear in `σ − ½` (constant `1/2400` vs Selberg's `1/4`). Heights are chosen once for
all displacements, so dyadic sums over displacement shells are legitimate.

## Log
- 2026-09-30 — created (cycle 49).
- 2026-09-30 — formalized: three modules, MUST-571. Stage 3.
