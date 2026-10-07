# The resonance budget of the Weil cone

- **ID:** weil-cone-resonance-budget
- **Stage:** 3-formalized (MUST-817)
- **Type:** THEOREM
- **Source:** loop row 552; extends MUST-815 (`ZetaLineResonatorLargeValues`) from the symbol `ζ` to every element of the Weil cone
- **Statement:** Let `λ` be full-cone Weil-positive and `½ < σ₀ ≤ 3/4`. There are `K₁, K₂` such that for every finite set `P` of primes
  `Σ_{C⊆P} λ(∏C)(∏C)^{−σ₀}2^{−|C|} ≤ K₁ + K₂ log ∏_{p∈P} p`.
  **Corollary.** For every `c > 0` and `n₀` there is a squarefree `n > n₀` with `λ(n) < c`. So `liminf` of `λ` over the squarefree integers is `≤ 0` for every element of the cone.

## Lean
- `RHTower/WeilConeResonanceMoments.lean` (namespace `RHTower.WeilResonance`):
  - `lamSeriesCont hW s = G(s) + 1/(s−1) − Φ(s)`, the continuation of `Σλ(n)n^{−s}` to `Re s > ½` (`lamSeriesCont_eq_LSeries`);
  - Herglotz bound `re_lamSeriesCont_le`, and its logarithmic form `exists_re_lamSeriesCont_le`;
  - Borel–Carathéodory growth bound `exists_norm_lamSeriesCont_le` on `½+δ ≤ Re s ≤ 5/4`;
  - twisted first moments `exists_norm_integral_lamSeriesCont_sub_le`, via the rectangle shift to `Re s = 5/4`.
- `RHTower/WeilConeResonanceBudget.lean`:
  - the resonator expansion `resW_eq_sum` and the divisibility collapse `sdiff_eq_empty_of_dvd`, `sum_twistMain_eq`;
  - the error and mass bounds `norm_integral_resW_sub_le`, `integral_resW_le`, `re_integral_mul_resW_le`;
  - the main theorems `resonance_budget` and `exists_squarefree_lt`.
- Standard axioms only. Both modules are wired after `WeilConeVonMangoldtZetaPencil`.

## Paper proof (as formalized)
1. **Continuation and positivity.** `Φ = G + 1/(s−1) − D` with `D = Σλ(n)n^{−s}` on `Re s > 1`. Full-cone positivity continues `Φ` holomorphically to `Re s > ½` with `Re Φ ≥ 0`. So `D := G + 1/(s−1) − Φ` is holomorphic there except at `1`, and `Re D ≤ Re(G + 1/(s−1)) ≤ K log(|t|+3) + 1`.
2. **Growth.** Borel–Carathéodory on discs of radius `< δ` around `σ + it`, centred at `Re s = 5/4` where `D` is an absolutely convergent series, gives `|D| ≤ C(1 + log(|t|+4))` on `½+δ ≤ Re s ≤ 5/4`.
3. **Twisted moments.** Shift `∫_T^{2T} D(σ₀+it)(m/d)^{it}dt` to `Re s = 5/4`. The horizontal edges cost `O((md)^4 log T)` by step 2. The vertical integral at `5/4` is `[d∣m]λ(m/d)(m/d)^{−5/4}T`, up to `O(m²)` from the off-diagonal terms, because `|log(m/k)| ≥ 1/(4m²)`. On `Re s = σ₀` this gives the main term `[d∣m]λ(m/d)(m/d)^{−σ₀}T`.
4. **Resonator.** Expand `W_P(t) = ∏_{p∈P}(2 + 2cos(t log p))` as `Σ_{C⊆P} Σ_{A⊆C} 2^{|P∖C|}(∏A/∏(C∖A))^{it}`. Since `∏(C∖A) ∣ ∏A` forces `C∖A = ∅`, `∫ D W_P = T Σ_C 2^{|P∖C|}λ(∏C)(∏C)^{−σ₀} + O(8^{|P|}Q⁴ log T)`, where `Q = ∏_{p∈P} p`.
5. **Budget.** `W_P ≥ 0` has mass `≤ 2^{|P|}T + 2·4^{|P|}Q²`, and `Re D ≤ K log(2T+3) + 1` on `[T, 2T]`. Take `T = 2Q⁸`, so that every error is `O(2^{|P|}T)`, and divide by `2^{|P|}T`.
6. **Corollary.** Suppose `λ ≥ c` on the squarefree `n > n₀`. Take `P` = the primes in `(n₀, N⁸]`. The left side is then at least `c(∏_P(1 + p^{−3/4}/2) − 1) ≥ c(exp(Σ_P p^{−3/4}/4) − 1)`. Here `Σ_{p≤N⁸} p^{−3/4} ≥ θ(N⁸)/(N⁶ log N⁸) ≥ N/16`, from `θ(N⁸) ≥ N⁸/2`. The right side is `≤ |K₁| + 2|K₂|N⁸`, from `log primorial(y) ≤ y log 4`. Then `exp(N/128) ≥ (N/128)⁹/9!` gives a contradiction for large `N`.

## Why it matters
- MUST-815 is the special case "the symbol `ζ` itself". The budget transfers the resonance method from `ζ` to an arbitrary element of `W`, without any regularity class. It is the first constraint here that applies to all of `W`. MUST-801/804/810/816 each need a regularity class (absolute convergence on or beyond the line, a Möbius part, or a pencil).
- The budget sees only squarefree values: the resonator `∏|1+p^{it}|²` produces exactly the frequencies `log ∏C`. Values of `λ` on non-squarefree integers, prime powers included, are invisible to it.

## Scope and limits
- Necessary condition only. `Λ` satisfies it with a large margin (left side `Σ_p log p·p^{−σ₀}/2` against `K₂θ`). So the budget cannot decide `Λ ∈ W` and is RH-blind.
- `log Q` against the true size of the left side: the factor `K₂ log Q` comes from the Herglotz bound `Re D ≤ K log t`, used at `T = Q^{O(1)}`. A sharper inequality would need `Re D = O(1)` on average against the resonator, which is a property of the specific `λ`.
- [P, not formalized] The same proof gives `liminf_{n squarefree} λ(n)n^{β} ≤ 0` for every `β < ½` (take `σ₀ = 3/4 − β/2`, so that `σ₀ + β < 1`).

## Novelty audit (2026-10-07): REDISCOVERED, weaker than the corpus
- `RHTower.weil_multiplicativeToeplitz_bound` (`WeilPositivityMultiplicativeToeplitzBound`) proves `2Σ_{2≤n≤N}λ(n)n^{−½}Re Σ_m c(nm)c̄(m) ≤ (log N + C₀)Σ|c|²` for every `c` on `[1, N]`. That is the budget at `σ = ½` with the sharp constant `1` in front of `log N`, for every resonator rather than only squarefree ones. It needs no twisted moments: narrow polar-free bumps at `log m` are used directly as Weil tests.
- `PrimorialResonance.not_forall_squarefree_le_of_weilPositiveFull` excludes `λ(n) ≥ cn^{−δ}` on all squarefree `n ≥ 2` for every `δ < ½`, including sign twists. That contains the [P] remark above.
- What remains of this card: the eventual form (`n > n₀`, `δ = 0`), and the twisted first moments of `D_λ` on `Re s = σ₀` (`exists_norm_integral_lamSeriesCont_sub_le`). The growth bound overlaps the corpus Harnack bound `|E(σ+it)| ≪ log|t|/(σ−½)` (L148).
- Lesson: search `multiplicative Toeplitz` and `resonator` before any resonance argument on `W`.

## Log
- 2026-10-07: card created and formalized (loop row 552).
- 2026-10-07: novelty audit. Rediscovered; the corpus result is stronger (see above).
