# Weil-cone rigidity for log-summable deviations (rough-fiber truncation of the |ζ|² notch)

- **ID:** weil-cone-log-summable-rigidity
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** MC conjecture loop, cycle 168. It extends MUST-570 (`3-formalized/11-rh-zero-divisor-geometry/weil-cone-finitely-generated-support-rigidity.md`) and answers the target of HF L165 ("polylog-sparse large-deviation rigidity is not reachable by radical tests") in full generality.
- **Statement.**
  - **Theorem.** Let `v : ℕ → ℝ` with `v(0) = v(1) = 0` and `|v(n)| ≤ 2 log n + A`. Assume `Σ_n |v(n)| (1 + log n)^{−J} < ∞` for some `J`. If `ψ_v` or `−ψ_v` is positive definite, then `v = 0`.
  - **Corollary.** If `lam` is full-cone Weil-positive and `Σ_{n≥2} |lam(n) − Λ(n)| n^{−1/2} (1 + log n)^{−J} < ∞`, then `lam = Λ`. In particular `lam = Λ` whenever `lam = Λ` off a set `S` with `#(S ∩ [1, X]) ≤ C (1 + log X)^D`.

## Place in the corpus

The theorem contains every sparse-support rigidity class of the corpus:
- lacunary supports with ratio 3/2 (MUST-565 [L]) and 4/3 [P]; with this theorem, every ratio `> 1`;
- powers of 2 and dyadic supports;
- two-geometric supports (MUST-568);
- finite unions of geometric progressions (MUST-569(B), second entry, [P]);
- finitely generated semigroups (MUST-570 [L]);
- log-square-summable deviations (`eq_vonMangoldt_of_weilPositiveFull_of_log_square_summable`). By Cauchy–Schwarz, `Σ d²(1+log n)^{−K} < ∞` implies `Σ |d| n^{−1/2}(1+log n)^{−J} < ∞` for `2J > K + 1`.

It is not implied by summable excess or deficit (`…_of_summable_excess`, `…_of_summable_deficit`), nor by the mean-balance / CauchyBounded results (MUST-536/537). Box-size deviations `≍ log n` on an infinite sparse set violate all of those hypotheses.

## Proof

Fix `n₀ ≥ 2` and a sign `ε ∈ {±1}`. For `y ≥ n₀` let `P = P_y` be the primes `≤ y`. Write `n = n_P n_R`, where `n_P` is the `P`-part and `n_R` is `P`-rough. Let `a(n) = (v_p(n))_{p∈P}` and `a₀ = a(n₀)`.

**Step 1 (pairing).** As in MUST-570, with compact block windows, take `q = |1 + ε n₀^{it}|² Π_{p∈P} |1 − p^{−1/2+it}|²`. The Bochner pairing needs only `Σ |v(n)|(1 + log n)^{−J} < ∞`, since the kernel smoothing of polynomial decay carries the decay of `𝓕g` to the samples `±log n`. It gives `Σ_n v(n) Re M_q(log n) ≤ 0`.

**Step 2 (main terms at every `n`).** `M_q(log n) = Σ_{j,c} e_j(−ε) E(c) · ∫ ω|ζ|² e^{−i(log n − j log n₀ − λ(c))t}`.
- The twist is `h/k = (h(b) n_R)/k(b)`, with `b = a(n) − (j a₀ + c)`. It is coprime, because `n_R` is `P`-rough and `k(b)` is `P`-smooth.
- Its main term is `(hk)^{−1/2} ∫ω log t = Π_p s_p^{|b_p|} · n_R^{−1/2} ∫ω log t`, with `s_p = p^{−1/2}`.
- The per-prime Poisson cancellation (`sum_bohrVec_mul_prod_pow`) gives
  `Σ_{j,c} e_j E(c) Π_p s_p^{|b_p|} n_R^{−1/2} = Π_p(1 − 1/p) · n_R^{−1/2} · (2 [a(n) = 0] + ε [a(n) = a₀])`.
- The case `j = −1` never contributes: `a(n) + a₀ = 0` with both nonnegative forces `a₀ = 0`.

So the main part of the pairing is `Π_p(1 − 1/p) ∫ω log t · X_y` with
`X_y = ε v(n₀) + ε A_y + 2 B_y`, where
- `A_y = Σ_{n ≠ n₀, a(n) = a₀} v(n) n_R^{−1/2}`, the fiber of `n₀`;
- `B_y = Σ_{n ≥ 2, a(n) = 0} v(n) n^{−1/2}`, the `P`-rough numbers.

**Step 3 (errors, `y` fixed).** These are the MUST-570 envelopes with `K₀ = n₀ Π_{p≤y} p`.
- For `n` in the fiber, `(hk)^{−1/2} ≤ √K₀ n^{−1/2}`, `log(hk) ≤ log n + log K₀`, and `k ≤ K₀`.
- The Rankin sums against `Σ |v(n)|(1 + log n)^{−J}` treat twists with `log n ≤ M`. The crude Cauchy tail treats `log n > M`.
- The main-term tail `Σ_{n > e^M} |v(n)| n^{−1/2} L log L ≤ C e^{−M/4} L log L` is also negligible.
- With `L = M^{8J}` all errors are `O_y(L)` while `∫ ω log t ≥ L log L`. Hence `X_y ≤ 0` for every `y ≥ n₀` and both signs.

**Step 4 (`y → ∞`).** A `P_y`-rough `m ≥ 2` exceeds `y`. Hence
- `|B_y| ≤ Σ_{n > y} |v(n)| n^{−1/2}`, and
- `|A_y| ≤ √n₀ Σ_{n > y} |v(n)| n^{−1/2}`.

Both tend to `0`, because `Σ |v(n)| n^{−1/2} ≤ C_J Σ |v(n)| (1 + log n)^{−J} < ∞`. The two signs give `|v(n₀) + A_y| ≤ −2B_y`, hence `|v(n₀)| ≤ |A_y| + 2|B_y| → 0`. ∎

**Corollary.** `v = weilDeviation lam` is log-bounded by the universal box, and `−ψ_v` is positive definite (`positiveDefiniteOnReal_neg_deviationPotential`). For sparse `S`: `Σ_{n ∈ S} (1 + log n)^{1 − J} < ∞` when `J > D + 2`, by partial summation.

## Remarks

- **Reach.** Log-summability is exactly what compactly supported windows can pair against, since their transforms decay only polynomially in `log n`. Supports with counting `X^{o(1)}` need analytic windows. Supports with `Σ_{n ∈ S} n^{−1/2} = ∞` meet the critical Poisson/GCD wall. The `|ζ|²`-lifted main-term functional is the gcd kernel `gcd(n, m)/√(nm)` (Aistleitner–Berkes–Seip, α = ½). It annihilates `μ(n)/√n` formally because `Σ μ(n)/n = 0`.
- **What is new.** One fixed truncation `P_y` handles every support: the rough fibers are pushed into tails, and `y → ∞` comes after `L → ∞`. No multiplicative structure of the support is used.

## Log
- 2026-09-30 — created (MC cycle 168) with a complete paper proof; Lean plan: refactor the pairing inequality to take log-summability; the twist main term for general coprime `(h, k)`; rough-part decomposition; general mode main term; key inequality; `y`-limit.
- 2026-09-30 — **Formalized.** Module `RHTower/WeilLogSummableRigidity.lean` (namespace `RHTower.WeilLogSummable`):
  - `eq_zero_of_positiveDefinite_neg_nullPotential_of_logSummable` and `…_nullPotential_of_logSummable`: Theorem, both signs.
  - `eq_vonMangoldt_of_weilPositiveFull_of_logSummable`: Corollary for log-summable `weilDeviation`.
  - `eq_vonMangoldt_of_weilPositiveFull_of_sparse`: `lam = Λ` off any `S` with `Σ_{n∈S}(1 + log n)^{−K} < ∞`.

  Proof components:
  - `smoothPart` / `roughPart` over `primesUpTo y`.
  - `sum_modeCoeff_mul_weight_general`: truncated Poisson cancellation, with rough fibers.
  - `exists_norm_weightedMoment_sub_main_le_general`: coprime twist `(h(b) n_R, k(b))`.
  - `exists_key_bound_trunc`: `X_y · Π(1 − 1/p) · L log L ≤ C_y L`, via the Rankin bookkeeping lemmas `sum_abs_mul_le_of_pointwise` and `abs_tsum_compl_le`.
  - `nonpos_of_scale_bound`.
  - `tendsto_roughTail`, for the limit `y → ∞`.

  Refactors used: `sum_mul_re_weightedMoment_nonpos_of_summable` (the pairing now takes log-summability directly); `exists_norm_twistedMoment_hk_sub_le` (twist main term for any coprime `(h, k)`); `weight_mode_le_prod` / `log_mode_norm_le_prod`.
