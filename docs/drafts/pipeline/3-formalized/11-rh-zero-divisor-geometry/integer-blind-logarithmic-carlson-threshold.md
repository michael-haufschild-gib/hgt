# Integer blindness under logarithmic room: the exact constant π/2 (C553 refuted)

- **ID:** integer-blind-logarithmic-carlson-threshold
- **Stage:** 3-formalized (exact iff `K ≤ π/2` in Lean, boundary included; unconditional, standard axioms)
- **Type:** THEOREM (sharp constant) + correction of conjecture C553
- **Parent:** `prime-blind-carlson-threshold` (MUST-812/818). There, conjecture C553 predicted that blindness at log-dense nodes with `|w(t)| ≤ e^{−(π/2)|t| + ρ(|t|)}` forces `ŵ ≡ 0` iff `∫ρ(t)t^{−2}dt < ∞`.

## Statement
Let `N ⊆ [2, ∞)` with `Σ_{n∈N} 1/(n log n) = ∞` (all integers; every set of positive lower density). Call `w` *blind* on `N` if `∫ w(t) n^{−it} dt = 0` for all `n ∈ N`.

**Theorem A (uniqueness, Lean).** If `0 ≤ K < π/2` and `∫ |w(t)| e^{(π/2)|t| − K|t|/log(|t|+3)} dt < ∞`, then blindness on `N` forces `ŵ ≡ 0`.

**Theorem B (sharpness, Lean: `exists_integerBlind_logRoom`).** For every `K > π/2` there is a nonzero `w`, blind at every integer `n ≥ 1`, with `|w(t)| ≤ C e^{−(π/2)|t| + K|t|/log|t|}` for `|t| ≥ 3`. In particular `∫|w| e^{(π/2)|t| − K'|t|/log(|t|+3)} < ∞` for every `K' > K`.

**Corollary (exact boundary).** The room threshold of `log ℕ` is `ρ(t) = (π/2) t/log t`: a nonzero blind `w` cannot decay faster than `e^{−(π/2)(|t| − |t|/log|t|)}`, and it can decay at any rate `e^{−(π/2)|t| + (π/2+ε)|t|/log|t|}`.

**C553 verdict.** The "if" half holds: a regular `ρ` (`ρ(t)/t` decreasing) with `∫ρ/t² < ∞` satisfies `ρ(t) = o(t/log t)`, because `∫_{√t}^t ρ(s)s^{−2}ds ≥ (ρ(t)/t)(log t)/2`, so Theorem A applies. The "only if" half is FALSE. For example, `ρ(t) = t/log t` has `∫ρ/t² = ∞` (log-log divergence), yet `K = 1 < π/2` forces vanishing. The true boundary is a constant at the scale `t/log t`, not an integrability condition.

## Proof of Theorem A
1. `G(ζ) = ∫ w(t)e^{−it log ζ}dt` is analytic on `Re ζ > 0` (corpus `analyticOnNhd_logFourier`; the weight dominates every subcritical exponential).
   - From `K s/log(s+3) − δ s ≤ K e^{K/δ}` (case split at `log(s+3) = K/δ`) we get `|G(ζ)| ≤ A·exp(K e^{K/δ})`, with `δ = π/2 − |arg ζ|`.
2. **Narrowing.** For `Re u > 0` and `log|u| ≥ 4`, `Ψ(u) = u/log u` has `Re Ψ/|Ψ| = (L cos ψ + ψ sin ψ)/|log u|`, where `L = log|u|` and `ψ = arg u`.
   - The numerator is `≥ π/2`: with `s = π/2 − |ψ|`, use `sin s ≥ (2/π)s` and `cos s ≥ 1 − s²/2`, which works since `L ≥ 4 > (π/2)(1 + π²/8)`.
   - Hence the angle is `≥ (π/2)/(log|u| + 2)`.
3. **Growth on the disc.** Put `u = e⁴ + (1+z)/(1−z)` and `f = G∘Ψ∘u`.
   - Then `K/δ ≤ (2K/π)(log|u| + 2)`, so `log|f(z)| ≤ log A + K e^{4K/π}(2(e⁴+1))^{γ}|1−z|^{−γ}` with `γ = 2K/π < 1`.
   - The circle averages of `|1−z|^{−γ}` are `≤ (1+2π)/(1−γ)`, uniformly in `R`: lower-bound `|1−z| ≥ (2(1−R) + min(θ, 2π−θ))/π`, then integrate `(ε+θ)^{−γ}` exactly.
4. **Nodes.** For `n ≥ e⁴ + 2`, the IVT on `[e⁴+2, n²]` gives `x_n` with `x_n/log x_n = n`.
   - Since `2 log n ≤ n`, this gives `x_n = n log x_n ≤ 2n log n`.
   - The disc point `z_n = (x_n − e⁴ − 1)/(x_n − e⁴ + 1)` has `log(1/|z_n|) ≥ 2/(x_n − e⁴ + 1) ≥ 1/(n log n)`.
5. **Jensen.** If `f ≢ 0`, bounded circle averages force `Σ log(1/|z_n|) < ∞`, contradicting `Σ_N 1/(n log n) = ∞` (proved in Lean via `log log(n+1) − log log n ≤ 1/(n log n)`).
   - So `f ≡ 0`, `G` vanishes on the real ray `[e⁴+2, ∞)` (IVT again), the identity theorem gives `G ≡ 0`, and so `ŵ = G(e^x) ≡ 0`.

Why `π/2`: the composite exponent is `γ = K/(c')`, where `c' = απ/2` is the angular gain of `u/(log u)^α`. Blaschke divergence for the image nodes `n(log n)^α` needs `α ≤ 1`. So `K < π/2` is exactly what one narrowing allows.

## Proof of Theorem B (paper)
Take `G_c(ζ) = sin(πζ)e^{−πcζ log ζ}`, with `c > 1/(K − π/2)`.
- `F(x) = G_c(e^x)` is integrable on `ℝ`: `F ~ πe^x` at `−∞` and decays super-exponentially at `+∞`. So `w := F̌` exists, `w ≠ 0`, and `∫w(t)n^{−it}dt = F(log n) = sin(πn)(…) = 0`.
- Shift the contour to `Im x = ±(π/2 − δ)`: `|w(t)| ≤ e^{−(π/2)|t| + δ|t|}·∫|G_c(re^{±i(π/2−δ)})|dr/r`.
- `log|G_c(re^{iφ})| ≤ πr sin φ(1 + cφ) − πcr cos φ log r`. At `φ = π/2 − δ` its maximum over `r` is `≤ exp((1/c + π/2 + o(1))/δ)`, and the tail beyond `log r ≈ 2A/B` is integrable.
- Choosing `δ ≈ K₀/log|t|` with `K₀ = 1/c + π/2 < K` gives `|w(t)| ≤ C e^{−(π/2)|t| + K|t|/log|t|}`.

## Generalizations (paper)
- With `u/(log u)^α`, a node set with `Σ_N 1/(n(log n)^α) = ∞` has threshold constant `απ/2` (uniqueness for `K < απ/2`).
- The primes have `Σ_p 1/(p(log p)^α) < ∞` for every `α > 0`, so their threshold sits at a finer scale (`t/(log t)²` heuristically). MUST-818 Theorem A, with polynomial room, is the coarse form.

## Reading for the RH frontier
- **Certificate side of U (C-PIN).** A weight `Ξ²h` blind at every integer `n ≥ 2` has `Ξ² ≍ |t|^{7/2}|ζ(½+it)|²e^{−(π/2)|t|}`. So `∫|t|^{7/2}|ζ|²|h|e^{−K|t|/log(|t|+3)} = ∞` for every `K < π/2`.
- C-PIN multipliers grow at least like `e^{(π/2−ε)|t|/log|t|}` in mean. MUST-818 had only `e^{K√|t|}`.
- Signed integer-blind measures exist at `e^{(π/2+ε)|t|/log|t|}`. So positivity (`h > 0`, C556) is the only remaining lever: any C-PIN must sit above the signed threshold.
- **Γ-criticality, second order.** The first-order rate `π/2` is the archimedean decay of `Ξ²` (MUST-812). The second-order constant at scale `t/log t` is again `π/2`, the half-plane's angle seen through one logarithmic narrowing. The arithmetic enters only through `Σ 1/(n log n) = ∞`, i.e. the density of `log ℕ` pulled back by the narrowing.

## Lean
Module `RHTower/IntegerBlindLogarithmicCarlsonThreshold` (namespace `RHTower.PrimeBlindCarlson`), wired after `PrimeBlindCarlsonThreshold`. `lake build --old` passed; the direct `lake env lean` gives zero messages; axioms `[propext, Classical.choice, Quot.sound]`; lint reports nothing for this module.

| Claim | Declaration |
|-|-|
| Theorem A (node sets with `Σ1/(n log n) = ∞`) | `fourier_eq_zero_of_dirichletMoment_eq_zero_logRoom` |
| Theorem A at all integers `n ≥ 2` | `fourier_eq_zero_of_integerMoment_eq_zero_logRoom` |
| `Σ_{n≥2} 1/(n log n) = ∞`; telescoping bound | `not_summable_one_div_mul_log`, `log_log_le_sum_one_div_mul_log` |
| Narrowing `u/log u`: angle `≥ (π/2)/(log|u|+2)` | `re_div_log_pos_and_le`, `pi_div_two_le_mul_cos_add` |
| Growth `A e^{K e^{K/δ}}` under logarithmic room | `norm_logFourier_le_logRoom`, `mul_div_log_sub_le`, `dominatesSubcritical_logRoomWeight` |
| `avg_{|z|=R}|1−z|^{−γ} ≤ (1+2π)/(1−γ)` | `circleAverage_rpow_neg_norm_one_sub_le` |
| Blaschke from bounded circle averages (general nodes) | `summable_log_inv_of_circleAverage_le` |
| Real nodes and preimages of `x/log x` | `realNode`, `cayley_realNode`, `two_div_le_log_inv_realNode`, `exists_div_log_eq` |

## Novelty
- The analytic tools are classical: Jensen's formula, the Blaschke condition after conformal narrowing, and the Carlson-type extremal `sin(πζ)e^{−πcζ log ζ}`.
- New are the exact constant `π/2` at the scale `t/log t` for integer blindness with angle-only growth, and the refutation of C553.
- Corpus search found no source stating this threshold. MUST-818 and C553 were the corpus's own frontier. External search was not run (user directive: corpus only).

## Log
- 2026-10-09 (loop row 564): proved and formalized; C553 refuted.
- 2026-10-09 (loop row 568, MUST-830): generalized to analytic `G` with an extra polynomial factor `(1+|ζ|)^c` (`eqOn_zero_of_logRoom_growth`). Corollary: finitely many exceptional nodes change nothing (`eqOn_zero_of_logRoom_growth_off_finite`, `dirichletMoment_eq_zero_of_cofinite_logRoom`). So `n₀`-selective exact-null tests `Ξ²ĥ`, the explicit C-PIN construction target of `step-phase-torsion-lock-loop-2026-10-03.md` (S31), need `ĥ` above `e^{(π/2)|t|/log|t|}` in `|ζ|²`-weighted mean. Lean: build `--old` passed, the direct audit gave zero messages, standard axioms.
- 2026-10-09 (loop row 575, MUST-836): **Theorem B is formalized.** `exists_integerBlind_logRoom` (any `K > π/2`) and the two-sided capstone `logRoom_integerBlind_threshold`, module `RHTower/IntegerBlindLogarithmicCarlsonSharpness`. The witness is `w_c = 𝓕⁻(F_c(2π·))` with `c = 4/(K − π/2)`; its contour shift uses `δ = κ/log(t+3)`, `κ = (K + π/2)/2`, so `θ = A/(cκ) < 1`. Reused corpus tools: `integral_horizontal_shift_of_decay` and `HTGeometry.norm_sin_le_exp_abs_im`. Build `--old` passed, the direct `lake env lean` gave zero messages, axioms are standard, and lint reports nothing for this module. The card is now Lean in both halves; only `K = π/2` remains open.
- 2026-10-09 (loop row 576, MUST-839): **the boundary `K = π/2` is settled on the uniqueness side, in Lean.** Capstone `logRoom_integerBlind_iff` (for every real `K`): integer blindness with room `K` forces `ŵ ≡ 0` iff `K ≤ π/2`. Module `RHTower/IntegerBlindLogarithmicCarlsonCritical`.
  - Mechanism: the sharp supremum `Ke^{K/(2δ)} + (2δ²/K)e^{K/δ}` yields the extra factor `(log|u|+2)^{−2}`, and `w(x) = x/(log x+2)²` has bounded circle averages via an explicit primitive.
  - The Jensen tail is refactored as `eqOn_zero_of_logNarrow_circleAverage_le`, a reusable narrowed-Jensen uniqueness theorem with the map `logNarrow`.
  - Audit: build `--old` passed, the direct audit gave zero messages, axioms are standard, and lint reports nothing for this module.
  - Paper corollary for the CTF lane (MUST-837, stretched Bose): the second-order completeness transition for dilation systems sits exactly at Mellin decay `e^{−(π/2)|t| + (π/2)|t|/log|t|}`, and the boundary belongs to the complete side.
