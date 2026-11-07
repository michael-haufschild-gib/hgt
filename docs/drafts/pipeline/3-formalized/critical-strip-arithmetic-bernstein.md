# Two-transition architecture of Arithmetic Bernstein across the critical strip

- **ID:** critical-strip-arithmetic-bernstein
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `formal/GaloisForLFunctions/ArithmeticInnerFunctionTheory/README.md` Open Topic 3; `TheArithmeticBernsteinTheorem`; `TheFixedBaseConeAndCriticalBernstein`.
- **Statement:**
  Let `IsAllBaseHeckePositive f` mean `0 ≤ f x * ∑_i d_i² + ∑_{i,j} d_i d_j f(x + log p_i + log p_j)` for all finite tuples of distinct primes `p : Fin n → ℕ`, `x ∈ ℝ`, and `d : Fin n → ℝ`, and let `IsAllBaseTorusPositive f` mean `0 ≤ torusSum (ampl f (log p) x) θ` for all distinct primes `p : Fin n → ℕ`, `x ∈ ℝ`, and `θ : Fin n → ℝ`.
  1. *Subcritical coincidence (`κ < 1/2`) and exact intermediate transition at `κ = 1/2`.*
     - If `f` is continuous, satisfies `ExpDecayFrom x κ₀ f` (`κ₀ > 0`) at every `x`, and obeys `|f y| ≤ C e^{−κy}` on `(−∞, 0]` with `κ < 1/2`, then `IsAllBaseHeckePositive f ↔ IsAllBaseTorusPositive f ↔ ∀ x₀, IsExpConvexFrom x₀ f`.
     - For every `κ ≥ 1/2` (including the critical endpoint `κ = 1/2` itself), there exists `ε₀ > 0` such that for every `ε ∈ (0, ε₀]`, `f(y) = e^{−κy} − ε · tentBump y` satisfies `ExpDecayFrom x₀ κ f` at all `x₀`, `|f y| ≤ (1 + ε · 5^κ) e^{−κy}` on `(−∞, 0]`, and `IsAllBaseHeckePositive f`, yet fails `IsExpConvexFrom 0 f`; moreover, throughout the entire critical strip `κ ∈ [1/2, 1]`, `¬ IsAllBaseTorusPositive f` (failing already at `x = 0`).
  2. *`SU(2)` Poisson–Szegő kernel and complete-monotonicity module law.*
     For every `r ∈ (−1, 1)` and `θ, φ ∈ ℝ`,
     `∑'_{k : ℕ} r^k cosSum θ k cosSum φ k = (1 − r²) / ((1 − 2r cos(θ − φ) + r²)(1 − 2r cos(θ + φ) + r²)) > 0`.
     Integrating against `torusMeasure n` proves that for any `TraceSummable a` with `∀ φ, 0 ≤ torusSum a φ` and any `r : Fin n → (−1, 1)`, `k ↦ a k ∏_i (r i)^{k_i}` is trace-summable and torus-positive; in particular, multiplying any fixed-base or all-base torus-positive amplitude `f` by `e^{−βy}` (`β ≥ 0`) preserves torus positivity.
  3. *Critical-strip Mellin–Kronecker exponent collapse (`κ < min(1, κ₀)`).*
     If `f : ℝ → ℝ` is continuous, satisfies `IsAllBaseTorusPositive f`, `ExpDecayFrom 0 κ₀ f` (`κ₀ > 0`), and `|f y| ≤ C e^{−κy}` on `(−∞, 0]` with `κ < min(1, κ₀)` (covering every `κ ∈ [1/2, 1)` when `κ₀ > κ`), then `f = 0` identically.
  4. *Oscillatory Bernstein dichotomy at `α = 1`.*
     For `f(y) = e^{−αy}(1 + ε cos(ωy))` with `ω ≠ 0`:
     - If `0 < α ≤ 1` and `ε ≠ 0`, then `¬ IsAllBaseTorusPositive f`.
     - If `α > 1`, there exists `ε₀ > 0` such that for all `0 < |ε| ≤ ε₀`, `IsAllBaseTorusPositive f` holds strictly while `¬ IsExpConvexFrom 0 f`.
  5. *Signed finite Laplace mixture Bernstein dichotomy at `α = 1`.*
     - For strictly increasing `α : Fin m → ℝ` with `0 < α r ≤ 1` and any `c : Fin m → ℝ`, `f(y) = ∑_r c_r e^{−α_r y}` satisfies `IsAllBaseTorusPositive f` if and only if `∀ r, 0 ≤ c r` (if and only if `∀ x₀, IsExpConvexFrom x₀ f`).
     - For any `1 < α₀ < α₁ < α₂`, there exists `ε₀ > 0` such that for every `ε ∈ (0, ε₀]`, `e^{−α₀ y} − ε e^{−α₁ y} + e^{−α₂ y}` is strictly all-base torus-positive yet fails `IsExpConvexFrom 0`.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: `formal/GaloisForLFunctions/ArithmeticInnerFunctionTheory/CriticalStripArithmeticBernstein.lean` (`heckePositive_iff_expConvex_of_lt_half`, `exists_heckePositive_not_torusPositive_ge_half`, `hasSum_cosSum_mul_cosSum_geom`, `torusSum_mul_geom_eq_integral`, `IsAllBaseTorusPositive.mul_exp_neg`, `eq_zero_of_torusPositive_of_lt_min_one`, `oscillatory_bernstein_dichotomy`, `laplaceMixture_torusPositive_iff_nonneg`, `exists_supercritical_laplaceMixture_not_expConvex`), foreground `lake --old env lean` green, `#print axioms` PASS (`[propext, Classical.choice, Quot.sound]`)

## Lean verification
- **Module:** `formal/GaloisForLFunctions/ArithmeticInnerFunctionTheory/CriticalStripArithmeticBernstein.lean`
- **Declarations:**
  - `GaloisForLFunctions.ArithmeticInnerFunctionTheory.IsAllBaseHeckePositive`
  - `GaloisForLFunctions.ArithmeticInnerFunctionTheory.IsAllBaseTorusPositive`
  - `GaloisForLFunctions.ArithmeticInnerFunctionTheory.heckePositive_iff_expConvex_of_lt_half`
  - `GaloisForLFunctions.ArithmeticInnerFunctionTheory.abs_tentBump_prime_double_sum_le`
  - `GaloisForLFunctions.ArithmeticInnerFunctionTheory.exists_heckePositive_not_torusPositive_ge_half`
  - `GaloisForLFunctions.ArithmeticInnerFunctionTheory.su2PoissonKernel`
  - `GaloisForLFunctions.ArithmeticInnerFunctionTheory.su2PoissonKernel_pos`
  - `GaloisForLFunctions.ArithmeticInnerFunctionTheory.hasSum_cosSum_mul_cosSum_geom`
  - `GaloisForLFunctions.ArithmeticInnerFunctionTheory.torusSum_mul_geom_eq_integral`
  - `GaloisForLFunctions.ArithmeticInnerFunctionTheory.torusPositiveAt_mul_exp_neg`
  - `GaloisForLFunctions.ArithmeticInnerFunctionTheory.IsAllBaseTorusPositive.mul_exp_neg`
  - `GaloisForLFunctions.ArithmeticInnerFunctionTheory.exists_primes_cos_le_neg_half_prod_lt`
  - `GaloisForLFunctions.ArithmeticInnerFunctionTheory.eq_zero_of_torusPositive_of_lt_min_one`
  - `GaloisForLFunctions.ArithmeticInnerFunctionTheory.torusSum_ampl_exp_neg_mul_cos`
  - `GaloisForLFunctions.ArithmeticInnerFunctionTheory.oscillatory_bernstein_dichotomy`
  - `GaloisForLFunctions.ArithmeticInnerFunctionTheory.laplaceMixture_torusPositive_iff_nonneg`
  - `GaloisForLFunctions.ArithmeticInnerFunctionTheory.exists_supercritical_laplaceMixture_not_expConvex`
- **Audit:** `lake --old env lean GaloisForLFunctions/ArithmeticInnerFunctionTheory/CriticalStripArithmeticBernstein.lean` exited `0` with zero warnings and default heartbeats; all `#print axioms` checks report only `[propext, Classical.choice, Quot.sound]`.

## Proof

1. *Level-1 Hecke transition at `κ = 1/2` (`[PROVED HERE]`).*
   - *Subcritical (`κ < 1/2`):* `IsExpConvexFrom` implies `IsAllBaseTorusPositive` (`IsExpConvexFrom.torusSum`), which implies `IsAllBaseHeckePositive` (`hecke_primes_nonneg`). Conversely, spreading `c_v` uniformly across disjoint prime windows `P_v = primesInIoc ⌊e^{u+v}⌋₊ ⌊e^{u+v+ε}⌋₊` at base `x = y − 2u` (`u → ∞`) uses only `IsAllBaseHeckePositive f`: the off-diagonal sum converges to `∑_{v,w} c_v c_w f(y + v + w)` by uniform continuity of `f` on `[y − 2V, y + 2V]`, while `exists_card_primes_window_ge` bounds `f(y − 2u) ∑_v c_v² / |P_v| ≤ K₁ (u + V) e^{−(1 − 2κ)u} → 0` since `κ < 1/2`.
   - *Critical and supercritical (`κ ≥ 1/2`):* On `g_κ(y) = e^{−κy}`, `g_κ(x) ∑_i d_i² + ∑_{i,j} d_i d_j g_κ(x + log p_i + log p_j) = e^{−κx}(∑_i d_i² + (∑_i d_i p_i^{−κ})²) ≥ e^{−κx} ∑_i d_i²`. Since `tentBump` vanishes on `[log 5, ∞)` and is bounded by `1`, `tentBump(x) ≤ 5^κ e^{−κx}` for all `x ∈ ℝ`. For the double sum `B(x) = ∑_{i,j} d_i d_j tentBump(x + log p_i + log p_j)`:
     - If `x ≥ log(5/4)`, then `x + log p_i + log p_j ≥ log(5/4) + 2 log 2 = log 5`, so `B(x) = 0`.
     - If `x < log(5/4)`, set `W = e^{−x} > 4/5`. Every nonzero summand satisfies `p_i p_j < 5W`. By weighted Cauchy–AM–GM with weights `w_i = p_i^{−1/2}`, `2 |d_i d_j| ≤ d_i² √(p_i / p_j) + d_j² √(p_j / p_i)`, so symmetry and injectivity of `p : Fin n → ℕ` yield
       `|B(x)| ≤ ∑_i d_i² √p_i ∑_{1 ≤ m ≤ ⌊5W / p_i⌋₊} m^{−1/2}`.
       Since `m^{−1/2} ≤ 2/(√m + √(m − 1)) = 2(√m − √(m − 1))` for every `m ≥ 1`, telescoping bounds the inner sum by `2 √⌊5W / p_i⌋₊ ≤ 2 √(5W / p_i)`, giving `|B(x)| ≤ 2√5 e^{−x/2} ∑_i d_i²`. Because `κ ≥ 1/2` and `x < log(5/4)`, `(κ − 1/2)x ≤ (κ − 1/2) log(5/4)`, so `e^{−x/2} ≤ (5/4)^{κ − 1/2} e^{−κx}`.
     Choosing `ε₀ = (2(5^κ + 2√5 (5/4)^{κ − 1/2}))⁻¹ > 0` makes `e^{−κy} − ε · tentBump y` all-base Level-1 Hecke positive for all `0 < ε ≤ ε₀` (including `κ = 1/2`), while `¬ IsExpConvexFrom 0` holds at `(log 2, log 3)` and `exists_prime_set_torusSum_neg_of_le_one` negates `IsAllBaseTorusPositive` at `x = 0` for all `κ ∈ [1/2, 1]`.

2. *`SU(2)` Poisson–Szegő kernel and module law (`[PROVED HERE]`).*
   Let `c₁ = 2 cos θ`, `c₂ = 2 cos φ`, and `u_k = cosSum θ k cosSum φ k`. Applying `cosSum_add_two` three times expresses `cosSum α (k + 2), cosSum α (k + 3), cosSum α (k + 4)` as linear combinations of `cosSum α k` and `cosSum α (k + 1)`, verifying algebraically the fourth-order recurrence
   `u_{k+4} − c₁ c₂ u_{k+3} + (c₁² + c₂² − 2) u_{k+2} − c₁ c₂ u_{k+1} + u_k = 0`
   together with `(1 − 2r cos(θ − φ) + r²)(1 − 2r cos(θ + φ) + r²) = 1 − c₁ c₂ r + (c₁² + c₂² − 2) r² − c₁ c₂ r³ + r⁴` and initial numerator `1 − r²`. Series shifting `∑' r^k u_{k+j}` for `|r| < 1` proves `HasSum` to `su2PoissonKernel r θ φ > 0`.
   For `r : Fin n → (−1, 1)` and fixed `θ`, setting `b_θ k = (∏_i (r i)^{k_i}) chiProd θ k` gives `TraceSummable b_θ` and `torusSum b_θ φ = ∏_i su2PoissonKernel (r i) (θ i) (φ i) > 0`. Applying `integral_torusSum_mul_torusSum` yields
   `torusSum (fun k => a k ∏_i (r i)^{k_i}) θ = ∫ φ, torusSum a φ * torusSum b_θ φ ∂(torusMeasure n) ≥ 0`.
   Taking `r_i = e^{−β ℓ_i}` (`β > 0`) and `β = 0` directly proves closure under multiplication by `e^{−βy}` (`β ≥ 0`).

3. *Mellin–Kronecker exponent collapse (`[PROVED HERE]`).*
   Evaluating `IsAllBaseTorusPositive f` on `n = 0` gives `f y ≥ 0` for all `y ∈ ℝ`. Set `σ = (max κ 0 + min 1 κ₀)/2`, so `0 < σ < 1`, `κ < σ < κ₀`, and `y ↦ f y e^{σ y}` is nonnegative and integrable on `ℝ` with `|f y| e^{σ y} ≤ M_bd e^{−η|y|}` (`η = min(κ₀ − σ, σ − κ) > 0`).
   For any distinct primes `p : Fin n → ℕ` (`ℓ_i = log p_i`), `θ : Fin n → ℝ`, and `s = σ + it`, translating `y = x + ∑_i k_i ℓ_i` gives `∫ ‖f(x + L(k)) chiProd θ k e^{sx}‖ dx = |chiProd θ k| e^{−σ L(k)} ∫ f(y) e^{σy} dy`, summable in `k` by `traceSummable_ampl` (`σ > 0`). By `hasSum_integral_of_summable_integral_norm` and geometric factorization of `∑'_k chiProd θ k e^{−s L(k)}`,
   `∫ (torusSum (ampl f ℓ x) θ : ℂ) e^{sx} dx = Φ(s) ∏_i ((1 − e^{iθ_i} p_i^{−s})(1 − e^{−iθ_i} p_i^{−s}))⁻¹`,
   where `Φ(s) = ∫ (f y : ℂ) e^{sy} dy`. Nonnegativity of `torusSum (ampl f ℓ x) θ` implies
   `‖Φ(σ + it)‖ ≤ Φ(σ) ∏_i (‖(1 − e^{iθ_i} p_i^{−σ−it})(1 − e^{−iθ_i} p_i^{−σ−it})‖ / ‖1 − e^{iθ_i} p_i^{−σ}‖²)`.
   For `t ≠ 0`, set `θ_i = t log p_i`. On every prime `q` with `cos(t log q) ≤ −1/2`, the numerator is `‖(1 − q^{−σ})(1 − e^{−2it log q} q^{−σ})‖ ≤ (1 − q^{−σ})(1 + q^{−σ})` while the denominator is `1 − 2 q^{−σ} cos(t log q) + q^{−2σ} ≥ 1 + q^{−σ}`, bounding the `q`-factor by `1 − q^{−σ} ≤ e^{−q^{−σ}} ≤ e^{−q⁻¹}` (since `σ ≤ 1`). Disjoint windows `W_m = primesInIoc ⌊X_m⌋₊ ⌊e^ε X_m⌋₊` with `X_m = exp((2π m + 2π/3)/|t|)` and `ε = 2π/(3|t|)` have `cos(t log q) ≤ −1/2` on `W_m` and `∑_{q ∈ W_m} q⁻¹ ≥ c'/(m + 1)` for `m ≥ m₀` by `exists_card_primes_window_ge`. Letting `M → ∞` drives `∏_{q ∈ ⋃_{m=m₀}^M W_m} (1 − q^{−σ}) → 0`, so `Φ(σ + it) = 0` for all `t ≠ 0`. Continuity of `t ↦ Φ(σ + it)` (dominated by `f(y) e^{σy}`) forces `Φ(σ) = ∫ f(y) e^{σy} dy = 0`, and continuity of `f ≥ 0` forces `f = 0`.

4. *Oscillatory Bernstein dichotomy at `α = 1` (`[PROVED HERE]`).*
   Writing `cos(ωy) = Re(e^{iωy})`, geometric summation of `hasSum_chiProd_mul_pow_complex` gives for `α > 0`:
   `torusSum (ampl f (log p) x) θ = e^{−αx} (∏_j ‖1 − p_j^{−α} e^{iθ_j}‖⁻² + ε Re(e^{iωx} ∏_j ((1 − p_j^{−α+iω} e^{iθ_j})(1 − p_j^{−α+iω} e^{−iθ_j}))⁻¹))`.
   - If `0 < α ≤ 1` and `ε ≠ 0` (`ω ≠ 0`), set `θ_j = −ω log p_j` on `P_M = ⋃_{m=m₀}^M W_m`. Each `q ∈ P_M` has `cos(ω log q) ≤ −1/2`, so `A₀ / ‖Z‖ ≤ ∏_{q ∈ P_M} (1 − q^{−α}) → 0` as `M → ∞` (`α ≤ 1`). Choosing `M` with `A₀ < |ε| ‖Z‖` and `x = (π − arg(εZ))/ω` gives `ε Re(e^{iωx} Z) = −|ε| ‖Z‖`, making `torusSum < 0`.
   - If `α > 1`, `∏_j ‖1 − p_j^{−α} e^{iθ_j}‖⁻² ≥ exp(−2 ∑'_m m^{−α}) > 0`, while for `q ≥ 2` and `α > 1`, `q^{−α} ≤ 1/2` gives `(1 − q^{−α})⁻¹ ≤ exp(2 q^{−α})`, bounding `‖Z‖ ≤ exp(4 ∑'_m m^{−α}) = K_α` uniformly in `n, p, θ`. Taking `ε₀ = c_α / (2 K_α)` gives strict all-base torus positivity for `0 < |ε| ≤ ε₀`, whereas `2 × 2` Hankel tests at `(π/(2|ω|), 3π/(2|ω|))` (`ε > 0`) and `(0, π/|ω|)` (`ε < 0`) evaluate to `∓4ε < 0`, refuting `IsExpConvexFrom 0 f`.

5. *Signed finite Laplace mixture dichotomy at `α = 1` (`[PROVED HERE]`).*
   - *`0 < α₀ < … < α_{m−1} ≤ 1`:* Sufficiency of `c_r ≥ 0` follows from `isExpConvexFrom_exp` and `IsExpConvexFrom.torusSum`. Conversely, suppose `c_{r₁} < 0`. On any finite set `S` of primes `q ≥ 5` with `θ_q = π`, `torusSum (ampl f (log q) x) (fun _ => π) = ∑_r c_r exp(L_S(α_r, x))` where `L_S(α, x) = −αx − 2 ∑_{q ∈ S} log(1 + q^{−α})`. Set `x_S = ∑_{q ∈ S} 2 log q / (q^{α_{r₁}} + 1)`. For each `q ≥ 5`, `u_q(t) = −2 log(1 + q^{−t})` satisfies `u_q(α_r) − u_q(α_{r₁}) − u_q'(α_{r₁})(α_r − α_{r₁}) ≤ −(α_r − α_{r₁})²/(4q)` on `[0, 1]`, so summing over `q ∈ S` gives `L_S(α_r, x_S) − L_S(α_{r₁}, x_S) ≤ −(gap/4) ∑_{q ∈ S} q⁻¹` for all `r ≠ r₁`. Choosing `S` via `exists_finset_primes_ge_five_sum_gt` makes `torusSum < 0`.
   - *`1 < α₀ < α₁ < α₂`:* Pointwise `e^{−α₁ x} ≤ e^{−α₀ x} + e^{−α₂ x}` on `ℝ` together with uniform Euler bounds gives strict all-base torus positivity of `e^{−α₀ y} − ε e^{−α₁ y} + e^{−α₂ y}` for small `ε > 0`, whereas on `(t₀, t₁, t₂) = (0, 1, 2)` with `d = (e^{−α₀ − α₂}, −(e^{−α₀} + e^{−α₂}), 1)` the `3 × 3` Hankel form equals `−ε ((e^{−α₁} − e^{−α₀})(e^{−α₁} − e^{−α₂}))² < 0`.
