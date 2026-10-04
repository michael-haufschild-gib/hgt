import GaloisForLFunctions.RHTower.NicolasScaledDefectRH
import GaloisForLFunctions.RHTower.ChebyshevPsiErrorInputs

/-!
# Robin's inequality at `lcm(1, …, n)`

Let `L_n = lcm(1, …, n)`, so `log L_n = ψ(n)` and
`σ(L_n)/L_n = ∏_{p ≤ n} (1 - p^{-K_p - 1})/(1 - 1/p)` with `K_p = ⌊log_p n⌋`.  The Riemann
hypothesis holds if and only if `σ(L_n) < e^γ L_n log log L_n` for all large `n`.

The Robin defect `log(σ(L)/L) - γ - log log ψ` splits as
`G + Δ + [E/(x log x) - (log log ψ - log log x)] + Σ_p log(1 - p^{-K_p-1})`: the Mertens remainder
`G`,
the Euler-product prime tails `Δ`, a nonnegative second-order term, and the deficit of the
exponents.  Both `Δ √x log x → 1` and `Σ_p -log(1 - p^{-K_p-1}) √x log x → 2` follow from the prime
number theorem through `Σ_{√x < p ≤ x} p^{-2} ~ 2/(√x log x)`.  Under RH,
`G √x log x - Φ(log x) → 0`,
so the scaled defect tends to `Φ - 1 ≤ a₁ - 1 < 0`.  Conversely, the inequality for all large `n`
forces `G √x log x ≤ 1 + o(1)` (the second-order term has the favourable sign), the inversion of
`G` gives an upper bound for the lag primitive, and an upper bound for the lag function `Φ` is
the Riemann hypothesis.
-/

open MeasureTheory Set Filter Topology
open ArithmeticFunction (vonMangoldt sigma isMultiplicative_sigma sigma_one_apply_prime_pow)
open GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

/-! ## The prime number theorem for prime squares -/

/-- `θ(t)/t → 1`. -/
theorem tendsto_theta_div_self : Tendsto (fun t : ℝ => Chebyshev.theta t / t) atTop (𝓝 1) := by
  have hψ := tendsto_psi_div_self
  have h0 : Tendsto (fun t : ℝ => 2 * (Real.log t ^ 1 / t ^ (1 / 2 : ℝ))) atTop (𝓝 0) := by
    have := (tendsto_log_pow_div_rpow_atTop 1 (r := 1 / 2) (by norm_num)).const_mul 2
    rwa [mul_zero] at this
  have hsub := hψ.sub h0
  rw [sub_zero] at hsub
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hsub hψ ?_ ?_
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    have ht0 : 0 < t := by linarith
    have h1 := Chebyshev.psi_sub_theta_le ht
    have hst : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht0.le
    have hs0 : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
    have e : 2 * (Real.log t ^ 1 / t ^ (1 / 2 : ℝ)) = 2 * Real.sqrt t * Real.log t / t := by
      rw [← Real.sqrt_eq_rpow, pow_one]
      calc 2 * (Real.log t / Real.sqrt t)
            = 2 * Real.sqrt t * Real.log t / (Real.sqrt t * Real.sqrt t) := by field_simp
        _ = 2 * Real.sqrt t * Real.log t / t := by rw [hst]
    rw [e, ← sub_div]
    exact div_le_div_of_nonneg_right (by linarith) ht0.le
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    exact div_le_div_of_nonneg_right (Chebyshev.theta_le_psi t) ht.le


/-- Prime squares with a relative error `|θ(t) - t| ≤ η t` on `[y, x]`:
`|Σ_{y<p≤x} 1/p² - 1/(y log y)| ≤ 1/(x log x) + 1/(y log²y) + η(1/(x log x) + 4/(y log y))`. -/
theorem abs_sum_prime_inv_sq_sub_le_of_relative {η y x : ℝ} (hη : 0 ≤ η)
    (hS : ∀ t : ℝ, y ≤ t → t ≤ x → |Chebyshev.theta t - t| ≤ η * t) (hy : 16 ≤ y) (hyx : y ≤ x) :
    |∑ n ∈ Finset.Ioc ⌊y⌋₊ ⌊x⌋₊,
        1 / ((n : ℝ) ^ 2 * Real.log n) * (if n.Prime then Real.log n else 0)
        - 1 / (y * Real.log y)|
      ≤ 1 / (x * Real.log x) + 1 / (y * Real.log y ^ 2)
        + η * (1 / (x * Real.log x) + 4 / (y * Real.log y)) := by
  have hy0 : 0 < y := by linarith
  have hx0 : 0 < x := by linarith
  have hpos : ∀ t ∈ uIcc y x, 16 ≤ t := fun t ht => by
    rw [uIcc_of_le hyx] at ht; linarith [ht.1]
  have hwc : ContinuousOn (fun t : ℝ => (2 * Real.log t + 1) / (t ^ 3 * Real.log t ^ 2))
      (uIcc y x) := by
    refine ((continuousOn_const.mul (Real.continuousOn_log.mono ?_)).add continuousOn_const).div
      ((continuousOn_id.pow 3).mul ((Real.continuousOn_log.mono ?_).pow 2)) ?_
    · intro t ht; simp only [mem_compl_iff, mem_singleton_iff]; linarith [hpos t ht]
    · intro t ht; simp only [mem_compl_iff, mem_singleton_iff]; linarith [hpos t ht]
    · intro t ht
      have h1 := one_le_log_of_sixteen_le (hpos t ht)
      have h2 : 0 < t := by linarith [hpos t ht]
      exact mul_ne_zero (pow_ne_zero 3 h2.ne') (pow_ne_zero 2 (by linarith))
  have hti : IntervalIntegrable (fun t => t * ((2 * Real.log t + 1) / (t ^ 3 * Real.log t ^ 2)))
      volume y x := (continuousOn_id.mul hwc).intervalIntegrable
  have hSi : IntervalIntegrable (fun t => (Chebyshev.theta t - t)
      * ((2 * Real.log t + 1) / (t ^ 3 * Real.log t ^ 2))) volume y x :=
    (((Chebyshev.theta_mono.intervalIntegrable).sub
      (continuous_id.intervalIntegrable _ _))).mul_continuousOn hwc
  have hsplit : ∫ t in y..x, Chebyshev.theta t * ((2 * Real.log t + 1) / (t ^ 3 * Real.log t ^ 2))
      = (∫ t in y..x, t * ((2 * Real.log t + 1) / (t ^ 3 * Real.log t ^ 2)))
        + ∫ t in y..x, (Chebyshev.theta t - t)
            * ((2 * Real.log t + 1) / (t ^ 3 * Real.log t ^ 2)) := by
    rw [← intervalIntegral.integral_add hti hSi]
    exact intervalIntegral.integral_congr fun t _ => by ring
  rw [sum_prime_inv_sq_eq_abel (by linarith) hyx, hsplit]
  have hmain := prime_sq_main_identity hy hyx
  have hF := integral_inv_sq_log_eq hy hyx
  have hg := integral_inv_sq_log_sq_le hy hyx
  have hg0 : 0 ≤ ∫ t in y..x, 1 / (t ^ 2 * Real.log t ^ 2) :=
    intervalIntegral.integral_nonneg hyx fun t _ => by positivity
  have hly := one_le_log_of_sixteen_le hy
  have hlx := one_le_log_of_sixteen_le (show 16 ≤ x by linarith)
  have hly0 : 0 < Real.log y := by linarith
  have hlx0 : 0 < Real.log x := by linarith
  have hEx : |(Chebyshev.theta x - x) * (1 / (x ^ 2 * Real.log x))| ≤ η / (x * Real.log x) := by
    have hw : 0 < 1 / (x ^ 2 * Real.log x) := by positivity
    rw [abs_mul, abs_of_pos hw]
    calc |Chebyshev.theta x - x| * (1 / (x ^ 2 * Real.log x))
        ≤ η * x * (1 / (x ^ 2 * Real.log x)) :=
          mul_le_mul_of_nonneg_right (hS x hyx le_rfl) hw.le
      _ = η / (x * Real.log x) := by field_simp
  have hEy : |(Chebyshev.theta y - y) * (1 / (y ^ 2 * Real.log y))| ≤ η / (y * Real.log y) := by
    have hw : 0 < 1 / (y ^ 2 * Real.log y) := by positivity
    rw [abs_mul, abs_of_pos hw]
    calc |Chebyshev.theta y - y| * (1 / (y ^ 2 * Real.log y))
        ≤ η * y * (1 / (y ^ 2 * Real.log y)) :=
          mul_le_mul_of_nonneg_right (hS y le_rfl hyx) hw.le
      _ = η / (y * Real.log y) := by field_simp
  -- the integral error term
  have hEI : |∫ t in y..x, (Chebyshev.theta t - t)
      * ((2 * Real.log t + 1) / (t ^ 3 * Real.log t ^ 2))| ≤ 3 * η / (y * Real.log y) := by
    have hfc : ContinuousOn (fun t : ℝ => 1 / (t ^ 2 * Real.log t)) (uIcc y x) := by
      refine continuousOn_const.div ((continuousOn_id.pow 2).mul
        (Real.continuousOn_log.mono ?_)) ?_
      · intro t ht; simp only [mem_compl_iff, mem_singleton_iff]; linarith [hpos t ht]
      · intro t ht
        have h1 := one_le_log_of_sixteen_le (hpos t ht)
        have h2 : 0 < t := by linarith [hpos t ht]
        exact mul_ne_zero (pow_ne_zero 2 h2.ne') (by linarith)
    have hpt : ∀ᵐ t ∂volume, t ∈ Ioc y x → ‖(Chebyshev.theta t - t)
        * ((2 * Real.log t + 1) / (t ^ 3 * Real.log t ^ 2))‖
          ≤ 3 * η * (1 / (t ^ 2 * Real.log t)) := by
      refine Filter.Eventually.of_forall fun t ht => ?_
      have ht16 : 16 ≤ t := by linarith [ht.1]
      have ht0 : 0 < t := by linarith
      have hlt := one_le_log_of_sixteen_le ht16
      have hlt0 : 0 < Real.log t := by linarith
      have hw0 : 0 < (2 * Real.log t + 1) / (t ^ 3 * Real.log t ^ 2) := by positivity
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos hw0]
      have hwle : (2 * Real.log t + 1) / (t ^ 3 * Real.log t ^ 2) ≤ 3 / (t ^ 3 * Real.log t) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have h3 : 0 < t ^ 3 := pow_pos ht0 3
        nlinarith [mul_pos h3 hlt0]
      calc |Chebyshev.theta t - t| * ((2 * Real.log t + 1) / (t ^ 3 * Real.log t ^ 2))
          ≤ η * t * (3 / (t ^ 3 * Real.log t)) :=
            mul_le_mul (hS t ht.1.le ht.2) hwle hw0.le (by positivity)
        _ = 3 * η * (1 / (t ^ 2 * Real.log t)) := by field_simp
    have hle := intervalIntegral.norm_integral_le_of_norm_le hyx hpt
      (hfc.intervalIntegrable.const_mul (3 * η))
    rw [Real.norm_eq_abs, intervalIntegral.integral_const_mul, hF] at hle
    have hc : 0 ≤ 3 * η := by positivity
    have hxl : 0 ≤ 1 / (x * Real.log x) := by positivity
    calc _ ≤ 3 * η * (1 / (y * Real.log y) - 1 / (x * Real.log x)
          - ∫ t in y..x, 1 / (t ^ 2 * Real.log t ^ 2)) := hle
      _ ≤ 3 * η * (1 / (y * Real.log y)) := mul_le_mul_of_nonneg_left (by linarith) hc
      _ = 3 * η / (y * Real.log y) := by ring
  -- assemble
  have hdecomp : Chebyshev.theta x / (x ^ 2 * Real.log x) - Chebyshev.theta y / (y ^ 2 * Real.log y)
      + ((∫ t in y..x, t * ((2 * Real.log t + 1) / (t ^ 3 * Real.log t ^ 2)))
        + ∫ t in y..x, (Chebyshev.theta t - t) * ((2 * Real.log t + 1) / (t ^ 3 * Real.log t ^ 2)))
      - 1 / (y * Real.log y)
      = -(1 / (x * Real.log x)) - (∫ t in y..x, 1 / (t ^ 2 * Real.log t ^ 2))
        + (Chebyshev.theta x - x) * (1 / (x ^ 2 * Real.log x))
        - (Chebyshev.theta y - y) * (1 / (y ^ 2 * Real.log y))
        + ∫ t in y..x, (Chebyshev.theta t - t)
            * ((2 * Real.log t + 1) / (t ^ 3 * Real.log t ^ 2)) := by
    have e1 : Chebyshev.theta x / (x ^ 2 * Real.log x)
        = x * (1 / (x ^ 2 * Real.log x))
          + (Chebyshev.theta x - x) * (1 / (x ^ 2 * Real.log x)) := by ring
    have e2 : Chebyshev.theta y / (y ^ 2 * Real.log y)
        = y * (1 / (y ^ 2 * Real.log y))
          + (Chebyshev.theta y - y) * (1 / (y ^ 2 * Real.log y)) := by ring
    rw [e1, e2]
    linarith
  rw [hdecomp]
  have hA := abs_add_le (-(1 / (x * Real.log x)) - (∫ t in y..x, 1 / (t ^ 2 * Real.log t ^ 2))
      + (Chebyshev.theta x - x) * (1 / (x ^ 2 * Real.log x))
      - (Chebyshev.theta y - y) * (1 / (y ^ 2 * Real.log y)))
    (∫ t in y..x, (Chebyshev.theta t - t) * ((2 * Real.log t + 1) / (t ^ 3 * Real.log t ^ 2)))
  have hB := abs_sub (-(1 / (x * Real.log x)) - (∫ t in y..x, 1 / (t ^ 2 * Real.log t ^ 2))
      + (Chebyshev.theta x - x) * (1 / (x ^ 2 * Real.log x)))
    ((Chebyshev.theta y - y) * (1 / (y ^ 2 * Real.log y)))
  have hC := abs_add_le (-(1 / (x * Real.log x)) - (∫ t in y..x, 1 / (t ^ 2 * Real.log t ^ 2)))
    ((Chebyshev.theta x - x) * (1 / (x ^ 2 * Real.log x)))
  have hD : |(-(1 / (x * Real.log x)) - (∫ t in y..x, 1 / (t ^ 2 * Real.log t ^ 2)))|
      ≤ 1 / (x * Real.log x) + 1 / (y * Real.log y ^ 2) := by
    have : 0 ≤ 1 / (x * Real.log x) := by positivity
    rw [abs_le]; constructor <;> linarith
  have e3 : η * (1 / (x * Real.log x) + 4 / (y * Real.log y))
      = η / (x * Real.log x) + η / (y * Real.log y) + 3 * η / (y * Real.log y) := by ring
  rw [e3]
  linarith only [hA, hB, hC, hD, hEx, hEy, hEI]

/-- **Prime squares beyond `√x`, unconditionally.**  `(Σ_{√x<p≤x} 1/p²) √x log x → 2`. -/
theorem tendsto_sum_prime_inv_sq_scaled_pnt :
    Tendsto (fun x : ℝ =>
      (∑ p ∈ ((Finset.Icc 0 ⌊x⌋₊).filter Nat.Prime).filter (fun p : ℕ => Real.sqrt x < p),
        1 / (p : ℝ) ^ 2) * (Real.sqrt x * Real.log x)) atTop (𝓝 2) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- relative error `η = ε/16` for `θ`
  have hθ := tendsto_theta_div_self
  obtain ⟨t₀, ht₀⟩ := eventually_atTop.mp ((tendsto_iff_norm_sub_tendsto_zero.mp hθ).eventually
    (gt_mem_nhds (show (0 : ℝ) < ε / 16 by positivity)))
  have hsmall : Tendsto (fun x : ℝ => 1 / Real.sqrt x + 4 / Real.log x + ε / 16 * (1 / Real.sqrt x))
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun x : ℝ => 1 / Real.sqrt x) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop Real.tendsto_sqrt_atTop
    have h2 : Tendsto (fun x : ℝ => 4 / Real.log x) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
    have := (h1.add h2).add (h1.const_mul (ε / 16))
    simpa using this
  obtain ⟨X₁, hX₁⟩ := eventually_atTop.mp (hsmall.eventually (gt_mem_nhds
    (show (0 : ℝ) < ε / 4 by positivity)))
  obtain ⟨X₂, hX₂⟩ := eventually_atTop.mp (Real.tendsto_sqrt_atTop.eventually
    (eventually_ge_atTop (max 16 (max t₀ 1))))
  refine ⟨max (max X₁ X₂) 256, fun x hx => ?_⟩
  have hx256 : 256 ≤ x := le_trans (le_max_right _ _) hx
  have hx0 : 0 < x := by linarith
  have hsx := hX₂ x (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx)
  have hy16 : 16 ≤ Real.sqrt x := le_trans (le_max_left _ _) hsx
  have hyt : t₀ ≤ Real.sqrt x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hsx
  have hy0 : 0 < Real.sqrt x := by linarith
  have hyy : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
  have hyx : Real.sqrt x ≤ x := by nlinarith
  have hlogy : Real.log (Real.sqrt x) = Real.log x / 2 := Real.log_sqrt hx0.le
  have hlx : 0 < Real.log x := Real.log_pos (by linarith)
  have hS : ∀ t : ℝ, Real.sqrt x ≤ t → t ≤ x → |Chebyshev.theta t - t| ≤ ε / 16 * t := by
    intro t ht _
    have ht0 : 0 < t := by linarith
    have h := ht₀ t (le_trans hyt ht)
    rw [Real.norm_eq_abs, show Chebyshev.theta t / t - 1 = (Chebyshev.theta t - t) / t by
      field_simp, abs_div, abs_of_pos ht0, div_lt_iff₀ ht0] at h
    linarith
  have hb := abs_sum_prime_inv_sq_sub_le_of_relative (by positivity) hS hy16 hyx
  rw [← sum_filter_prime_inv_sq_eq (Real.sqrt_nonneg x)] at hb
  set Sm := ∑ p ∈ ((Finset.Icc 0 ⌊x⌋₊).filter Nat.Prime).filter (fun p : ℕ => Real.sqrt x < p),
    1 / (p : ℝ) ^ 2 with hSm
  have hD : 0 < Real.sqrt x * Real.log x := by positivity
  have hkey : Sm * (Real.sqrt x * Real.log x) - 2
      = (Sm - 1 / (Real.sqrt x * Real.log (Real.sqrt x))) * (Real.sqrt x * Real.log x) := by
    rw [hlogy]; field_simp
  rw [Real.dist_eq, hkey, abs_mul, abs_of_pos hD]
  have hX1x := hX₁ x (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx)
  have hval : (1 / (x * Real.log x) + 1 / (Real.sqrt x * Real.log (Real.sqrt x) ^ 2)
      + ε / 16 * (1 / (x * Real.log x) + 4 / (Real.sqrt x * Real.log (Real.sqrt x))))
      * (Real.sqrt x * Real.log x)
      = 1 / Real.sqrt x + 4 / Real.log x + ε / 16 * (1 / Real.sqrt x) + ε / 2 := by
    rw [hlogy]
    have e1 : 1 / (x * Real.log x) * (Real.sqrt x * Real.log x) = 1 / Real.sqrt x := by
      calc 1 / (x * Real.log x) * (Real.sqrt x * Real.log x) = Real.sqrt x / x := by field_simp
        _ = Real.sqrt x / (Real.sqrt x * Real.sqrt x) := by rw [hyy]
        _ = 1 / Real.sqrt x := by field_simp
    have e2 : 1 / (Real.sqrt x * (Real.log x / 2) ^ 2) * (Real.sqrt x * Real.log x)
        = 4 / Real.log x := by field_simp; norm_num
    have e3 : 4 / (Real.sqrt x * (Real.log x / 2)) * (Real.sqrt x * Real.log x) = 8 := by
      field_simp; norm_num
    calc _ = 1 / (x * Real.log x) * (Real.sqrt x * Real.log x)
          + 1 / (Real.sqrt x * (Real.log x / 2) ^ 2) * (Real.sqrt x * Real.log x)
          + ε / 16 * (1 / (x * Real.log x) * (Real.sqrt x * Real.log x)
            + 4 / (Real.sqrt x * (Real.log x / 2)) * (Real.sqrt x * Real.log x)) := by ring
      _ = _ := by rw [e1, e2, e3]; ring
  calc |Sm - 1 / (Real.sqrt x * Real.log (Real.sqrt x))| * (Real.sqrt x * Real.log x)
      ≤ (1 / (x * Real.log x) + 1 / (Real.sqrt x * Real.log (Real.sqrt x) ^ 2)
          + ε / 16 * (1 / (x * Real.log x) + 4 / (Real.sqrt x * Real.log (Real.sqrt x))))
          * (Real.sqrt x * Real.log x) := mul_le_mul_of_nonneg_right hb hD.le
    _ = 1 / Real.sqrt x + 4 / Real.log x + ε / 16 * (1 / Real.sqrt x) + ε / 2 := hval
    _ < ε := by linarith


/-! ## The divisor sum of `lcm(1, …, n)` -/

/-- The exponent factor `1 - p^{-(K_p + 1)}`, `K_p = ⌊log_p n⌋`. -/
def robinExponentFactor (n p : ℕ) : ℝ := 1 - 1 / (p : ℝ) ^ (Nat.log p n + 1)

theorem robinExponentFactor_pos (n : ℕ) {p : ℕ} (hp : p.Prime) : 0 < robinExponentFactor n p := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have h1 : (1 : ℝ) < (p : ℝ) ^ (Nat.log p n + 1) := one_lt_pow₀ hp1 (Nat.succ_ne_zero _)
  unfold robinExponentFactor
  have : 1 / (p : ℝ) ^ (Nat.log p n + 1) < 1 := by rw [div_lt_one (by linarith)]; exact h1
  linarith

/-- `σ(L_n)/L_n = ∏_{p ≤ n} (1 - p^{-(K_p+1)})/(1 - 1/p)`. -/
theorem sigma_lcmUpto_div_eq (n : ℕ) :
    (sigma 1 (Nat.lcmUpto n) : ℝ) / (Nat.lcmUpto n : ℝ)
      = ∏ p ∈ (Finset.Icc 0 n).filter Nat.Prime, robinExponentFactor n p / (1 - 1 / (p : ℝ)) := by
  rw [Nat.lcmUpto_eq_prod_pow_log, ← Nat.primesLE_eq_filter_Icc_zero,
    isMultiplicative_sigma.map_prod (fun p => p ^ Nat.log p n) n.primesLE ?_]
  · push_cast
    rw [← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun p hp => ?_
    have hpp : p.Prime := Nat.prime_of_mem_primesLE hp
    rw [sigma_one_apply_prime_pow hpp]
    push_cast
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hpp.one_lt
    have hp0 : (p : ℝ) ≠ 0 := by positivity
    have hp1' : (p : ℝ) - 1 ≠ 0 := by linarith
    rw [geom_sum_eq hp1.ne']
    unfold robinExponentFactor
    field_simp
    ring
  · intro p hp q hq hpq
    exact Nat.Coprime.pow _ _ ((Nat.coprime_primes (Nat.prime_of_mem_primesLE hp)
      (Nat.prime_of_mem_primesLE hq)).mpr hpq)

/-- The exponent deficit `E(n) = Σ_{p ≤ n} -log(1 - p^{-(K_p+1)})`. -/
def robinExponentDeficit (n : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Icc 0 n).filter Nat.Prime, -Real.log (robinExponentFactor n p)

/-- `log(σ(L_n)/L_n) = -log ∏_{p ≤ n}(1 - 1/p) - E(n)`. -/
theorem log_sigma_lcmUpto_div_eq (n : ℕ) :
    Real.log ((sigma 1 (Nat.lcmUpto n) : ℝ) / (Nat.lcmUpto n : ℝ))
      = -Real.log (mertensPrimeProduct n) - robinExponentDeficit n := by
  have hq : ∀ p ∈ (Finset.Icc 0 n).filter Nat.Prime, 0 < 1 - 1 / (p : ℝ) := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Finset.mem_filter.mp hp).2.two_le
    have : 1 / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
    linarith
  rw [sigma_lcmUpto_div_eq, Real.log_prod (fun p hp => (div_pos (robinExponentFactor_pos n
    (Finset.mem_filter.mp hp).2) (hq p hp)).ne'), neg_log_mertensPrimeProduct_eq,
    robinExponentDeficit, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Real.log_div (robinExponentFactor_pos n (Finset.mem_filter.mp hp).2).ne' (hq p hp).ne']
  ring

/-- The Robin defect at `L_n`: `log(σ(L_n)/L_n) - γ - log log ψ(n)`. -/
def robinLcmDefect (n : ℕ) : ℝ :=
  Real.log ((sigma 1 (Nat.lcmUpto n) : ℝ) / (Nat.lcmUpto n : ℝ)) - Real.eulerMascheroniConstant
    - Real.log (Real.log (Chebyshev.psi n))

/-- **The decomposition of the Robin defect.**  For `n ≥ 2`,
`D(n) = Δ(n) + G(log n) + [(ψ(n) - n)/(n log n) - (log log ψ(n) - log log n)] - E(n)`. -/
theorem robinLcmDefect_eq {n : ℕ} (hn : 2 ≤ n) :
    robinLcmDefect n = (mertensProductError n - mertensError n)
      + mertensErrorRemainder (Real.log n)
      + ((Chebyshev.psi n - n) / (n * Real.log n)
        - (Real.log (Real.log (Chebyshev.psi n)) - Real.log (Real.log n)))
      - robinExponentDeficit n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  rw [robinLcmDefect, log_sigma_lcmUpto_div_eq, mertensErrorRemainder, Real.exp_log hn0]
  unfold mertensProductError
  rw [Nat.floor_natCast]
  ring

/-- **Robin's inequality at `L_n` is the negativity of the defect.** -/
theorem robin_lcmUpto_iff {n : ℕ} (hψ : 1 < Chebyshev.psi n) :
    (sigma 1 (Nat.lcmUpto n) : ℝ)
        < Real.exp Real.eulerMascheroniConstant * Nat.lcmUpto n
          * Real.log (Real.log (Nat.lcmUpto n))
      ↔ robinLcmDefect n < 0 := by
  have hL : (0 : ℝ) < Nat.lcmUpto n := by exact_mod_cast Nat.lcmUpto_pos n
  have hσ : (0 : ℝ) < sigma 1 (Nat.lcmUpto n) := by
    exact_mod_cast ArithmeticFunction.sigma_pos 1 (Nat.lcmUpto n) (Nat.lcmUpto_ne_zero n)
  rw [← Chebyshev.psi_eq_log_lcmUpto]
  have hll : 0 < Real.log (Chebyshev.psi n) := Real.log_pos hψ
  have hR : 0 < Real.exp Real.eulerMascheroniConstant * Real.log (Chebyshev.psi n) :=
    mul_pos (Real.exp_pos _) hll
  rw [robinLcmDefect, sub_sub, sub_neg, ← Real.log_exp Real.eulerMascheroniConstant,
    ← Real.log_mul (Real.exp_pos _).ne' hll.ne', Real.log_lt_log_iff (div_pos hσ hL) hR,
    Real.log_exp, div_lt_iff₀ hL]
  constructor <;> intro h <;> linarith


/-! ## The exponent deficit -/

/-- `y ≤ -log(1 - y) ≤ y + 2y²` for `y ≤ 1/2`. -/
theorem neg_log_one_sub_mem {y : ℝ} (hy : y ≤ 1 / 2) :
    y ≤ -Real.log (1 - y) ∧ -Real.log (1 - y) ≤ y + 2 * y ^ 2 := by
  have h1 : 0 < 1 - y := by linarith
  constructor
  · have := Real.log_le_sub_one_of_pos h1
    linarith
  · have h2 := Real.one_sub_inv_le_log_of_pos h1
    have h3 : (1 - y)⁻¹ ≤ 1 + y + 2 * y ^ 2 := by
      rw [inv_le_iff_one_le_mul₀ h1]
      nlinarith
    linarith

/-- For a prime `√n < p ≤ n`, the exponent is `K_p = 1`. -/
theorem nat_log_eq_one_of_sqrt_lt {n p : ℕ} (hp : p.Prime) (hpn : p ≤ n)
    (hsp : Real.sqrt n < p) : Nat.log p n = 1 := by
  rw [Nat.log_eq_one_iff]
  refine ⟨?_, hp.one_lt, hpn⟩
  have h := (Real.sqrt_lt' (by exact_mod_cast hp.pos)).mp hsp
  have : (n : ℝ) < (p * p : ℕ) := by push_cast; nlinarith
  exact_mod_cast this

/-- For a prime `p ≤ √n`, `p^{K_p + 1} ≥ n^{2/3} p`. -/
theorem rpow_two_thirds_mul_le_pow {n p : ℕ} (hn : 0 < n) (hp : p.Prime)
    (hsp : ¬ Real.sqrt n < p) :
    ((n : ℝ) ^ ((1 : ℝ) / 3)) ^ 2 * p ≤ (p : ℝ) ^ (Nat.log p n + 1) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  set t := (n : ℝ) ^ ((1 : ℝ) / 3) with ht
  have ht0 : 0 ≤ t := Real.rpow_nonneg hn0.le _
  have ht3 : t ^ 3 = n := by
    rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul hn0.le]; norm_num
  have hpsq : (p : ℝ) ^ 2 ≤ n := by
    have h := not_lt.mp hsp
    rw [Real.le_sqrt (by positivity) hn0.le] at h
    exact h
  have hK : 2 ≤ Nat.log p n := Nat.le_log_of_pow_le hp.one_lt (by exact_mod_cast hpsq)
  have hY1 : (n : ℝ) < (p : ℝ) ^ (Nat.log p n + 1) := by
    have := Nat.lt_pow_succ_log_self hp.one_lt n
    exact_mod_cast this
  have hY2 : (p : ℝ) ^ 3 ≤ (p : ℝ) ^ (Nat.log p n + 1) :=
    pow_le_pow_right₀ hp1.le (by omega)
  by_cases hpt : (p : ℝ) ≤ t
  · calc t ^ 2 * p ≤ t ^ 2 * t := mul_le_mul_of_nonneg_left hpt (sq_nonneg t)
      _ = t ^ 3 := by ring
      _ ≤ _ := by rw [ht3]; exact hY1.le
  · have h2 : t ^ 2 ≤ (p : ℝ) ^ 2 := pow_le_pow_left₀ ht0 (not_le.mp hpt).le 2
    calc t ^ 2 * p ≤ (p : ℝ) ^ 2 * p := mul_le_mul_of_nonneg_right h2 (by positivity)
      _ = (p : ℝ) ^ 3 := by ring
      _ ≤ _ := hY2

/-- The large primes: `S ≤ Σ_{√n<p≤n} -log(1 - p^{-(K_p+1)}) ≤ (1 + 2/n) S`,
`S = Σ_{√n<p≤n} 1/p²`. -/
theorem sum_large_robinExponent_mem {n : ℕ} (hn : 0 < n) :
    let F := ((Finset.Icc 0 n).filter Nat.Prime).filter (fun p : ℕ => Real.sqrt n < p)
    ∑ p ∈ F, 1 / (p : ℝ) ^ 2 ≤ ∑ p ∈ F, -Real.log (robinExponentFactor n p) ∧
      ∑ p ∈ F, -Real.log (robinExponentFactor n p)
        ≤ ∑ p ∈ F, 1 / (p : ℝ) ^ 2 + 2 / n * ∑ p ∈ F, 1 / (p : ℝ) ^ 2 := by
  intro F
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hterm : ∀ p ∈ F, 1 / (p : ℝ) ^ 2 ≤ -Real.log (robinExponentFactor n p) ∧
      -Real.log (robinExponentFactor n p) ≤ 1 / (p : ℝ) ^ 2 + 2 / n * (1 / (p : ℝ) ^ 2) := by
    intro p hp
    simp only [F, Finset.mem_filter, Finset.mem_Icc] at hp
    obtain ⟨⟨⟨_, hpn⟩, hpp⟩, hsp⟩ := hp
    have hK := nat_log_eq_one_of_sqrt_lt hpp hpn hsp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
    have hp0 : (0 : ℝ) < p := by linarith
    have hy0 : 0 ≤ 1 / (p : ℝ) ^ 2 := by positivity
    have hy : 1 / (p : ℝ) ^ 2 ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    have hnp : (n : ℝ) < (p : ℝ) ^ 2 := (Real.sqrt_lt' hp0).mp hsp
    unfold robinExponentFactor
    rw [hK]
    obtain ⟨h1, h2⟩ := neg_log_one_sub_mem hy
    refine ⟨h1, h2.trans ?_⟩
    have : (1 / (p : ℝ) ^ 2) ^ 2 ≤ 1 / n * (1 / (p : ℝ) ^ 2) := by
      rw [div_pow, one_pow, one_div_mul_one_div, ← pow_mul]
      refine one_div_le_one_div_of_le (by positivity) ?_
      rw [show (p : ℝ) ^ (2 * 2) = (p : ℝ) ^ 2 * (p : ℝ) ^ 2 by ring]
      exact mul_le_mul_of_nonneg_right hnp.le (by positivity)
    have e : 2 / (n : ℝ) * (1 / (p : ℝ) ^ 2) = 2 * (1 / n * (1 / (p : ℝ) ^ 2)) := by ring
    rw [e]
    linarith
  refine ⟨Finset.sum_le_sum fun p hp => (hterm p hp).1, ?_⟩
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun p hp => (hterm p hp).2

/-- The small primes: `0 ≤ Σ_{p ≤ √n} -log(1 - p^{-(K_p+1)}) ≤ 2(1 + log n)/n^{2/3}`. -/
theorem sum_small_robinExponent_mem {n : ℕ} (hn : 0 < n) :
    let F := ((Finset.Icc 0 n).filter Nat.Prime).filter (fun p : ℕ => ¬ Real.sqrt n < p)
    0 ≤ ∑ p ∈ F, -Real.log (robinExponentFactor n p) ∧
      ∑ p ∈ F, -Real.log (robinExponentFactor n p)
        ≤ 2 / ((n : ℝ) ^ ((1 : ℝ) / 3)) ^ 2 * (1 + Real.log n) := by
  intro F
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  set t := (n : ℝ) ^ ((1 : ℝ) / 3) with ht
  have ht0 : 0 < t := Real.rpow_pos_of_pos hn0 _
  have hterm : ∀ p ∈ F, 0 ≤ -Real.log (robinExponentFactor n p) ∧
      -Real.log (robinExponentFactor n p) ≤ 2 / t ^ 2 * (1 / (p : ℝ)) := by
    intro p hp
    simp only [F, Finset.mem_filter, Finset.mem_Icc] at hp
    obtain ⟨⟨⟨_, hpn⟩, hpp⟩, hsp⟩ := hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
    have hp0 : (0 : ℝ) < p := by linarith
    have hK1 : 1 ≤ Nat.log p n := Nat.log_pos hpp.one_lt hpn
    have hY := rpow_two_thirds_mul_le_pow hn hpp hsp
    rw [← ht] at hY
    have hYp : (0 : ℝ) < (p : ℝ) ^ (Nat.log p n + 1) := by positivity
    have hy0 : 0 ≤ 1 / (p : ℝ) ^ (Nat.log p n + 1) := by positivity
    have hpp2 : (p : ℝ) ^ 2 ≤ (p : ℝ) ^ (Nat.log p n + 1) :=
      pow_le_pow_right₀ (by linarith) (by omega)
    have hy : 1 / (p : ℝ) ^ (Nat.log p n + 1) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ hYp (by norm_num)]; nlinarith
    obtain ⟨h1, h2⟩ := neg_log_one_sub_mem hy
    unfold robinExponentFactor
    refine ⟨le_trans hy0 h1, h2.trans ?_⟩
    have hsq : 2 * (1 / (p : ℝ) ^ (Nat.log p n + 1)) ^ 2
        ≤ 1 / (p : ℝ) ^ (Nat.log p n + 1) := by
      have := mul_le_mul_of_nonneg_left hy hy0
      nlinarith
    have hfin : 1 / (p : ℝ) ^ (Nat.log p n + 1) ≤ 1 / t ^ 2 * (1 / (p : ℝ)) := by
      rw [one_div_mul_one_div]
      exact one_div_le_one_div_of_le (by positivity) hY
    have e : 2 / t ^ 2 * (1 / (p : ℝ)) = 2 * (1 / t ^ 2 * (1 / (p : ℝ))) := by ring
    rw [e]
    linarith
  refine ⟨Finset.sum_nonneg fun p hp => (hterm p hp).1, ?_⟩
  have hH : ∑ p ∈ F, 1 / (p : ℝ) ≤ 1 + Real.log n := by
    have h := harmonic_le_one_add_log n
    rw [harmonic_eq_sum_Icc] at h
    refine le_trans ?_ h
    have hsub : F ⊆ Finset.Icc 1 n := by
      intro p hp
      simp only [F, Finset.mem_filter, Finset.mem_Icc] at hp ⊢
      exact ⟨hp.1.2.one_lt.le, hp.1.1.2⟩
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun i _ _ => by positivity
  calc ∑ p ∈ F, -Real.log (robinExponentFactor n p)
      ≤ ∑ p ∈ F, 2 / t ^ 2 * (1 / (p : ℝ)) := Finset.sum_le_sum fun p hp => (hterm p hp).2
    _ = 2 / t ^ 2 * ∑ p ∈ F, 1 / (p : ℝ) := by rw [Finset.mul_sum]
    _ ≤ 2 / t ^ 2 * (1 + Real.log n) := mul_le_mul_of_nonneg_left hH (by positivity)


/-- `n^{1/2} n^{1/6} = (n^{1/3})²`. -/
theorem sqrt_mul_rpow_sixth {x : ℝ} (hx : 0 < x) :
    Real.sqrt x * x ^ ((1 : ℝ) / 6) = (x ^ ((1 : ℝ) / 3)) ^ 2 := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_add hx, ← Real.rpow_natCast, ← Real.rpow_mul hx.le]
  norm_num

/-- **The exponent deficit, unconditionally.**  `E(n) √n log n → 2`. -/
theorem tendsto_robinExponentDeficit_scaled :
    Tendsto (fun n : ℕ => robinExponentDeficit n * (Real.sqrt n * Real.log n)) atTop (𝓝 2) := by
  set S : ℕ → ℝ := fun n => ∑ p ∈ ((Finset.Icc 0 n).filter Nat.Prime).filter
    (fun p : ℕ => Real.sqrt n < p), 1 / (p : ℝ) ^ 2 with hSdef
  have hS : Tendsto (fun n : ℕ => S n * (Real.sqrt n * Real.log n)) atTop (𝓝 2) := by
    have h := tendsto_sum_prime_inv_sq_scaled_pnt.comp tendsto_natCast_atTop_atTop
    refine h.congr fun n => ?_
    simp only [Function.comp, Nat.floor_natCast, hSdef]
  have hB : Tendsto (fun n : ℕ => 2 / (n : ℝ) * (S n * (Real.sqrt n * Real.log n))
      + 2 * (Real.log n ^ 1 / (n : ℝ) ^ ((1 : ℝ) / 6) + Real.log n ^ 2 / (n : ℝ) ^ ((1 : ℝ) / 6)))
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => 2 / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    have h2 := ((tendsto_log_pow_div_rpow_atTop 1 (r := 1 / 6) (by norm_num)).add
      (tendsto_log_pow_div_rpow_atTop 2 (r := 1 / 6) (by norm_num))).comp
        tendsto_natCast_atTop_atTop
    have := (h1.mul hS).add (h2.const_mul 2)
    simp only [zero_mul, add_zero, mul_zero] at this
    exact this
  have herr : Tendsto (fun n : ℕ => robinExponentDeficit n * (Real.sqrt n * Real.log n)
      - S n * (Real.sqrt n * Real.log n)) atTop (𝓝 0) := by
    refine squeeze_zero' ?_ ?_ hB
    · filter_upwards [eventually_ge_atTop 1] with n hn
      obtain ⟨hl, _⟩ := sum_large_robinExponent_mem (n := n) hn
      obtain ⟨hs, _⟩ := sum_small_robinExponent_mem (n := n) hn
      have hsplit := Finset.sum_filter_add_sum_filter_not ((Finset.Icc 0 n).filter Nat.Prime)
        (fun p : ℕ => Real.sqrt n < p) (fun p => -Real.log (robinExponentFactor n p))
      have hD : 0 ≤ Real.sqrt n * Real.log n :=
        mul_nonneg (Real.sqrt_nonneg _) (Real.log_natCast_nonneg n)
      rw [← sub_mul]
      refine mul_nonneg ?_ hD
      rw [robinExponentDeficit, ← hsplit]
      simp only [hSdef]
      linarith
    · filter_upwards [eventually_ge_atTop 2] with n hn
      have hn1 : 0 < n := by omega
      obtain ⟨_, hl⟩ := sum_large_robinExponent_mem (n := n) hn1
      obtain ⟨_, hs⟩ := sum_small_robinExponent_mem (n := n) hn1
      have hsplit := Finset.sum_filter_add_sum_filter_not ((Finset.Icc 0 n).filter Nat.Prime)
        (fun p : ℕ => Real.sqrt n < p) (fun p => -Real.log (robinExponentFactor n p))
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
      have hlx : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
      have hsx : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
      have hD : 0 < Real.sqrt n * Real.log n := mul_pos hsx hlx
      have h6 := sqrt_mul_rpow_sixth hn0
      have h60 : 0 < (n : ℝ) ^ ((1 : ℝ) / 6) := Real.rpow_pos_of_pos hn0 _
      have hE : robinExponentDeficit n - S n
          ≤ 2 / n * S n + 2 / ((n : ℝ) ^ ((1 : ℝ) / 3)) ^ 2 * (1 + Real.log n) := by
        rw [robinExponentDeficit, ← hsplit]
        simp only [hSdef]
        linarith
      have hval : 2 / ((n : ℝ) ^ ((1 : ℝ) / 3)) ^ 2 * (1 + Real.log n)
          * (Real.sqrt n * Real.log n)
          = 2 * (Real.log n ^ 1 / (n : ℝ) ^ ((1 : ℝ) / 6)
            + Real.log n ^ 2 / (n : ℝ) ^ ((1 : ℝ) / 6)) := by
        rw [← h6]
        field_simp
      rw [← sub_mul]
      calc (robinExponentDeficit n - S n) * (Real.sqrt n * Real.log n)
          ≤ (2 / n * S n + 2 / ((n : ℝ) ^ ((1 : ℝ) / 3)) ^ 2 * (1 + Real.log n))
            * (Real.sqrt n * Real.log n) := mul_le_mul_of_nonneg_right hE hD.le
        _ = _ := by rw [add_mul, hval]; ring
  have := hS.add herr
  rw [add_zero] at this
  refine this.congr fun n => ?_
  ring


/-! ## The forward direction -/

/-- `log log F ≤ log log x + (F - x)/(x log x)` for `x > 1`, `F > 1`. -/
theorem log_log_le_add_div {x F : ℝ} (hx : 1 < x) (hF : 1 < F) :
    Real.log (Real.log F) ≤ Real.log (Real.log x) + (F - x) / (x * Real.log x) := by
  have hx0 : 0 < x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos hx
  have hF0 : 0 < F := by linarith
  have hlF : 0 < Real.log F := Real.log_pos hF
  have h1 : Real.log (Real.log F) - Real.log (Real.log x) ≤ Real.log F / Real.log x - 1 := by
    rw [← Real.log_div hlF.ne' hlx.ne']
    exact Real.log_le_sub_one_of_pos (div_pos hlF hlx)
  have h2 : Real.log F - Real.log x ≤ F / x - 1 := by
    rw [← Real.log_div hF0.ne' hx0.ne']
    exact Real.log_le_sub_one_of_pos (div_pos hF0 hx0)
  have h3 : Real.log F / Real.log x - 1 = (Real.log F - Real.log x) / Real.log x := by field_simp
  have h4 : (Real.log F - Real.log x) / Real.log x ≤ (F / x - 1) / Real.log x :=
    div_le_div_of_nonneg_right h2 hlx.le
  have h5 : (F / x - 1) / Real.log x = (F - x) / (x * Real.log x) := by field_simp
  linarith

/-- Von Koch for `ψ`: under RH, `|ψ(t) - t| ≤ K √t log² t` for `t ≥ 16`. -/
theorem exists_abs_psi_sub_le_of_riemannHypothesis (hRH : RiemannHypothesis) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ, 16 ≤ t →
      |Chebyshev.psi t - t| ≤ K * Real.sqrt t * Real.log t ^ 2 := by
  refine ⟨max 0 (200 * (xiLineTwoLogDerivConstant + 2)), le_max_left _ _, fun t ht => ?_⟩
  have h := abs_chebyshevPsi_sub_le_of_riemannHypothesis hRH ht
  have hst : 0 ≤ Real.sqrt t * Real.log t ^ 2 := by positivity
  calc |Chebyshev.psi t - t| ≤ 200 * (xiLineTwoLogDerivConstant + 2) * Real.sqrt t
        * Real.log t ^ 2 := h
    _ = 200 * (xiLineTwoLogDerivConstant + 2) * (Real.sqrt t * Real.log t ^ 2) := by ring
    _ ≤ max 0 (200 * (xiLineTwoLogDerivConstant + 2)) * (Real.sqrt t * Real.log t ^ 2) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) hst
    _ = _ := by ring

/-- **The second-order ψ-term.**  Under RH,
`√x log x ((ψ(x) - x)/(x log x) - (log log ψ(x) - log log x)) → 0`. -/
theorem tendsto_psi_second_order (hRH : RiemannHypothesis) :
    Tendsto (fun x : ℝ => Real.sqrt x * Real.log x * ((Chebyshev.psi x - x) / (x * Real.log x)
      - (Real.log (Real.log (Chebyshev.psi x)) - Real.log (Real.log x)))) atTop (𝓝 0) := by
  obtain ⟨K, hK, hS⟩ := exists_abs_psi_sub_le_of_riemannHypothesis hRH
  have h0 : Tendsto (fun x : ℝ => 35 / 4 * K ^ 2 * (Real.log x ^ 4 / x ^ (1 / 2 : ℝ))) atTop
      (𝓝 0) := by
    have := (tendsto_log_pow_div_rpow_atTop 4 (r := 1 / 2) (by norm_num)).const_mul (35 / 4 * K ^ 2)
    rwa [mul_zero] at this
  have hψ25 : ∀ᶠ x : ℝ in atTop, 2 / 5 * x ≤ Chebyshev.psi x := by
    filter_upwards [eventually_two_fifths_le_theta] with x hx
    exact hx.trans (Chebyshev.theta_le_psi x)
  refine squeeze_zero' ?_ ?_ h0
  · filter_upwards [hψ25, eventually_ge_atTop (16 : ℝ)] with x hψ hx
    have hψ1 : 1 < Chebyshev.psi x := by linarith
    have h1 := log_log_le_add_div (by linarith : (1 : ℝ) < x) hψ1
    have hD : 0 ≤ Real.sqrt x * Real.log x :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.log_nonneg (by linarith))
    exact mul_nonneg hD (by linarith)
  · filter_upwards [hψ25, eventually_ge_atTop (16 : ℝ)] with x hψ hx
    have hx0 : 0 < x := by linarith
    have hlx : 0 < Real.log x := Real.log_pos (by linarith)
    have hψ1 : 1 < Chebyshev.psi x := by linarith
    have hlψ1 : 1 ≤ Real.log (Chebyshev.psi x) := by
      rw [Real.le_log_iff_exp_le (by linarith)]
      have := Real.exp_one_lt_d9; linarith
    have h1 := log_log_ge_add (by linarith : (1 : ℝ) < x) hψ1
    have h2 := sub_div_sub_le_sq (by linarith : (1 : ℝ) < x) hψ hlψ1
    have hD : 0 < Real.sqrt x * Real.log x := mul_pos (Real.sqrt_pos.mpr hx0) hlx
    have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
    have hsq : (Chebyshev.psi x - x) ^ 2 ≤ (K * Real.sqrt x * Real.log x ^ 2) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hS x hx) 2
    calc Real.sqrt x * Real.log x * ((Chebyshev.psi x - x) / (x * Real.log x)
          - (Real.log (Real.log (Chebyshev.psi x)) - Real.log (Real.log x)))
        ≤ Real.sqrt x * Real.log x * (35 / 4 * ((Chebyshev.psi x - x) ^ 2
            / (x ^ 2 * Real.log x))) := by
          refine mul_le_mul_of_nonneg_left ?_ hD.le
          linarith
      _ ≤ Real.sqrt x * Real.log x * (35 / 4 * ((K * Real.sqrt x * Real.log x ^ 2) ^ 2
            / (x ^ 2 * Real.log x))) := by
          refine mul_le_mul_of_nonneg_left ?_ hD.le
          exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hsq (by positivity))
            (by norm_num)
      _ = 35 / 4 * K ^ 2 * (Real.log x ^ 4 / x ^ (1 / 2 : ℝ)) := by
          have hsq' : (K * Real.sqrt x * Real.log x ^ 2) ^ 2 = K ^ 2 * x * Real.log x ^ 4 := by
            rw [mul_pow, mul_pow, Real.sq_sqrt hx0.le]; ring
          rw [hsq', ← Real.sqrt_eq_rpow]
          have h3 : Real.sqrt x * Real.log x * (35 / 4 * (K ^ 2 * x * Real.log x ^ 4
              / (x ^ 2 * Real.log x))) = 35 / 4 * K ^ 2 * Real.log x ^ 4 * (Real.sqrt x / x) := by
            field_simp
          have h4 : Real.sqrt x / x = 1 / Real.sqrt x := by
            rw [div_eq_div_iff hx0.ne' hsx.ne']
            rw [Real.mul_self_sqrt hx0.le]; ring
          rw [h3, h4]; ring

/-- **The scaled Robin defect at `L_n` is the lag minus one.**  Under RH,
`D(n) √n log n - Φ(log n) → -1`. -/
theorem tendsto_robinLcmDefect_scaled_sub_lag (hRH : RiemannHypothesis) :
    Tendsto (fun n : ℕ => robinLcmDefect n * (Real.sqrt n * Real.log n)
      - weilLagFunctionReal (Real.log n)) atTop (𝓝 (-1)) := by
  have hc := tendsto_natCast_atTop_atTop (R := ℝ)
  have h := ((((tendsto_mertensProductError_sub_scaled hRH).comp hc).add
    ((tendsto_mertensErrorRemainder_scaled_sub_lag hRH).comp hc)).add
      ((tendsto_psi_second_order hRH).comp hc)).sub tendsto_robinExponentDeficit_scaled
  rw [show (1 : ℝ) + 0 + 0 - 2 = -1 by norm_num] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with n hn
  simp only [Function.comp]
  rw [robinLcmDefect_eq hn]
  ring

/-- `1 < ψ(n)` for all large `n`. -/
theorem eventually_one_lt_psi_natCast : ∀ᶠ n : ℕ in atTop, 1 < Chebyshev.psi n := by
  have h := tendsto_natCast_atTop_atTop.eventually
    (eventually_two_fifths_le_theta.and (eventually_ge_atTop (16 : ℝ)))
  filter_upwards [h] with n ⟨hθ, h16⟩
  have := Chebyshev.theta_le_psi (n : ℝ)
  linarith

/-- **Robin's inequality at `L_n` under RH, with Nicolas-type constants.**  Under RH, for every
`ε > 0`: `-1 - a₁ - ε < D(n) √n log n < -1 + a₁ + ε` for all large `n`, and
`D(p) √p log p > -1 + a₁ - ε` for infinitely many primes `p`. -/
theorem robinLcmDefect_scaled_bounds_of_riemannHypothesis (hRH : RiemannHypothesis) {ε : ℝ}
    (hε : 0 < ε) :
    (∀ᶠ n : ℕ in atTop, -1 - poleSharpConstant - ε < robinLcmDefect n * (Real.sqrt n * Real.log n)
      ∧ robinLcmDefect n * (Real.sqrt n * Real.log n) < -1 + poleSharpConstant + ε) ∧
    ∃ᶠ p : ℕ in atTop, p.Prime ∧
      -1 + poleSharpConstant - ε < robinLcmDefect p * (Real.sqrt p * Real.log p) := by
  have hT := tendsto_robinLcmDefect_scaled_sub_lag hRH
  have hev : ∀ᶠ n : ℕ in atTop, |robinLcmDefect n * (Real.sqrt n * Real.log n)
      - weilLagFunctionReal (Real.log n) - (-1)| < ε / 2 := by
    have := (tendsto_iff_norm_sub_tendsto_zero.mp hT).eventually
      (gt_mem_nhds (show (0 : ℝ) < ε / 2 by positivity))
    simpa [Real.norm_eq_abs] using this
  have hΦ : ∀ L : ℝ, |weilLagFunctionReal L| ≤ poleSharpConstant := fun L => by
    have := norm_weilLagFunction_le_of_riemannHypothesis hRH L
    rwa [weilLagFunction_eq_ofReal, Complex.norm_real, Real.norm_eq_abs] at this
  constructor
  · filter_upwards [hev] with n hn
    have h1 := abs_lt.mp hn
    have h2 := abs_le.mp (hΦ (Real.log n))
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  · refine ((frequently_prime_integerLag_gt (show 0 < ε / 2 by positivity)).and_eventually
      hev).mono fun p ⟨⟨hp, hlag⟩, hclose⟩ => ⟨hp, ?_⟩
    unfold integerLag at hlag
    have := (abs_lt.mp hclose).1
    linarith

/-- **Robin's inequality holds at `lcm(1, …, n)` for all large `n` under RH.** -/
theorem eventually_robin_lcmUpto_of_riemannHypothesis (hRH : RiemannHypothesis) :
    ∀ᶠ n : ℕ in atTop, (sigma 1 (Nat.lcmUpto n) : ℝ)
      < Real.exp Real.eulerMascheroniConstant * Nat.lcmUpto n
        * Real.log (Real.log (Nat.lcmUpto n)) := by
  have ha3 := poleSharpConstant_lt_three_tenths
  obtain ⟨h, _⟩ := robinLcmDefect_scaled_bounds_of_riemannHypothesis hRH
    (show (0 : ℝ) < 1 / 2 by norm_num)
  filter_upwards [h, eventually_one_lt_psi_natCast, eventually_ge_atTop 2] with n hn hψ hn2
  rw [robin_lcmUpto_iff hψ]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hD : 0 < Real.sqrt n * Real.log n :=
    mul_pos (Real.sqrt_pos.mpr hn0) (Real.log_pos (by exact_mod_cast (by omega : 1 < n)))
  have hneg : robinLcmDefect n * (Real.sqrt n * Real.log n) < 0 := by linarith [hn.2]
  exact neg_of_mul_neg_left hneg hD.le

end

end RHTower
