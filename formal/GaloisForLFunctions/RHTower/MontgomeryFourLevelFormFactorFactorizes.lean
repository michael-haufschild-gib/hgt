import GaloisForLFunctions.RHTower.MontgomeryTripleFormFactorVanishes

/-!
# The 4-level form factor of ζ zeros factorizes below threshold

For the Lorentzian zero sum `S(x, t)` of Montgomery's method over all zeros of `ξ` (complex
ordinates, no hypothesis):

* **Theorem** (`tendsto_fourLevelFormFactor`): for `0 < α < β` with `α + β < 1`,
  `∫_0^T |S(T^α, t)|² |S(T^β, t)|² dt ~ (αβ/16) T log² T`,
  the product of the pair forms `~ (γ/4) T log T` divided by `T`: the 4-level statistic is Gaussian.
* **The diagonal** (`tendsto_fourthMoment`): for `0 < α < 1/2`,
  `∫_0^T |S(T^α, t)|⁴ dt ~ (α²/8) T log² T`, twice the square of the pair form over `T` — the
  Gaussian fourth moment `E|X|⁴ = 2(E|X|²)²`; the swapped factorizations `(v, u)` supply the
  second copy (`sq_conv_eq_of_not_isPrimePow`, `sum_sq_conv_ge`).

Proof. `|S₁|²|S₂|² = |Z₁Z₂|²/(16x₁x₂)` and `|P₁P₂| = |K[d₁ ⍟ d₂]|`; by the mean value theorem
`∫_0^T |K₁K₂|² = T Σ (d₁ ⍟ d₂)² + O(x₁²x₂² log²)`, and by the pair structure of prime powers
`Σd₁² Σd₂² ≤ Σ (d₁ ⍟ d₂)² ≤ Σd₁² Σd₂² + (Σ d₁d₂)² + c₁x₁x₂`
(`integral_normSq_primeConjSum_mul_bounds`). The cross energy is a vanishing fraction:
`d₁d₂ ≤ √(x₁/x₂) Λ² w_y` with `y = √(x₁x₂)` (`primeAmp_mul_primeAmp_le`), so
`Σ d₁d₂ ≤ 4 T^α log T` (`eventually_tsum_primeAmp_mul_le`). The remainder `E₁Z₂ + P₁E₂` costs
`(1/λ)∫|K₁K₂|² + (λ+1)·O(x₁²x₂² log² + T log³T (x₂/x₁ + x₁/x₂))` with `λ = log T`
(`abs_quadruple_sub_le`, `quad_ratio_le`).
-/

open Complex MeasureTheory Filter Topology
open ArithmeticFunction (vonMangoldt)
open scoped ComplexConjugate LSeries.notation

noncomputable section

namespace RHTower

open PhaseSeries PrimePowerPairs

/-! ### The cross energy `Σ d₁ d₂` -/

/-- `d_x(n) = Λ(n) √n/√x` for `n ≤ x` and `Λ(n) (x/n) √x/√n` for `n > x`. -/
theorem primeAmp_eq_sqrt {x : ℝ} (hx : 0 < x) {n : ℕ} (hn : 0 < n) :
    primeAmp x n = vonMangoldt n * (if (n : ℝ) ≤ x then Real.sqrt n / Real.sqrt x
      else x / n * (Real.sqrt x / Real.sqrt n)) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hy : 0 < x / n := by positivity
  have hsq : (x / n) ^ (1 / 2 : ℝ) = Real.sqrt x / Real.sqrt n := by
    rw [← Real.sqrt_eq_rpow, Real.sqrt_div' _ hn'.le]
  unfold primeAmp
  congr 1
  split_ifs
  · rw [Real.rpow_neg hy.le, hsq, inv_div]
  · rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hy, Real.rpow_one, hsq]

/-- The real inequality behind the cross bound, with `x₁ = a²`, `x₂ = b²`, `n = s²`. -/
theorem cross_weight_le {a b s : ℝ} (ha : 0 < a) (hab : a ≤ b) (hs : 0 < s) :
    (if s ^ 2 ≤ a ^ 2 then s / a else a ^ 2 / s ^ 2 * (a / s)) *
      (if s ^ 2 ≤ b ^ 2 then s / b else b ^ 2 / s ^ 2 * (b / s)) ≤
      a / b * (if s ^ 2 ≤ a * b then 1 else a ^ 2 * b ^ 2 / (s ^ 2) ^ 2) := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  split_ifs with h1 h2 h3 h3 h2 h3 h3
  · rw [div_mul_div_comm, mul_one, div_le_div_iff₀ (by positivity) hb]; nlinarith
  · nlinarith [mul_le_mul_of_nonneg_left hab ha.le]
  · nlinarith
  · nlinarith
  · have e : a ^ 2 / s ^ 2 * (a / s) * (s / b) = a ^ 2 * a / (s ^ 2 * b) := by
      field_simp
    rw [e, mul_one, div_le_div_iff₀ (by positivity) hb]
    nlinarith
  · have e : a ^ 2 / s ^ 2 * (a / s) * (s / b) = a ^ 2 * a / (s ^ 2 * b) := by
      field_simp
    have e2 : a / b * (a ^ 2 * b ^ 2 / (s ^ 2) ^ 2) = a ^ 2 * a * b / (s ^ 2) ^ 2 := by
      field_simp
    rw [e, e2, div_le_div_iff₀ (by positivity) (by positivity)]
    have : s ^ 2 * b * (s ^ 2 * b) ≥ 0 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ a ^ 2 * a * s ^ 2)]
  · nlinarith [mul_le_mul_of_nonneg_left hab hb.le]
  · have e : a ^ 2 / s ^ 2 * (a / s) * (b ^ 2 / s ^ 2 * (b / s)) =
        a ^ 2 * a * (b ^ 2 * b) / ((s ^ 2) ^ 2 * s ^ 2) := by
      field_simp
    have e2 : a / b * (a ^ 2 * b ^ 2 / (s ^ 2) ^ 2) = a ^ 2 * a * b / (s ^ 2) ^ 2 := by
      field_simp
    rw [e, e2, div_le_div_iff₀ (by positivity) (by positivity)]
    have h2' : b ^ 2 ≤ s ^ 2 := le_of_lt (not_le.mp h2)
    have := mul_le_mul_of_nonneg_left h2' (by positivity : (0 : ℝ) ≤ a ^ 2 * a * b * (s ^ 2) ^ 2)
    nlinarith

/-- **The cross energy is a small fraction.** For `1 ≤ x₁ ≤ x₂` and `y = √(x₁x₂)`:
`Σ d_{x₁} d_{x₂} ≤ √(x₁/x₂) Σ_n Λ(n)² w(n)` with `w = 1` on `n ≤ y` and `y²/n²` beyond. -/
theorem primeAmp_mul_primeAmp_le {x₁ x₂ : ℝ} (hx₁ : 1 ≤ x₁) (h12 : x₁ ≤ x₂) (n : ℕ) :
    primeAmp x₁ n * primeAmp x₂ n ≤ Real.sqrt (x₁ / x₂) * (vonMangoldt n ^ 2 *
      (if (n : ℝ) ≤ Real.sqrt (x₁ * x₂) then 1 else x₁ * x₂ / (n : ℝ) ^ 2)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [primeAmp]
  have hx₂ : 1 ≤ x₂ := hx₁.trans h12
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set a := Real.sqrt x₁
  set b := Real.sqrt x₂
  set s := Real.sqrt n
  have ha : 0 < a := Real.sqrt_pos.mpr (by linarith)
  have hb : 0 < b := Real.sqrt_pos.mpr (by linarith)
  have hs : 0 < s := Real.sqrt_pos.mpr hn'
  have ha2 : a ^ 2 = x₁ := Real.sq_sqrt (by linarith)
  have hb2 : b ^ 2 = x₂ := Real.sq_sqrt (by linarith)
  have hs2 : s ^ 2 = n := Real.sq_sqrt hn'.le
  have hab : a ≤ b := Real.sqrt_le_sqrt h12
  have hy : Real.sqrt (x₁ * x₂) = a * b := Real.sqrt_mul (by linarith) _
  have hr : Real.sqrt (x₁ / x₂) = a / b := Real.sqrt_div' _ (by linarith)
  have hw := cross_weight_le ha hab hs
  rw [ha2, hb2, hs2] at hw
  rw [primeAmp_eq_sqrt (by linarith) hn, primeAmp_eq_sqrt (by linarith) hn, hr, hy]
  have hyn : ((n : ℝ) ≤ a * b) ↔ (s ^ 2 ≤ a * b) := by rw [hs2]
  have hx1n : x₁ / n * (a / s) = a ^ 2 / s ^ 2 * (a / s) := by rw [ha2, hs2]
  have hx2n : x₂ / n * (b / s) = b ^ 2 / s ^ 2 * (b / s) := by rw [hb2, hs2]
  have hw' : (if (n : ℝ) ≤ x₁ then s / a else x₁ / n * (a / s)) *
      (if (n : ℝ) ≤ x₂ then s / b else x₂ / n * (b / s)) ≤
      a / b * (if (n : ℝ) ≤ a * b then 1 else x₁ * x₂ / (n : ℝ) ^ 2) := by
    rw [hx1n, hx2n, show x₁ * x₂ / (n : ℝ) ^ 2 = a ^ 2 * b ^ 2 / ((s ^ 2) ^ 2) by
      rw [ha2, hb2, hs2]]
    simp only [← hs2, ← ha2, ← hb2] at hw ⊢
    convert hw using 2
  have hΛ := ArithmeticFunction.vonMangoldt_nonneg (n := n)
  calc vonMangoldt n * (if (n : ℝ) ≤ x₁ then s / a else x₁ / n * (a / s)) *
        (vonMangoldt n * (if (n : ℝ) ≤ x₂ then s / b else x₂ / n * (b / s)))
      = vonMangoldt n ^ 2 * ((if (n : ℝ) ≤ x₁ then s / a else x₁ / n * (a / s)) *
          (if (n : ℝ) ≤ x₂ then s / b else x₂ / n * (b / s))) := by ring
    _ ≤ vonMangoldt n ^ 2 * (a / b * (if (n : ℝ) ≤ a * b then 1 else x₁ * x₂ / (n : ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_left hw' (sq_nonneg _)
    _ = _ := by ring

theorem summable_primeAmp_mul {x₁ x₂ : ℝ} (hx₁ : 1 ≤ x₁) (hx₂ : 1 ≤ x₂) :
    Summable fun n => primeAmp x₁ n * primeAmp x₂ n :=
  ((summable_primeAmp_sq hx₁).add (summable_primeAmp_sq hx₂)).of_nonneg_of_le
    (fun n => mul_nonneg (primeAmp_nonneg (by linarith) n) (primeAmp_nonneg (by linarith) n))
    fun n => by nlinarith [sq_nonneg (primeAmp x₁ n - primeAmp x₂ n)]

theorem summable_vonMangoldt_sq_tail (y : ℝ) :
    Summable fun n : ℕ => if y < (n : ℝ) then vonMangoldt n ^ 2 / (n : ℝ) ^ 2 else 0 := by
  refine (summable_vonMangoldt_tail 0 y).of_nonneg_of_le (fun n => ?_) fun n => ?_
  · split_ifs <;> positivity
  · split_ifs with h
    · have h1 := vonMangoldt_sq_le_log_mul n
      have e : (n : ℝ) ^ (0 + 2) = (n : ℝ) ^ 2 := by norm_num
      rw [e]
      exact div_le_div_of_nonneg_right (by linarith [mul_comm (Real.log n) (vonMangoldt n)])
        (by positivity)
    · exact le_rfl

/-- `Σ d₁d₂ ≤ √(x₁/x₂) (Σ_{n ≤ y} Λ(n)² + x₁x₂ Σ_{n > y} Λ(n)²/n²)`, `y = √(x₁x₂)`. -/
theorem tsum_primeAmp_mul_le {x₁ x₂ : ℝ} (hx₁ : 1 ≤ x₁) (h12 : x₁ ≤ x₂) :
    ∑' n, primeAmp x₁ n * primeAmp x₂ n ≤ Real.sqrt (x₁ / x₂) *
      ((∑ n ∈ Finset.Icc 0 ⌊Real.sqrt (x₁ * x₂)⌋₊, vonMangoldt n ^ 2) +
        x₁ * x₂ * ∑' n : ℕ, if Real.sqrt (x₁ * x₂) < (n : ℝ) then
          vonMangoldt n ^ 2 / (n : ℝ) ^ 2 else 0) := by
  set y := Real.sqrt (x₁ * x₂)
  have hy0 : 0 ≤ y := Real.sqrt_nonneg _
  have hsplit : ∀ n : ℕ, vonMangoldt n ^ 2 * (if (n : ℝ) ≤ y then 1 else x₁ * x₂ / (n : ℝ) ^ 2) =
      (if (n : ℝ) ≤ y then vonMangoldt n ^ 2 else 0) +
        x₁ * x₂ * (if y < (n : ℝ) then vonMangoldt n ^ 2 / (n : ℝ) ^ 2 else 0) := by
    intro n
    by_cases h : (n : ℝ) ≤ y
    · rw [if_pos h, if_pos h, if_neg (not_lt.mpr h)]; ring
    · rw [if_neg h, if_neg h, if_pos (not_le.mp h)]; ring
  have hfin : Summable fun n : ℕ => if (n : ℝ) ≤ y then vonMangoldt n ^ 2 else 0 := by
    refine summable_of_ne_finset_zero (s := Finset.Icc 0 ⌊y⌋₊) fun n hn => ?_
    rw [if_neg]
    intro h
    exact hn (Finset.mem_Icc.mpr ⟨Nat.zero_le _, Nat.le_floor h⟩)
  have hfinsum : ∑' n : ℕ, (if (n : ℝ) ≤ y then vonMangoldt n ^ 2 else 0) =
      ∑ n ∈ Finset.Icc 0 ⌊y⌋₊, vonMangoldt n ^ 2 := by
    rw [tsum_eq_sum (s := Finset.Icc 0 ⌊y⌋₊) fun n hn => ?_]
    · refine Finset.sum_congr rfl fun n hn => ?_
      rw [if_pos ((Nat.le_floor_iff hy0).mp (Finset.mem_Icc.mp hn).2)]
    · rw [if_neg]
      intro h
      exact hn (Finset.mem_Icc.mpr ⟨Nat.zero_le _, Nat.le_floor h⟩)
  have hS : Summable fun n : ℕ => Real.sqrt (x₁ / x₂) * (vonMangoldt n ^ 2 *
      (if (n : ℝ) ≤ y then 1 else x₁ * x₂ / (n : ℝ) ^ 2)) := by
    simp_rw [hsplit]
    exact (hfin.add ((summable_vonMangoldt_sq_tail y).mul_left _)).mul_left _
  refine ((summable_primeAmp_mul hx₁ (hx₁.trans h12)).tsum_le_tsum
    (primeAmp_mul_primeAmp_le hx₁ h12) hS).trans (le_of_eq ?_)
  rw [tsum_mul_left, tsum_congr hsplit,
    hfin.tsum_add ((summable_vonMangoldt_sq_tail y).mul_left _), tsum_mul_left, hfinsum]

/-- **Eventually `Σ d_{T^α} d_{T^β} ≤ 4 T^α log T`** for `0 < α < β`. -/
theorem eventually_tsum_primeAmp_mul_le {α β : ℝ} (hα : 0 < α) (hαβ : α < β) (hαβ2 : α + β ≤ 2) :
    ∀ᶠ T : ℝ in atTop, ∑' n, primeAmp (T ^ α) n * primeAmp (T ^ β) n ≤
      4 * T ^ α * Real.log T := by
  have hγ : 0 < (α + β) / 2 := by linarith
  have hy := tendsto_rpow_atTop hγ
  have hψ := hy.eventually (tendsto_partialSumReal_vonMangoldt_div.eventually
    (eventually_le_nhds (by norm_num : (1 : ℝ) < 2)))
  have htail := hy.eventually ((tendsto_tail_vonMangoldt_sq 0).eventually
    (eventually_le_nhds (by norm_num : 1 / (((0 : ℕ) : ℝ) + 1) < 2)))
  have hy1 := hy.eventually (eventually_gt_atTop (1 : ℝ))
  filter_upwards [hψ, htail, hy1, eventually_gt_atTop (1 : ℝ)] with T hψ htail hy1 hT1
  have hT0 : 0 < T := by linarith
  have hx₁ : 1 ≤ T ^ α := Real.one_le_rpow hT1.le hα.le
  have h12 : T ^ α ≤ T ^ β := Real.rpow_le_rpow_of_exponent_le hT1.le hαβ.le
  set y := T ^ ((α + β) / 2) with hydef
  have hyeq : Real.sqrt (T ^ α * T ^ β) = y := by
    rw [← Real.rpow_add hT0, Real.sqrt_eq_rpow, ← Real.rpow_mul hT0.le, hydef]; ring_nf
  have hy0 : 0 < y := by linarith
  have hlogy : 0 < Real.log y := Real.log_pos hy1
  have hlogyT : Real.log y ≤ Real.log T := by
    rw [hydef, Real.log_rpow hT0]
    exact mul_le_of_le_one_left (Real.log_nonneg hT1.le) (by linarith)
  have h := tsum_primeAmp_mul_le hx₁ h12
  rw [hyeq] at h
  -- the head `Σ_{n ≤ y} Λ² ≤ log y · ψ(y) ≤ 2 y log y`
  have hhead : ∑ n ∈ Finset.Icc 0 ⌊y⌋₊, vonMangoldt n ^ 2 ≤ 2 * y * Real.log y := by
    have hle : ∀ n ∈ Finset.Icc 0 ⌊y⌋₊, vonMangoldt n ^ 2 ≤ Real.log y * vonMangoldt n := by
      intro n hn
      rcases Nat.eq_zero_or_pos n with rfl | hn0
      · simp
      have hny : (n : ℝ) ≤ y := (Nat.le_floor_iff hy0.le).mp (Finset.mem_Icc.mp hn).2
      have hlog : vonMangoldt n ≤ Real.log y := ArithmeticFunction.vonMangoldt_le_log.trans
        (Real.log_le_log (by exact_mod_cast hn0) hny)
      rw [sq]
      exact mul_le_mul_of_nonneg_right hlog ArithmeticFunction.vonMangoldt_nonneg
    refine (Finset.sum_le_sum hle).trans ?_
    rw [← Finset.mul_sum]
    have hps : ∑ n ∈ Finset.Icc 0 ⌊y⌋₊, vonMangoldt n ≤ 2 * y := by
      have := hψ; simp only [partialSumReal] at this; rw [div_le_iff₀ hy0] at this; exact this
    have := mul_le_mul_of_nonneg_left hps hlogy.le
    linarith
  -- the tail `Σ_{n > y} Λ²/n² ≤ 2 log y/y`
  have htail' : (∑' n : ℕ, if y < (n : ℝ) then vonMangoldt n ^ 2 / (n : ℝ) ^ 2 else 0) ≤
      2 * Real.log y / y := by
    have := htail
    simp only [zero_add, pow_one] at this
    rw [div_mul_eq_mul_div, div_le_iff₀ hlogy] at this
    rw [le_div_iff₀ hy0]; linarith
  have hxy : T ^ α * T ^ β = y ^ 2 := by
    rw [← Real.rpow_add hT0, hydef, ← Real.rpow_natCast, ← Real.rpow_mul hT0.le]; ring_nf
  have hr : Real.sqrt (T ^ α / T ^ β) * y = T ^ α := by
    rw [← hyeq, ← Real.sqrt_mul (div_nonneg (by positivity) (by positivity)),
      show T ^ α / T ^ β * (T ^ α * T ^ β) = (T ^ α) ^ 2 by
        field_simp]
    exact Real.sqrt_sq (by positivity)
  have hsq0 : 0 ≤ Real.sqrt (T ^ α / T ^ β) := Real.sqrt_nonneg _
  calc ∑' n, primeAmp (T ^ α) n * primeAmp (T ^ β) n
      ≤ Real.sqrt (T ^ α / T ^ β) * (2 * y * Real.log y + y ^ 2 * (2 * Real.log y / y)) := by
        rw [hxy] at h
        refine h.trans (mul_le_mul_of_nonneg_left (add_le_add hhead ?_) hsq0)
        exact mul_le_mul_of_nonneg_left htail' (by positivity)
    _ = 4 * (Real.sqrt (T ^ α / T ^ β) * y) * Real.log y := by field_simp; ring
    _ ≤ 4 * T ^ α * Real.log T := by
        rw [hr]; exact mul_le_mul_of_nonneg_left hlogyT (by positivity)

/-! ### The quadruple on the prime side -/

/-- The energy of a product of prime sides:
`(Σ d₁²)(Σ d₂²) − 104 B ≤ ∫_0^T |K₁K₂|² − 0 ≤ T((Σ d₁²)(Σ d₂²) + (Σ d₁d₂)² + c₁x₁x₂) + 104 B`,
`B = 2 A₁A₂ + c₁ x₁²x₂²`, `A_i = Σ n d_{x_i}(n)²`. -/
theorem integral_normSq_primeConjSum_mul_bounds {x₁ x₂ : ℝ} (hx₁ : 1 ≤ x₁) (hx₂ : 1 ≤ x₂) {T : ℝ}
    (hT : 0 ≤ T) :
    T * ((∑' n, primeAmp x₁ n ^ 2) * ∑' n, primeAmp x₂ n ^ 2) -
        104 * (2 * (∑' n : ℕ, (n : ℝ) * primeAmp x₁ n ^ 2) * (∑' n : ℕ, (n : ℝ) * primeAmp x₂ n ^ 2)
          + x₁ ^ 2 * x₂ ^ 2 * ∑' m, ppWeight m) ≤
      ∫ t in (0 : ℝ)..T, ‖primeConjSum x₁ t * primeConjSum x₂ t‖ ^ 2 ∧
    ∫ t in (0 : ℝ)..T, ‖primeConjSum x₁ t * primeConjSum x₂ t‖ ^ 2 ≤
      T * ((∑' n, primeAmp x₁ n ^ 2) * (∑' n, primeAmp x₂ n ^ 2) +
          (∑' n, primeAmp x₁ n * primeAmp x₂ n) ^ 2 + x₁ * x₂ * ∑' m, ppWeight m) +
        104 * (2 * (∑' n : ℕ, (n : ℝ) * primeAmp x₁ n ^ 2) * (∑' n : ℕ, (n : ℝ) * primeAmp x₂ n ^ 2)
          + x₁ ^ 2 * x₂ ^ 2 * ∑' m, ppWeight m) := by
  have h1 := ppBound_primeAmp_half hx₁
  have h2 := ppBound_primeAmp_half hx₂
  have h1' := ppBound_primeAmp_threeHalves hx₁
  have h2' := ppBound_primeAmp_threeHalves hx₂
  have hd1 := fun n => primeAmp_nonneg (x := x₁) (by linarith) n
  have hd2 := fun n => primeAmp_nonneg (x := x₂) (by linarith) n
  set c : ℕ → ℝ := primeAmp x₁ ⍟ primeAmp x₂ with hc
  have hc0 : ∀ n, 0 ≤ c n := conv_nonneg hd1 hd2
  have hcs : Summable c := (hasSum_conv hd1 hd2 (primeAmp_zero _) (primeAmp_zero _)
    (summable_primeAmp hx₁) (summable_primeAmp hx₂)).summable
  have hn12 : Summable fun n : ℕ => (n : ℝ) * (primeAmp x₁ n * primeAmp x₂ n) := by
    refine ((summable_mul_primeAmp_sq hx₁).add (summable_mul_primeAmp_sq hx₂)).of_nonneg_of_le
      (fun n => mul_nonneg (Nat.cast_nonneg n) (mul_nonneg (hd1 n) (hd2 n))) fun n => ?_
    have := Nat.cast_nonneg (α := ℝ) n
    nlinarith [sq_nonneg (primeAmp x₁ n - primeAmp x₂ n), mul_nonneg this
      (sq_nonneg (primeAmp x₁ n - primeAmp x₂ n))]
  obtain ⟨hnc, hncle⟩ := sum_mul_sq_conv h1 h2 h1' h2' (summable_mul_primeAmp_sq hx₁)
    (summable_mul_primeAmp_sq hx₂) hn12
  obtain ⟨-, hlow, hup⟩ := sum_sq_conv h1 h2 (summable_primeAmp_sq hx₁)
    (summable_primeAmp_sq hx₂) (summable_primeAmp_mul hx₁ hx₂)
  have hcs2 : (∑' n : ℕ, (n : ℝ) * (primeAmp x₁ n * primeAmp x₂ n)) ^ 2 ≤
      (∑' n : ℕ, (n : ℝ) * primeAmp x₁ n ^ 2) * ∑' n : ℕ, (n : ℝ) * primeAmp x₂ n ^ 2 := by
    have := sq_tsum_mul_le (u := fun n => Real.sqrt n * primeAmp x₁ n)
      (v := fun n => Real.sqrt n * primeAmp x₂ n)
      (fun n => mul_nonneg (Real.sqrt_nonneg _) (hd1 n))
      (fun n => mul_nonneg (Real.sqrt_nonneg _) (hd2 n))
      (by simpa [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)] using summable_mul_primeAmp_sq hx₁)
      (by simpa [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)] using summable_mul_primeAmp_sq hx₂)
    have e1 : ∀ n : ℕ, Real.sqrt n * primeAmp x₁ n * (Real.sqrt n * primeAmp x₂ n) =
        (n : ℝ) * (primeAmp x₁ n * primeAmp x₂ n) := fun n => by
      rw [show Real.sqrt n * primeAmp x₁ n * (Real.sqrt n * primeAmp x₂ n) =
        (Real.sqrt n * Real.sqrt n) * (primeAmp x₁ n * primeAmp x₂ n) by ring,
        Real.mul_self_sqrt (Nat.cast_nonneg _)]
    simp_rw [e1, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)] at this
    exact this
  have hab : Real.sqrt x₁ * Real.sqrt x₂ * x₁ ^ (3 / 2 : ℝ) * x₂ ^ (3 / 2 : ℝ) = x₁ ^ 2 * x₂ ^ 2 := by
    have e : ∀ y : ℝ, 0 ≤ y → Real.sqrt y * y ^ (3 / 2 : ℝ) = y ^ 2 := fun y hy => by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add' hy (by norm_num)]; norm_num
    rw [show Real.sqrt x₁ * Real.sqrt x₂ * x₁ ^ (3 / 2 : ℝ) * x₂ ^ (3 / 2 : ℝ) =
      (Real.sqrt x₁ * x₁ ^ (3 / 2 : ℝ)) * (Real.sqrt x₂ * x₂ ^ (3 / 2 : ℝ)) by ring,
      e x₁ (by linarith), e x₂ (by linarith)]
  rw [hab] at hncle
  have hsq12 : Real.sqrt x₁ ^ 2 * Real.sqrt x₂ ^ 2 = x₁ * x₂ := by
    rw [Real.sq_sqrt (by linarith), Real.sq_sqrt (by linarith)]
  rw [hsq12] at hup
  -- the mean value theorem for `K[c]`
  have hcC0 : (fun n => (c n : ℂ)) 0 = 0 := by simp [hc, LSeries.convolution_map_zero]
  have hcCs : Summable fun n => ‖(fun n => (c n : ℂ)) n‖ := by
    simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hc0 _)] using hcs
  have hcCn : Summable fun n : ℕ => (n : ℝ) * ‖(fun n => (c n : ℂ)) n‖ ^ 2 := by
    simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hc0 _), sq_abs] using hnc
  have hmv := integral_normSq_phaseSeries_sub_le hcC0 hcCs hcCn hT
  have hprod : ∀ t, primeConjSum x₁ t * primeConjSum x₂ t = phaseSeries (fun n => (c n : ℂ)) t :=
    fun t => by
      rw [primeConjSum_eq_phaseSeries, primeConjSum_eq_phaseSeries,
        phaseSeries_mul (by simp [ampC, primeAmp_zero]) (by simp [ampC, primeAmp_zero])
          (by simpa [ampC, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hd1 _)] using
            summable_primeAmp hx₁)
          (by simpa [ampC, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hd2 _)] using
            summable_primeAmp hx₂)]
      congr 1
      funext n; rw [ampC_conv]
  simp_rw [hprod]
  have hn1 : ∑' n, ‖(fun n => (c n : ℂ)) n‖ ^ 2 = ∑' m, c m ^ 2 := by
    simp [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hn2 : ∑' n : ℕ, (n : ℝ) * ‖(fun n => (c n : ℂ)) n‖ ^ 2 = ∑' m : ℕ, (m : ℝ) * c m ^ 2 := by
    simp [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [hn1, hn2] at hmv
  have hA1 : 0 ≤ ∑' n : ℕ, (n : ℝ) * primeAmp x₁ n ^ 2 := tsum_nonneg fun n => by positivity
  have hA2 : 0 ≤ ∑' n : ℕ, (n : ℝ) * primeAmp x₂ n ^ 2 := tsum_nonneg fun n => by positivity
  have hB : ∑' m : ℕ, (m : ℝ) * c m ^ 2 ≤
      2 * (∑' n : ℕ, (n : ℝ) * primeAmp x₁ n ^ 2) * (∑' n : ℕ, (n : ℝ) * primeAmp x₂ n ^ 2) +
        x₁ ^ 2 * x₂ ^ 2 * ∑' m, ppWeight m := by
    nlinarith [hncle, hcs2]
  have hmv' := abs_le.mp hmv
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hlow hT]
  · nlinarith [mul_le_mul_of_nonneg_left hup hT]

/-! ### The zero side -/

theorem normSq_mul_zSide_eq {x₁ x₂ : ℝ} (hx₁ : 1 < x₁) (hx₂ : 1 < x₂) (t : ℝ) :
    ‖zSide x₁ t * zSide x₂ t‖ ^ 2 =
      16 * x₁ * x₂ * (‖lorentzZeroSumAll x₁ t‖ ^ 2 * ‖lorentzZeroSumAll x₂ t‖ ^ 2) := by
  rw [zSide_eq hx₁, zSide_eq hx₂]
  simp only [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [h2]
  have e1 : Real.sqrt x₁ ^ 2 = x₁ := Real.sq_sqrt (by linarith)
  have e2 : Real.sqrt x₂ ^ 2 = x₂ := Real.sq_sqrt (by linarith)
  calc (2 * Real.sqrt x₁ * ‖lorentzZeroSumAll x₁ t‖ * (2 * Real.sqrt x₂ * ‖lorentzZeroSumAll x₂ t‖)) ^ 2
      = 16 * Real.sqrt x₁ ^ 2 * Real.sqrt x₂ ^ 2 *
          (‖lorentzZeroSumAll x₁ t‖ ^ 2 * ‖lorentzZeroSumAll x₂ t‖ ^ 2) := by ring
    _ = _ := by rw [e1, e2]

theorem norm_primeSide_mul_eq {x₁ x₂ : ℝ} (hx₁ : 1 ≤ x₁) (hx₂ : 1 ≤ x₂) (t : ℝ) :
    ‖primeSide x₁ t * primeSide x₂ t‖ = ‖primeConjSum x₁ t * primeConjSum x₂ t‖ := by
  rw [primeSide_eq_conjSum hx₁, primeSide_eq_conjSum hx₂]
  simp only [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]

/-- `|‖a+b‖² − ‖a‖²| ≤ ‖a‖²/λ + (λ+1)‖b‖²`. -/
theorem abs_normSq_add_sub_le_lambda (a b : ℂ) {lam : ℝ} (hlam : 0 < lam) :
    |‖a + b‖ ^ 2 - ‖a‖ ^ 2| ≤ ‖a‖ ^ 2 / lam + (lam + 1) * ‖b‖ ^ 2 := by
  refine (PhaseSeries.abs_normSq_add_sub_normSq_le' a b).trans ?_
  have h := mul_le_half_sq_add_sq (‖a‖ / Real.sqrt lam) (Real.sqrt lam * ‖b‖)
  rw [div_pow, mul_pow, Real.sq_sqrt hlam.le] at h
  have e : ‖a‖ / Real.sqrt lam * (Real.sqrt lam * ‖b‖) = ‖a‖ * ‖b‖ := by
    field_simp
  rw [e] at h
  nlinarith [norm_nonneg b]

/-- **The quadruple assembly.** With `W = ∫‖Z‖²`, `W' = ∫‖P‖²`, `Λ ≥ C + log(T+4)`, `λ > 0`:
`|16 x₁x₂ ∫ |S₁|²|S₂|² − ∫ |K₁K₂|²| ≤ (1/λ)∫|K₁K₂|² + (λ+1) R`,
`R = 128·133657 x₁²x₂²Λ² + 4Λ²W₂/x₁ + 4Λ²W'₁/x₂`. -/
theorem abs_quadruple_sub_le {x₁ x₂ : ℝ} (hx₁ : 1 < x₁) (hx₂ : 1 < x₂) {T Λ lam : ℝ} (hT : 0 ≤ T)
    (hΛ : xbBlockConstant + xiLineTwoLogDerivConstant + 16 + Real.log (T + 4) ≤ Λ) (hlam : 0 < lam) :
    |16 * x₁ * x₂ * (∫ t in (0 : ℝ)..T, ‖lorentzZeroSumAll x₁ t‖ ^ 2 * ‖lorentzZeroSumAll x₂ t‖ ^ 2)
        - ∫ t in (0 : ℝ)..T, ‖primeConjSum x₁ t * primeConjSum x₂ t‖ ^ 2| ≤
      (∫ t in (0 : ℝ)..T, ‖primeConjSum x₁ t * primeConjSum x₂ t‖ ^ 2) / lam +
        (lam + 1) * (128 * 133657 * (x₁ ^ 2 * x₂ ^ 2) * Λ ^ 2 +
          4 * Λ ^ 2 / x₁ * (∫ t in (0 : ℝ)..T, ‖zSide x₂ t‖ ^ 2) +
          4 * Λ ^ 2 / x₂ * (∫ t in (0 : ℝ)..T, ‖primeSide x₁ t‖ ^ 2)) := by
  have hb := xbBlockConstant_nonneg
  have hξ := xiLineTwoLogDerivConstant_nonneg
  have hlog4 : 0 ≤ Real.log (T + 4) := Real.log_nonneg (by linarith)
  have hΛ1 : 1 ≤ Λ := by linarith
  have hΛE : xbBlockConstant + Real.log (T + 4) + 16 ≤ Λ := by linarith
  have hΛZ : xiLineTwoLogDerivConstant + Real.log (T + 4) ≤ Λ := by linarith
  have huIcc : Set.uIcc 0 T = Set.Icc 0 T := Set.uIcc_of_le hT
  have hintR : ∀ {f : ℝ → ℝ}, ContinuousOn f (Set.Icc 0 T) → IntervalIntegrable f volume 0 T :=
    fun hf => (huIcc ▸ hf).intervalIntegrable
  have hcZ₁ := continuousOn_zSide hx₁ T
  have hcZ₂ := continuousOn_zSide hx₂ T
  have hcP₁ := (continuous_primeSide hx₁.le).continuousOn (s := Set.Icc 0 T)
  have hcP₂ := (continuous_primeSide hx₂.le).continuousOn (s := Set.Icc 0 T)
  -- `P` bounds on the window (as in the triple assembly)
  have hP : ∀ x : ℝ, 1 < x → ∀ t ∈ Set.Icc 0 T, ‖primeSide x t‖ ≤ 261 * x * Λ := by
    intro x hx t ht
    have hZ := norm_zSide_le_window hx ht hΛZ
    have hE := norm_montgomeryRemainder_le_window hx ht hΛE
    have hPe : primeSide x t = zSide x t - montgomeryRemainder x t := by rw [zSide]; ring
    have hsx : 1 ≤ Real.sqrt x := by rw [Real.one_le_sqrt]; linarith
    have hpol : 4 * x / (1 + t ^ 2) ≤ 4 * x := div_le_self (by linarith) (by nlinarith)
    have hΛx : Λ / Real.sqrt x ≤ x * Λ := by
      rw [div_le_iff₀ (by linarith)]
      have h1 : 1 ≤ x * Real.sqrt x := one_le_mul_of_one_le_of_one_le hx.le hsx
      nlinarith [mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ Λ)]
    calc ‖primeSide x t‖ ≤ ‖zSide x t‖ + ‖montgomeryRemainder x t‖ := by
          rw [hPe]; exact norm_sub_le _ _
      _ ≤ 256 * x * Λ + (4 * x + x * Λ) := add_le_add hZ (hE.trans (add_le_add hpol hΛx))
      _ ≤ 261 * x * Λ := by nlinarith
  -- the remainder `Z₁Z₂ − P₁P₂ = E₁Z₂ + P₁E₂`
  have hEsq : ∀ x : ℝ, 1 < x → ∀ t ∈ Set.Icc 0 T,
      ‖montgomeryRemainder x t‖ ^ 2 ≤ 32 * x ^ 2 / (1 + t ^ 2) + 2 * Λ ^ 2 / x := by
    intro x hx t ht
    have hE := norm_montgomeryRemainder_le_window hx ht hΛE
    have hs : Real.sqrt x ^ 2 = x := Real.sq_sqrt (by linarith)
    have h1t : 1 ≤ 1 + t ^ 2 := by nlinarith
    have hp : (4 * x / (1 + t ^ 2)) ^ 2 ≤ 16 * x ^ 2 / (1 + t ^ 2) := by
      rw [div_pow, show (4 * x) ^ 2 = 16 * x ^ 2 by ring]
      exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by nlinarith)
    have hq : (Λ / Real.sqrt x) ^ 2 = Λ ^ 2 / x := by rw [div_pow, hs]
    have h1 := pow_le_pow_left₀ (norm_nonneg _) hE 2
    have h2 : (4 * x / (1 + t ^ 2) + Λ / Real.sqrt x) ^ 2 ≤
        2 * (4 * x / (1 + t ^ 2)) ^ 2 + 2 * (Λ / Real.sqrt x) ^ 2 := by
      nlinarith [sq_nonneg (4 * x / (1 + t ^ 2) - Λ / Real.sqrt x)]
    rw [hq] at h2
    calc ‖montgomeryRemainder x t‖ ^ 2 ≤ (4 * x / (1 + t ^ 2) + Λ / Real.sqrt x) ^ 2 := h1
      _ ≤ 2 * (4 * x / (1 + t ^ 2)) ^ 2 + 2 * (Λ ^ 2 / x) := h2
      _ ≤ 2 * (16 * x ^ 2 / (1 + t ^ 2)) + 2 * (Λ ^ 2 / x) := by gcongr
      _ = 32 * x ^ 2 / (1 + t ^ 2) + 2 * Λ ^ 2 / x := by ring
  set g : ℝ → ℝ := fun t => 64 / (1 + t ^ 2) * (x₁ ^ 2 * (256 * x₂ * Λ) ^ 2 +
    x₂ ^ 2 * (261 * x₁ * Λ) ^ 2) + 4 * Λ ^ 2 / x₁ * ‖zSide x₂ t‖ ^ 2 +
    4 * Λ ^ 2 / x₂ * ‖primeSide x₁ t‖ ^ 2
  have hRle : ∀ t ∈ Set.Icc 0 T, ‖montgomeryRemainder x₁ t * zSide x₂ t +
      primeSide x₁ t * montgomeryRemainder x₂ t‖ ^ 2 ≤ g t := by
    intro t ht
    have e₁ := hEsq x₁ hx₁ t ht
    have e₂ := hEsq x₂ hx₂ t ht
    have z₂ := norm_zSide_le_window hx₂ ht hΛZ
    have p₁ := hP x₁ hx₁ t ht
    have hz₂ : ‖zSide x₂ t‖ ^ 2 ≤ (256 * x₂ * Λ) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) z₂ 2
    have hp₁ : ‖primeSide x₁ t‖ ^ 2 ≤ (261 * x₁ * Λ) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) p₁ 2
    have hsum : ‖montgomeryRemainder x₁ t * zSide x₂ t + primeSide x₁ t * montgomeryRemainder x₂ t‖ ^ 2
        ≤ 2 * (‖montgomeryRemainder x₁ t‖ ^ 2 * ‖zSide x₂ t‖ ^ 2) +
          2 * (‖primeSide x₁ t‖ ^ 2 * ‖montgomeryRemainder x₂ t‖ ^ 2) := by
      have h := norm_add_le (montgomeryRemainder x₁ t * zSide x₂ t)
        (primeSide x₁ t * montgomeryRemainder x₂ t)
      rw [norm_mul, norm_mul] at h
      have h0 := norm_nonneg (montgomeryRemainder x₁ t * zSide x₂ t +
        primeSide x₁ t * montgomeryRemainder x₂ t)
      nlinarith [sq_nonneg (‖montgomeryRemainder x₁ t‖ * ‖zSide x₂ t‖ -
        ‖primeSide x₁ t‖ * ‖montgomeryRemainder x₂ t‖), norm_nonneg (montgomeryRemainder x₁ t),
        norm_nonneg (zSide x₂ t), norm_nonneg (primeSide x₁ t),
        norm_nonneg (montgomeryRemainder x₂ t)]
    have k₁ : ‖montgomeryRemainder x₁ t‖ ^ 2 * ‖zSide x₂ t‖ ^ 2 ≤
        32 * x₁ ^ 2 / (1 + t ^ 2) * (256 * x₂ * Λ) ^ 2 + 2 * Λ ^ 2 / x₁ * ‖zSide x₂ t‖ ^ 2 := by
      have := mul_le_mul_of_nonneg_right e₁ (sq_nonneg ‖zSide x₂ t‖)
      have h2 : 32 * x₁ ^ 2 / (1 + t ^ 2) * ‖zSide x₂ t‖ ^ 2 ≤
          32 * x₁ ^ 2 / (1 + t ^ 2) * (256 * x₂ * Λ) ^ 2 :=
        mul_le_mul_of_nonneg_left hz₂ (by positivity)
      nlinarith
    have k₂ : ‖primeSide x₁ t‖ ^ 2 * ‖montgomeryRemainder x₂ t‖ ^ 2 ≤
        32 * x₂ ^ 2 / (1 + t ^ 2) * (261 * x₁ * Λ) ^ 2 + 2 * Λ ^ 2 / x₂ * ‖primeSide x₁ t‖ ^ 2 := by
      have := mul_le_mul_of_nonneg_left e₂ (sq_nonneg ‖primeSide x₁ t‖)
      have h2 : ‖primeSide x₁ t‖ ^ 2 * (32 * x₂ ^ 2 / (1 + t ^ 2)) ≤
          (261 * x₁ * Λ) ^ 2 * (32 * x₂ ^ 2 / (1 + t ^ 2)) :=
        mul_le_mul_of_nonneg_right hp₁ (by positivity)
      nlinarith
    have e : g t = 2 * (32 * x₁ ^ 2 / (1 + t ^ 2) * (256 * x₂ * Λ) ^ 2 +
        2 * Λ ^ 2 / x₁ * ‖zSide x₂ t‖ ^ 2) + 2 * (32 * x₂ ^ 2 / (1 + t ^ 2) * (261 * x₁ * Λ) ^ 2 +
        2 * Λ ^ 2 / x₂ * ‖primeSide x₁ t‖ ^ 2) := by
      simp only [g]; ring
    rw [e]; linarith
  -- integrate
  have hcR : ContinuousOn (fun t => ‖montgomeryRemainder x₁ t * zSide x₂ t +
      primeSide x₁ t * montgomeryRemainder x₂ t‖ ^ 2) (Set.Icc 0 T) :=
    ((((continuousOn_montgomeryRemainder hx₁ T).mul hcZ₂).add
      (hcP₁.mul (continuousOn_montgomeryRemainder hx₂ T))).norm).pow 2
  have hcpol : Continuous fun t : ℝ => 64 / (1 + t ^ 2) * (x₁ ^ 2 * (256 * x₂ * Λ) ^ 2 +
      x₂ ^ 2 * (261 * x₁ * Λ) ^ 2) :=
    (continuous_const.div (by fun_prop) fun t => by positivity).mul continuous_const
  have iA : IntervalIntegrable (fun t : ℝ => 64 / (1 + t ^ 2) * (x₁ ^ 2 * (256 * x₂ * Λ) ^ 2 +
      x₂ ^ 2 * (261 * x₁ * Λ) ^ 2)) volume 0 T := hcpol.continuousOn.intervalIntegrable
  have iB : IntervalIntegrable (fun t => 4 * Λ ^ 2 / x₁ * ‖zSide x₂ t‖ ^ 2) volume 0 T :=
    (hintR (hcZ₂.norm.pow 2)).const_mul _
  have iC : IntervalIntegrable (fun t => 4 * Λ ^ 2 / x₂ * ‖primeSide x₁ t‖ ^ 2) volume 0 T :=
    (hintR (hcP₁.norm.pow 2)).const_mul _
  have iAB : IntervalIntegrable (fun t : ℝ => 64 / (1 + t ^ 2) * (x₁ ^ 2 * (256 * x₂ * Λ) ^ 2 +
      x₂ ^ 2 * (261 * x₁ * Λ) ^ 2) + 4 * Λ ^ 2 / x₁ * ‖zSide x₂ t‖ ^ 2) volume 0 T := iA.add iB
  have hRint : ∫ t in (0 : ℝ)..T, ‖montgomeryRemainder x₁ t * zSide x₂ t +
      primeSide x₁ t * montgomeryRemainder x₂ t‖ ^ 2 ≤
      128 * 133657 * (x₁ ^ 2 * x₂ ^ 2) * Λ ^ 2 +
        4 * Λ ^ 2 / x₁ * (∫ t in (0 : ℝ)..T, ‖zSide x₂ t‖ ^ 2) +
        4 * Λ ^ 2 / x₂ * (∫ t in (0 : ℝ)..T, ‖primeSide x₁ t‖ ^ 2) := by
    have s1 : ∫ t in (0 : ℝ)..T, (64 / (1 + t ^ 2) * (x₁ ^ 2 * (256 * x₂ * Λ) ^ 2 +
        x₂ ^ 2 * (261 * x₁ * Λ) ^ 2) + 4 * Λ ^ 2 / x₁ * ‖zSide x₂ t‖ ^ 2 +
        4 * Λ ^ 2 / x₂ * ‖primeSide x₁ t‖ ^ 2) =
        (∫ t in (0 : ℝ)..T, (64 / (1 + t ^ 2) * (x₁ ^ 2 * (256 * x₂ * Λ) ^ 2 +
          x₂ ^ 2 * (261 * x₁ * Λ) ^ 2) + 4 * Λ ^ 2 / x₁ * ‖zSide x₂ t‖ ^ 2)) +
        ∫ t in (0 : ℝ)..T, 4 * Λ ^ 2 / x₂ * ‖primeSide x₁ t‖ ^ 2 :=
      intervalIntegral.integral_add iAB iC
    have s2 : ∫ t in (0 : ℝ)..T, (64 / (1 + t ^ 2) * (x₁ ^ 2 * (256 * x₂ * Λ) ^ 2 +
          x₂ ^ 2 * (261 * x₁ * Λ) ^ 2) + 4 * Λ ^ 2 / x₁ * ‖zSide x₂ t‖ ^ 2) =
        (∫ t in (0 : ℝ)..T, 64 / (1 + t ^ 2) * (x₁ ^ 2 * (256 * x₂ * Λ) ^ 2 +
          x₂ ^ 2 * (261 * x₁ * Λ) ^ 2)) + ∫ t in (0 : ℝ)..T, 4 * Λ ^ 2 / x₁ * ‖zSide x₂ t‖ ^ 2 :=
      intervalIntegral.integral_add iA iB
    have hpol : ∫ t in (0 : ℝ)..T, 64 / (1 + t ^ 2) * (x₁ ^ 2 * (256 * x₂ * Λ) ^ 2 +
        x₂ ^ 2 * (261 * x₁ * Λ) ^ 2) ≤ 128 * 133657 * (x₁ ^ 2 * x₂ ^ 2) * Λ ^ 2 := by
      rw [intervalIntegral.integral_mul_const, show (fun t : ℝ => 64 / (1 + t ^ 2)) =
        fun t => 64 * (1 / (1 + t ^ 2)) from funext fun t => by ring,
        intervalIntegral.integral_const_mul]
      have hM : 0 ≤ x₁ ^ 2 * (256 * x₂ * Λ) ^ 2 + x₂ ^ 2 * (261 * x₁ * Λ) ^ 2 := by positivity
      have hI := integral_inv_one_add_sq_le T
      have e : 128 * 133657 * (x₁ ^ 2 * x₂ ^ 2) * Λ ^ 2 =
          64 * 2 * (x₁ ^ 2 * (256 * x₂ * Λ) ^ 2 + x₂ ^ 2 * (261 * x₁ * Λ) ^ 2) := by ring
      rw [e]
      exact mul_le_mul_of_nonneg_right (by linarith) hM
    calc ∫ t in (0 : ℝ)..T, ‖montgomeryRemainder x₁ t * zSide x₂ t +
          primeSide x₁ t * montgomeryRemainder x₂ t‖ ^ 2 ≤ ∫ t in (0 : ℝ)..T, g t :=
          intervalIntegral.integral_mono_on hT (hintR hcR) (iAB.add iC) hRle
      _ = (∫ t in (0 : ℝ)..T, 64 / (1 + t ^ 2) * (x₁ ^ 2 * (256 * x₂ * Λ) ^ 2 +
            x₂ ^ 2 * (261 * x₁ * Λ) ^ 2)) + 4 * Λ ^ 2 / x₁ * (∫ t in (0 : ℝ)..T, ‖zSide x₂ t‖ ^ 2) +
          4 * Λ ^ 2 / x₂ * (∫ t in (0 : ℝ)..T, ‖primeSide x₁ t‖ ^ 2) := by
          simp only [g]
          rw [s1, s2, intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
      _ ≤ _ := by linarith
  -- the comparison of the two mean squares
  have hZZ : 16 * x₁ * x₂ * (∫ t in (0 : ℝ)..T, ‖lorentzZeroSumAll x₁ t‖ ^ 2 *
      ‖lorentzZeroSumAll x₂ t‖ ^ 2) = ∫ t in (0 : ℝ)..T, ‖zSide x₁ t * zSide x₂ t‖ ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun t _ => (normSq_mul_zSide_eq hx₁ hx₂ t).symm
  have hPP : ∫ t in (0 : ℝ)..T, ‖primeConjSum x₁ t * primeConjSum x₂ t‖ ^ 2 =
      ∫ t in (0 : ℝ)..T, ‖primeSide x₁ t * primeSide x₂ t‖ ^ 2 :=
    intervalIntegral.integral_congr fun t _ => by rw [norm_primeSide_mul_eq hx₁.le hx₂.le]
  have hdec : ∀ t, zSide x₁ t * zSide x₂ t = primeSide x₁ t * primeSide x₂ t +
      (montgomeryRemainder x₁ t * zSide x₂ t + primeSide x₁ t * montgomeryRemainder x₂ t) :=
    fun t => by simp only [zSide]; ring
  have iZ : IntervalIntegrable (fun t => ‖zSide x₁ t * zSide x₂ t‖ ^ 2) volume 0 T :=
    hintR ((hcZ₁.mul hcZ₂).norm.pow 2)
  have iP : IntervalIntegrable (fun t => ‖primeSide x₁ t * primeSide x₂ t‖ ^ 2) volume 0 T :=
    hintR ((hcP₁.mul hcP₂).norm.pow 2)
  rw [hZZ, hPP, ← intervalIntegral.integral_sub iZ iP]
  have hpt : ∀ t ∈ Set.Icc 0 T, |‖zSide x₁ t * zSide x₂ t‖ ^ 2 -
      ‖primeSide x₁ t * primeSide x₂ t‖ ^ 2| ≤ ‖primeSide x₁ t * primeSide x₂ t‖ ^ 2 / lam +
      (lam + 1) * ‖montgomeryRemainder x₁ t * zSide x₂ t +
        primeSide x₁ t * montgomeryRemainder x₂ t‖ ^ 2 := fun t _ => by
    rw [hdec t]; exact abs_normSq_add_sub_le_lambda _ _ hlam
  have iD : IntervalIntegrable (fun t => |‖zSide x₁ t * zSide x₂ t‖ ^ 2 -
      ‖primeSide x₁ t * primeSide x₂ t‖ ^ 2|) volume 0 T := (iZ.sub iP).abs
  have iPl : IntervalIntegrable (fun t => ‖primeSide x₁ t * primeSide x₂ t‖ ^ 2 / lam) volume 0 T :=
    iP.div_const _
  have iRl : IntervalIntegrable (fun t => (lam + 1) * ‖montgomeryRemainder x₁ t * zSide x₂ t +
      primeSide x₁ t * montgomeryRemainder x₂ t‖ ^ 2) volume 0 T := (hintR hcR).const_mul _
  calc |∫ t in (0 : ℝ)..T, (‖zSide x₁ t * zSide x₂ t‖ ^ 2 - ‖primeSide x₁ t * primeSide x₂ t‖ ^ 2)|
      ≤ ∫ t in (0 : ℝ)..T, |‖zSide x₁ t * zSide x₂ t‖ ^ 2 - ‖primeSide x₁ t * primeSide x₂ t‖ ^ 2| :=
        intervalIntegral.abs_integral_le_integral_abs hT
    _ ≤ ∫ t in (0 : ℝ)..T, (‖primeSide x₁ t * primeSide x₂ t‖ ^ 2 / lam + (lam + 1) *
          ‖montgomeryRemainder x₁ t * zSide x₂ t + primeSide x₁ t * montgomeryRemainder x₂ t‖ ^ 2) :=
        intervalIntegral.integral_mono_on hT iD (iPl.add iRl) hpt
    _ = (∫ t in (0 : ℝ)..T, ‖primeSide x₁ t * primeSide x₂ t‖ ^ 2) / lam + (lam + 1) *
          ∫ t in (0 : ℝ)..T, ‖montgomeryRemainder x₁ t * zSide x₂ t +
            primeSide x₁ t * montgomeryRemainder x₂ t‖ ^ 2 := by
        rw [intervalIntegral.integral_add iPl iRl, intervalIntegral.integral_div,
          intervalIntegral.integral_const_mul]
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left hRint (by linarith))

/-! ### The limit -/

/-- The normalized comparison: with `N = αβ x₁x₂ T ℓ²`, the ratio `16x₁x₂J/N` is within an
explicit error of `T D/N`, `D = Σd₁² Σd₂²`. -/
theorem quad_ratio_le {J KK D Q B Rb x₁ x₂ T ℓ α β c₁ Kc : ℝ} (hx₁ : 1 ≤ x₁) (hx₂ : 1 ≤ x₂)
    (hT : 0 < T) (hℓ : 1 ≤ ℓ) (hα : 0 < α) (hβ : 0 < β) (hc₁ : 0 ≤ c₁)
    (hQ0 : 0 ≤ Q) (hB0 : 0 ≤ B)
    (h1 : |16 * x₁ * x₂ * J - KK| ≤ KK / ℓ + (ℓ + 1) * Rb)
    (h2l : T * D - 104 * B ≤ KK) (h2u : KK ≤ T * (D + Q + x₁ * x₂ * c₁) + 104 * B)
    (hB : B ≤ (18 * ℓ ^ 2 + c₁) * (x₁ ^ 2 * x₂ ^ 2)) (hQ : Q ≤ 16 * x₁ ^ 2 * ℓ ^ 2)
    (hRb : Rb ≤ Kc * (x₁ ^ 2 * x₂ ^ 2) * ℓ ^ 2 + 252 * T * x₂ * ℓ ^ 3 / x₁ +
      108 * T * x₁ * ℓ ^ 3 / x₂) :
    |16 * x₁ * x₂ * J / (α * β * x₁ * x₂ * T * ℓ ^ 2) - T * D / (α * β * x₁ * x₂ * T * ℓ ^ 2)| ≤
      T * D / (α * β * x₁ * x₂ * T * ℓ ^ 2) / ℓ + 32 / (α * β) * (x₁ / x₂) +
        2 * c₁ / (α * β) / ℓ ^ 2 + 208 * (18 + c₁) / (α * β) * (x₁ * x₂ / T) +
        (ℓ + 1) * (Kc / (α * β) * (x₁ * x₂ / T) + 252 / (α * β) * (ℓ / x₁ ^ 2) +
          108 / (α * β) * (ℓ / x₂ ^ 2)) := by
  have hx₁0 : 0 < x₁ := by linarith
  have hx₂0 : 0 < x₂ := by linarith
  have hℓ0 : 0 < ℓ := by linarith
  have hN : 0 < α * β * x₁ * x₂ * T * ℓ ^ 2 := by positivity
  set N := α * β * x₁ * x₂ * T * ℓ ^ 2 with hNdef
  -- the unnormalized bound
  have hKK : |KK - T * D| ≤ T * (Q + x₁ * x₂ * c₁) + 104 * B := by
    have h0 : 0 ≤ T * (Q + x₁ * x₂ * c₁) := by positivity
    rw [abs_le]; constructor <;> linarith
  have hKK' : KK / ℓ ≤ (T * D + T * (Q + x₁ * x₂ * c₁) + 104 * B) / ℓ :=
    div_le_div_of_nonneg_right (by linarith) hℓ0.le
  have hsplit : (T * (Q + x₁ * x₂ * c₁) + 104 * B) / ℓ ≤ T * (Q + x₁ * x₂ * c₁) + 104 * B :=
    div_le_self (by positivity) hℓ
  have hun : |16 * x₁ * x₂ * J - T * D| ≤ T * D / ℓ + 2 * (T * (Q + x₁ * x₂ * c₁) + 104 * B) +
      (ℓ + 1) * Rb := by
    have h3 := abs_sub_le (16 * x₁ * x₂ * J) KK (T * D)
    have e : (T * D + T * (Q + x₁ * x₂ * c₁) + 104 * B) / ℓ =
        T * D / ℓ + (T * (Q + x₁ * x₂ * c₁) + 104 * B) / ℓ := by ring
    linarith
  -- each piece against its normalized counterpart
  have p1 : T * D / ℓ = T * D / N / ℓ * N := by field_simp
  have p2 : 2 * T * Q ≤ 32 / (α * β) * (x₁ / x₂) * N := by
    have e : 32 / (α * β) * (x₁ / x₂) * N = 2 * T * (16 * x₁ ^ 2 * ℓ ^ 2) := by
      rw [hNdef]; field_simp; ring
    rw [e]; nlinarith
  have p3 : 2 * T * x₁ * x₂ * c₁ = 2 * c₁ / (α * β) / ℓ ^ 2 * N := by
    rw [hNdef]; field_simp
  have p4 : 208 * B ≤ 208 * (18 + c₁) / (α * β) * (x₁ * x₂ / T) * N := by
    have e : 208 * (18 + c₁) / (α * β) * (x₁ * x₂ / T) * N =
        208 * ((18 + c₁) * ℓ ^ 2) * (x₁ ^ 2 * x₂ ^ 2) := by
      rw [hNdef]; field_simp
    rw [e]
    have hc : (18 * ℓ ^ 2 + c₁) ≤ (18 + c₁) * ℓ ^ 2 := by
      have := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ ℓ ^ 2 by nlinarith) hc₁
      linarith
    have := mul_le_mul_of_nonneg_right hc (by positivity : (0 : ℝ) ≤ x₁ ^ 2 * x₂ ^ 2)
    linarith
  have p5 : (ℓ + 1) * Rb ≤ (ℓ + 1) * (Kc / (α * β) * (x₁ * x₂ / T) + 252 / (α * β) * (ℓ / x₁ ^ 2) +
      108 / (α * β) * (ℓ / x₂ ^ 2)) * N := by
    have e : (Kc / (α * β) * (x₁ * x₂ / T) + 252 / (α * β) * (ℓ / x₁ ^ 2) +
        108 / (α * β) * (ℓ / x₂ ^ 2)) * N = Kc * (x₁ ^ 2 * x₂ ^ 2) * ℓ ^ 2 +
        252 * T * x₂ * ℓ ^ 3 / x₁ + 108 * T * x₁ * ℓ ^ 3 / x₂ := by
      rw [hNdef]; field_simp
    rw [mul_assoc, e]
    exact mul_le_mul_of_nonneg_left hRb (by linarith)
  have hsum : T * D / ℓ + (2 * T * Q + 2 * T * x₁ * x₂ * c₁ + 208 * B) + (ℓ + 1) * Rb ≤
      (T * D / N / ℓ + 32 / (α * β) * (x₁ / x₂) + 2 * c₁ / (α * β) / ℓ ^ 2 +
        208 * (18 + c₁) / (α * β) * (x₁ * x₂ / T) +
        (ℓ + 1) * (Kc / (α * β) * (x₁ * x₂ / T) + 252 / (α * β) * (ℓ / x₁ ^ 2) +
          108 / (α * β) * (ℓ / x₂ ^ 2))) * N := by
    have e : (T * D / N / ℓ + 32 / (α * β) * (x₁ / x₂) + 2 * c₁ / (α * β) / ℓ ^ 2 +
        208 * (18 + c₁) / (α * β) * (x₁ * x₂ / T) +
        (ℓ + 1) * (Kc / (α * β) * (x₁ * x₂ / T) + 252 / (α * β) * (ℓ / x₁ ^ 2) +
          108 / (α * β) * (ℓ / x₂ ^ 2))) * N = T * D / N / ℓ * N + 32 / (α * β) * (x₁ / x₂) * N +
        2 * c₁ / (α * β) / ℓ ^ 2 * N + 208 * (18 + c₁) / (α * β) * (x₁ * x₂ / T) * N +
        (ℓ + 1) * (Kc / (α * β) * (x₁ * x₂ / T) + 252 / (α * β) * (ℓ / x₁ ^ 2) +
          108 / (α * β) * (ℓ / x₂ ^ 2)) * N := by ring
    rw [e]
    linarith
  -- normalize
  rw [← sub_div, abs_div, abs_of_pos hN, div_le_iff₀ hN]
  calc |16 * x₁ * x₂ * J - T * D| ≤ T * D / ℓ + 2 * (T * (Q + x₁ * x₂ * c₁) + 104 * B) +
        (ℓ + 1) * Rb := hun
    _ = T * D / ℓ + (2 * T * Q + 2 * T * x₁ * x₂ * c₁ + 208 * B) + (ℓ + 1) * Rb := by ring
    _ ≤ _ := hsum

/-- **The 4-level form factor of the zeros of `ζ` factorizes below threshold.** Unconditionally,
with complex ordinates, for `0 < α < β` with `α + β < 1`,
`∫_0^T |S(T^α, t)|² |S(T^β, t)|² dt ~ (αβ/16) T log² T`,
the product of the two pair forms `∫_0^T |S(T^γ, t)|² ~ (γ/4) T log T` divided by `T`: the
fourth moment is Gaussian (Wick), with no connected 4-point contribution in this range. -/
theorem tendsto_fourLevelFormFactor {α β : ℝ} (hα : 0 < α) (hαβ : α < β) (hsum : α + β < 1) :
    Tendsto (fun T : ℝ => (∫ t in (0 : ℝ)..T, ‖lorentzZeroSumAll (T ^ α) t‖ ^ 2 *
        ‖lorentzZeroSumAll (T ^ β) t‖ ^ 2) / (α * β / 16 * T * Real.log T ^ 2)) atTop (𝓝 1) := by
  have hβ : 0 < β := hα.trans hαβ
  set c₁ := ∑' m, ppWeight m
  have hc₁ : 0 ≤ c₁ := tsum_nonneg ppWeight_nonneg
  set C := xbBlockConstant + xiLineTwoLogDerivConstant + 16
  set Kc : ℝ := 128 * 133657 * 9
  -- the main term `u = Σd₁² Σd₂² / (αβ x₁x₂ log²T)`
  set u : ℝ → ℝ := fun T => (∑' n, primeAmp (T ^ α) n ^ 2) * (∑' n, primeAmp (T ^ β) n ^ 2) /
    (α * β * T ^ α * T ^ β * Real.log T ^ 2)
  have hu : Tendsto u atTop (𝓝 1) := by
    have h1 := tendsto_tsum_primeAmp_sq_div.comp (tendsto_rpow_atTop hα)
    have h2 := tendsto_tsum_primeAmp_sq_div.comp (tendsto_rpow_atTop hβ)
    have := h1.mul h2
    rw [mul_one] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
    have hT0 : 0 < T := by linarith
    have hl : 0 < Real.log T := Real.log_pos hT
    simp only [Function.comp_apply, u, Real.log_rpow hT0]
    have hx1 : 0 < T ^ α := by positivity
    have hx2 : 0 < T ^ β := by positivity
    field_simp
  -- the error `η`
  set η : ℝ → ℝ := fun T => u T / Real.log T + 32 / (α * β) * (T ^ α / T ^ β) +
    2 * c₁ / (α * β) / Real.log T ^ 2 + 208 * (18 + c₁) / (α * β) * (T ^ α * T ^ β / T) +
    (Real.log T + 1) * (Kc / (α * β) * (T ^ α * T ^ β / T) +
      252 / (α * β) * (Real.log T / (T ^ α) ^ 2) + 108 / (α * β) * (Real.log T / (T ^ β) ^ 2))
  have hη : Tendsto η atTop (𝓝 0) := by
    have hl := Real.tendsto_log_atTop
    have i1 : Tendsto (fun T => (Real.log T)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hl
    have t1 : Tendsto (fun T => u T / Real.log T) atTop (𝓝 0) := by
      simpa [div_eq_mul_inv] using hu.mul i1
    have t2 : Tendsto (fun T : ℝ => T ^ α / T ^ β) atTop (𝓝 0) := by
      refine (tendsto_rpow_neg_atTop (by linarith : 0 < β - α)).congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
      rw [Real.rpow_neg hT.le, ← Real.rpow_sub hT, ← Real.rpow_neg hT.le]; ring_nf
    have t3 : Tendsto (fun T => 2 * c₁ / (α * β) / Real.log T ^ 2) atTop (𝓝 0) := by
      have := (i1.pow 2).const_mul (2 * c₁ / (α * β))
      simpa [div_eq_mul_inv, inv_pow] using this
    have t4 : Tendsto (fun T : ℝ => T ^ α * T ^ β / T) atTop (𝓝 0) := by
      refine (tendsto_rpow_div_self hsum).congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
      rw [Real.rpow_add hT]
    have t5 : Tendsto (fun T : ℝ => Real.log T * (T ^ α * T ^ β / T)) atTop (𝓝 0) := by
      refine (tendsto_log_pow_div_rpow 1 (by linarith : (0 : ℝ) < 1 - (α + β))).congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
      rw [pow_one, ← Real.rpow_add hT, Real.rpow_sub hT, Real.rpow_one]; field_simp
    have t6 : ∀ γ : ℝ, 0 < γ → Tendsto (fun T : ℝ => (Real.log T + 1) *
        (Real.log T / (T ^ γ) ^ 2)) atTop (𝓝 0) := by
      intro γ hγ
      have a := tendsto_log_pow_div_rpow 2 (by linarith : 0 < 2 * γ)
      have b := tendsto_log_pow_div_rpow 1 (by linarith : 0 < 2 * γ)
      have ab := a.add b
      rw [add_zero] at ab
      refine ab.congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
      rw [show (T ^ γ) ^ 2 = T ^ (2 * γ) by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hT.le]; ring_nf]
      ring
    have := ((((t1.add (t2.const_mul (32 / (α * β)))).add t3).add
      (t4.const_mul (208 * (18 + c₁) / (α * β)))).add
      ((((t5.add t4).const_mul (Kc / (α * β))).add ((t6 α hα).const_mul (252 / (α * β)))).add
        ((t6 β hβ).const_mul (108 / (α * β)))))
    simp only [mul_zero, add_zero] at this
    refine this.congr' (Filter.Eventually.of_forall fun T => ?_)
    simp only [η]; ring
  -- `r − u → 0`
  have hdiff : Tendsto (fun T => (∫ t in (0 : ℝ)..T, ‖lorentzZeroSumAll (T ^ α) t‖ ^ 2 *
        ‖lorentzZeroSumAll (T ^ β) t‖ ^ 2) / (α * β / 16 * T * Real.log T ^ 2) - u T)
      atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hη
    have hlC := Real.tendsto_log_atTop.eventually_ge_atTop C
    filter_upwards [eventually_energy_bounds hα (by linarith),
      eventually_energy_bounds hβ (by linarith),
      eventually_tsum_primeAmp_mul_le hα hαβ (by linarith), eventually_log_bounds,
      eventually_gt_atTop (1 : ℝ), hlC] with T h₁ h₂ hQ hlb hT1 hlC
    obtain ⟨hl1, -, -, hl4⟩ := hlb
    have hT0 : 0 < T := by linarith
    have hx₁ : 1 < T ^ α := Real.one_lt_rpow hT1 hα
    have hx₂ : 1 < T ^ β := Real.one_lt_rpow hT1 hβ
    set Λ := C + Real.log (T + 4)
    have hΛ : xbBlockConstant + xiLineTwoLogDerivConstant + 16 + Real.log (T + 4) ≤ Λ := le_rfl
    have hΛ0 : 0 ≤ Λ := by
      have := xbBlockConstant_nonneg; have := xiLineTwoLogDerivConstant_nonneg
      have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ T + 4)
      simp only [Λ, C]; linarith
    have hΛ3 : Λ ≤ 3 * Real.log T := by simp only [Λ]; linarith
    have hA := abs_quadruple_sub_le hx₁ hx₂ hT0.le hΛ (by linarith : 0 < Real.log T)
    obtain ⟨hKl, hKu⟩ := integral_normSq_primeConjSum_mul_bounds hx₁.le hx₂.le hT0.le
    -- the constants of the error
    have hd12 : 0 ≤ ∑' n, primeAmp (T ^ α) n * primeAmp (T ^ β) n :=
      tsum_nonneg fun n => mul_nonneg (primeAmp_nonneg (by linarith) n)
        (primeAmp_nonneg (by linarith) n)
    have hQ' : (∑' n, primeAmp (T ^ α) n * primeAmp (T ^ β) n) ^ 2 ≤
        16 * (T ^ α) ^ 2 * Real.log T ^ 2 :=
      (pow_le_pow_left₀ hd12 hQ 2).trans (le_of_eq (by ring))
    have hA1 := h₁.1
    have hA2 := h₂.1
    have hA10 : 0 ≤ ∑' n : ℕ, (n : ℝ) * primeAmp (T ^ α) n ^ 2 := tsum_nonneg fun n => by positivity
    have hA20 : 0 ≤ ∑' n : ℕ, (n : ℝ) * primeAmp (T ^ β) n ^ 2 := tsum_nonneg fun n => by positivity
    have hB : 2 * (∑' n : ℕ, (n : ℝ) * primeAmp (T ^ α) n ^ 2) *
        (∑' n : ℕ, (n : ℝ) * primeAmp (T ^ β) n ^ 2) + (T ^ α) ^ 2 * (T ^ β) ^ 2 * c₁ ≤
        (18 * Real.log T ^ 2 + c₁) * ((T ^ α) ^ 2 * (T ^ β) ^ 2) := by
      have h := mul_le_mul hA1 hA2 hA20 (by positivity)
      have e : 3 * (T ^ α) ^ 2 * Real.log T * (3 * (T ^ β) ^ 2 * Real.log T) =
          9 * ((T ^ α) ^ 2 * (T ^ β) ^ 2) * Real.log T ^ 2 := by ring
      rw [e] at h
      have e2 : (18 * Real.log T ^ 2 + c₁) * ((T ^ α) ^ 2 * (T ^ β) ^ 2) =
          2 * (9 * ((T ^ α) ^ 2 * (T ^ β) ^ 2) * Real.log T ^ 2) +
          (T ^ α) ^ 2 * (T ^ β) ^ 2 * c₁ := by ring
      linarith
    have hRb : 128 * 133657 * ((T ^ α) ^ 2 * (T ^ β) ^ 2) * Λ ^ 2 +
        4 * Λ ^ 2 / T ^ α * (∫ t in (0 : ℝ)..T, ‖zSide (T ^ β) t‖ ^ 2) +
        4 * Λ ^ 2 / T ^ β * (∫ t in (0 : ℝ)..T, ‖primeSide (T ^ α) t‖ ^ 2) ≤
        Kc * ((T ^ α) ^ 2 * (T ^ β) ^ 2) * Real.log T ^ 2 +
        252 * T * T ^ β * Real.log T ^ 3 / T ^ α + 108 * T * T ^ α * Real.log T ^ 3 / T ^ β := by
      have hΛ2 : Λ ^ 2 ≤ 9 * Real.log T ^ 2 := by nlinarith
      have hx1p : 0 < T ^ α := by positivity
      have hx2p : 0 < T ^ β := by positivity
      have k1 : 128 * 133657 * ((T ^ α) ^ 2 * (T ^ β) ^ 2) * Λ ^ 2 ≤
          Kc * ((T ^ α) ^ 2 * (T ^ β) ^ 2) * Real.log T ^ 2 := by
        have h := mul_le_mul_of_nonneg_left hΛ2
          (by positivity : (0 : ℝ) ≤ 128 * 133657 * ((T ^ α) ^ 2 * (T ^ β) ^ 2))
        have e : Kc * ((T ^ α) ^ 2 * (T ^ β) ^ 2) * Real.log T ^ 2 =
            128 * 133657 * ((T ^ α) ^ 2 * (T ^ β) ^ 2) * (9 * Real.log T ^ 2) := by
          simp only [Kc]; ring
        rw [e]; exact h
      have hW2 := h₂.2.2
      have hW1 := h₁.2.1
      have hW20 : 0 ≤ ∫ t in (0 : ℝ)..T, ‖zSide (T ^ β) t‖ ^ 2 :=
        intervalIntegral.integral_nonneg hT0.le fun t _ => by positivity
      have hW10 : 0 ≤ ∫ t in (0 : ℝ)..T, ‖primeSide (T ^ α) t‖ ^ 2 :=
        intervalIntegral.integral_nonneg hT0.le fun t _ => by positivity
      have k2 : 4 * Λ ^ 2 / T ^ α * (∫ t in (0 : ℝ)..T, ‖zSide (T ^ β) t‖ ^ 2) ≤
          252 * T * T ^ β * Real.log T ^ 3 / T ^ α := by
        rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hx1p]
        have h := mul_le_mul (mul_le_mul_of_nonneg_left hΛ2 (by norm_num : (0 : ℝ) ≤ 4)) hW2 hW20
          (by positivity)
        have e : 4 * (9 * Real.log T ^ 2) * (7 * T * T ^ β * Real.log T) =
            252 * T * T ^ β * Real.log T ^ 3 := by ring
        rw [e] at h; exact h
      have k3 : 4 * Λ ^ 2 / T ^ β * (∫ t in (0 : ℝ)..T, ‖primeSide (T ^ α) t‖ ^ 2) ≤
          108 * T * T ^ α * Real.log T ^ 3 / T ^ β := by
        rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hx2p]
        have h := mul_le_mul (mul_le_mul_of_nonneg_left hΛ2 (by norm_num : (0 : ℝ) ≤ 4)) hW1 hW10
          (by positivity)
        have e : 4 * (9 * Real.log T ^ 2) * (3 * T * T ^ α * Real.log T) =
            108 * T * T ^ α * Real.log T ^ 3 := by ring
        rw [e] at h; exact h
      linarith
    have hfin := quad_ratio_le hx₁.le hx₂.le hT0 hl1 hα hβ hc₁
      (sq_nonneg _) (by positivity) hA hKl hKu hB hQ' hRb
    have hx12 : (0 : ℝ) < T ^ α * T ^ β := by positivity
    have e1 : (∫ t in (0 : ℝ)..T, ‖lorentzZeroSumAll (T ^ α) t‖ ^ 2 *
        ‖lorentzZeroSumAll (T ^ β) t‖ ^ 2) / (α * β / 16 * T * Real.log T ^ 2) =
        16 * T ^ α * T ^ β * (∫ t in (0 : ℝ)..T, ‖lorentzZeroSumAll (T ^ α) t‖ ^ 2 *
          ‖lorentzZeroSumAll (T ^ β) t‖ ^ 2) / (α * β * T ^ α * T ^ β * T * Real.log T ^ 2) := by
      have hl0 : 0 < Real.log T := Real.log_pos hT1
      rw [div_eq_div_iff (by positivity) (by positivity)]; ring
    have e2 : u T = T * ((∑' n, primeAmp (T ^ α) n ^ 2) * ∑' n, primeAmp (T ^ β) n ^ 2) /
        (α * β * T ^ α * T ^ β * T * Real.log T ^ 2) := by
      have hl0 : 0 < Real.log T := Real.log_pos hT1
      simp only [u]
      rw [div_eq_div_iff (by positivity) (by positivity)]; ring
    rw [Real.norm_eq_abs, e1, e2]
    refine hfin.trans (le_of_eq ?_)
    simp only [η]
    rw [e2]
  have := hdiff.add hu
  simp only [zero_add] at this
  refine this.congr' (Filter.Eventually.of_forall fun T => ?_)
  ring

/-! ### The diagonal: the fourth moment of one form -/

/-- The fourth power of one prime side: `|∫_0^T |K_x|⁴ − T Σ (d ⍟ d)²| ≤ 104 B` with
`B = 2A² + c₁x⁴`, and `2D² − 2c₁x² ≤ Σ (d ⍟ d)² ≤ 2D² + c₁x²`, `D = Σ d_x²`. -/
theorem integral_primeConjSum_fourth_bounds {x : ℝ} (hx : 1 ≤ x) {T : ℝ} (hT : 0 ≤ T) :
    T * (2 * (∑' n, primeAmp x n ^ 2) ^ 2 - 2 * x ^ 2 * ∑' m, ppWeight m) -
        104 * (2 * (∑' n : ℕ, (n : ℝ) * primeAmp x n ^ 2) ^ 2 + x ^ 4 * ∑' m, ppWeight m) ≤
      ∫ t in (0 : ℝ)..T, ‖primeConjSum x t * primeConjSum x t‖ ^ 2 ∧
    ∫ t in (0 : ℝ)..T, ‖primeConjSum x t * primeConjSum x t‖ ^ 2 ≤
      T * (2 * (∑' n, primeAmp x n ^ 2) ^ 2 + x ^ 2 * ∑' m, ppWeight m) +
        104 * (2 * (∑' n : ℕ, (n : ℝ) * primeAmp x n ^ 2) ^ 2 + x ^ 4 * ∑' m, ppWeight m) := by
  have h1 := ppBound_primeAmp_half hx
  have h1' := ppBound_primeAmp_threeHalves hx
  have hd := fun n => primeAmp_nonneg (x := x) (by linarith) n
  set c : ℕ → ℝ := primeAmp x ⍟ primeAmp x with hc
  have hc0 : ∀ n, 0 ≤ c n := conv_nonneg hd hd
  have hcs : Summable c := (hasSum_conv hd hd (primeAmp_zero _) (primeAmp_zero _)
    (summable_primeAmp hx) (summable_primeAmp hx)).summable
  have hsq := summable_primeAmp_sq hx
  have hself : (fun n => primeAmp x n * primeAmp x n) = fun n => primeAmp x n ^ 2 :=
    funext fun n => (sq _).symm
  have hsq' : Summable fun n => primeAmp x n * primeAmp x n := by rw [hself]; exact hsq
  have hn : Summable fun n : ℕ => (n : ℝ) * (primeAmp x n * primeAmp x n) := by
    simpa [sq] using summable_mul_primeAmp_sq hx
  obtain ⟨hnc, hncle⟩ := sum_mul_sq_conv h1 h1 h1' h1' (summable_mul_primeAmp_sq hx)
    (summable_mul_primeAmp_sq hx) hn
  obtain ⟨-, -, hup⟩ := sum_sq_conv h1 h1 hsq hsq hsq'
  have hlow := sum_sq_conv_ge h1 h1 hsq hsq hsq'
  have hss : (∑' n, primeAmp x n * primeAmp x n) = ∑' n, primeAmp x n ^ 2 := by rw [hself]
  have hnn : (∑' n : ℕ, (n : ℝ) * (primeAmp x n * primeAmp x n)) =
      ∑' n : ℕ, (n : ℝ) * primeAmp x n ^ 2 := by simp [sq]
  rw [hss] at hup hlow
  rw [hnn] at hncle
  have hx2 : Real.sqrt x ^ 2 * Real.sqrt x ^ 2 = x ^ 2 := by
    rw [Real.sq_sqrt (by linarith)]; ring
  have hx4 : Real.sqrt x * Real.sqrt x * x ^ (3 / 2 : ℝ) * x ^ (3 / 2 : ℝ) = x ^ 4 := by
    have e : Real.sqrt x * x ^ (3 / 2 : ℝ) = x ^ 2 := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add' (by linarith) (by norm_num)]; norm_num
    rw [show Real.sqrt x * Real.sqrt x * x ^ (3 / 2 : ℝ) * x ^ (3 / 2 : ℝ) =
      (Real.sqrt x * x ^ (3 / 2 : ℝ)) * (Real.sqrt x * x ^ (3 / 2 : ℝ)) by ring, e]; ring
  rw [hx2] at hup hlow
  rw [hx4] at hncle
  -- the mean value theorem for `K[c]`
  have hcC0 : (fun n => (c n : ℂ)) 0 = 0 := by simp [hc, LSeries.convolution_map_zero]
  have hcCs : Summable fun n => ‖(fun n => (c n : ℂ)) n‖ := by
    simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hc0 _)] using hcs
  have hcCn : Summable fun n : ℕ => (n : ℝ) * ‖(fun n => (c n : ℂ)) n‖ ^ 2 := by
    simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hc0 _), sq_abs] using hnc
  have hmv := integral_normSq_phaseSeries_sub_le hcC0 hcCs hcCn hT
  have hprod : ∀ t, primeConjSum x t * primeConjSum x t = phaseSeries (fun n => (c n : ℂ)) t :=
    fun t => by
      rw [primeConjSum_eq_phaseSeries, phaseSeries_mul (by simp [ampC, primeAmp_zero])
        (by simp [ampC, primeAmp_zero])
        (by simpa [ampC, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hd _)] using
          summable_primeAmp hx)
        (by simpa [ampC, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hd _)] using
          summable_primeAmp hx)]
      congr 1
      funext n; rw [ampC_conv]
  simp_rw [hprod]
  have hn1 : ∑' n, ‖(fun n => (c n : ℂ)) n‖ ^ 2 = ∑' m, c m ^ 2 := by
    simp [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hn2 : ∑' n : ℕ, (n : ℝ) * ‖(fun n => (c n : ℂ)) n‖ ^ 2 = ∑' m : ℕ, (m : ℝ) * c m ^ 2 := by
    simp [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [hn1, hn2] at hmv
  have hA : 0 ≤ ∑' n : ℕ, (n : ℝ) * primeAmp x n ^ 2 := tsum_nonneg fun n => by positivity
  have hB : ∑' m : ℕ, (m : ℝ) * c m ^ 2 ≤
      2 * (∑' n : ℕ, (n : ℝ) * primeAmp x n ^ 2) ^ 2 + x ^ 4 * ∑' m, ppWeight m := by
    have e : (∑' n : ℕ, (n : ℝ) * primeAmp x n ^ 2) * (∑' n : ℕ, (n : ℝ) * primeAmp x n ^ 2) +
        (∑' n : ℕ, (n : ℝ) * primeAmp x n ^ 2) ^ 2 =
        2 * (∑' n : ℕ, (n : ℝ) * primeAmp x n ^ 2) ^ 2 := by ring
    linarith
  have hmv' := abs_le.mp hmv
  have hW : 0 ≤ ∑' m, ppWeight m := tsum_nonneg ppWeight_nonneg
  constructor
  · have := mul_le_mul_of_nonneg_left hlow hT
    have e : (∑' n, primeAmp x n ^ 2) * (∑' n, primeAmp x n ^ 2) + (∑' n, primeAmp x n ^ 2) ^ 2 -
        2 * x ^ 2 * ∑' m, ppWeight m = 2 * (∑' n, primeAmp x n ^ 2) ^ 2 -
        2 * x ^ 2 * ∑' m, ppWeight m := by ring
    rw [e] at this
    linarith
  · have := mul_le_mul_of_nonneg_left hup hT
    have e : (∑' n, primeAmp x n ^ 2) * (∑' n, primeAmp x n ^ 2) + (∑' n, primeAmp x n ^ 2) ^ 2 +
        x ^ 2 * ∑' m, ppWeight m = 2 * (∑' n, primeAmp x n ^ 2) ^ 2 + x ^ 2 * ∑' m, ppWeight m := by
      ring
    rw [e] at this
    linarith

/-- The diagonal normalized comparison, `N = 2α² x² T ℓ²`. -/
theorem quad_diag_ratio_le {J KK D B Rb x T ℓ α c₁ Kc : ℝ} (hx : 1 ≤ x) (hT : 0 < T)
    (hℓ : 1 ≤ ℓ) (hα : 0 < α) (hc₁ : 0 ≤ c₁) (hB0 : 0 ≤ B)
    (h1 : |16 * x * x * J - KK| ≤ KK / ℓ + (ℓ + 1) * Rb)
    (h2l : T * (2 * D - 2 * x ^ 2 * c₁) - 104 * B ≤ KK)
    (h2u : KK ≤ T * (2 * D + x ^ 2 * c₁) + 104 * B)
    (hB : B ≤ (18 * ℓ ^ 2 + c₁) * x ^ 4) (hRb : Rb ≤ Kc * x ^ 4 * ℓ ^ 2 + 360 * T * ℓ ^ 3) :
    |16 * x * x * J / (2 * α ^ 2 * x ^ 2 * T * ℓ ^ 2) - 2 * T * D / (2 * α ^ 2 * x ^ 2 * T * ℓ ^ 2)| ≤
      2 * T * D / (2 * α ^ 2 * x ^ 2 * T * ℓ ^ 2) / ℓ + 3 * c₁ / (2 * α ^ 2) / ℓ ^ 2 +
        104 * (18 + c₁) / α ^ 2 * (x ^ 2 / T) +
        (ℓ + 1) * (Kc / (2 * α ^ 2) * (x ^ 2 / T) + 180 / α ^ 2 * (ℓ / x ^ 2)) := by
  have hx0 : 0 < x := by linarith
  have hℓ0 : 0 < ℓ := by linarith
  have hN : 0 < 2 * α ^ 2 * x ^ 2 * T * ℓ ^ 2 := by positivity
  set N := 2 * α ^ 2 * x ^ 2 * T * ℓ ^ 2 with hNdef
  have hc0 : 0 ≤ T * x ^ 2 * c₁ := by positivity
  have hKK : |KK - 2 * T * D| ≤ 2 * T * x ^ 2 * c₁ + 104 * B := by
    rw [abs_le]; constructor <;> nlinarith
  have hKK' : KK / ℓ ≤ 2 * T * D / ℓ + (T * x ^ 2 * c₁ + 104 * B) := by
    have h := div_le_div_of_nonneg_right h2u hℓ0.le
    have e : (T * (2 * D + x ^ 2 * c₁) + 104 * B) / ℓ =
        2 * T * D / ℓ + (T * x ^ 2 * c₁ + 104 * B) / ℓ := by ring
    have h3 : (T * x ^ 2 * c₁ + 104 * B) / ℓ ≤ T * x ^ 2 * c₁ + 104 * B :=
      div_le_self (by positivity) hℓ
    linarith
  have hun : |16 * x * x * J - 2 * T * D| ≤ 2 * T * D / ℓ + 3 * T * x ^ 2 * c₁ + 208 * B +
      (ℓ + 1) * Rb := by
    have h3 := abs_sub_le (16 * x * x * J) KK (2 * T * D)
    linarith
  have q1 : 2 * T * D / ℓ = 2 * T * D / N / ℓ * N := by field_simp
  have q2 : 3 * T * x ^ 2 * c₁ = 3 * c₁ / (2 * α ^ 2) / ℓ ^ 2 * N := by
    rw [hNdef]; field_simp
  have q3 : 208 * B ≤ 104 * (18 + c₁) / α ^ 2 * (x ^ 2 / T) * N := by
    have e : 104 * (18 + c₁) / α ^ 2 * (x ^ 2 / T) * N = 208 * ((18 + c₁) * ℓ ^ 2) * x ^ 4 := by
      rw [hNdef]; field_simp; ring
    rw [e]
    have hc : 18 * ℓ ^ 2 + c₁ ≤ (18 + c₁) * ℓ ^ 2 := by
      have := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ ℓ ^ 2 by nlinarith) hc₁
      linarith
    have := mul_le_mul_of_nonneg_right hc (by positivity : (0 : ℝ) ≤ x ^ 4)
    linarith
  have q4 : (ℓ + 1) * Rb ≤ (ℓ + 1) * (Kc / (2 * α ^ 2) * (x ^ 2 / T) + 180 / α ^ 2 * (ℓ / x ^ 2)) * N := by
    have e : (Kc / (2 * α ^ 2) * (x ^ 2 / T) + 180 / α ^ 2 * (ℓ / x ^ 2)) * N =
        Kc * x ^ 4 * ℓ ^ 2 + 360 * T * ℓ ^ 3 := by
      rw [hNdef]; field_simp; ring
    rw [mul_assoc, e]
    exact mul_le_mul_of_nonneg_left hRb (by linarith)
  have e : (2 * T * D / N / ℓ + 3 * c₁ / (2 * α ^ 2) / ℓ ^ 2 +
      104 * (18 + c₁) / α ^ 2 * (x ^ 2 / T) +
      (ℓ + 1) * (Kc / (2 * α ^ 2) * (x ^ 2 / T) + 180 / α ^ 2 * (ℓ / x ^ 2))) * N =
      2 * T * D / N / ℓ * N + 3 * c₁ / (2 * α ^ 2) / ℓ ^ 2 * N +
      104 * (18 + c₁) / α ^ 2 * (x ^ 2 / T) * N +
      (ℓ + 1) * (Kc / (2 * α ^ 2) * (x ^ 2 / T) + 180 / α ^ 2 * (ℓ / x ^ 2)) * N := by ring
  rw [← sub_div, abs_div, abs_of_pos hN, div_le_iff₀ hN, e]
  linarith

/-- **The fourth moment of one form is Gaussian.** Unconditionally, with complex ordinates, for
`0 < α < 1/2`, `∫_0^T |S(T^α, t)|⁴ dt ~ (α²/8) T log² T = 2 · (1/T)(∫_0^T |S(T^α, t)|²)²`. -/
theorem tendsto_fourthMoment {α : ℝ} (hα : 0 < α) (hα2 : α < 1 / 2) :
    Tendsto (fun T : ℝ => (∫ t in (0 : ℝ)..T, ‖lorentzZeroSumAll (T ^ α) t‖ ^ 4) /
      (α ^ 2 / 8 * T * Real.log T ^ 2)) atTop (𝓝 1) := by
  set c₁ := ∑' m, ppWeight m
  have hc₁ : 0 ≤ c₁ := tsum_nonneg ppWeight_nonneg
  set C := xbBlockConstant + xiLineTwoLogDerivConstant + 16
  set Kc : ℝ := 128 * 133657 * 9
  set u : ℝ → ℝ := fun T => (∑' n, primeAmp (T ^ α) n ^ 2) ^ 2 /
    (α ^ 2 * (T ^ α) ^ 2 * Real.log T ^ 2)
  have hu : Tendsto u atTop (𝓝 1) := by
    have h1 := tendsto_tsum_primeAmp_sq_div.comp (tendsto_rpow_atTop hα)
    have := h1.pow 2
    rw [one_pow] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
    have hT0 : 0 < T := by linarith
    have hl : 0 < Real.log T := Real.log_pos hT
    simp only [Function.comp_apply, u, Real.log_rpow hT0]
    have hx1 : 0 < T ^ α := by positivity
    field_simp
  set η : ℝ → ℝ := fun T => u T / Real.log T + 3 * c₁ / (2 * α ^ 2) / Real.log T ^ 2 +
    104 * (18 + c₁) / α ^ 2 * ((T ^ α) ^ 2 / T) + (Real.log T + 1) *
      (Kc / (2 * α ^ 2) * ((T ^ α) ^ 2 / T) + 180 / α ^ 2 * (Real.log T / (T ^ α) ^ 2))
  have hη : Tendsto η atTop (𝓝 0) := by
    have hl := Real.tendsto_log_atTop
    have i1 : Tendsto (fun T => (Real.log T)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hl
    have t1 : Tendsto (fun T => u T / Real.log T) atTop (𝓝 0) := by
      simpa [div_eq_mul_inv] using hu.mul i1
    have t3 : Tendsto (fun T => 3 * c₁ / (2 * α ^ 2) / Real.log T ^ 2) atTop (𝓝 0) := by
      have := (i1.pow 2).const_mul (3 * c₁ / (2 * α ^ 2))
      simpa [div_eq_mul_inv, inv_pow] using this
    have hsq : ∀ T : ℝ, 0 < T → (T ^ α) ^ 2 = T ^ (2 * α) := fun T hT => by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hT.le]; ring_nf
    have t4 : Tendsto (fun T : ℝ => (T ^ α) ^ 2 / T) atTop (𝓝 0) := by
      refine (tendsto_rpow_div_self (by linarith : 2 * α < 1)).congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
      rw [hsq T hT]
    have t5 : Tendsto (fun T : ℝ => Real.log T * ((T ^ α) ^ 2 / T)) atTop (𝓝 0) := by
      refine (tendsto_log_pow_div_rpow 1 (by linarith : (0 : ℝ) < 1 - 2 * α)).congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
      rw [hsq T hT, pow_one, Real.rpow_sub hT, Real.rpow_one]; field_simp
    have t6 : Tendsto (fun T : ℝ => (Real.log T + 1) * (Real.log T / (T ^ α) ^ 2)) atTop (𝓝 0) := by
      have a := tendsto_log_pow_div_rpow 2 (by linarith : 0 < 2 * α)
      have b := tendsto_log_pow_div_rpow 1 (by linarith : 0 < 2 * α)
      have ab := a.add b
      rw [add_zero] at ab
      refine ab.congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
      rw [hsq T hT]; ring
    have := (((t1.add t3).add (t4.const_mul (104 * (18 + c₁) / α ^ 2))).add
      (((t5.add t4).const_mul (Kc / (2 * α ^ 2))).add (t6.const_mul (180 / α ^ 2))))
    simp only [mul_zero, add_zero] at this
    refine this.congr' (Filter.Eventually.of_forall fun T => ?_)
    simp only [η]; ring
  have hdiff : Tendsto (fun T => (∫ t in (0 : ℝ)..T, ‖lorentzZeroSumAll (T ^ α) t‖ ^ 4) /
      (α ^ 2 / 8 * T * Real.log T ^ 2) - u T) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hη
    have hlC := Real.tendsto_log_atTop.eventually_ge_atTop C
    filter_upwards [eventually_energy_bounds hα (by linarith), eventually_log_bounds,
      eventually_gt_atTop (1 : ℝ), hlC] with T h₁ hlb hT1 hlC
    obtain ⟨hl1, -, -, hl4⟩ := hlb
    have hT0 : 0 < T := by linarith
    have hx : 1 < T ^ α := Real.one_lt_rpow hT1 hα
    have hxp : 0 < T ^ α := by linarith
    set Λ := C + Real.log (T + 4)
    have hΛ : xbBlockConstant + xiLineTwoLogDerivConstant + 16 + Real.log (T + 4) ≤ Λ := le_rfl
    have hΛ3 : Λ ≤ 3 * Real.log T := by simp only [Λ]; linarith
    have hΛ0 : 0 ≤ Λ := by
      have := xbBlockConstant_nonneg; have := xiLineTwoLogDerivConstant_nonneg
      have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ T + 4)
      simp only [Λ, C]; linarith
    have hA := abs_quadruple_sub_le hx hx hT0.le hΛ (by linarith : 0 < Real.log T)
    obtain ⟨hKl, hKu⟩ := integral_primeConjSum_fourth_bounds hx.le hT0.le
    have hA1 := h₁.1
    have hA0 : 0 ≤ ∑' n : ℕ, (n : ℝ) * primeAmp (T ^ α) n ^ 2 := tsum_nonneg fun n => by positivity
    have hB : 2 * (∑' n : ℕ, (n : ℝ) * primeAmp (T ^ α) n ^ 2) ^ 2 + (T ^ α) ^ 4 * c₁ ≤
        (18 * Real.log T ^ 2 + c₁) * (T ^ α) ^ 4 := by
      have h := pow_le_pow_left₀ hA0 hA1 2
      have e : (3 * (T ^ α) ^ 2 * Real.log T) ^ 2 = 9 * (T ^ α) ^ 4 * Real.log T ^ 2 := by ring
      rw [e] at h
      have e2 : (18 * Real.log T ^ 2 + c₁) * (T ^ α) ^ 4 =
          2 * (9 * (T ^ α) ^ 4 * Real.log T ^ 2) + (T ^ α) ^ 4 * c₁ := by ring
      linarith
    have hRb : 128 * 133657 * ((T ^ α) ^ 2 * (T ^ α) ^ 2) * Λ ^ 2 +
        4 * Λ ^ 2 / T ^ α * (∫ t in (0 : ℝ)..T, ‖zSide (T ^ α) t‖ ^ 2) +
        4 * Λ ^ 2 / T ^ α * (∫ t in (0 : ℝ)..T, ‖primeSide (T ^ α) t‖ ^ 2) ≤
        Kc * (T ^ α) ^ 4 * Real.log T ^ 2 + 360 * T * Real.log T ^ 3 := by
      have hΛ2 : Λ ^ 2 ≤ 9 * Real.log T ^ 2 := by nlinarith
      have hW2 := h₁.2.2
      have hW1 := h₁.2.1
      have hW20 : 0 ≤ ∫ t in (0 : ℝ)..T, ‖zSide (T ^ α) t‖ ^ 2 :=
        intervalIntegral.integral_nonneg hT0.le fun t _ => by positivity
      have hW10 : 0 ≤ ∫ t in (0 : ℝ)..T, ‖primeSide (T ^ α) t‖ ^ 2 :=
        intervalIntegral.integral_nonneg hT0.le fun t _ => by positivity
      have k1 : 128 * 133657 * ((T ^ α) ^ 2 * (T ^ α) ^ 2) * Λ ^ 2 ≤
          Kc * (T ^ α) ^ 4 * Real.log T ^ 2 := by
        have h := mul_le_mul_of_nonneg_left hΛ2
          (by positivity : (0 : ℝ) ≤ 128 * 133657 * ((T ^ α) ^ 2 * (T ^ α) ^ 2))
        have e : Kc * (T ^ α) ^ 4 * Real.log T ^ 2 =
            128 * 133657 * ((T ^ α) ^ 2 * (T ^ α) ^ 2) * (9 * Real.log T ^ 2) := by
          simp only [Kc]; ring
        rw [e]; exact h
      have k2 : 4 * Λ ^ 2 / T ^ α * (∫ t in (0 : ℝ)..T, ‖zSide (T ^ α) t‖ ^ 2) ≤
          252 * T * Real.log T ^ 3 := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hxp]
        have h := mul_le_mul (mul_le_mul_of_nonneg_left hΛ2 (by norm_num : (0 : ℝ) ≤ 4)) hW2 hW20
          (by positivity)
        have e : 4 * (9 * Real.log T ^ 2) * (7 * T * T ^ α * Real.log T) =
            252 * T * Real.log T ^ 3 * T ^ α := by ring
        rw [e] at h; exact h
      have k3 : 4 * Λ ^ 2 / T ^ α * (∫ t in (0 : ℝ)..T, ‖primeSide (T ^ α) t‖ ^ 2) ≤
          108 * T * Real.log T ^ 3 := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hxp]
        have h := mul_le_mul (mul_le_mul_of_nonneg_left hΛ2 (by norm_num : (0 : ℝ) ≤ 4)) hW1 hW10
          (by positivity)
        have e : 4 * (9 * Real.log T ^ 2) * (3 * T * T ^ α * Real.log T) =
            108 * T * Real.log T ^ 3 * T ^ α := by ring
        rw [e] at h; exact h
      linarith
    have hB0 : 0 ≤ 2 * (∑' n : ℕ, (n : ℝ) * primeAmp (T ^ α) n ^ 2) ^ 2 + (T ^ α) ^ 4 * c₁ := by
      positivity
    have hfin := quad_diag_ratio_le hx.le hT0 hl1 hα hc₁ hB0 hA hKl hKu hB hRb
    have hint : (∫ t in (0 : ℝ)..T, ‖lorentzZeroSumAll (T ^ α) t‖ ^ 4) =
        ∫ t in (0 : ℝ)..T, ‖lorentzZeroSumAll (T ^ α) t‖ ^ 2 * ‖lorentzZeroSumAll (T ^ α) t‖ ^ 2 :=
      intervalIntegral.integral_congr fun t _ => by ring
    have hl0 : 0 < Real.log T := Real.log_pos hT1
    have e1 : (∫ t in (0 : ℝ)..T, ‖lorentzZeroSumAll (T ^ α) t‖ ^ 4) /
        (α ^ 2 / 8 * T * Real.log T ^ 2) =
        16 * T ^ α * T ^ α * (∫ t in (0 : ℝ)..T, ‖lorentzZeroSumAll (T ^ α) t‖ ^ 2 *
          ‖lorentzZeroSumAll (T ^ α) t‖ ^ 2) / (2 * α ^ 2 * (T ^ α) ^ 2 * T * Real.log T ^ 2) := by
      rw [hint, div_eq_div_iff (by positivity) (by positivity)]; ring
    have e2 : u T = 2 * T * (∑' n, primeAmp (T ^ α) n ^ 2) ^ 2 /
        (2 * α ^ 2 * (T ^ α) ^ 2 * T * Real.log T ^ 2) := by
      simp only [u]
      rw [div_eq_div_iff (by positivity) (by positivity)]; ring
    rw [Real.norm_eq_abs, e1, e2]
    refine hfin.trans (le_of_eq ?_)
    simp only [η]
    rw [e2]
  have := hdiff.add hu
  simp only [zero_add] at this
  refine this.congr' (Filter.Eventually.of_forall fun T => ?_)
  ring

end RHTower
