import GaloisForLFunctions.RHTower.BaezDuarteScaleLaw

/-!
# The gamma majorant and the weighted scale law

`(1-y)^n ≤ e^{-ny}` and a rescaling of the truncated gamma integral give
`∫_0^1 y^α(1-y)^n dy ≤ Γ(α+1) n^{-(α+1)}`.  Combined with the closed form of the weighted wavelet
energy and Cauchy--Schwarz this is the card's scale law `c_k = O_α(k^{-(1+α)/2})`.
-/

namespace RHTower

open Real MeasureTheory

noncomputable section

theorem one_sub_pow_le_exp {y : ℝ} (hy1 : y ≤ 1) (n : ℕ) :
    (1 - y) ^ n ≤ Real.exp (-((n : ℝ) * y)) := by
  have h1 : 1 - y ≤ Real.exp (-y) := by
    have := Real.add_one_le_exp (-y)
    linarith
  have h2 : (1 - y) ^ n ≤ (Real.exp (-y)) ^ n := pow_le_pow_left₀ (by linarith) h1 n
  have h3 : (Real.exp (-y)) ^ n = Real.exp (-((n : ℝ) * y)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  linarith [h2, h3.le, h3.ge]

theorem image_mul_left_Ioo {c : ℝ} (hc : 0 < c) :
    (fun y : ℝ => c * y) '' Set.Ioo 0 1 = Set.Ioo 0 c := by
  ext u
  constructor
  · rintro ⟨y, ⟨hy0, hy1⟩, rfl⟩
    exact ⟨by positivity, by nlinarith⟩
  · rintro ⟨hu0, huc⟩
    exact ⟨u / c, ⟨by positivity, by rw [div_lt_one hc]; exact huc⟩, by field_simp⟩

/-- Rescaling the truncated gamma integral. -/
theorem integral_Ioo_rpow_mul_exp_scale (α : ℝ) {c : ℝ} (hc : 0 < c) :
    (∫ y in Set.Ioo (0 : ℝ) 1, y ^ α * Real.exp (-(c * y)))
      = (1 / c) ^ (α + 1) * ∫ u in Set.Ioo (0 : ℝ) c, u ^ α * Real.exp (-u) := by
  have hderiv : ∀ y ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivWithinAt (fun y : ℝ => c * y) c (Set.Ioo (0 : ℝ) 1) y := by
    intro y _
    have h : HasDerivAt (fun y : ℝ => c * y) c y := by
      simpa using (hasDerivAt_id' (x := y)).const_mul c
    exact h.hasDerivWithinAt
  have hinj : Set.InjOn (fun y : ℝ => c * y) (Set.Ioo 0 1) := by
    intro x _ y _ hxy
    have : c * x = c * y := hxy
    exact mul_left_cancel₀ (ne_of_gt hc) this
  have hkey := MeasureTheory.integral_image_eq_integral_abs_deriv_smul
    measurableSet_Ioo hderiv hinj
    (fun u : ℝ => (1 / c) ^ (α + 1) * (u ^ α * Real.exp (-u)))
  rw [image_mul_left_Ioo hc] at hkey
  rw [MeasureTheory.integral_const_mul] at hkey
  rw [hkey]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo fun y hy => ?_
  have hy0 : (0 : ℝ) < y := hy.1
  simp only [smul_eq_mul, abs_of_pos hc]
  have hpow : (c * y) ^ α = c ^ α * y ^ α := Real.mul_rpow hc.le hy0.le
  have hcpow : (1 / c) ^ (α + 1) = (c ^ (α + 1))⁻¹ := by
    rw [one_div, ← Real.rpow_neg_one c, ← Real.rpow_mul hc.le, neg_one_mul,
      Real.rpow_neg hc.le]
  rw [hpow, hcpow]
  have hc1 : c ^ (α + 1) = c ^ α * c := by
    rw [Real.rpow_add hc, Real.rpow_one]
  rw [hc1]
  have hca : (0 : ℝ) < c ^ α := Real.rpow_pos_of_pos hc α
  field_simp

/-- **The gamma majorant.**  `∫_0^1 y^α (1-y)^n dy ≤ Γ(α+1) n^{-(α+1)}`. -/
theorem bdBeta_le_gamma {α : ℝ} (hα : 0 ≤ α) {n : ℕ} (hn : 1 ≤ n) :
    bdBeta α n ≤ (1 / (n : ℝ)) ^ (α + 1) * Real.Gamma (α + 1) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hα1 : (0 : ℝ) < α + 1 := by linarith
  have hGint : MeasureTheory.IntegrableOn
      (fun u : ℝ => u ^ α * Real.exp (-u)) (Set.Ioi (0 : ℝ)) := by
    have h := Real.GammaIntegral_convergent hα1
    refine h.congr_fun ?_ measurableSet_Ioi
    intro u _
    rw [show α + 1 - 1 = α by ring]
    ring
  have hGval : (∫ u in Set.Ioi (0 : ℝ), u ^ α * Real.exp (-u)) = Real.Gamma (α + 1) := by
    rw [Real.Gamma_eq_integral hα1]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    rw [show α + 1 - 1 = α by ring]
    ring
  have hstep1 : bdBeta α n ≤ ∫ y in Set.Ioo (0 : ℝ) 1, y ^ α * Real.exp (-((n : ℝ) * y)) := by
    rw [bdBeta_eq_integral_Ioo]
    refine MeasureTheory.setIntegral_mono_on (integrableOn_bdBetaIntegrand hα n) ?_
      measurableSet_Ioo ?_
    · have hsub : MeasureTheory.IntegrableOn
          (fun y : ℝ => y ^ α * Real.exp (-((n : ℝ) * y))) (Set.Ioo (0 : ℝ) 1) := by
        refine MeasureTheory.Measure.integrableOn_of_bounded (M := 1) (by simp) ?_ ?_
        · exact ((measurable_id.pow_const α).mul
            (Real.measurable_exp.comp (by fun_prop))).aestronglyMeasurable
        · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with y hy
          obtain ⟨hy0, hy1⟩ := hy
          have h1 : y ^ α ≤ 1 := Real.rpow_le_one hy0.le hy1.le hα
          have h2 : Real.exp (-((n : ℝ) * y)) ≤ 1 := by
            have h : Real.exp (-((n : ℝ) * y)) ≤ Real.exp 0 :=
              Real.exp_le_exp.mpr (by nlinarith)
            rwa [Real.exp_zero] at h
          have h3 : (0 : ℝ) ≤ y ^ α := Real.rpow_nonneg hy0.le α
          rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
          nlinarith [Real.exp_pos (-((n : ℝ) * y))]
      exact hsub
    · intro y hy
      have hy0 : (0 : ℝ) < y := hy.1
      have hy1 : y < 1 := hy.2
      have h3 : (0 : ℝ) ≤ y ^ α := Real.rpow_nonneg hy0.le α
      exact mul_le_mul_of_nonneg_left (one_sub_pow_le_exp hy1.le n) h3
  have hstep2 : (∫ y in Set.Ioo (0 : ℝ) 1, y ^ α * Real.exp (-((n : ℝ) * y)))
      = (1 / (n : ℝ)) ^ (α + 1) * ∫ u in Set.Ioo (0 : ℝ) (n : ℝ), u ^ α * Real.exp (-u) :=
    integral_Ioo_rpow_mul_exp_scale α hn0
  have hstep3 : (∫ u in Set.Ioo (0 : ℝ) (n : ℝ), u ^ α * Real.exp (-u))
      ≤ ∫ u in Set.Ioi (0 : ℝ), u ^ α * Real.exp (-u) := by
    refine MeasureTheory.setIntegral_mono_set hGint ?_ ?_
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with u hu
      have hu0 : (0 : ℝ) < u := hu
      positivity
    · exact Filter.Eventually.of_forall (fun u hu => hu.1)
  have hpos : (0 : ℝ) < (1 / (n : ℝ)) ^ (α + 1) := by positivity
  calc bdBeta α n ≤ ∫ y in Set.Ioo (0 : ℝ) 1, y ^ α * Real.exp (-((n : ℝ) * y)) := hstep1
    _ = (1 / (n : ℝ)) ^ (α + 1) * ∫ u in Set.Ioo (0 : ℝ) (n : ℝ), u ^ α * Real.exp (-u) := hstep2
    _ ≤ (1 / (n : ℝ)) ^ (α + 1) * ∫ u in Set.Ioi (0 : ℝ), u ^ α * Real.exp (-u) :=
        mul_le_mul_of_nonneg_left hstep3 hpos.le
    _ = (1 / (n : ℝ)) ^ (α + 1) * Real.Gamma (α + 1) := by rw [hGval]

theorem integral_norm_sq_weightedBdKernelVector (α : ℝ) (k : ℕ) :
    (∫ t : ℝ, ‖weightedBdKernelVector α k t‖ ^ (2 : ℝ))
      = ∫ t in Set.Ioi (0 : ℝ), (Real.exp (-(α * t)) * bdKernel k t) ^ 2 := by
  have hfun : (fun t : ℝ => ‖weightedBdKernelVector α k t‖ ^ (2 : ℝ))
      = Set.indicator (Set.Ioi (0 : ℝ))
          (fun t : ℝ => (Real.exp (-(α * t)) * bdKernel k t) ^ 2) := by
    funext t
    by_cases ht : t ∈ Set.Ioi (0 : ℝ)
    · rw [Set.indicator_of_mem ht, weightedBdKernelVector, bdKernelVector,
        Set.indicator_of_mem ht, norm_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, ← abs_mul,
        show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]
    · rw [Set.indicator_of_notMem ht, weightedBdKernelVector, bdKernelVector,
        Set.indicator_of_notMem ht, mul_zero, norm_zero, Real.zero_rpow (by norm_num)]
  rw [hfun, MeasureTheory.integral_indicator measurableSet_Ioi]

/-- The rational bracket of the closed form is bounded uniformly in `k`. -/
theorem bdBracket_le (k : ℕ) {α : ℝ} (hα : 0 ≤ α) :
    ((α ^ 2 + α + 1) * (2 * (k : ℝ) + 3) ^ 2 - (2 * α ^ 2 + 1) * (2 * (k : ℝ) + 3)
        + (α ^ 2 - α))
      / ((α + 2 * (k : ℝ) + 2) * (α + 2 * (k : ℝ) + 3)) ≤ 3 * (α ^ 2 + α + 1) := by
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hu : (0 : ℝ) < α + 2 * (k : ℝ) + 2 := by linarith
  have hv : (0 : ℝ) < α + 2 * (k : ℝ) + 3 := by linarith
  rw [div_le_iff₀ (by positivity)]
  nlinarith [sq_nonneg α, sq_nonneg ((k : ℝ)), sq_nonneg (α * (k : ℝ)), mul_nonneg hα hk,
    mul_nonneg (mul_nonneg hα hα) hk, mul_nonneg hα (mul_nonneg hk hk)]

/-- **Equation (10), as a bound.**  The weighted wavelet energy is `O_α(k^{-(1+α)})`. -/
theorem integral_bdKernel_weighted_sq_le {k : ℕ} (hk : 1 ≤ k) {α : ℝ} (hα : 0 ≤ α) :
    (∫ t in Set.Ioi (0 : ℝ), (Real.exp (-(α * t)) * bdKernel k t) ^ 2)
      ≤ (3 * (α ^ 2 + α + 1) / 2) * Real.Gamma (α + 1) * (1 / (2 * (k : ℝ))) ^ (α + 1) := by
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hbeta0 : 0 ≤ bdBeta α (2 * k) := by
    rw [bdBeta_eq_prod hα]
    have := bdBetaProd_pos hα (2 * k)
    positivity
  have hbeta := bdBeta_le_gamma hα (n := 2 * k) (by omega)
  have hcast : ((2 * k : ℕ) : ℝ) = 2 * (k : ℝ) := by push_cast; ring
  rw [hcast] at hbeta
  have hG : 0 ≤ Real.Gamma (α + 1) := (Real.Gamma_pos_of_pos (by linarith)).le
  rw [integral_bdKernel_weighted_sq_closed k hα]
  have hbr := bdBracket_le k hα
  calc bdBeta α (2 * k) / 2
        * (((α ^ 2 + α + 1) * (2 * (k : ℝ) + 3) ^ 2 - (2 * α ^ 2 + 1) * (2 * (k : ℝ) + 3)
              + (α ^ 2 - α))
           / ((α + 2 * (k : ℝ) + 2) * (α + 2 * (k : ℝ) + 3)))
      ≤ bdBeta α (2 * k) / 2 * (3 * (α ^ 2 + α + 1)) := by
        refine mul_le_mul_of_nonneg_left hbr (by positivity)
    _ ≤ ((1 / (2 * (k : ℝ))) ^ (α + 1) * Real.Gamma (α + 1)) / 2 * (3 * (α ^ 2 + α + 1)) := by
        have h3 : (0 : ℝ) ≤ 3 * (α ^ 2 + α + 1) := by positivity
        have hdiv : bdBeta α (2 * k) / 2
            ≤ ((1 / (2 * (k : ℝ))) ^ (α + 1) * Real.Gamma (α + 1)) / 2 := by linarith
        exact mul_le_mul_of_nonneg_right hdiv h3
    _ = (3 * (α ^ 2 + α + 1) / 2) * Real.Gamma (α + 1) * (1 / (2 * (k : ℝ))) ^ (α + 1) := by
        ring

/-- **Equation (12).**  A weighted `L²` moment `(11)` gives the `k^{-(1+α)/2}` scale law for the
Báez--Duarte coefficients. -/
theorem norm_bdCoeff_le_scaleLaw {α : ℝ} (hα : 0 ≤ α) (hmom : WeightedMertensMoment α) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, 1 ≤ k →
      ‖bdCoeff (k + 1)‖ ≤ C * ((k : ℝ)) ^ (-(1 + α) / 2) := by
  have hG : (0 : ℝ) < Real.Gamma (α + 1) := Real.Gamma_pos_of_pos (by linarith)
  set D : ℝ := (3 * (α ^ 2 + α + 1) / 2) * Real.Gamma (α + 1) with hD
  have hD0 : 0 ≤ D := by rw [hD]; positivity
  set M : ℝ := (∫ t : ℝ, ‖weightedMertensVector α t‖ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) with hM
  have hX0 : (0 : ℝ) ≤ ∫ t : ℝ, ‖weightedMertensVector α t‖ ^ (2 : ℝ) := by
    refine MeasureTheory.integral_nonneg fun t => ?_
    positivity
  have hM0 : 0 ≤ M := by rw [hM]; exact Real.rpow_nonneg hX0 _
  refine ⟨M * (D ^ ((1 : ℝ) / 2) * (2 : ℝ) ^ (-(1 + α) / 2)), by positivity, ?_⟩
  intro k hk
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have h1 := norm_bdCoeff_le_weighted k hα hmom
  rw [integral_norm_sq_weightedBdKernelVector] at h1
  have h2 := integral_bdKernel_weighted_sq_le hk hα
  have hE0 : (0 : ℝ) ≤ ∫ t in Set.Ioi (0 : ℝ), (Real.exp (-(α * t)) * bdKernel k t) ^ 2 := by
    refine MeasureTheory.setIntegral_nonneg measurableSet_Ioi fun t _ => ?_
    positivity
  have hstep : (∫ t in Set.Ioi (0 : ℝ), (Real.exp (-(α * t)) * bdKernel k t) ^ 2) ^ ((1 : ℝ) / 2)
      ≤ (D * (1 / (2 * (k : ℝ))) ^ (α + 1)) ^ ((1 : ℝ) / 2) :=
    Real.rpow_le_rpow hE0 h2 (by norm_num)
  have hsplit : (D * (1 / (2 * (k : ℝ))) ^ (α + 1)) ^ ((1 : ℝ) / 2)
      = D ^ ((1 : ℝ) / 2) * (2 : ℝ) ^ (-(1 + α) / 2) * ((k : ℝ)) ^ (-(1 + α) / 2) := by
    have hinv0 : (0 : ℝ) ≤ (1 / (2 * (k : ℝ))) ^ (α + 1) := by positivity
    rw [Real.mul_rpow hD0 hinv0, ← Real.rpow_mul (by positivity)]
    have hpow : (1 / (2 * (k : ℝ))) ^ ((α + 1) * ((1 : ℝ) / 2))
        = (2 : ℝ) ^ (-(1 + α) / 2) * ((k : ℝ)) ^ (-(1 + α) / 2) := by
      rw [one_div, ← Real.rpow_neg_one (2 * (k : ℝ)), ← Real.rpow_mul (by positivity),
        Real.mul_rpow (by norm_num) hk0.le]
      congr 2 <;> ring
    rw [hpow]
    ring
  rw [hsplit] at hstep
  calc ‖bdCoeff (k + 1)‖
      ≤ M * (∫ t in Set.Ioi (0 : ℝ), (Real.exp (-(α * t)) * bdKernel k t) ^ 2) ^ ((1 : ℝ) / 2) :=
        h1
    _ ≤ M * (D ^ ((1 : ℝ) / 2) * (2 : ℝ) ^ (-(1 + α) / 2) * ((k : ℝ)) ^ (-(1 + α) / 2)) :=
        mul_le_mul_of_nonneg_left hstep hM0
    _ = M * (D ^ ((1 : ℝ) / 2) * (2 : ℝ) ^ (-(1 + α) / 2)) * ((k : ℝ)) ^ (-(1 + α) / 2) := by ring

end

end RHTower
