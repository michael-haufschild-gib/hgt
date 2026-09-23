import GaloisForLFunctions.RHTower.BaezDuarteBetaWavelet

/-!
# The exact weighted `L²` norm of the Báez--Duarte beta wavelet

Substituting `y = e^{-2t}` turns the `e^{-αt}`-weighted square of the wavelet into a beta integral
on the unit interval, and expanding the sign factor splits it into three beta values with the same
second parameter `2k+1`.  At a positive first parameter each beta value is the explicit rational
`n!/∏_{j≤n}(a+1+j)`.
-/

namespace RHTower

open Real MeasureTheory

noncomputable section

/-- The real beta integral `∫_0^(1 : ℕ) y^a (1-y)^n dy`. -/
def bdBeta (a : ℝ) (n : ℕ) : ℝ := ∫ y in (0:ℝ)..1, y ^ a * (1 - y) ^ n

theorem bdBeta_eq {a : ℝ} (ha : 0 ≤ a) (n : ℕ) :
    bdBeta a n = (n.factorial : ℝ) / ∏ j ∈ Finset.range (n + 1), (a + 1 + (j : ℝ)) := by
  have hu : (0 : ℝ) < a + 1 := by linarith
  have hure : 0 < (((a + 1 : ℝ) : ℂ)).re := by simpa using hu
  have hB := Complex.betaIntegral_eval_nat_add_one_right hure n
  have hint : Complex.betaIntegral ((a + 1 : ℝ) : ℂ) ((n : ℂ) + 1) = ((bdBeta a n : ℝ) : ℂ) := by
    rw [Complex.betaIntegral, bdBeta, ← intervalIntegral.integral_ofReal]
    refine intervalIntegral.integral_congr ?_
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hx
    have hx0 : (0 : ℝ) ≤ x := hx.1
    have hx1 : x ≤ 1 := hx.2
    have h1 : ((a + 1 : ℝ) : ℂ) - 1 = ((a : ℝ) : ℂ) := by norm_num
    have h2 : ((n : ℂ) + 1) - 1 = ((n : ℕ) : ℂ) := by ring
    have h3 : (1 : ℂ) - (x : ℂ) = (((1 - x : ℝ)) : ℂ) := by norm_num
    simp only [h1, h2, h3]
    rw [← Complex.ofReal_cpow hx0, Complex.cpow_natCast, ← Complex.ofReal_pow,
      ← Complex.ofReal_mul]
  have hprod : (∏ j ∈ Finset.range (n + 1), (((a + 1 : ℝ) : ℂ) + (j : ℂ)))
      = ((∏ j ∈ Finset.range (n + 1), (a + 1 + (j : ℝ)) : ℝ) : ℂ) := by
    rw [Complex.ofReal_prod]
    exact Finset.prod_congr rfl fun j _ => by push_cast; ring
  rw [hint, hprod, ← Complex.ofReal_natCast, ← Complex.ofReal_div] at hB
  exact_mod_cast hB

/-- The exponential substitution `y = e^{-2t}` maps the positive ray onto the unit interval. -/
theorem image_exp_neg_two_mul : (fun t : ℝ => Real.exp (-2 * t)) '' Set.Ioi 0 = Set.Ioo 0 1 := by
  ext y
  constructor
  · rintro ⟨t, ht, rfl⟩
    rw [Set.mem_Ioi] at ht
    refine ⟨Real.exp_pos _, ?_⟩
    have h : Real.exp (-2 * t) < Real.exp 0 := Real.exp_lt_exp.mpr (by linarith)
    rwa [Real.exp_zero] at h
  · rintro ⟨hy0, hy1⟩
    refine ⟨-Real.log y / 2, ?_, ?_⟩
    · rw [Set.mem_Ioi]
      have h := Real.log_neg hy0 hy1
      linarith
    · show Real.exp (-2 * (-Real.log y / 2)) = y
      rw [show -2 * (-Real.log y / 2) = Real.log y by ring, Real.exp_log hy0]

/-- **Equation (8).**  The `e^{-αt}`-weighted square of the kernel, after `y = e^{-2t}`. -/
theorem integral_bdKernel_weighted_sq (k : ℕ) (α : ℝ) :
    ∫ t in Set.Ioi (0 : ℝ), (Real.exp (-(α * t)) * bdKernel k t) ^ 2
      = ∫ y in Set.Ioo (0 : ℝ) 1,
          (1 / 2) * (y ^ α * (1 - y) ^ (2 * k) * (1 - (2 * (k : ℝ) + 3) * y) ^ 2) := by
  have hderiv : ∀ t ∈ Set.Ioi (0 : ℝ),
      HasDerivWithinAt (fun t : ℝ => Real.exp (-2 * t)) (-2 * Real.exp (-2 * t))
        (Set.Ioi (0 : ℝ)) t := by
    intro t _
    have hlin : HasDerivAt (fun t : ℝ => -2 * t) (-2 : ℝ) t := by
      simpa using (hasDerivAt_id' (x := t)).const_mul (-2 : ℝ)
    have h : HasDerivAt (fun t : ℝ => Real.exp (-2 * t)) (Real.exp (-2 * t) * (-2)) t := hlin.exp
    have h2 : HasDerivAt (fun t : ℝ => Real.exp (-2 * t)) (-2 * Real.exp (-2 * t)) t :=
      h.congr_deriv (by ring)
    exact h2.hasDerivWithinAt
  have hinj : Set.InjOn (fun t : ℝ => Real.exp (-2 * t)) (Set.Ioi 0) := by
    intro x _ y _ hxy
    have h := Real.exp_injective hxy
    linarith
  have hkey := MeasureTheory.integral_image_eq_integral_abs_deriv_smul
    (measurableSet_Ioi) hderiv hinj
    (fun y : ℝ => (1 / 2) * (y ^ α * (1 - y) ^ (2 * k) * (1 - (2 * (k : ℝ) + 3) * y) ^ 2))
  rw [image_exp_neg_two_mul] at hkey
  rw [hkey]
  refine setIntegral_congr_fun measurableSet_Ioi ?_
  intro t ht
  rw [Set.mem_Ioi] at ht
  have hE : (0 : ℝ) < Real.exp (-2 * t) := Real.exp_pos _
  have habs : |(-2 : ℝ) * Real.exp (-2 * t)| = 2 * Real.exp (-2 * t) := by
    rw [abs_of_nonpos (by nlinarith)]
    ring
  have hrpow : (Real.exp (-2 * t)) ^ α = Real.exp (-(2 * α * t)) := by
    rw [← Real.exp_mul]
    congr 1
    ring
  have hsq : Real.exp (-(α * t)) ^ 2 = Real.exp (-(2 * α * t)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hee : Real.exp (-t) ^ 2 = Real.exp (-2 * t) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  simp only [smul_eq_mul, habs, hrpow, bdKernel, mul_pow, hsq, hee]
  rw [← pow_mul, Nat.mul_comm k 2]
  ring

/-! ## The three-term beta expansion -/

theorem intervalIntegrable_bdBetaIntegrand {a : ℝ} (ha : 0 ≤ a) (n : ℕ) :
    IntervalIntegrable (fun y : ℝ => y ^ a * (1 - y) ^ n) MeasureTheory.volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  refine MeasureTheory.Measure.integrableOn_of_bounded (M := 1) (by simp) ?_ ?_
  · exact ((measurable_id.pow_const a).mul
      ((measurable_const.sub measurable_id).pow_const n)).aestronglyMeasurable
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with y hy
    obtain ⟨hy0, hy1⟩ := hy
    have h1 : y ^ a ≤ 1 := Real.rpow_le_one hy0.le hy1 ha
    have h2 : (1 - y) ^ n ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
    have h3 : (0 : ℝ) ≤ y ^ a := Real.rpow_nonneg hy0.le a
    have h4 : (0 : ℝ) ≤ (1 - y) ^ n := pow_nonneg (by linarith) n
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    nlinarith

theorem integrableOn_bdBetaIntegrand {a : ℝ} (ha : 0 ≤ a) (n : ℕ) :
    MeasureTheory.IntegrableOn (fun y : ℝ => y ^ a * (1 - y) ^ n) (Set.Ioo (0 : ℝ) 1) := by
  have h := intervalIntegrable_bdBetaIntegrand ha n
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at h
  exact h.mono_set Set.Ioo_subset_Ioc_self

theorem bdBeta_eq_integral_Ioo (a : ℝ) (n : ℕ) :
    bdBeta a n = ∫ y in Set.Ioo (0 : ℝ) 1, y ^ a * (1 - y) ^ n := by
  rw [bdBeta, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    MeasureTheory.integral_Ioc_eq_integral_Ioo]

/-- **Equation (9).**  Expanding the square gives three beta integrals. -/
theorem integral_Ioo_bdKernelSquare (k : ℕ) {α : ℝ} (hα : 0 ≤ α) :
    (∫ y in Set.Ioo (0 : ℝ) 1,
        (1 / 2) * (y ^ α * (1 - y) ^ (2 * k) * (1 - (2 * (k : ℝ) + 3) * y) ^ 2))
      = (1 / 2) * (bdBeta α (2 * k) - 2 * (2 * (k : ℝ) + 3) * bdBeta (α + 1) (2 * k)
          + (2 * (k : ℝ) + 3) ^ 2 * bdBeta (α + 2) (2 * k)) := by
  have hα1 : (0 : ℝ) ≤ α + 1 := by linarith
  have hα2 : (0 : ℝ) ≤ α + 2 := by linarith
  have hI0 := integrableOn_bdBetaIntegrand hα (2 * k)
  have hI1 := integrableOn_bdBetaIntegrand hα1 (2 * k)
  have hI2 := integrableOn_bdBetaIntegrand hα2 (2 * k)
  have hsplit : ∀ y ∈ Set.Ioo (0 : ℝ) 1,
      (1 / 2) * (y ^ α * (1 - y) ^ (2 * k) * (1 - (2 * (k : ℝ) + 3) * y) ^ 2)
        = (1 / 2) * (y ^ α * (1 - y) ^ (2 * k))
          - (2 * (k : ℝ) + 3) * (y ^ (α + 1) * (1 - y) ^ (2 * k))
          + ((1 / 2) * (2 * (k : ℝ) + 3) ^ 2) * (y ^ (α + 2) * (1 - y) ^ (2 * k)) := by
    intro y hy
    have hy0 : (0 : ℝ) < y := hy.1
    have e1 : y ^ (α + 1) = y ^ α * y := by
      rw [Real.rpow_add hy0, Real.rpow_one]
    have e2 : y ^ (α + 2) = y ^ α * y ^ 2 := by
      rw [Real.rpow_add hy0, show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num,
        Real.rpow_natCast]
    rw [e1, e2]
    ring
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioo hsplit]
  have hint1 : MeasureTheory.IntegrableOn
      (fun x : ℝ => (1 / 2) * (x ^ α * (1 - x) ^ (2 * k))) (Set.Ioo (0 : ℝ) 1) :=
    hI0.const_mul _
  have hint2 : MeasureTheory.IntegrableOn
      (fun x : ℝ => (2 * (k : ℝ) + 3) * (x ^ (α + 1) * (1 - x) ^ (2 * k)))
      (Set.Ioo (0 : ℝ) 1) := hI1.const_mul _
  have hint3 : MeasureTheory.IntegrableOn
      (fun x : ℝ => ((1 / 2) * (2 * (k : ℝ) + 3) ^ 2) * (x ^ (α + 2) * (1 - x) ^ (2 * k)))
      (Set.Ioo (0 : ℝ) 1) := hI2.const_mul _
  have hstep : (∫ x in Set.Ioo (0 : ℝ) 1,
        ((1 / 2) * (x ^ α * (1 - x) ^ (2 * k))
          - (2 * (k : ℝ) + 3) * (x ^ (α + 1) * (1 - x) ^ (2 * k))
          + ((1 / 2) * (2 * (k : ℝ) + 3) ^ 2) * (x ^ (α + 2) * (1 - x) ^ (2 * k))))
      = (∫ x in Set.Ioo (0 : ℝ) 1, (1 / 2) * (x ^ α * (1 - x) ^ (2 * k)))
        - (∫ x in Set.Ioo (0 : ℝ) 1, (2 * (k : ℝ) + 3) * (x ^ (α + 1) * (1 - x) ^ (2 * k)))
        + (∫ x in Set.Ioo (0 : ℝ) 1,
            ((1 / 2) * (2 * (k : ℝ) + 3) ^ 2) * (x ^ (α + 2) * (1 - x) ^ (2 * k))) := by
    have hint12 : MeasureTheory.IntegrableOn
        (fun x : ℝ => (1 / 2) * (x ^ α * (1 - x) ^ (2 * k))
          - (2 * (k : ℝ) + 3) * (x ^ (α + 1) * (1 - x) ^ (2 * k)))
        (Set.Ioo (0 : ℝ) 1) := hint1.sub hint2
    rw [MeasureTheory.integral_add hint12 hint3, MeasureTheory.integral_sub hint1 hint2]
  rw [hstep, MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_const_mul, ← bdBeta_eq_integral_Ioo, ← bdBeta_eq_integral_Ioo,
    ← bdBeta_eq_integral_Ioo]
  ring

/-- **Equations (8)–(9).**  The exact `e^{-αt}`-weighted `L²` norm of the beta wavelet. -/
theorem integral_bdKernel_weighted_sq_eq (k : ℕ) {α : ℝ} (hα : 0 ≤ α) :
    ∫ t in Set.Ioi (0 : ℝ), (Real.exp (-(α * t)) * bdKernel k t) ^ 2
      = (1 / 2) * (bdBeta α (2 * k) - 2 * (2 * (k : ℝ) + 3) * bdBeta (α + 1) (2 * k)
          + (2 * (k : ℝ) + 3) ^ 2 * bdBeta (α + 2) (2 * k)) := by
  rw [integral_bdKernel_weighted_sq, integral_Ioo_bdKernelSquare k hα]

end

end RHTower
