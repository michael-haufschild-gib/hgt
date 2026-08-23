import GaloisForLFunctions.RHTower.XiHeightSelection

/-!
# Polynomial Xi ratios on selected horizontal lines

Burnol's good-height selection controls movement of `log ‖xi‖` across the full classical strip.
The resulting selected lines are zero-free and the ratio of any two Xi values on one line is
bounded by one fixed power of the height, at both signs of that height.
-/

open Complex Set MeasureTheory intervalIntegral Filter Topology

namespace RHTower

noncomputable section

theorem tsum_logKernel_reflect (T : ℝ) :
    (∑' q : XiZeroCopy, Real.log (1 + 9 / (T + (q.1 : ℂ).im) ^ 2)) =
      ∑' q : XiZeroCopy, Real.log (1 + 9 / (T - (q.1 : ℂ).im) ^ 2) := by
  rw [← (xiZeroCopyReflectEquiv).tsum_eq
    (fun q : XiZeroCopy => Real.log (1 + 9 / (T + (q.1 : ℂ).im) ^ 2))]
  refine tsum_congr fun q => ?_
  have him : ((xiZeroCopyReflectEquiv q).1 : ℂ).im = -((q.1 : ℂ).im) := by
    rw [xiZeroCopyReflect_coe]
    simp
  rw [him]
  congr 2

theorem xi_ne_zero_horizontal_of_avoids_zero_ordinates
    {T : ℝ} (hT : ∀ q : XiZeroCopy, T - (q.1 : ℂ).im ≠ 0) :
    ∀ u : ℝ, xi ((u : ℂ) + (T : ℂ) * I) ≠ 0 := by
  intro u hzero
  have hmem := mem_xi_divisor_support_of_eq_zero hzero
  set rho : XiDivisorSupport := ⟨(u : ℂ) + (T : ℂ) * I, hmem⟩ with hrho
  have hpos := xi_divisor_pos_on_support rho
  have hnpos : 0 < Int.toNat ((MeromorphicOn.divisor xi Set.univ) (rho : ℂ)) := by omega
  have him : ((rho : XiDivisorSupport) : ℂ).im = T := by rw [hrho]; simp
  exact hT (⟨rho, ⟨0, hnpos⟩⟩ : XiZeroCopy) (by rw [him]; ring)

private theorem abs_integral_re_logDeriv_xi_le_goodHeight
    {T B : ℝ}
    (hzero : ∀ u : ℝ, xi ((u : ℂ) + (T : ℂ) * I) ≠ 0)
    (hminus : ∀ q : XiZeroCopy, T - (q.1 : ℂ).im ≠ 0)
    (hplus : ∀ q : XiZeroCopy, T + (q.1 : ℂ).im ≠ 0)
    (hB : (∑' q : XiZeroCopy,
      Real.log (1 + 9 / (T - (q.1 : ℂ).im) ^ 2)) ≤ B)
    {sigma : ℝ} (hsigma1 : -1 ≤ sigma) (hsigma2 : sigma ≤ 2) :
    |(∫ u in sigma..2, logDeriv xi ((u : ℂ) + (T : ℂ) * I)).re| ≤ B := by
  have hseg := abs_two_mul_integral_re_logDeriv_xi_le
    hzero hminus hplus hsigma1 hsigma2
  have hplusSum := tsum_logKernel_reflect T
  have hsummablePlus : Summable
      (fun q : XiZeroCopy => Real.log (1 + 9 / (T + (q.1 : ℂ).im) ^ 2)) := by
    refine (summable_logKernel (-T)).congr fun q => ?_
    rw [show (-T - (q.1 : ℂ).im) ^ 2 = (T + (q.1 : ℂ).im) ^ 2 by ring]
  have hsum :
      (∑' q : XiZeroCopy,
          (Real.log (1 + 9 / (T - (q.1 : ℂ).im) ^ 2) +
            Real.log (1 + 9 / (T + (q.1 : ℂ).im) ^ 2))) =
        2 * ∑' q : XiZeroCopy,
          Real.log (1 + 9 / (T - (q.1 : ℂ).im) ^ 2) := by
    rw [(summable_logKernel T).tsum_add hsummablePlus, hplusSum]
    ring
  rw [hsum] at hseg
  have htwo :
      |2 * (∫ u in sigma..2, logDeriv xi ((u : ℂ) + (T : ℂ) * I)).re| ≤ 2 * B := by
    linarith
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at htwo
  linarith

/-- Selected horizontal Xi ratios are uniformly polynomial throughout the classical strip, at
both signs of the selected height. -/
theorem exists_xi_horizontal_ratio_bound :
    ∃ A : ℝ, 0 < A ∧ ∃ n0 : ℝ, ∀ n : ℝ, n0 ≤ n → ∃ T : ℝ,
      n ≤ T ∧ T ≤ n + 1 ∧
      ∀ sigma tau : ℝ, -1 ≤ sigma → sigma ≤ 2 → -1 ≤ tau → tau ≤ 2 →
        ‖xi ((sigma : ℂ) + (T : ℂ) * I)‖ ≤
            T ^ A * ‖xi ((tau : ℂ) + (T : ℂ) * I)‖ ∧
          ‖xi ((sigma : ℂ) - (T : ℂ) * I)‖ ≤
            T ^ A * ‖xi ((tau : ℂ) - (T : ℂ) * I)‖ := by
  obtain ⟨C, hC, n1, hgood⟩ := exists_good_height
  refine ⟨2 * C, by positivity, max n1 10, ?_⟩
  intro n hn
  have hn1 : n1 ≤ n := le_trans (le_max_left _ _) hn
  have hn10 : 10 ≤ n := le_trans (le_max_right _ _) hn
  obtain ⟨T, hnT, hTn, hminus, hplus, hsum⟩ := hgood n hn1
  refine ⟨T, hnT, hTn, ?_⟩
  have hTzero := xi_ne_zero_horizontal_of_avoids_zero_ordinates hminus
  have hnpos : 0 < n := by linarith
  have hTpos : 0 < T := lt_of_lt_of_le hnpos hnT
  have hlognT : Real.log n ≤ Real.log T := Real.log_le_log hnpos hnT
  intro sigma tau hsigma1 hsigma2 htau1 htau2
  have hsigmaInt := abs_integral_re_logDeriv_xi_le_goodHeight
    hTzero hminus hplus hsum hsigma1 hsigma2
  have htauInt := abs_integral_re_logDeriv_xi_le_goodHeight
    hTzero hminus hplus hsum htau1 htau2
  have hsigmaLog := log_norm_xi_horizontal hTzero 2 sigma
  have htauLog := log_norm_xi_horizontal hTzero 2 tau
  rw [intervalIntegral.integral_symm] at hsigmaLog htauLog
  simp only [Complex.neg_re] at hsigmaLog htauLog
  have hlog :
      Real.log ‖xi ((sigma : ℂ) + (T : ℂ) * I)‖ ≤
        Real.log ‖xi ((tau : ℂ) + (T : ℂ) * I)‖ + (2 * C) * Real.log T := by
    have hClogn : C * Real.log n ≤ C * Real.log T :=
      mul_le_mul_of_nonneg_left hlognT hC.le
    rw [abs_le] at hsigmaInt htauInt
    linarith
  have hsigmaPos : 0 < ‖xi ((sigma : ℂ) + (T : ℂ) * I)‖ :=
    norm_pos_iff.mpr (hTzero sigma)
  have htauPos : 0 < ‖xi ((tau : ℂ) + (T : ℂ) * I)‖ :=
    norm_pos_iff.mpr (hTzero tau)
  have hpow : T ^ (2 * C) = Real.exp ((2 * C) * Real.log T) := by
    rw [Real.rpow_def_of_pos hTpos]
    congr 1
    ring
  have hpositive : ‖xi ((sigma : ℂ) + (T : ℂ) * I)‖ ≤
      T ^ (2 * C) * ‖xi ((tau : ℂ) + (T : ℂ) * I)‖ := by
    rw [hpow, ← Real.exp_log htauPos, ← Real.exp_add]
    rw [← Real.exp_log hsigmaPos]
    exact Real.exp_le_exp.mpr (by linarith)
  refine ⟨hpositive, ?_⟩
  have hsigmaConj :
      ‖xi ((sigma : ℂ) - (T : ℂ) * I)‖ =
        ‖xi ((sigma : ℂ) + (T : ℂ) * I)‖ := by
    rw [show (sigma : ℂ) - (T : ℂ) * I =
        (starRingEnd ℂ) ((sigma : ℂ) + (T : ℂ) * I) by
      apply Complex.ext <;> simp]
    rw [xi_conj, norm_conj]
  have htauConj :
      ‖xi ((tau : ℂ) - (T : ℂ) * I)‖ =
        ‖xi ((tau : ℂ) + (T : ℂ) * I)‖ := by
    rw [show (tau : ℂ) - (T : ℂ) * I =
        (starRingEnd ℂ) ((tau : ℂ) + (T : ℂ) * I) by
      apply Complex.ext <;> simp]
    rw [xi_conj, norm_conj]
  rw [hsigmaConj, htauConj]
  exact hpositive

/-- Natural-exponent form of the selected Xi-ratio estimate. -/
theorem exists_xi_horizontal_ratio_nat_bound :
    ∃ M : ℕ, ∃ n0 : ℝ, ∀ n : ℝ, n0 ≤ n → ∃ T : ℝ,
      n ≤ T ∧ T ≤ n + 1 ∧
      ∀ sigma tau : ℝ, -1 ≤ sigma → sigma ≤ 2 → -1 ≤ tau → tau ≤ 2 →
        ‖xi ((sigma : ℂ) + (T : ℂ) * I)‖ ≤
            T ^ M * ‖xi ((tau : ℂ) + (T : ℂ) * I)‖ ∧
          ‖xi ((sigma : ℂ) - (T : ℂ) * I)‖ ≤
            T ^ M * ‖xi ((tau : ℂ) - (T : ℂ) * I)‖ := by
  obtain ⟨A, hA, n0, hsel⟩ := exists_xi_horizontal_ratio_bound
  refine ⟨⌈A⌉₊, max n0 10, ?_⟩
  intro n hn
  obtain ⟨T, hnT, hTn, hratio⟩ := hsel n (le_trans (le_max_left _ _) hn)
  refine ⟨T, hnT, hTn, ?_⟩
  have hT1 : 1 ≤ T := by
    have hn10 : 10 ≤ n := le_trans (le_max_right _ _) hn
    linarith
  have hpow : T ^ A ≤ T ^ ⌈A⌉₊ := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hT1 (Nat.le_ceil A)
  intro sigma tau hsigma1 hsigma2 htau1 htau2
  obtain ⟨hpos, hneg⟩ := hratio sigma tau hsigma1 hsigma2 htau1 htau2
  constructor
  · exact hpos.trans (mul_le_mul_of_nonneg_right hpow (norm_nonneg _))
  · exact hneg.trans (mul_le_mul_of_nonneg_right hpow (norm_nonneg _))

end

end RHTower
