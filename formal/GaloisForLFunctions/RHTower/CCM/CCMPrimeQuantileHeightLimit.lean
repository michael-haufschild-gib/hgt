import GaloisForLFunctions.RHTower.CCM.CCMActualHeadMatchedQuantilePolarRelativeDisplacement

/-!
# Literal prime quantile cells shrink in logarithmic height

Both endpoints approach the logarithm of the corresponding prime-power
index. The statement includes composite indices and zero-mass cells.
-/

open Filter Topology Set
noncomputable section
namespace RHTower

private theorem scale_zero :
    Tendsto (fun n : ℕ => Real.exp (-Real.log (n : ℝ) / 2)) atTop (𝓝 0) := by
  have hl : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hh := tendsto_neg_atBot_iff.mpr
    (hl.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 2))
  have ha : Tendsto (fun n : ℕ => -Real.log (n : ℝ) / 2) atTop atBot := by
    convert hh using 1
    ext n
    ring
  exact Real.tendsto_exp_atBot.comp ha

private theorem scaled_upper :
    Tendsto (fun n : ℕ => Real.exp (-Real.log (n : ℝ) / 2) *
      (1 + ccmOutgoingPrimeCumulative (n + 1) / 2)) atTop (𝓝 1) := by
  have hh := (tendsto_const_nhds (x := (1 : ℝ))).sub
    (tendsto_scaled_ccmActualHeadOutgoingNodeError_atTop_zero.div_const 2)
  norm_num only [zero_div, sub_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have he := two_exp_log_half_sub_quantile_succ_eq_outgoingNodeError n (by omega)
  rw [ccmActualHeadQuantilePolarCoordinate_eq_two_add_cumulative] at he
  have hc : Real.exp (-Real.log (n : ℝ) / 2) * Real.exp (Real.log n / 2) = 1 := by
    rw [← Real.exp_add, show -Real.log (n : ℝ) / 2 + Real.log n / 2 = 0 by ring,
      Real.exp_zero]
  have hm := congrArg (fun x : ℝ => Real.exp (-Real.log (n : ℝ) / 2) * x) he
  nlinarith only [hm, hc]

private theorem scaled_atom_zero :
    Tendsto (fun n : ℕ => Real.exp (-Real.log (n : ℝ) / 2) *
      criticalMellinAtomWeight n) atTop (𝓝 0) := by
  apply squeeze_zero' _ _ (by simpa using scale_zero.mul_const 2)
  · filter_upwards with n
    exact mul_nonneg (Real.exp_pos _).le
      (criticalMellinAtomWeight_nonneg_cCMActualHeadWallGramSignedProducer n)
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    exact mul_le_mul_of_nonneg_left (criticalMellinAtomWeight_le_two_of_pos (by omega))
      (Real.exp_pos _).le

private theorem height_eq (n N : ℕ) :
    ccmOutgoingPrimeQuantileBoundary N - Real.log n =
      2 * Real.log (Real.exp (-Real.log (n : ℝ) / 2) *
        (1 + ccmOutgoingPrimeCumulative N / 2)) := by
  have hc := ccmOutgoingPrimeCumulative_nonneg N
  rw [Real.log_mul (Real.exp_ne_zero _) (by positivity), Real.log_exp]
  unfold ccmOutgoingPrimeQuantileBoundary
  ring

theorem tendsto_ccmOutgoingPrimeQuantileUpper_sub_log :
    Tendsto (fun n : ℕ => ccmOutgoingPrimeQuantileBoundary (n + 1) - Real.log n)
      atTop (𝓝 0) := by
  have hh := ((Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp
    scaled_upper).const_mul 2
  simpa only [Real.log_one, mul_zero, Function.comp_def, ← height_eq] using hh

theorem tendsto_ccmOutgoingPrimeQuantileLower_sub_log :
    Tendsto (fun n : ℕ => ccmOutgoingPrimeQuantileBoundary n - Real.log n)
      atTop (𝓝 0) := by
  have hl : Tendsto (fun n : ℕ => Real.exp (-Real.log (n : ℝ) / 2) *
      (1 + ccmOutgoingPrimeCumulative n / 2)) atTop (𝓝 1) := by
    have hh := scaled_upper.sub (scaled_atom_zero.div_const 2)
    norm_num only [zero_div, sub_zero] at hh
    apply hh.congr
    intro n
    rw [ccmOutgoingPrimeCumulative_succ]
    ring
  have hh := ((Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hl).const_mul 2
  simpa only [Real.log_one, mul_zero, Function.comp_def, ← height_eq] using hh

/-- Uniform control of every point of every sufficiently late actual cell. -/
theorem eventually_ccmOutgoingPrimeQuantileCell_near_log (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, ∀ h ∈ Icc (ccmOutgoingPrimeQuantileBoundary n)
      (ccmOutgoingPrimeQuantileBoundary (n + 1)), |h - Real.log n| < δ := by
  have hl := tendsto_ccmOutgoingPrimeQuantileLower_sub_log
    (Metric.ball_mem_nhds (0 : ℝ) hδ)
  have hu := tendsto_ccmOutgoingPrimeQuantileUpper_sub_log
    (Metric.ball_mem_nhds (0 : ℝ) hδ)
  filter_upwards [hl, hu] with n hn₁ hn₂ h hh
  change dist (ccmOutgoingPrimeQuantileBoundary n - Real.log n) 0 < δ at hn₁
  change dist (ccmOutgoingPrimeQuantileBoundary (n + 1) - Real.log n) 0 < δ at hn₂
  simp only [Real.dist_eq, sub_zero] at hn₁ hn₂
  rw [abs_lt] at hn₁ hn₂ ⊢
  constructor <;> linarith [hh.1, hh.2]

end RHTower
