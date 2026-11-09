import GaloisForLFunctions.EulerFETransportTheory.FiniteEnergyDefectsObeyTheTentIdentity

/-!
# Finite-energy tent errors vanish

Cauchy–Schwarz bounds every tent error by the square root of its width times the
boundary energy. Restricting the boundary to the moving tent window also gives
decay at large positive heights. These are the two error estimates needed by the
atomic recurrence argument.
-/

open Complex MeasureTheory Filter Topology Set
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.ArithmeticPositiveDuality

noncomputable section
namespace GaloisForLFunctions.EulerFETransportTheory

private def tentWindow (h n : ℝ) : Set ℝ := Icc (h * (n - 1)) (h * (n + 1))

private theorem norm_defectTentTest_le_one (h n y : ℝ) : ‖defectTentTest h n y‖ ≤ 1 := by
  rw [defectTentTest, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (unitTent_nonneg _ _)]
  exact unitTent_le_one _ _

private theorem defectTentTest_eq_zero_off_window {h : ℝ} (hh : 0 < h) (n y : ℝ)
    (hy : y ∉ tentWindow h n) : defectTentTest h n y = 0 := by
  by_contra hn
  exact hy (support_defectTentTest hh n hn)

private theorem norm_defectTentTest_toLp_le {h : ℝ} (hh : 0 < h) (n : ℝ) :
    ‖(memLp_defectTentTest hh n).toLp (defectTentTest h n)‖ ≤ Real.sqrt (2 * h) := by
  have hfin : volume (tentWindow h n) ≠ ⊤ := by
    rw [tentWindow, Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  let k : DefectL2 := indicatorConstLp 2 (μ := volume)
    (s := tentWindow h n) measurableSet_Icc hfin (1 : ℂ)
  have hle : ‖(memLp_defectTentTest hh n).toLp (defectTentTest h n)‖ ≤ ‖k‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [(memLp_defectTentTest hh n).coeFn_toLp,
      (indicatorConstLp_coeFn (p := 2) (hs := measurableSet_Icc)
        (hμs := hfin) (c := (1 : ℂ)))]
      with y hy hk
    rw [hy]
    change k y = (tentWindow h n).indicator (fun _ => (1 : ℂ)) y at hk
    rw [hk]
    by_cases hmem : y ∈ tentWindow h n
    · simpa only [indicator_of_mem hmem, norm_one] using norm_defectTentTest_le_one h n y
    · simp only [indicator_of_notMem hmem,
        defectTentTest_eq_zero_off_window hh n y hmem, norm_zero, le_refl]
  have hk : ‖k‖ = Real.sqrt (2 * h) := by
    dsimp only [k]
    rw [norm_indicatorConstLp (by norm_num : (2 : ENNReal) ≠ 0) (by norm_num)]
    have hv : volume.real (tentWindow h n) = 2 * h := by
      rw [tentWindow, Real.volume_real_Icc]
      have he : h * (n + 1) - h * (n - 1) = 2 * h := by ring
      rw [he, max_eq_left (by positivity)]
    rw [hv]
    norm_num only [norm_one, ENNReal.toReal_ofNat, one_mul]
    exact (Real.sqrt_eq_rpow _).symm
  exact hle.trans_eq hk

private theorem tent_pairing_eq_inner {h : ℝ} (hh : 0 < h) (n : ℝ) (f : DefectL2) :
    (∫ y : ℝ, defectTentTest h n y * f y) =
      inner ℂ ((memLp_defectTentTest hh n).toLp (defectTentTest h n)) f := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(memLp_defectTentTest hh n).coeFn_toLp] with y hy
  change defectTentTest h n y * f y = inner ℂ
    (((memLp_defectTentTest hh n).toLp (defectTentTest h n)) y) (f y)
  rw [hy, RCLike.inner_apply]
  simp only [defectTentTest, Complex.conj_ofReal, mul_comm]

private theorem norm_tent_pairing_le {h : ℝ} (hh : 0 < h) (n : ℝ) (f : DefectL2) :
    ‖∫ y : ℝ, defectTentTest h n y * f y‖ ≤ Real.sqrt (2 * h) * ‖f‖ := by
  rw [tent_pairing_eq_inner hh n f]
  exact (norm_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_right (norm_defectTentTest_toLp_le hh n) (norm_nonneg _))

/-- Uniform small-window control, independent of the tent centre. -/
theorem abs_finiteEnergyTentError_le (g : DefectL2) {h : ℝ} (hh : 0 < h) (n : ℝ) :
    |finiteEnergyTentError g h n| ≤ Real.sqrt (2 * h) * ‖defectBoundaryL2 g‖ :=
  (Complex.abs_re_le_norm _).trans (norm_tent_pairing_le hh n (defectBoundaryL2 g))

private def tentCutoff (f : DefectL2) (h n : ℝ) : DefectL2 :=
  ((Lp.memLp f).indicator measurableSet_Icc).toLp ((tentWindow h n).indicator f)

private theorem tent_pairing_eq_cutoff (f : DefectL2) {h : ℝ} (hh : 0 < h) (n : ℝ) :
    (∫ y : ℝ, defectTentTest h n y * f y) =
      ∫ y : ℝ, defectTentTest h n y * tentCutoff f h n y := by
  apply integral_congr_ae
  filter_upwards [((Lp.memLp f).indicator (s := tentWindow h n) measurableSet_Icc).coeFn_toLp]
    with y hy
  change tentCutoff f h n y = (tentWindow h n).indicator f y at hy
  rw [hy]
  by_cases hmem : y ∈ tentWindow h n
  · rw [indicator_of_mem hmem]
  · rw [defectTentTest_eq_zero_off_window hh n y hmem, zero_mul, zero_mul]

private theorem norm_sq_tentCutoff (f : DefectL2) (h n : ℝ) :
    ‖tentCutoff f h n‖ ^ 2 =
      ∫ y : ℝ, (tentWindow h n).indicator (fun y => ‖f y‖ ^ 2) y := by
  rw [Lp_two_norm_sq_eq_integral]
  apply integral_congr_ae
  filter_upwards [((Lp.memLp f).indicator (s := tentWindow h n) measurableSet_Icc).coeFn_toLp]
    with y hy
  change tentCutoff f h n y = (tentWindow h n).indicator f y at hy
  rw [hy]
  by_cases hmem : y ∈ tentWindow h n
  · simp only [indicator_of_mem hmem]
  · simp only [indicator_of_notMem hmem, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]

private theorem tendsto_norm_tentCutoff (f : DefectL2) {h : ℝ} (hh : 0 < h) :
    Tendsto (fun n : ℝ => ‖tentCutoff f h n‖) atTop (𝓝 0) := by
  have hsq : Integrable (fun y : ℝ => ‖f y‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm (Lp.memLp f).1).mp (Lp.memLp f)
  have hlim : Tendsto (fun n : ℝ =>
      ∫ y : ℝ, (tentWindow h n).indicator (fun y => ‖f y‖ ^ 2) y)
      atTop (𝓝 0) := by
    have ht := tendsto_integral_filter_of_dominated_convergence (fun y => ‖f y‖ ^ 2)
      (l := (atTop : Filter ℝ))
      (F := fun n : ℝ => (tentWindow h n).indicator (fun y => ‖f y‖ ^ 2))
      (f := fun _ : ℝ => (0 : ℝ))
      (Eventually.of_forall fun n => hsq.aestronglyMeasurable.indicator measurableSet_Icc)
      (Eventually.of_forall fun n => Eventually.of_forall fun y => by
        by_cases hy : y ∈ tentWindow h n
        · rw [indicator_of_mem hy, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖f y‖)]
        · simp only [indicator_of_notMem hy, norm_zero]
          exact sq_nonneg _)
      hsq ?_
    · simpa only [integral_zero] using ht
    · apply Eventually.of_forall
      intro y
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_gt_atTop (y / h + 1)] with n hn
      have hy : y ∉ tentWindow h n := by
        intro hy
        have hl : y / h < n - 1 := by linarith only [hn]
        have hlt := (div_lt_iff₀ hh).mp hl
        change h * (n - 1) ≤ y ∧ y ≤ h * (n + 1) at hy
        linarith only [hlt, hy.1]
      exact (indicator_of_notMem hy _).symm
  have ht := Real.continuous_sqrt.continuousAt.tendsto.comp hlim
  simpa only [Function.comp_def, ← norm_sq_tentCutoff,
    Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using ht

/-- At a fixed width the actual boundary error disappears at large positive heights. -/
theorem tendsto_finiteEnergyTentError_atTop (g : DefectL2) {h : ℝ} (hh : 0 < h) :
    Tendsto (finiteEnergyTentError g h) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hbound (n : ℝ) : ‖finiteEnergyTentError g h n‖ ≤
      Real.sqrt (2 * h) * ‖tentCutoff (defectBoundaryL2 g) h n‖ := by
    rw [Real.norm_eq_abs]
    apply (Complex.abs_re_le_norm _).trans
    rw [tent_pairing_eq_cutoff (defectBoundaryL2 g) hh n]
    exact norm_tent_pairing_le hh n _
  exact squeeze_zero (fun _ => norm_nonneg _) hbound
    (by simpa using tendsto_const_nhds.mul (tendsto_norm_tentCutoff (defectBoundaryL2 g) hh))

/-- Small-width errors vanish even when their centres move arbitrarily. -/
theorem tendsto_finiteEnergyTentError_smallWidth (g : DefectL2) (n : ℝ → ℝ) :
    Tendsto (fun h : ℝ => finiteEnergyTentError g h (n h))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have ht : Tendsto (fun h : ℝ => Real.sqrt (2 * h) * ‖defectBoundaryL2 g‖)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hc : Continuous (fun h : ℝ => Real.sqrt (2 * h) * ‖defectBoundaryL2 g‖) := by
      fun_prop
    simpa using (hc.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ ht
  filter_upwards [self_mem_nhdsWithin] with h hh
  exact abs_finiteEnergyTentError_le g hh (n h)

end GaloisForLFunctions.EulerFETransportTheory

#print axioms GaloisForLFunctions.EulerFETransportTheory.abs_finiteEnergyTentError_le
#print axioms GaloisForLFunctions.EulerFETransportTheory.tendsto_finiteEnergyTentError_atTop
#print axioms GaloisForLFunctions.EulerFETransportTheory.tendsto_finiteEnergyTentError_smallWidth
