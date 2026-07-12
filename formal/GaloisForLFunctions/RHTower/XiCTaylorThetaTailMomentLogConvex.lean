import GaloisForLFunctions.RHTower.XiCTaylorThetaTailCompletedSource

/-!
# Log-convexity of all completed theta-source moments

The positive completed theta source gives a Stieltjes moment sequence.  This module records the
all-order adjacent log-convexity inequality needed to test finite critical-Laguerre moment
representations of the theta-tail core.
-/

open Complex Real MeasureTheory Set Filter Topology Polynomial
namespace RHTower
noncomputable section

/-- Every completed theta-source even moment is strictly positive. -/
theorem thetaCuspRawEvenMoment_pos (n : ℕ) :
    0 < thetaCuspRawEvenMoment n := by
  rw [thetaCuspRawEvenMoment]
  let f : ℝ → ℝ := fun x => x ^ (2 * n) * thetaCuspFullSource x
  have hfcont : Continuous f := by
    dsimp [f]
    exact (continuous_id.pow _).mul contDiff_thetaCuspFullSource.continuous
  have hfint : IntegrableOn f (Ioi 0) := by
    simpa only [f] using integrableOn_thetaCuspRawMoment (2 * n)
  have hfnn : 0 ≤ᵐ[volume.restrict (Ioi 0)] f := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    dsimp [f]
    exact mul_nonneg (pow_nonneg hx.le _) (thetaCuspFullSource_pos_of_pos hx).le
  have hpos : 0 < ∫ x : ℝ in Ioi 0, f x := by
    apply (setIntegral_pos_iff_support_of_nonneg_ae hfnn hfint).2
    have hopen : IsOpen (Function.support f ∩ Ioi (0 : ℝ)) :=
      hfcont.isOpen_support.inter isOpen_Ioi
    apply hopen.measure_pos (volume : Measure ℝ)
    refine ⟨1, ?_, by norm_num⟩
    change f 1 ≠ 0
    dsimp [f]
    positivity [thetaCuspFullSource_pos_of_pos (x := 1) (by norm_num)]
  change 0 < 2 * ∫ x : ℝ in Ioi 0, f x
  positivity

/-- Every positive-order completed theta moment is log-convex between its two adjacent moments. -/
theorem thetaCuspRawEvenMoment_sq_le_adjacent
    (n : ℕ) (hn : 1 ≤ n) :
    thetaCuspRawEvenMoment n ^ 2 ≤
      thetaCuspRawEvenMoment (n - 1) * thetaCuspRawEvenMoment (n + 1) := by
  let μ : Measure ℝ := volume.restrict (Ioi 0)
  let f : ℝ → ℝ := fun x => x ^ (n - 1) * Real.sqrt (thetaCuspFullSource x)
  let g : ℝ → ℝ := fun x => x ^ (n + 1) * Real.sqrt (thetaCuspFullSource x)
  have hphi : 0 ≤ᵐ[μ] thetaCuspFullSource := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact (thetaCuspFullSource_pos_of_pos hx).le
  have hf_meas : AEStronglyMeasurable f μ := by
    exact ((((continuous_id.pow (n - 1)).mul
      (Real.continuous_sqrt.comp
        contDiff_thetaCuspFullSource.continuous))).aestronglyMeasurable).mono_measure
      Measure.restrict_le_self
  have hg_meas : AEStronglyMeasurable g μ := by
    exact ((((continuous_id.pow (n + 1)).mul
      (Real.continuous_sqrt.comp
        contDiff_thetaCuspFullSource.continuous))).aestronglyMeasurable).mono_measure
      Measure.restrict_le_self
  have hf_sq : Integrable (fun x => f x ^ 2) μ := by
    have h := integrableOn_thetaCuspRawMoment (2 * (n - 1))
    apply h.congr
    filter_upwards [hphi] with x hx
    dsimp [f]
    rw [mul_pow, Real.sq_sqrt hx]
    rw [← pow_mul]
    congr 2
    omega
  have hg_sq : Integrable (fun x => g x ^ 2) μ := by
    have h := integrableOn_thetaCuspRawMoment (2 * (n + 1))
    apply h.congr
    filter_upwards [hphi] with x hx
    dsimp [g]
    rw [mul_pow, Real.sq_sqrt hx]
    rw [← pow_mul]
    congr 2
    omega
  have hf : MemLp f 2 μ :=
    (memLp_two_iff_integrable_sq hf_meas).2 hf_sq
  have hg : MemLp g 2 μ :=
    (memLp_two_iff_integrable_sq hg_meas).2 hg_sq
  have hf' : MemLp f (ENNReal.ofReal (2 : ℝ)) μ := by simpa using hf
  have hg' : MemLp g (ENNReal.ofReal (2 : ℝ)) μ := by simpa using hg
  have hcs := integral_mul_norm_le_Lp_mul_Lq
    (μ := μ) (p := (2 : ℝ)) (q := (2 : ℝ))
    (Real.HolderConjugate.two_two) hf' hg'
  have hfg : (∫ x, ‖f x‖ * ‖g x‖ ∂μ) =
      ∫ x in Ioi 0, x ^ (2 * n) * thetaCuspFullSource x := by
    apply integral_congr_ae
    filter_upwards [hphi, ae_restrict_mem measurableSet_Ioi] with x hx hxi
    dsimp [f, g]
    rw [abs_of_nonneg (mul_nonneg (pow_nonneg hxi.le _) (Real.sqrt_nonneg _)),
      abs_of_nonneg (mul_nonneg (pow_nonneg hxi.le _) (Real.sqrt_nonneg _))]
    calc
      x ^ (n - 1) * √(thetaCuspFullSource x) *
          (x ^ (n + 1) * √(thetaCuspFullSource x)) =
        x ^ ((n - 1) + (n + 1)) * (√(thetaCuspFullSource x)) ^ 2 := by
          rw [pow_add]
          ring
      _ = x ^ (2 * n) * thetaCuspFullSource x := by
        rw [Real.sq_sqrt hx]
        congr 2
        omega
  have hf2 : (∫ x, ‖f x‖ ^ (2 : ℝ) ∂μ) =
      ∫ x in Ioi 0, x ^ (2 * (n - 1)) * thetaCuspFullSource x := by
    apply integral_congr_ae
    filter_upwards [hphi] with x hx
    dsimp [f]
    rw [show (2 : ℝ) = (2 : ℕ) by norm_num, Real.rpow_natCast]
    calc
      |x ^ (n - 1) * √(thetaCuspFullSource x)| ^ 2 =
          (x ^ (n - 1) * √(thetaCuspFullSource x)) ^ 2 := sq_abs _
      _ = x ^ (2 * (n - 1)) * thetaCuspFullSource x := by
        rw [mul_pow, Real.sq_sqrt hx, ← pow_mul]
        congr 2
        omega
  have hg2 : (∫ x, ‖g x‖ ^ (2 : ℝ) ∂μ) =
      ∫ x in Ioi 0, x ^ (2 * (n + 1)) * thetaCuspFullSource x := by
    apply integral_congr_ae
    filter_upwards [hphi] with x hx
    dsimp [g]
    rw [show (2 : ℝ) = (2 : ℕ) by norm_num, Real.rpow_natCast]
    calc
      |x ^ (n + 1) * √(thetaCuspFullSource x)| ^ 2 =
          (x ^ (n + 1) * √(thetaCuspFullSource x)) ^ 2 := sq_abs _
      _ = x ^ (2 * (n + 1)) * thetaCuspFullSource x := by
        rw [mul_pow, Real.sq_sqrt hx, ← pow_mul]
        congr 2
        omega
  rw [hfg, hf2, hg2] at hcs
  have hmPrev : 0 ≤ ∫ x in Ioi 0,
      x ^ (2 * (n - 1)) * thetaCuspFullSource x := by
    exact integral_nonneg_of_ae (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact mul_nonneg (pow_nonneg hx.le _) (thetaCuspFullSource_pos_of_pos hx).le)
  have hmNext : 0 ≤ ∫ x in Ioi 0,
      x ^ (2 * (n + 1)) * thetaCuspFullSource x := by
    exact integral_nonneg_of_ae (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact mul_nonneg (pow_nonneg hx.le _) (thetaCuspFullSource_pos_of_pos hx).le)
  have hm : 0 ≤ ∫ x in Ioi 0,
      x ^ (2 * n) * thetaCuspFullSource x := by
    exact integral_nonneg_of_ae (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact mul_nonneg (pow_nonneg hx.le _) (thetaCuspFullSource_pos_of_pos hx).le)
  have hcs' : (∫ x in Ioi 0, x ^ (2 * n) * thetaCuspFullSource x) ≤
      Real.sqrt (∫ x in Ioi 0,
        x ^ (2 * (n - 1)) * thetaCuspFullSource x) *
      Real.sqrt (∫ x in Ioi 0,
        x ^ (2 * (n + 1)) * thetaCuspFullSource x) := by
    simpa only [← Real.sqrt_eq_rpow] using hcs
  have hright : 0 ≤
      Real.sqrt (∫ x in Ioi 0,
        x ^ (2 * (n - 1)) * thetaCuspFullSource x) *
      Real.sqrt (∫ x in Ioi 0,
        x ^ (2 * (n + 1)) * thetaCuspFullSource x) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hsq := (sq_le_sq₀ hm hright).2 hcs'
  rw [mul_pow] at hsq
  rw [Real.sq_sqrt hmPrev, Real.sq_sqrt hmNext] at hsq
  norm_num [thetaCuspRawEvenMoment]
  nlinarith [hsq]

/-- Consecutive completed theta-moment ratios are nondecreasing. -/
theorem thetaCuspRawEvenMoment_ratio_mono (k : ℕ) :
    thetaCuspRawEvenMoment (k + 1) / thetaCuspRawEvenMoment k ≤
      thetaCuspRawEvenMoment (k + 2) / thetaCuspRawEvenMoment (k + 1) := by
  rw [div_le_div_iff₀ (thetaCuspRawEvenMoment_pos k)
    (thetaCuspRawEvenMoment_pos (k + 1))]
  have h := thetaCuspRawEvenMoment_sq_le_adjacent (k + 1) (by omega)
  rw [show k + 1 - 1 = k by omega, show k + 1 + 1 = k + 2 by omega] at h
  nlinarith

end
end RHTower
