import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import GaloisForLFunctions.HTGeometry.L2GridApproximation
import GaloisForLFunctions.HTGeometry.IntegralCauchySchwarz

/-!
# Smooth recovery of weighted terminal mass

Expanding smooth cutoffs preserve interval support in square-integrable
approximation. Exponential conjugation then identifies the dual supremum
of smooth terminal tests with the exact eighth-power weighted mass.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal
namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

/-- Smooth compact tests approximate square-integrable functions in squared integral norm. -/
theorem exists_smooth_sq_integral_approx {f : ℝ → ℝ} (hf : MemLp f 2)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℝ → ℝ, HasCompactSupport g ∧ ContDiff ℝ ∞ g ∧
      (∫ y, (f y - g y) ^ 2) ≤ ε := by
  obtain ⟨g, hgc, hgd, hclose⟩ := hf.exist_eLpNorm_sub_le
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) (by norm_num) (Real.sqrt_pos.mpr hε)
  have hg : MemLp g 2 := hgd.continuous.memLp_of_hasCompactSupport hgc
  have hnorm : ‖(hf.sub hg).toLp (f - g)‖ ≤ Real.sqrt ε := by
    rw [Lp.norm_toLp]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hclose).trans_eq
      (ENNReal.toReal_ofReal (Real.sqrt_nonneg ε))
  refine ⟨g, hgc, hgd, ?_⟩
  have hsq := pow_le_pow_left₀ (norm_nonneg ((hf.sub hg).toLp (f - g))) hnorm 2
  rw [HTGeometry.norm_toLp_sq, Real.sq_sqrt hε.le] at hsq
  simpa only [Pi.sub_apply] using hsq

private def intervalRecoveryBump (a b : ℝ) (hab : a < b) (n : ℕ) :
    ContDiffBump ((a + b) / 2) where
  rIn := ((b - a) / 2) * (1 - 1 / ((n : ℝ) + 2))
  rOut := (b - a) / 2
  rIn_pos := by
    have hn : (1 : ℝ) < (n : ℝ) + 2 := by
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith only [hn0]
    have hi : 1 / ((n : ℝ) + 2) < 1 := (div_lt_one (by positivity)).mpr hn
    exact mul_pos (by linarith only [hab]) (sub_pos.mpr hi)
  rIn_lt_rOut := by
    have hr : 0 < (b - a) / 2 := by linarith only [hab]
    have hi : 0 < 1 / ((n : ℝ) + 2) := by positivity
    nlinarith only [mul_pos hr hi]

private theorem intervalRecoveryBump_zero {a b : ℝ} (hab : a < b) (n : ℕ)
    (y : ℝ) (hy : y ∉ Icc a b) : intervalRecoveryBump a b hab n y = 0 := by
  apply ContDiffBump.zero_of_le_dist
  change (b - a) / 2 ≤ dist y ((a + b) / 2)
  rw [Real.dist_eq]
  simp only [mem_Icc, not_and_or, not_le] at hy
  rcases hy with hy | hy
  · rw [abs_of_nonpos (by linarith only [hab, hy])]
    linarith only [hy]
  · rw [abs_of_nonneg (by linarith only [hab, hy])]
    linarith only [hy]

private theorem intervalRecoveryBump_eventually_one {a b : ℝ} (hab : a < b)
    {y : ℝ} (hy : y ∈ Ioo a b) :
    ∀ᶠ n : ℕ in atTop, intervalRecoveryBump a b hab n y = 1 := by
  have hni : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 2)) atTop (𝓝 0) := by
    have hnat : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop := by
      refine tendsto_atTop.2 fun t => ?_
      filter_upwards [(tendsto_natCast_atTop_atTop :
        Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).eventually_ge_atTop t] with n hn
      linarith only [hn]
    simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp hnat
  have hr : Tendsto (fun n : ℕ => (intervalRecoveryBump a b hab n).rIn) atTop
      (𝓝 ((b - a) / 2)) := by
    have h1 : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    simpa only [intervalRecoveryBump, sub_zero, mul_one] using
      ((h1.sub hni).const_mul ((b - a) / 2))
  have hd : dist y ((a + b) / 2) < (b - a) / 2 := by
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith only [hy.1, hy.2]
  filter_upwards [hr.eventually (eventually_gt_nhds hd)] with n hn
  exact (intervalRecoveryBump a b hab n).one_of_mem_closedBall hn.le

private theorem tendsto_intervalRecoveryBump_sq_error {f : ℝ → ℝ}
    (hf : MemLp f 2) {a b : ℝ} (hab : a < b)
    (hs : ∀ y, y ∉ Ioo a b → f y = 0) :
    Tendsto (fun n : ℕ => ∫ y, ((1 - intervalRecoveryBump a b hab n y) * f y) ^ 2)
      atTop (𝓝 0) := by
  have hfi : Integrable (fun y => f y ^ 2) := by
    simpa only [Real.norm_eq_abs, sq_abs] using
      (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
  have hmeas (n : ℕ) : AEStronglyMeasurable
      (fun y => ((1 - intervalRecoveryBump a b hab n y) * f y) ^ 2) :=
    ((aestronglyMeasurable_const.sub
      (intervalRecoveryBump a b hab n).continuous.aestronglyMeasurable).mul
        hf.aestronglyMeasurable).pow 2
  have hbound (n : ℕ) (y : ℝ) :
      ‖((1 - intervalRecoveryBump a b hab n y) * f y) ^ 2‖ ≤ f y ^ 2 := by
    have hη0 := (intervalRecoveryBump a b hab n).nonneg (x := y)
    have hη1 := (intervalRecoveryBump a b hab n).le_one (x := y)
    have he : (1 - intervalRecoveryBump a b hab n y) ^ 2 ≤ 1 := by
      nlinarith only [hη0, hη1, mul_nonneg hη0 (sub_nonneg.mpr hη1)]
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), mul_pow]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right he (sq_nonneg (f y))
  have hlim (y : ℝ) : Tendsto
      (fun n : ℕ => ((1 - intervalRecoveryBump a b hab n y) * f y) ^ 2) atTop (𝓝 0) := by
    by_cases hy : y ∈ Ioo a b
    · apply tendsto_const_nhds.congr'
      filter_upwards [intervalRecoveryBump_eventually_one hab hy] with n hn
      simp only [hn, sub_self, zero_mul, zero_pow (by decide : 2 ≠ 0)]
    · simp only [hs y hy, mul_zero, zero_pow (by decide : 2 ≠ 0)]
      exact tendsto_const_nhds
  have h := tendsto_integral_of_dominated_convergence (fun y => f y ^ 2)
    hmeas hfi (fun n => Eventually.of_forall (hbound n)) (Eventually.of_forall hlim)
  simpa only [integral_zero] using h

/-- Smooth functions supported in a closed interval approximate every square-integrable
function supported in its interior. -/
theorem exists_smooth_sq_integral_approx_in_interval {f : ℝ → ℝ}
    (hf : MemLp f 2) {a b : ℝ} (hab : a < b)
    (hs : ∀ y, y ∉ Ioo a b → f y = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℝ → ℝ, ContDiff ℝ ∞ g ∧ (∀ y, y ∉ Icc a b → g y = 0) ∧
      (∫ y, (f y - g y) ^ 2) < ε := by
  obtain ⟨g, hgc, hgd, hclose⟩ := exists_smooth_sq_integral_approx hf
    (by positivity : 0 < ε / 8)
  have hcut := tendsto_intervalRecoveryBump_sq_error hf hab hs
  obtain ⟨n, hn⟩ := (hcut.eventually
    (eventually_lt_nhds (by positivity : (0 : ℝ) < ε / 8))).exists
  let η := intervalRecoveryBump a b hab n
  have hη : ContDiff ℝ ∞ η := η.contDiff
  have hg : MemLp g 2 := hgd.continuous.memLp_of_hasCompactSupport hgc
  have hηg : MemLp (fun y => η y * g y) 2 :=
    (hη.mul hgd).continuous.memLp_of_hasCompactSupport (η.hasCompactSupport.mul_right)
  have hd : Integrable (fun y => (f y - η y * g y) ^ 2) := by
    simpa only [Pi.sub_apply, Real.norm_eq_abs, sq_abs] using
      (memLp_two_iff_integrable_sq_norm (hf.sub hηg).aestronglyMeasurable).mp (hf.sub hηg)
  have he : Integrable (fun y => (f y - g y) ^ 2) := by
    simpa only [Pi.sub_apply, Real.norm_eq_abs, sq_abs] using
      (memLp_two_iff_integrable_sq_norm (hf.sub hg).aestronglyMeasurable).mp (hf.sub hg)
  have hf2 : Integrable (fun y => f y ^ 2) := by
    simpa only [Real.norm_eq_abs, sq_abs] using
      (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
  have hb (y : ℝ) : ((1 - η y) * f y) ^ 2 ≤ f y ^ 2 := by
    have hη0 := η.nonneg (x := y)
    have hη1 := η.le_one (x := y)
    have ht : (1 - η y) ^ 2 ≤ 1 := by
      nlinarith only [hη0, hη1, mul_nonneg hη0 (sub_nonneg.mpr hη1)]
    simpa only [mul_pow, one_mul] using mul_le_mul_of_nonneg_right ht (sq_nonneg (f y))
  have hci : Integrable (fun y => ((1 - η y) * f y) ^ 2) :=
    hf2.mono' (((aestronglyMeasurable_const.sub hη.continuous.aestronglyMeasurable).mul
      hf.aestronglyMeasurable).pow 2) (Eventually.of_forall fun y => by
        simpa only [Pi.pow_apply, Real.norm_eq_abs, abs_pow, sq_abs] using hb y)
  refine ⟨fun y => η y * g y, hη.mul hgd,
    fun y hy => by
      change intervalRecoveryBump a b hab n y * g y = 0
      rw [intervalRecoveryBump_zero hab n y hy, zero_mul], ?_⟩
  have hpoint (y : ℝ) : (f y - η y * g y) ^ 2 ≤
      2 * ((1 - η y) * f y) ^ 2 + 2 * (f y - g y) ^ 2 := by
    have hη0 := η.nonneg (x := y)
    have hη1 := η.le_one (x := y)
    have hsq : (η y * (f y - g y)) ^ 2 ≤ (f y - g y) ^ 2 := by
      have ht : η y ^ 2 ≤ 1 := by nlinarith only [hη0, hη1, mul_nonneg hη0 (sub_nonneg.mpr hη1)]
      simpa only [mul_pow, one_mul] using mul_le_mul_of_nonneg_right ht (sq_nonneg (f y - g y))
    nlinarith only [hsq, sq_nonneg ((1 - η y) * f y - η y * (f y - g y))]
  have hi := integral_mono hd ((hci.const_mul 2).add (he.const_mul 2)) hpoint
  simp only [Pi.add_apply] at hi
  rw [integral_add (hci.const_mul 2) (he.const_mul 2), integral_const_mul,
    integral_const_mul] at hi
  change (∫ y, ((1 - η y) * f y) ^ 2) < ε / 8 at hn
  linarith only [hi, hn, hclose, hε]

/-- Smooth terminal tests attain every strict lower bound below the weighted square mass. -/
theorem exists_smooth_exponential_dual_floor {F : ℝ → ℝ} (hF : MemLp F 2)
    {A b : ℝ} (hA : 0 < A)
    (hb : b < ∫ y in Ioo (-A) 0, F y ^ 2 * Real.exp (-(8 * y))) :
    ∃ H : ℝ → ℝ, ContDiff ℝ ∞ H ∧ (∀ y, y ∉ Icc (-A) 0 → H y = 0) ∧
      b < 2 * (∫ y, (F y * H y) * Real.exp (-(8 * y))) -
        ∫ y, H y ^ 2 * Real.exp (-(8 * y)) := by
  let G : ℝ → ℝ := (Ioo (-A) 0).indicator (fun y => F y * Real.exp (-(4 * y)))
  have hFm := hF.aestronglyMeasurable
  have hF2 : Integrable (fun y => F y ^ 2) := by
    simpa only [Real.norm_eq_abs, sq_abs] using
      (memLp_two_iff_integrable_sq_norm hFm).mp hF
  have hGm : AEStronglyMeasurable G :=
    (hFm.mul (by fun_prop : Continuous (fun y : ℝ => Real.exp (-(4 * y)))).aestronglyMeasurable).indicator
      measurableSet_Ioo
  have hGe (y : ℝ) : G y ^ 2 =
      (Ioo (-A) 0).indicator (fun y => F y ^ 2 * Real.exp (-(8 * y))) y := by
    by_cases hy : y ∈ Ioo (-A) 0
    · simp only [G, indicator_of_mem hy, mul_pow, ← Real.exp_nat_mul]
      congr 2
      ring
    · simp only [G, indicator_of_notMem hy, zero_pow (by decide : 2 ≠ 0)]
  have hG2 : Integrable (fun y => G y ^ 2) := by
    apply (hF2.const_mul (Real.exp (8 * A))).mono' (hGm.pow 2)
    filter_upwards with y
    simp only [Pi.pow_apply, Real.norm_eq_abs, abs_pow, sq_abs]
    rw [hGe]
    by_cases hy : y ∈ Ioo (-A) 0
    · rw [indicator_of_mem hy]
      have he : Real.exp (-(8 * y)) ≤ Real.exp (8 * A) :=
        Real.exp_le_exp.mpr (by linarith only [hy.1])
      exact (mul_le_mul_of_nonneg_left he (sq_nonneg (F y))).trans_eq (mul_comm _ _)
    · rw [indicator_of_notMem hy]
      positivity
  have hG : MemLp G 2 := (memLp_two_iff_integrable_sq_norm hGm).mpr
    (by simpa only [Real.norm_eq_abs, sq_abs] using hG2)
  have hGI : (∫ y, G y ^ 2) = ∫ y in Ioo (-A) 0, F y ^ 2 * Real.exp (-(8 * y)) := by
    simp_rw [hGe]
    exact integral_indicator measurableSet_Ioo
  have hGs (y : ℝ) (hy : y ∉ Ioo (-A) 0) : G y = 0 := indicator_of_notMem hy _
  obtain ⟨g, hgd, hgs, he⟩ := exists_smooth_sq_integral_approx_in_interval hG
    (by linarith only [hA] : -A < 0) hGs (sub_pos.mpr hb)
  have hgc : HasCompactSupport g := HasCompactSupport.intro isCompact_Icc hgs
  have hg : MemLp g 2 := hgd.continuous.memLp_of_hasCompactSupport hgc
  have hg2 : Integrable (fun y => g y ^ 2) := by
    simpa only [Real.norm_eq_abs, sq_abs] using
      (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mp hg
  have hGg : Integrable (fun y => G y * g y) :=
    HTGeometry.integrable_mul_of_sq_integrable hGm hg.aestronglyMeasurable hG2 hg2
  have hid : (∫ y, (G y - g y) ^ 2) =
      (∫ y, G y ^ 2) - 2 * (∫ y, G y * g y) + ∫ y, g y ^ 2 := by
    have hdiff : Integrable (fun y => G y ^ 2 - 2 * (G y * g y)) :=
      hG2.sub (hGg.const_mul 2)
    simp_rw [show ∀ y, (G y - g y) ^ 2 = G y ^ 2 - 2 * (G y * g y) + g y ^ 2 by
      intro y; ring]
    rw [integral_add hdiff hg2,
      integral_sub hG2 (hGg.const_mul 2), integral_const_mul]
  let H : ℝ → ℝ := fun y => Real.exp (4 * y) * g y
  have hHd : ContDiff ℝ ∞ H :=
    (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)).mul hgd
  have hHs (y : ℝ) (hy : y ∉ Icc (-A) 0) : H y = 0 := by
    simp only [H, hgs y hy, mul_zero]
  have hself (y : ℝ) : H y ^ 2 * Real.exp (-(8 * y)) = g y ^ 2 := by
    have he : Real.exp (4 * y) ^ 2 * Real.exp (-(8 * y)) = 1 := by
      have harg : ((2 : ℕ) : ℝ) * (4 * y) + -(8 * y) = 0 := by push_cast; ring
      rw [← Real.exp_nat_mul, ← Real.exp_add, harg, Real.exp_zero]
    calc
      _ = (Real.exp (4 * y) ^ 2 * Real.exp (-(8 * y))) * g y ^ 2 := by dsimp only [H]; ring
      _ = _ := by rw [he, one_mul]
  have hpair : (fun y => (F y * H y) * Real.exp (-(8 * y))) =ᵐ[volume]
      (fun y => G y * g y) := by
    have ha : ∀ᵐ y : ℝ, y ≠ -A := by simp [ae_iff]
    have hz : ∀ᵐ y : ℝ, y ≠ 0 := by simp [ae_iff]
    filter_upwards [ha, hz] with y hya hyz
    have hexp : Real.exp (4 * y) * Real.exp (-(8 * y)) = Real.exp (-(4 * y)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    by_cases hy : y ∈ Ioo (-A) 0
    · simp only [G, indicator_of_mem hy]
      calc
        _ = (F y * g y) * (Real.exp (4 * y) * Real.exp (-(8 * y))) := by dsimp only [H]; ring
        _ = _ := by rw [hexp]; ring
    · have hout : y ∉ Icc (-A) 0 := by
        rintro ⟨hlo, hhi⟩
        exact hy ⟨lt_of_le_of_ne hlo hya.symm, lt_of_le_of_ne hhi hyz⟩
      simp only [hHs y hout, hGs y hy, mul_zero, zero_mul]
  refine ⟨H, hHd, hHs, ?_⟩
  rw [integral_congr_ae hpair]
  simp_rw [hself]
  rw [hid, hGI] at he
  linarith only [he]

#print axioms exists_smooth_sq_integral_approx_in_interval
#print axioms exists_smooth_exponential_dual_floor
end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
