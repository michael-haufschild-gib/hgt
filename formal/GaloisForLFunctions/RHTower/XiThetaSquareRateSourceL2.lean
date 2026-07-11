import GaloisForLFunctions.RHTower.XiThetaSquareRateHardy
import Mathlib.Analysis.Fourier.LpSpace

open Complex Real Set Filter Topology MeasureTheory FourierTransform
open scoped ENNReal

noncomputable section

namespace RHTower

/-- The physical boundary reader in mathlib's Fourier frequency normalization. -/
def thetaHeatRateReaderFourierProfile (n : ℕ) (ξ : ℝ) : ℂ :=
  thetaHeatRateReaderSymbol n (((2 * Real.pi * ξ : ℝ) : ℂ) * I)

lemma thetaHeatRateReaderFourierProfile_continuousAt {n : ℕ} (hn : 1 ≤ n)
    {ξ : ℝ} (hξ : ξ ≠ 0) :
    ContinuousAt (thetaHeatRateReaderFourierProfile n) ξ := by
  have ht : 2 * Real.pi * ξ ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) hξ
  have houter := thetaSquareBlaschkeReaderSymbol_continuousAt_mul_I hn
    (t := (2 * Real.pi * ξ) / Real.pi) (div_ne_zero ht Real.pi_ne_zero)
  have hline : ContinuousAt (fun u : ℝ =>
      (((2 * Real.pi * u : ℝ) : ℂ) * I) / (Real.pi : ℂ)) ξ := by
    fun_prop
  unfold thetaHeatRateReaderFourierProfile thetaHeatRateReaderSymbol
  exact houter.comp_of_eq hline (by
    push_cast
    field_simp
  )

theorem thetaHeatRateReaderFourierProfile_aestronglyMeasurable
    {n : ℕ} (hn : 1 ≤ n) :
    AEStronglyMeasurable (thetaHeatRateReaderFourierProfile n) := by
  refine (measurable_of_continuousOn_compl_singleton (0 : ℝ) ?_).aestronglyMeasurable
  exact continuousOn_of_forall_continuousAt fun ξ hξ =>
    thetaHeatRateReaderFourierProfile_continuousAt hn hξ

private lemma integrable_inv_sq_add_sq_source {a : ℝ} (ha : 0 < a) :
    Integrable (fun t : ℝ => (a ^ 2 + t ^ 2)⁻¹) := by
  have hbase := integrable_inv_one_add_sq.comp_div ha.ne'
  have hscaled := hbase.const_mul (a⁻¹ ^ 2)
  apply hscaled.congr
  exact Filter.Eventually.of_forall fun t => by
    dsimp
    field_simp

private lemma integrable_sq_norm_thetaSquareBlaschkeReaderSymbol_boundary
    {n : ℕ} (hn : 1 ≤ n) :
    Integrable (fun t : ℝ => ‖thetaSquareBlaschkeReaderSymbol n ((t : ℂ) * I)‖ ^ 2) := by
  let C : ℝ := ((2 * n * Real.sinh (Real.pi * n)) ^ 2 / Real.pi ^ 2)
  let g : ℝ → ℝ := fun t => C * ((((n : ℝ) ^ 2) ^ 2 + t ^ 2)⁻¹)
  have hnR : (0 : ℝ) < n := by positivity
  have hgInt : Integrable g :=
    (integrable_inv_sq_add_sq_source (sq_pos_of_pos hnR)).const_mul C
  have hmeas : AEStronglyMeasurable
      (fun t : ℝ => ‖thetaSquareBlaschkeReaderSymbol n ((t : ℂ) * I)‖ ^ 2) := by
    refine (measurable_of_continuousOn_compl_singleton (0 : ℝ) ?_).aestronglyMeasurable
    exact continuousOn_of_forall_continuousAt fun t ht => by
      have hline : ContinuousAt (fun u : ℝ => (u : ℂ) * I) t := by fun_prop
      have hcomp :=
        (thetaSquareBlaschkeReaderSymbol_continuousAt_mul_I hn ht).comp_of_eq hline rfl
      simpa [Function.comp_def] using hcomp.norm.pow 2
  refine hgInt.congr ?_
  have ht0 : ∀ᵐ t : ℝ, t ≠ 0 := by simp [ae_iff, measure_singleton]
  filter_upwards [ht0] with t ht
  dsimp [g, C]
  rw [norm_thetaSquareBlaschkeReaderSymbol_mul_I hn ht, div_pow]
  have hden :
      (Real.pi * Real.sqrt (((n : ℝ) ^ 2) ^ 2 + t ^ 2)) ^ 2 =
        Real.pi ^ 2 * (((n : ℝ) ^ 2) ^ 2 + t ^ 2) := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
  rw [hden]
  field_simp

private lemma integrable_sq_norm_thetaHeatRateReaderSymbol_boundary
    {n : ℕ} (hn : 1 ≤ n) :
    Integrable (fun t : ℝ => ‖thetaHeatRateReaderSymbol n ((t : ℂ) * I)‖ ^ 2) := by
  let g : ℝ → ℝ := fun u =>
    ‖thetaSquareBlaschkeReaderSymbol n ((u : ℂ) * I)‖ ^ 2
  have hg : Integrable g := integrable_sq_norm_thetaSquareBlaschkeReaderSymbol_boundary hn
  have hcomp := hg.comp_div Real.pi_ne_zero
  apply hcomp.congr
  exact Filter.Eventually.of_forall fun t => by
    dsimp [g, thetaHeatRateReaderSymbol]
    congr 2
    push_cast
    field_simp

theorem thetaHeatRateReaderFourierProfile_memLp_two
    {n : ℕ} (hn : 1 ≤ n) :
    MemLp (thetaHeatRateReaderFourierProfile n) 2 (volume : Measure ℝ) := by
  have hsq : Integrable (fun ξ : ℝ => ‖thetaHeatRateReaderFourierProfile n ξ‖ ^ 2) := by
    have hphys := integrable_sq_norm_thetaHeatRateReaderSymbol_boundary hn
    have hcomp := hphys.comp_mul_left' (mul_ne_zero two_ne_zero Real.pi_ne_zero)
    simpa [thetaHeatRateReaderFourierProfile, mul_assoc] using hcomp
  exact (memLp_two_iff_integrable_sq_norm
    (thetaHeatRateReaderFourierProfile_aestronglyMeasurable hn)).2 hsq

/-- The scaled physical boundary reader as a canonical `L²(ℝ)` element. -/
def thetaHeatRateReaderFourierProfileL2 (n : ℕ) (hn : 1 ≤ n) :
    Lp ℂ 2 (volume : Measure ℝ) :=
  (thetaHeatRateReaderFourierProfile_memLp_two hn).toLp
    (thetaHeatRateReaderFourierProfile n)

theorem thetaHeatRateReaderFourierProfileL2_ae (n : ℕ) (hn : 1 ≤ n) :
    (fun ξ : ℝ => thetaHeatRateReaderFourierProfileL2 n hn ξ) =ᵐ[volume]
      thetaHeatRateReaderFourierProfile n :=
  MemLp.coeFn_toLp (thetaHeatRateReaderFourierProfile_memLp_two hn)

theorem integral_sq_norm_thetaHeatRateReaderFourierProfile
    {n : ℕ} (hn : 1 ≤ n) :
    (∫ ξ : ℝ, ‖thetaHeatRateReaderFourierProfile n ξ‖ ^ 2) =
      (2 / Real.pi) * Real.sinh (Real.pi * n) ^ 2 := by
  let g : ℝ → ℝ := fun t => ‖thetaHeatRateReaderSymbol n ((t : ℂ) * I)‖ ^ 2
  have heq : (fun ξ : ℝ => ‖thetaHeatRateReaderFourierProfile n ξ‖ ^ 2) =
      fun ξ => g ((2 * Real.pi) * ξ) := by
    funext ξ
    rfl
  rw [heq]
  have hscale := MeasureTheory.Measure.integral_comp_mul_left g (2 * Real.pi)
  rw [hscale, integral_sq_norm_thetaHeatRateReaderSymbol_boundary hn]
  simp only [smul_eq_mul]
  rw [abs_of_pos (inv_pos.mpr (mul_pos (by norm_num) Real.pi_pos))]
  field_simp
  norm_num

/-- Squared `L²(ℝ,ℂ)` norm as the integral of the squared pointwise norm. -/
theorem norm_l2_sq_complex (K : Lp (α := ℝ) ℂ 2) :
    ‖K‖ ^ 2 = ∫ x : ℝ, ‖K x‖ ^ 2 := by
  rw [Lp.norm_def, toReal_eLpNorm (Lp.aestronglyMeasurable K),
    lpNorm_eq_integral_norm_rpow_toReal (p := (2 : ENNReal)) (by norm_num) (by norm_num)
      (Lp.aestronglyMeasurable K)]
  norm_num [← Real.sqrt_eq_rpow]
  rw [Real.sq_sqrt]
  exact integral_nonneg fun x => sq_nonneg _

theorem norm_thetaHeatRateReaderFourierProfileL2_sq
    {n : ℕ} (hn : 1 ≤ n) :
    ‖thetaHeatRateReaderFourierProfileL2 n hn‖ ^ 2 =
      (2 / Real.pi) * Real.sinh (Real.pi * n) ^ 2 := by
  rw [norm_l2_sq_complex]
  calc
    (∫ ξ : ℝ, ‖thetaHeatRateReaderFourierProfileL2 n hn ξ‖ ^ 2) =
        ∫ ξ : ℝ, ‖thetaHeatRateReaderFourierProfile n ξ‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [thetaHeatRateReaderFourierProfileL2_ae n hn] with ξ hξ
      rw [hξ]
    _ = _ := integral_sq_norm_thetaHeatRateReaderFourierProfile hn

/-- The canonical source-side `L²` reader before the positive-support theorem: inverse unitary
Fourier transform of the correctly scaled physical boundary profile. -/
def thetaHeatRateSourceReaderL2 (n : ℕ) (hn : 1 ≤ n) :
    Lp ℂ 2 (volume : Measure ℝ) :=
  (Lp.fourierTransformₗᵢ ℝ ℂ).symm (thetaHeatRateReaderFourierProfileL2 n hn)

theorem norm_thetaHeatRateSourceReaderL2_sq
    {n : ℕ} (hn : 1 ≤ n) :
    ‖thetaHeatRateSourceReaderL2 n hn‖ ^ 2 =
      (2 / Real.pi) * Real.sinh (Real.pi * n) ^ 2 := by
  rw [thetaHeatRateSourceReaderL2, LinearIsometryEquiv.norm_map,
    norm_thetaHeatRateReaderFourierProfileL2_sq hn]

theorem norm_thetaHeatRateSourceReaderL2
    {n : ℕ} (hn : 1 ≤ n) :
    ‖thetaHeatRateSourceReaderL2 n hn‖ =
      Real.sqrt (2 / Real.pi) * Real.sinh (Real.pi * n) := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _)
    (Real.sinh_nonneg_iff.mpr (by positivity)))]
  rw [norm_thetaHeatRateSourceReaderL2_sq hn, mul_pow,
    Real.sq_sqrt (by positivity)]

end RHTower
