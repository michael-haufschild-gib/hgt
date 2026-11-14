import GaloisForLFunctions.MetaplecticMobiusDescent.Poisson.QuarticAngularCancellation
import GaloisForLFunctions.MetaplecticMobiusDescent.Poisson.GaussianFourierDerivativeScale
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Smooth annular angular kernels and uniform dual-lattice bounds

A fixed radial cutoff equals one on norm squares in `[1/2, 2]` and vanishes
near the origin. Multiplying the normalized angular factor by this cutoff
removes its singularity and gives a smooth compactly supported multiplier.
The resulting Schwartz kernels have vanishing zero Fourier mode in each
nontrivial quarter-turn sector. Their phase-modulated dual lattice sums
therefore satisfy an absolute bound independent of the sampling scale.
-/

noncomputable section
open Complex MeasureTheory Filter
open scoped Classical Topology ContDiff SchwartzMap FourierTransform

namespace GaloisForLFunctions.MetaplecticMobiusDescent.QuarticPoisson
open CubicEisenstein.SchwartzPlanePoisson

/-- A radial cutoff preserving the norm-square interval `[1/2, 2]`. -/
def annularBump : ContDiffBump (5 / 4 : ℝ) where
  rIn := 3 / 4
  rOut := 1
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

private theorem annularBump_zero_left {t : ℝ} (ht : t ≤ 1 / 4) : annularBump t = 0 := by
  apply annularBump.zero_of_le_dist
  change 1 ≤ dist t (5 / 4 : ℝ)
  rw [Real.dist_eq, abs_of_nonpos (by linarith)]
  linarith only [ht]

private theorem annularBump_zero_right {t : ℝ} (ht : 9 / 4 ≤ t) : annularBump t = 0 := by
  apply annularBump.zero_of_le_dist
  change 1 ≤ dist t (5 / 4 : ℝ)
  rw [Real.dist_eq, abs_of_nonneg (by linarith)]
  linarith only [ht]

/-- The cutoff is exactly one throughout the original annulus. -/
theorem annularBump_one (t : Set.Icc (1 / 2 : ℝ) 2) : annularBump t.val = 1 := by
  apply annularBump.one_of_mem_closedBall
  change dist t.val (5 / 4 : ℝ) ≤ 3 / 4
  rw [Real.dist_eq, abs_le]
  constructor <;> linarith only [t.property.1, t.property.2]

/-- A normalized angular multiplier with its singularity cut out. -/
def annularAngularMask (k : ℕ) (z : ℂ) : ℂ :=
  (z / (‖z‖ : ℂ)) ^ k * (annularBump (‖z‖ ^ 2) : ℂ)

private theorem annularAngularMask_zero_near (k : ℕ) {z : ℂ} (hz : ‖z‖ < 1 / 2) :
    annularAngularMask k z = 0 := by
  have hs := pow_le_pow_left₀ (norm_nonneg z) hz.le 2
  have hb := annularBump_zero_left (t := ‖z‖ ^ 2) (by norm_num at hs ⊢; exact hs)
  simp only [annularAngularMask, hb, Complex.ofReal_zero, mul_zero]

/-- The cutoff removes the only possible singularity of the angular multiplier. -/
theorem contDiff_annularAngularMask (k : ℕ) : ContDiff ℝ ∞ (annularAngularMask k) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z = 0
  · subst z
    apply (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : ℂ => (0 : ℂ)) 0).congr_of_eventuallyEq
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1 / 2)] with w hw
    apply annularAngularMask_zero_near
    simpa only [Metric.mem_ball, dist_zero_right] using hw
  · have hn : ContDiffAt ℝ ∞ (fun w : ℂ => ‖w‖) z := contDiffAt_norm ℝ hz
    have hu : ContDiffAt ℝ ∞ (fun w : ℂ => w / (‖w‖ : ℂ)) z := by
      have hr : ContDiffAt ℝ ∞ (fun w : ℂ => (1 : ℝ) / ‖w‖) z :=
        contDiffAt_const.div hn (norm_ne_zero_iff.mpr hz)
      have h := hr.smul (contDiffAt_id : ContDiffAt ℝ ∞ (fun w : ℂ => w) z)
      change ContDiffAt ℝ ∞ (fun w : ℂ => ((1 : ℝ) / ‖w‖) • w) z at h
      simpa only [one_div, Algebra.smul_def, Complex.ofReal_inv, div_eq_mul_inv, mul_comm] using h
    have hb : ContDiff ℝ ∞ (fun w : ℂ => (annularBump (‖w‖ ^ 2) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (annularBump.contDiff.comp (contDiff_norm_sq ℝ))
    exact (hu.pow k).mul hb.contDiffAt

/-- The multiplier is supported inside a fixed compact disk. -/
theorem hasCompactSupport_annularAngularMask (k : ℕ) : HasCompactSupport (annularAngularMask k) := by
  apply HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) 2)
  intro z hz
  have hn : 2 < ‖z‖ := by
    simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hz
  have hs := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hn.le 2
  have hb := annularBump_zero_right (t := ‖z‖ ^ 2) (by norm_num at hs; linarith only [hs])
  simp only [annularAngularMask, hb, Complex.ofReal_zero, mul_zero]

/-- The smooth compact angular multiplier as a Schwartz function. -/
def annularMaskSchwartz (k : ℕ) : 𝓢(ℂ, ℂ) :=
  (hasCompactSupport_annularAngularMask k).toSchwartzMap (contDiff_annularAngularMask k)

/-- Annular angular localization is a continuous linear operator on radial tests. -/
def annularAngularCLM (k : ℕ) : 𝓢(ℝ, ℂ) →L[ℝ] 𝓢(ℂ, ℂ) :=
  ((SchwartzMap.smulLeftCLM ℂ (annularMaskSchwartz k)).restrictScalars ℝ).comp radialTestCLM

/-- The constructed Schwartz function has the required normalized angular formula. -/
theorem annularAngularCLM_apply (k : ℕ) (W : 𝓢(ℝ, ℂ)) (z : ℂ) :
    annularAngularCLM k W z =
      angularRadial k (fun t => (annularBump t : ℂ) * W t) z := by
  change SchwartzMap.smulLeftCLM ℂ (annularMaskSchwartz k) (radialTest W) z = _
  rw [SchwartzMap.smulLeftCLM_apply_apply (annularMaskSchwartz k).hasTemperateGrowth]
  change annularAngularMask k z * W (‖z‖ ^ 2) = _
  simp only [annularAngularMask, angularRadial, mul_assoc]

/-- The Fourier transform of annular angular localization is itself a Schwartz operator. -/
def annularFourierCLM (k : ℕ) : 𝓢(ℝ, ℂ) →L[ℝ] 𝓢(ℂ, ℂ) :=
  (FourierTransform.fourierCLM ℝ 𝓢(ℂ, ℂ)).comp (annularAngularCLM k)

private theorem annularFourier_zero_of_paper (k : ℕ) (W : 𝓢(ℝ, ℂ))
    (h : paperFourier (angularRadial k (fun t => (annularBump t : ℂ) * W t)) 0 = 0) :
    annularFourierCLM k W 0 = 0 := by
  rw [paperFourier_eq_standard] at h
  simp only [paperFrequency, zero_div, map_zero, mul_zero] at h
  have hz := (smul_eq_zero.mp h).resolve_left (by positivity : (2 / Real.sqrt 3 : ℝ) ≠ 0)
  change (𝓕 (annularAngularCLM k W)) 0 = 0
  rw [SchwartzMap.fourier_coe,
    show (annularAngularCLM k W : ℂ → ℂ) =
      angularRadial k (fun t => (annularBump t : ℂ) * W t) from
        funext (annularAngularCLM_apply k W)]
  exact hz

/-- Every nontrivial quarter-turn sector has zero Fourier mass at the origin. -/
theorem annularFourier_zero (n : ℕ) (j : Fin 3) (W : 𝓢(ℝ, ℂ)) :
    annularFourierCLM (4 * n + (j.val + 1)) W 0 = 0 := by
  apply annularFourier_zero_of_paper
  fin_cases j
  · exact angular_zero_mode_one n _
  · exact angular_zero_mode_two n _
  · exact angular_zero_mode_three n _

/-- The entire dual lattice has uniformly bounded absolute mass in each nontrivial sector. -/
theorem scaled_annularFourier_mass_le (n : ℕ) (j : Fin 3) (W : 𝓢(ℝ, ℂ))
    (s : PositiveScale) (a : ℂ) :
    s.val ^ 2 * (∑' z : GaussianInt,
      ‖gaussianPhase a z * annularFourierCLM (4 * n + (j.val + 1)) W
        ((s.val : ℂ) * (z : ℂ))‖) ≤
      12 * fourthDecayConstant (annularFourierCLM (4 * n + (j.val + 1)) W) := by
  have h := scaled_schwartz_mass_sub_zero_le
    (annularFourierCLM (4 * n + (j.val + 1)) W) s a
  simpa only [annularFourier_zero, norm_zero, sub_zero] using h

/-- The cubic angular dual sum satisfies the same bound at every scale and phase. -/
theorem scaled_cubic_annularFourier_sum_le (W : 𝓢(ℝ, ℂ)) (s : PositiveScale) (a : ℂ) :
    s.val ^ 2 * ‖schwartzLatticeSum (annularFourierCLM 3 W) s a‖ ≤
      12 * fourthDecayConstant (annularFourierCLM 3 W) := by
  have hz := annularFourier_zero 0 (2 : Fin 3) W
  have h := scaled_schwartz_sum_sub_zero_le (annularFourierCLM 3 W) s a
  change annularFourierCLM 3 W 0 = 0 at hz
  simpa only [hz, sub_zero] using h

/-- Physical derivatives through order four control the complete dual lattice in every
nontrivial quarter-turn sector; no Fourier decay estimate is assumed. -/
theorem scaled_annularFourier_mass_le_derivatives (n : ℕ) (j : Fin 3) (W : 𝓢(ℝ, ℂ))
    (s : PositiveScale) (a : ℂ) :
    s.val ^ 2 * (∑' z : GaussianInt,
      ‖gaussianPhase a z * annularFourierCLM (4 * n + (j.val + 1)) W
        ((s.val : ℂ) * (z : ℂ))‖) ≤
      1632 * derivativeMass 4 (annularAngularCLM (4 * n + (j.val + 1)) W) := by
  have h := scaled_fourier_mass_sub_zero_le_derivativeMass
    (annularAngularCLM (4 * n + (j.val + 1)) W) s a
  change s.val ^ 2 * ((∑' z : GaussianInt,
    ‖gaussianPhase a z * annularFourierCLM (4 * n + (j.val + 1)) W
      ((s.val : ℂ) * (z : ℂ))‖) - ‖annularFourierCLM (4 * n + (j.val + 1)) W 0‖) ≤ _ at h
  simpa only [annularFourier_zero, norm_zero, sub_zero] using h

end GaloisForLFunctions.MetaplecticMobiusDescent.QuarticPoisson
