import GaloisForLFunctions.HTGeometry.SchwartzLogMellinFourierEvaluation
import GaloisForLFunctions.HTGeometry.WeightedAtomHilbert
import GaloisForLFunctions.RHTower.ZetaRealBound
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-!
# Continuous arithmetic-progression Weil forms on Schwartz space

Evaluation of a Schwartz Fourier transform on the shifted lattice `alpha + ℕ` defines a
continuous linear map into `ℓ²` for every `alpha > 0`. Its squared norm is the absolutely
convergent, continuous, nonnegative zero-side Weil form of the reflected-Gamma carrier.
-/

open MeasureTheory Filter Set
open scoped ENNReal FourierTransform Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Sample a Schwartz function at Fourier coordinates corresponding to Mellin heights
`alpha + n`. -/
def shiftedFourierSample (alpha : ℝ) (q : SchwartzMap ℝ ℂ) (n : ℕ) : ℂ :=
  q (-(alpha + n) / (2 * Real.pi))

theorem min_alpha_one_mul_nat_add_one_le
    (alpha : ℝ) (n : ℕ) :
    min alpha 1 * ((n : ℝ) + 1) ≤ alpha + n := by
  have hc1 : min alpha 1 ≤ 1 := min_le_right _ _
  have hca : min alpha 1 ≤ alpha := min_le_left _ _
  calc
    min alpha 1 * ((n : ℝ) + 1) = min alpha 1 * n + min alpha 1 := by ring
    _ ≤ 1 * n + alpha := by gcongr
    _ = alpha + n := by ring

/-- First Schwartz seminorm controls each shifted sample with the exact linear weight. -/
theorem min_alpha_one_mul_nat_add_one_mul_norm_shiftedFourierSample_le
    {alpha : ℝ} (halpha : 0 < alpha) (q : SchwartzMap ℝ ℂ) (n : ℕ) :
    (min alpha 1 * ((n : ℝ) + 1)) * ‖shiftedFourierSample alpha q n‖ ≤
      (2 * Real.pi) * SchwartzMap.seminorm ℂ 1 0 q := by
  have hpi : 0 < 2 * Real.pi := by positivity
  let x : ℝ := -(alpha + (n : ℝ)) / (2 * Real.pi)
  have hxnorm : ‖x‖ = (alpha + (n : ℝ)) / (2 * Real.pi) := by
    dsimp [x]
    rw [abs_div, abs_neg, abs_of_pos hpi, abs_of_pos]
    positivity
  have hweight := SchwartzMap.le_seminorm ℂ 1 0 q x
  have hweight' : ‖x‖ * ‖q x‖ ≤ SchwartzMap.seminorm ℂ 1 0 q := by
    simpa only [pow_one, norm_iteratedFDeriv_eq_norm_iteratedDeriv,
      iteratedDeriv_zero] using hweight
  have hlow : min alpha 1 * ((n : ℝ) + 1) ≤ (2 * Real.pi) * ‖x‖ := by
    rw [hxnorm]
    field_simp [Real.pi_ne_zero]
    exact min_alpha_one_mul_nat_add_one_le alpha n
  change (min alpha 1 * ((n : ℝ) + 1)) * ‖q x‖ ≤ _
  calc
    (min alpha 1 * ((n : ℝ) + 1)) * ‖q x‖ ≤
        ((2 * Real.pi) * ‖x‖) * ‖q x‖ := by
      gcongr
    _ = (2 * Real.pi) * (‖x‖ * ‖q x‖) := by ring
    _ ≤ (2 * Real.pi) * SchwartzMap.seminorm ℂ 1 0 q := by gcongr

/-- Reciprocal-linear decay of every shifted sample. -/
theorem norm_shiftedFourierSample_le_div
    {alpha : ℝ} (halpha : 0 < alpha) (q : SchwartzMap ℝ ℂ) (n : ℕ) :
    ‖shiftedFourierSample alpha q n‖ ≤
      (((2 * Real.pi) / min alpha 1) * SchwartzMap.seminorm ℂ 1 0 q) /
        ((n : ℝ) + 1) := by
  have hc : 0 < min alpha 1 := lt_min halpha zero_lt_one
  have hn : 0 < (n : ℝ) + 1 := by positivity
  have h := min_alpha_one_mul_nat_add_one_mul_norm_shiftedFourierSample_le halpha q n
  apply (le_div_iff₀ hn).2
  calc
    ‖shiftedFourierSample alpha q n‖ * ((n : ℝ) + 1) =
        ((min alpha 1 * ((n : ℝ) + 1)) *
          ‖shiftedFourierSample alpha q n‖) / min alpha 1 := by
      field_simp
    _ ≤ ((2 * Real.pi) * SchwartzMap.seminorm ℂ 1 0 q) / min alpha 1 :=
      div_le_div_of_nonneg_right h hc.le
    _ = (2 * Real.pi) / min alpha 1 * SchwartzMap.seminorm ℂ 1 0 q := by ring

/-- The squared shifted samples are summable. -/
theorem summable_norm_sq_shiftedFourierSample
    {alpha : ℝ} (halpha : 0 < alpha) (q : SchwartzMap ℝ ℂ) :
    Summable (fun n : ℕ => ‖shiftedFourierSample alpha q n‖ ^ 2) := by
  have hsquare : Summable (fun n : ℕ => 1 / (((n : ℝ) + 1) ^ 2)) := by
    refine (GaloisForLFunctions.RHTower.summable_one_div_nat_add_one_rpow
      (a := 2) (by norm_num)).congr fun n => ?_
    rw [show ((n : ℝ) + 1) ^ (2 : ℝ) = ((n : ℝ) + 1) ^ (2 : ℕ) by
      rw [← Real.rpow_natCast ((n : ℝ) + 1) 2]
      norm_num]
  let C : ℝ := ((2 * Real.pi) / min alpha 1) * SchwartzMap.seminorm ℂ 1 0 q
  have hbase : Summable (fun n : ℕ => C ^ 2 * (1 / (((n : ℝ) + 1) ^ 2))) :=
    hsquare.mul_left (C ^ 2)
  refine hbase.of_nonneg_of_le (fun n => sq_nonneg _) (fun n => ?_)
  have h := norm_shiftedFourierSample_le_div halpha q n
  calc
    ‖shiftedFourierSample alpha q n‖ ^ 2 ≤ (C / ((n : ℝ) + 1)) ^ 2 := by
      exact pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = C ^ 2 * (1 / (((n : ℝ) + 1) ^ 2)) := by
      field_simp [show ((n : ℝ) + 1) ≠ 0 by positivity]

/-- Critical-line arithmetic-progression samples as an `ℓ²` vector. -/
def shiftedFourierSamplesLp (alpha : ℝ) (halpha : 0 < alpha)
    (q : SchwartzMap ℝ ℂ) : lp (fun _ : ℕ => ℂ) 2 :=
  ⟨shiftedFourierSample alpha q,
    by
      apply memℓp_gen
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
        summable_norm_sq_shiftedFourierSample halpha q⟩

@[simp] theorem shiftedFourierSamplesLp_apply
    (alpha : ℝ) (halpha : 0 < alpha) (q : SchwartzMap ℝ ℂ) (n : ℕ) :
    shiftedFourierSamplesLp alpha halpha q n = shiftedFourierSample alpha q n := rfl

/-- Norm control used to build the continuous `ℓ²` sampler. -/
theorem norm_shiftedFourierSamplesLp_le
    {alpha : ℝ} (halpha : 0 < alpha) (q : SchwartzMap ℝ ℂ) :
    ‖shiftedFourierSamplesLp alpha halpha q‖ ≤
      ((2 * Real.pi) / min alpha 1) *
        Real.sqrt (∑' n : ℕ, 1 / (((n : ℝ) + 1) ^ 2)) *
        SchwartzMap.seminorm ℂ 1 0 q := by
  let c : ℝ := (2 * Real.pi) / min alpha 1
  let p : ℝ := SchwartzMap.seminorm ℂ 1 0 q
  let S : ℝ := ∑' n : ℕ, 1 / (((n : ℝ) + 1) ^ 2)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hp : 0 ≤ p := by dsimp [p]; positivity
  have hsquare : Summable (fun n : ℕ => 1 / (((n : ℝ) + 1) ^ 2)) := by
    refine (GaloisForLFunctions.RHTower.summable_one_div_nat_add_one_rpow
      (a := 2) (by norm_num)).congr fun n => ?_
    rw [show ((n : ℝ) + 1) ^ (2 : ℝ) = ((n : ℝ) + 1) ^ (2 : ℕ) by
      rw [← Real.rpow_natCast ((n : ℝ) + 1) 2]
      norm_num]
  have hS : 0 ≤ S := tsum_nonneg fun _ => by positivity
  have hsample := summable_norm_sq_shiftedFourierSample halpha q
  have hmajor : Summable (fun n : ℕ => (c * p) ^ 2 *
      (1 / (((n : ℝ) + 1) ^ 2))) := hsquare.mul_left ((c * p) ^ 2)
  have hsum : (∑' n : ℕ, ‖shiftedFourierSample alpha q n‖ ^ 2) ≤
      (c * p) ^ 2 * S := by
    rw [← tsum_mul_left]
    exact Summable.tsum_le_tsum (fun n => by
      have h := norm_shiftedFourierSample_le_div halpha q n
      change ‖shiftedFourierSample alpha q n‖ ≤ c * p / ((n : ℝ) + 1) at h
      calc
        ‖shiftedFourierSample alpha q n‖ ^ 2 ≤
            (c * p / ((n : ℝ) + 1)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h 2
        _ = (c * p) ^ 2 * (1 / (((n : ℝ) + 1) ^ 2)) := by
          field_simp [show ((n : ℝ) + 1) ≠ 0 by positivity]) hsample hmajor
  have hnormsq : ‖shiftedFourierSamplesLp alpha halpha q‖ ^ 2 ≤ (c * p) ^ 2 * S := by
    rw [lp_two_norm_sq_eq_tsum]
    simpa only [shiftedFourierSamplesLp_apply] using hsum
  have hsqrt := Real.sqrt_le_sqrt hnormsq
  rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)] at hsqrt
  have hsqrtprod : Real.sqrt ((c * p) ^ 2 * S) = c * Real.sqrt S * p := by
    rw [Real.sqrt_mul (sq_nonneg (c * p)), Real.sqrt_sq_eq_abs,
      abs_of_nonneg (mul_nonneg hc hp)]
    ring
  rw [hsqrtprod] at hsqrt
  simpa [c, p, S] using hsqrt

/-- Continuous `ℓ²` sampler of a Schwartz function on the shifted height lattice. -/
def shiftedFourierSamplesCLM (alpha : ℝ) (halpha : 0 < alpha) :
    SchwartzMap ℝ ℂ →L[ℂ] lp (fun _ : ℕ => ℂ) 2 := by
  refine SchwartzMap.mkCLMtoNormedSpace (shiftedFourierSamplesLp alpha halpha) ?_ ?_ ?_
  · intro f g
    apply lp.ext
    funext n
    simp [shiftedFourierSample]
  · intro a f
    apply lp.ext
    funext n
    simp [shiftedFourierSample]
  · refine ⟨{(1, 0)},
      ((2 * Real.pi) / min alpha 1) *
        Real.sqrt (∑' n : ℕ, 1 / (((n : ℝ) + 1) ^ 2)), by positivity, ?_⟩
    intro q
    calc
      ‖shiftedFourierSamplesLp alpha halpha q‖ ≤
          ((2 * Real.pi) / min alpha 1) *
            Real.sqrt (∑' n : ℕ, 1 / (((n : ℝ) + 1) ^ 2)) *
            SchwartzMap.seminorm ℂ 1 0 q :=
        norm_shiftedFourierSamplesLp_le halpha q
      _ = ((2 * Real.pi) / min alpha 1) *
            Real.sqrt (∑' n : ℕ, 1 / (((n : ℝ) + 1) ^ 2)) *
            (({(1, 0)} : Finset (ℕ × ℕ)).sup
              (schwartzSeminormFamily ℂ ℝ ℂ)) q := by
        rw [Finset.sup_singleton, SchwartzMap.schwartzSeminormFamily_apply]

@[simp] theorem shiftedFourierSamplesCLM_apply_apply
    (alpha : ℝ) (halpha : 0 < alpha) (q : SchwartzMap ℝ ℂ) (n : ℕ) :
    shiftedFourierSamplesCLM alpha halpha q n = shiftedFourierSample alpha q n := rfl

/-- Shifted critical-line Mellin samples of a Schwartz logarithmic profile. -/
def logMellinCriticalSamplesCLM (alpha : ℝ) (halpha : 0 < alpha) :
    SchwartzMap ℝ ℂ →L[ℂ] lp (fun _ : ℕ => ℂ) 2 :=
  shiftedFourierSamplesCLM alpha halpha ∘L SchwartzMap.fourierTransformCLM ℂ

@[simp] theorem logMellinCriticalSamplesCLM_apply_apply
    (alpha : ℝ) (halpha : 0 < alpha) (q : SchwartzMap ℝ ℂ) (n : ℕ) :
    logMellinCriticalSamplesCLM alpha halpha q n =
      𝓕 (q : ℝ → ℂ) (-(alpha + n) / (2 * Real.pi)) := rfl

theorem logMellinCriticalSamplesCLM_logAperture_apply
    (alpha : ℝ) (halpha : 0 < alpha) {A : ℝ}
    (f : LogApertureSchwartz A) (n : ℕ) :
    logMellinCriticalSamplesCLM alpha halpha f.1 n =
      logMellinHeightEvaluation (logApertureSchwartzToL1 f) (alpha + n) := by
  rw [logMellinCriticalSamplesCLM_apply_apply, logMellinHeightEvaluation,
    logMellinL1Fourier, Real.Lp.fourierTransform_apply]
  exact (Real.fourier_congr_ae (SchwartzMap.coeFn_toLp f.1 1 volume)
    (-(alpha + n) / (2 * Real.pi))).symm

/-- Nonnegative zero-side form of the reflected-Gamma critical-line arithmetic progression. -/
def reflectedGammaCriticalLineWeilForm
    (alpha : ℝ) (halpha : 0 < alpha) (q : SchwartzMap ℝ ℂ) : ℝ :=
  2 * ‖logMellinCriticalSamplesCLM alpha halpha q‖ ^ 2

theorem reflectedGammaCriticalLineWeilForm_nonneg
    (alpha : ℝ) (halpha : 0 < alpha) (q : SchwartzMap ℝ ℂ) :
    0 ≤ reflectedGammaCriticalLineWeilForm alpha halpha q := by
  unfold reflectedGammaCriticalLineWeilForm
  positivity

theorem continuous_reflectedGammaCriticalLineWeilForm
    (alpha : ℝ) (halpha : 0 < alpha) :
    Continuous (reflectedGammaCriticalLineWeilForm alpha halpha) := by
  unfold reflectedGammaCriticalLineWeilForm
  fun_prop

theorem reflectedGammaCriticalLineWeilForm_eq_tsum
    (alpha : ℝ) (halpha : 0 < alpha) (q : SchwartzMap ℝ ℂ) :
    reflectedGammaCriticalLineWeilForm alpha halpha q =
      2 * ∑' n : ℕ, ‖𝓕 (q : ℝ → ℂ)
        (-(alpha + n) / (2 * Real.pi))‖ ^ 2 := by
  rw [reflectedGammaCriticalLineWeilForm, lp_two_norm_sq_eq_tsum]
  rfl

/-- Reflected-Gamma zero-side form pulled back to a fixed-aperture test space. -/
def logApertureReflectedGammaWeilForm
    (alpha : ℝ) (halpha : 0 < alpha) {A : ℝ}
    (f : LogApertureSchwartz A) : ℝ :=
  reflectedGammaCriticalLineWeilForm alpha halpha f.1

theorem continuous_logApertureReflectedGammaWeilForm
    (alpha : ℝ) (halpha : 0 < alpha) (A : ℝ) :
    Continuous (logApertureReflectedGammaWeilForm alpha halpha
      (A := A)) := by
  exact (continuous_reflectedGammaCriticalLineWeilForm alpha halpha).comp
    continuous_subtype_val

theorem logApertureReflectedGammaWeilForm_nonneg
    (alpha : ℝ) (halpha : 0 < alpha) {A : ℝ}
    (f : LogApertureSchwartz A) :
    0 ≤ logApertureReflectedGammaWeilForm alpha halpha f :=
  reflectedGammaCriticalLineWeilForm_nonneg alpha halpha f.1

theorem logApertureReflectedGammaWeilForm_eq_tsum
    (alpha : ℝ) (halpha : 0 < alpha) {A : ℝ}
    (f : LogApertureSchwartz A) :
    logApertureReflectedGammaWeilForm alpha halpha f =
      2 * ∑' n : ℕ,
        ‖logMellinHeightEvaluation (logApertureSchwartzToL1 f) (alpha + n)‖ ^ 2 := by
  rw [logApertureReflectedGammaWeilForm,
    reflectedGammaCriticalLineWeilForm, lp_two_norm_sq_eq_tsum]
  congr 1
  apply tsum_congr
  intro n
  rw [logMellinCriticalSamplesCLM_logAperture_apply]

end

end GaloisForLFunctions.HTGeometry
