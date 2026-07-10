import GaloisForLFunctions.RHTower.XiThetaSourceSeam
import GaloisForLFunctions.RHTower.SecondMoment

/-!
# The archimedean theta seam survives prime-power sampling

The finite-prime channel samples a test function at prime-power logarithms.  The first two such
locations leave the explicit open gap `(log 2, log 3)`.  A continuous tent carried by this gap has
every prime-power sample equal to zero, but its pairing with the actual positive-half completed-zeta
theta source is strictly positive.

Consequently the archimedean theta-seam functional does not factor through prime-power samples,
even if the proposed reconstruction from the samples is allowed to be arbitrary and nonlinear.
This replaces the support narrative in `SeamArchimedeanNoGo` by an exact positive quotient witness.
-/

open Complex Real MeasureTheory Set Filter Topology HurwitzZeta
open scoped ENNReal Topology

noncomputable section

namespace RHTower

/-- Evaluation of a real test function on the prime-power logarithmic sample set. -/
def primePowerSamples (φ : ℝ → ℝ) (n : ℕ) : ℝ :=
  if IsPrimePow n then φ (Real.log n) else 0

/-- The continuous tent carried by the first prime-power-free logarithmic gap. -/
def primePowerGapTent (u : ℝ) : ℝ :=
  max 0 (min (u - Real.log 2) (Real.log 3 - u))

/-- The real positive-half density underlying `xiThetaLogSource`. -/
def archimedeanThetaDensity (u : ℝ) : ℝ :=
  Real.exp (u / 4) * (evenKernel 0 (Real.exp u) - 1)

/-- Pair a real test function with the actual positive-half completed-zeta theta source
on the explicit gap between the first two prime-power logarithms. -/
def archimedeanThetaSeamFunctional (φ : ℝ → ℝ) : ℝ :=
  ∫ u in Real.log 2..Real.log 3, φ u * archimedeanThetaDensity u

theorem log_two_lt_log_three : Real.log 2 < Real.log 3 := by
  exact Real.strictMonoOn_log (by norm_num) (by norm_num) (by norm_num)

theorem primePowerGapTent_continuous : Continuous primePowerGapTent := by
  unfold primePowerGapTent
  fun_prop

theorem primePowerGapTent_nonneg (u : ℝ) : 0 ≤ primePowerGapTent u := by
  exact le_max_left _ _

theorem primePowerGapTent_eq_zero_of_not_mem {u : ℝ}
    (hu : u ∉ Ioo (Real.log 2) (Real.log 3)) :
    primePowerGapTent u = 0 := by
  rw [Set.mem_Ioo, not_and_or] at hu
  rcases hu with hu | hu
  · rw [primePowerGapTent, max_eq_left]
    exact le_trans (min_le_left _ _) (sub_nonpos.mpr (le_of_not_gt hu))
  · rw [primePowerGapTent, max_eq_left]
    exact le_trans (min_le_right _ _) (sub_nonpos.mpr (le_of_not_gt hu))

theorem primePowerLog_not_mem_first_gap {n : ℕ} (hpp : IsPrimePow n) :
    Real.log n ∉ Ioo (Real.log 2) (Real.log 3) := by
  intro hnlog
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_trans Nat.zero_lt_one hpp.one_lt)
  have h2n : (2 : ℝ) < n := by
    calc
      (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
      _ < Real.exp (Real.log n) := Real.exp_lt_exp.mpr hnlog.1
      _ = n := Real.exp_log hnpos
  have hn3 : (n : ℝ) < 3 := by
    calc
      (n : ℝ) = Real.exp (Real.log n) := (Real.exp_log hnpos).symm
      _ < Real.exp (Real.log 3) := Real.exp_lt_exp.mpr hnlog.2
      _ = 3 := Real.exp_log (by norm_num)
  have h2n' : 2 < n := by exact_mod_cast h2n
  have hn3' : n < 3 := by exact_mod_cast hn3
  omega

theorem primePowerGapTent_at_primePowerLog {n : ℕ} (hpp : IsPrimePow n) :
    primePowerGapTent (Real.log n) = 0 :=
  primePowerGapTent_eq_zero_of_not_mem (primePowerLog_not_mem_first_gap hpp)

theorem primePowerSamples_gapTent :
    primePowerSamples primePowerGapTent = 0 := by
  funext n
  by_cases hpp : IsPrimePow n
  · simp [primePowerSamples, hpp, primePowerGapTent_at_primePowerLog hpp]
  · simp [primePowerSamples, hpp]

theorem archimedeanThetaDensity_eq_re_positiveFormula (u : ℝ) :
    archimedeanThetaDensity u = (xiThetaPositiveFormula u).re := by
  rw [archimedeanThetaDensity, xiThetaPositiveFormula]
  rw [← Complex.ofReal_mul]
  exact (Complex.ofReal_re _).symm

/-- On the positive half-line, `archimedeanThetaDensity` is exactly the real part of the
completed-zeta logarithmic theta source, not an auxiliary positive weight. -/
theorem archimedeanThetaDensity_eq_re_logSource {u : ℝ} (hu : 0 < u) :
    archimedeanThetaDensity u = (xiThetaLogSource u).re := by
  rw [xiThetaLogSource_eq_positiveFormula hu]
  exact archimedeanThetaDensity_eq_re_positiveFormula u

theorem archimedeanThetaDensity_continuous : Continuous archimedeanThetaDensity := by
  have h : Continuous (fun u : ℝ => (xiThetaPositiveFormula u).re) :=
    Complex.continuous_re.comp continuous_xiThetaPositiveFormula
  exact h.congr (fun u => (archimedeanThetaDensity_eq_re_positiveFormula u).symm)

theorem archimedeanThetaDensity_pos (u : ℝ) : 0 < archimedeanThetaDensity u := by
  exact mul_pos (Real.exp_pos _) (evenKernel_zero_sub_one_pos (Real.exp_pos u))

theorem primePowerGapTent_midpoint_pos :
    0 < primePowerGapTent ((Real.log 2 + Real.log 3) / 2) := by
  have h23 := log_two_lt_log_three
  have hleft : 0 < (Real.log 2 + Real.log 3) / 2 - Real.log 2 := by linarith
  have hright : 0 < Real.log 3 - (Real.log 2 + Real.log 3) / 2 := by linarith
  rw [primePowerGapTent, max_eq_right]
  · exact lt_min hleft hright
  · exact (lt_min hleft hright).le

/-- The explicit sampling-kernel witness is detected positively by the actual archimedean
theta seam. -/
theorem archimedeanThetaSeamFunctional_gapTent_pos :
    0 < archimedeanThetaSeamFunctional primePowerGapTent := by
  unfold archimedeanThetaSeamFunctional
  refine intervalIntegral_pos_of_continuous_nonneg_of_exists_pos
    (primePowerGapTent_continuous.mul archimedeanThetaDensity_continuous) ?_ ?_
  · intro u _
    exact mul_nonneg (primePowerGapTent_nonneg u) (archimedeanThetaDensity_pos u).le
  · refine ⟨(Real.log 2 + Real.log 3) / 2, ?_, ?_⟩
    · constructor <;> linarith [log_two_lt_log_three]
    · exact mul_pos primePowerGapTent_midpoint_pos (archimedeanThetaDensity_pos _)

/-- The actual positive-half archimedean theta seam does not factor through prime-power
logarithmic samples on continuous real test functions, even through an arbitrary nonlinear
post-processing of those samples. -/
theorem archimedeanThetaSeamFunctional_not_factors_through_primePowerSamples :
    ¬ ∃ F : (ℕ → ℝ) → ℝ, ∀ φ : ℝ → ℝ, Continuous φ →
      archimedeanThetaSeamFunctional φ = F (primePowerSamples φ) := by
  rintro ⟨F, hF⟩
  have hs : primePowerSamples primePowerGapTent = primePowerSamples (fun _ => 0) := by
    rw [primePowerSamples_gapTent]
    funext n
    simp [primePowerSamples]
  have hzero : archimedeanThetaSeamFunctional (fun _ => 0) = 0 := by
    simp [archimedeanThetaSeamFunctional]
  have htent : archimedeanThetaSeamFunctional primePowerGapTent = 0 := by
    calc
      archimedeanThetaSeamFunctional primePowerGapTent =
          F (primePowerSamples primePowerGapTent) := hF _ primePowerGapTent_continuous
      _ = F (primePowerSamples (fun _ => 0)) := congrArg F hs
      _ = archimedeanThetaSeamFunctional (fun _ => 0) := (hF _ continuous_const).symm
      _ = 0 := hzero
  exact (ne_of_gt archimedeanThetaSeamFunctional_gapTent_pos) htent

end RHTower
