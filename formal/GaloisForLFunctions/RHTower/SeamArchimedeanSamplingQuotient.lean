import GaloisForLFunctions.RHTower.XiThetaSourceSeam
import GaloisForLFunctions.RHTower.SecondMoment

/-!
# Positive weighted gap functionals survive masked sampling

For arbitrary sample sites, any open interval avoiding every active site carries a canonical
continuous tent in the sampling kernel.  Every continuous density that is nonnegative on the
interval and positive somewhere inside detects that tent strictly positively.  Consequently the
weighted interval functional cannot factor through the masked samples, even through arbitrary
nonlinear post-processing.

The completed-zeta theta seam is the source-specific specialization.  The original witness on
`(log 2, log 3)` is retained as a compatibility theorem, while consecutive integer-log gaps show
that even sampling at every positive integer logarithm cannot recover the local theta functional.
-/

open Complex Real MeasureTheory Set Filter Topology HurwitzZeta
open scoped ENNReal Topology

noncomputable section

namespace RHTower

/-- Sample a function at the active sites and write zero at inactive indices. -/
def maskedSamples {ι : Type*} (active : ι → Prop) [DecidablePred active]
    (site : ι → ℝ) (φ : ℝ → ℝ) (i : ι) : ℝ :=
  if active i then φ (site i) else 0

/-- The continuous tent carried by an arbitrary real interval. -/
def gapTent (a b u : ℝ) : ℝ :=
  max 0 (min (u - a) (b - u))

/-- Pair a real test function with a real density on an arbitrary interval. -/
def weightedGapFunctional (a b : ℝ) (w φ : ℝ → ℝ) : ℝ :=
  ∫ u in a..b, φ u * w u

theorem gapTent_continuous (a b : ℝ) : Continuous (gapTent a b) := by
  unfold gapTent
  fun_prop

theorem gapTent_nonneg (a b u : ℝ) : 0 ≤ gapTent a b u := by
  exact le_max_left _ _

theorem gapTent_eq_zero_of_not_mem {a b u : ℝ} (hu : u ∉ Ioo a b) :
    gapTent a b u = 0 := by
  rw [Set.mem_Ioo, not_and_or] at hu
  rcases hu with hu | hu
  · rw [gapTent, max_eq_left]
    exact le_trans (min_le_left _ _) (sub_nonpos.mpr (le_of_not_gt hu))
  · rw [gapTent, max_eq_left]
    exact le_trans (min_le_right _ _) (sub_nonpos.mpr (le_of_not_gt hu))

theorem gapTent_pos_of_mem {a b u : ℝ} (hu : u ∈ Ioo a b) :
    0 < gapTent a b u := by
  have hleft : 0 < u - a := sub_pos.mpr hu.1
  have hright : 0 < b - u := sub_pos.mpr hu.2
  rw [gapTent, max_eq_right]
  · exact lt_min hleft hright
  · exact (lt_min hleft hright).le

theorem maskedSamples_gapTent {ι : Type*} {active : ι → Prop} [DecidablePred active]
    {site : ι → ℝ} {a b : ℝ}
    (hgap : ∀ i, active i → site i ∉ Ioo a b) :
    maskedSamples active site (gapTent a b) = 0 := by
  funext i
  by_cases hi : active i
  · simp [maskedSamples, hi, gapTent_eq_zero_of_not_mem (hgap i hi)]
  · simp [maskedSamples, hi]

/-- A positive continuous density detects the canonical tent in every nonempty sampling gap. -/
theorem weightedGapFunctional_gapTent_pos {a b : ℝ} {w : ℝ → ℝ}
    (hw : Continuous w) (hw_nonneg : ∀ u ∈ Icc a b, 0 ≤ w u)
    (hw_pos : ∃ u ∈ Ioo a b, 0 < w u) :
    0 < weightedGapFunctional a b w (gapTent a b) := by
  unfold weightedGapFunctional
  refine intervalIntegral_pos_of_continuous_nonneg_of_exists_pos
    ((gapTent_continuous a b).mul hw) ?_ ?_
  · intro u hu
    exact mul_nonneg (gapTent_nonneg a b u) (hw_nonneg u hu)
  · obtain ⟨u, hu, hwu⟩ := hw_pos
    exact ⟨u, hu, mul_pos (gapTent_pos_of_mem hu) hwu⟩

/-- No reconstruction, even nonlinear, from samples outside a gap can recover a positive
weighted interval functional on all continuous real test functions. -/
theorem weightedGapFunctional_not_factors_through_maskedSamples
    {ι : Type*} {active : ι → Prop} [DecidablePred active]
    {site : ι → ℝ} {a b : ℝ} {w : ℝ → ℝ}
    (hgap : ∀ i, active i → site i ∉ Ioo a b)
    (hw : Continuous w) (hw_nonneg : ∀ u ∈ Icc a b, 0 ≤ w u)
    (hw_pos : ∃ u ∈ Ioo a b, 0 < w u) :
    ¬ ∃ F : (ι → ℝ) → ℝ, ∀ φ : ℝ → ℝ, Continuous φ →
      weightedGapFunctional a b w φ = F (maskedSamples active site φ) := by
  rintro ⟨F, hF⟩
  have hs : maskedSamples active site (gapTent a b) =
      maskedSamples active site (fun _ => 0) := by
    rw [maskedSamples_gapTent hgap]
    funext i
    simp [maskedSamples]
  have hzero : weightedGapFunctional a b w (fun _ => 0) = 0 := by
    simp [weightedGapFunctional]
  have htent : weightedGapFunctional a b w (gapTent a b) = 0 := by
    calc
      weightedGapFunctional a b w (gapTent a b) =
          F (maskedSamples active site (gapTent a b)) := hF _ (gapTent_continuous a b)
      _ = F (maskedSamples active site (fun _ => 0)) := congrArg F hs
      _ = weightedGapFunctional a b w (fun _ => 0) := (hF _ continuous_const).symm
      _ = 0 := hzero
  exact (ne_of_gt (weightedGapFunctional_gapTent_pos hw hw_nonneg hw_pos)) htent

/-! ## The completed-zeta theta specialization -/

/-- Evaluation of a real test function on the prime-power logarithmic sample set. -/
def primePowerSamples (φ : ℝ → ℝ) : ℕ → ℝ :=
  maskedSamples (fun n : ℕ => IsPrimePow n) (fun n => Real.log n) φ

/-- Sampling at every positive integer logarithm, a strictly finer channel than prime-power
sampling. -/
def positiveIntegerLogSamples (φ : ℝ → ℝ) : ℕ → ℝ :=
  maskedSamples (fun _ : ℕ => True) (fun n => Real.log (n + 1)) φ

/-- The continuous tent carried by the first prime-power-free logarithmic gap. -/
def primePowerGapTent : ℝ → ℝ :=
  gapTent (Real.log 2) (Real.log 3)

/-- The real positive-half density underlying `xiThetaLogSource`. -/
def archimedeanThetaDensity (u : ℝ) : ℝ :=
  Real.exp (u / 4) * (evenKernel 0 (Real.exp u) - 1)

/-- Pair a real test function with the actual positive-half completed-zeta theta density on an
arbitrary interval. -/
def archimedeanThetaSeamFunctionalOn (a b : ℝ) (φ : ℝ → ℝ) : ℝ :=
  weightedGapFunctional a b archimedeanThetaDensity φ

/-- Compatibility specialization to the first prime-power-free logarithmic gap. -/
def archimedeanThetaSeamFunctional (φ : ℝ → ℝ) : ℝ :=
  archimedeanThetaSeamFunctionalOn (Real.log 2) (Real.log 3) φ

theorem log_two_lt_log_three : Real.log 2 < Real.log 3 := by
  exact Real.strictMonoOn_log (by norm_num) (by norm_num) (by norm_num)

theorem primePowerGapTent_continuous : Continuous primePowerGapTent := by
  exact gapTent_continuous (Real.log 2) (Real.log 3)

theorem primePowerGapTent_nonneg (u : ℝ) : 0 ≤ primePowerGapTent u := by
  exact gapTent_nonneg (Real.log 2) (Real.log 3) u

theorem primePowerGapTent_eq_zero_of_not_mem {u : ℝ}
    (hu : u ∉ Ioo (Real.log 2) (Real.log 3)) :
    primePowerGapTent u = 0 := by
  exact gapTent_eq_zero_of_not_mem hu

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
  simpa only [primePowerSamples, primePowerGapTent] using
    (maskedSamples_gapTent
      (active := fun n : ℕ => IsPrimePow n) (site := fun n => Real.log n)
      (a := Real.log 2) (b := Real.log 3)
      (fun n hpp => primePowerLog_not_mem_first_gap hpp))

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

/-- The actual theta density detects the canonical tent on every nonempty real interval. -/
theorem archimedeanThetaSeamFunctionalOn_gapTent_pos {a b : ℝ} (hab : a < b) :
    0 < archimedeanThetaSeamFunctionalOn a b (gapTent a b) := by
  apply weightedGapFunctional_gapTent_pos archimedeanThetaDensity_continuous
  · intro u _
    exact (archimedeanThetaDensity_pos u).le
  · refine ⟨(a + b) / 2, ?_, archimedeanThetaDensity_pos _⟩
    constructor <;> linarith

/-- On every sampling gap, the actual theta functional escapes arbitrary nonlinear
reconstruction from the active sample values. -/
theorem archimedeanThetaSeamFunctionalOn_not_factors_through_maskedSamples
    {ι : Type*} {active : ι → Prop} [DecidablePred active]
    {site : ι → ℝ} {a b : ℝ} (hab : a < b)
    (hgap : ∀ i, active i → site i ∉ Ioo a b) :
    ¬ ∃ F : (ι → ℝ) → ℝ, ∀ φ : ℝ → ℝ, Continuous φ →
      archimedeanThetaSeamFunctionalOn a b φ = F (maskedSamples active site φ) := by
  apply weightedGapFunctional_not_factors_through_maskedSamples hgap
    archimedeanThetaDensity_continuous
  · intro u _
    exact (archimedeanThetaDensity_pos u).le
  · refine ⟨(a + b) / 2, ?_, archimedeanThetaDensity_pos _⟩
    constructor <;> linarith

theorem consecutivePositiveIntegerLog_lt (N : ℕ) :
    Real.log (N + 1) < Real.log (N + 2) := by
  apply Real.strictMonoOn_log
  · exact (show (0 : ℝ) < N + 1 by positivity)
  · exact (show (0 : ℝ) < N + 2 by positivity)
  · exact_mod_cast (show N + 1 < N + 2 by omega)

/-- No positive integer logarithm lies strictly between two consecutive positive integer
logarithms. -/
theorem positiveIntegerLog_not_mem_consecutive_gap (N n : ℕ) :
    Real.log (n + 1) ∉ Ioo (Real.log (N + 1)) (Real.log (N + 2)) := by
  intro hnlog
  have hnpos : (0 : ℝ) < n + 1 := by positivity
  have hN1pos : (0 : ℝ) < N + 1 := by positivity
  have hN2pos : (0 : ℝ) < N + 2 := by positivity
  have hleft : (N + 1 : ℕ) < n + 1 := by
    exact_mod_cast (show (N + 1 : ℝ) < n + 1 by
      calc
        (N + 1 : ℝ) = Real.exp (Real.log (N + 1)) := (Real.exp_log hN1pos).symm
        _ < Real.exp (Real.log (n + 1)) := Real.exp_lt_exp.mpr hnlog.1
        _ = n + 1 := Real.exp_log hnpos)
  have hright : n + 1 < (N + 2 : ℕ) := by
    exact_mod_cast (show (n + 1 : ℝ) < N + 2 by
      calc
        (n + 1 : ℝ) = Real.exp (Real.log (n + 1)) := (Real.exp_log hnpos).symm
        _ < Real.exp (Real.log (N + 2)) := Real.exp_lt_exp.mpr hnlog.2
        _ = N + 2 := Real.exp_log hN2pos)
  omega

/-- The theta seam escapes even the strictly finer channel sampling at every positive integer
logarithm, on every consecutive logarithmic gap. -/
theorem archimedeanThetaSeamFunctionalOn_not_factors_through_positiveIntegerLogSamples
    (N : ℕ) :
    ¬ ∃ F : (ℕ → ℝ) → ℝ, ∀ φ : ℝ → ℝ, Continuous φ →
      archimedeanThetaSeamFunctionalOn (Real.log (N + 1)) (Real.log (N + 2)) φ =
        F (positiveIntegerLogSamples φ) := by
  exact archimedeanThetaSeamFunctionalOn_not_factors_through_maskedSamples
    (consecutivePositiveIntegerLog_lt N)
    (fun n _ => positiveIntegerLog_not_mem_consecutive_gap N n)

theorem primePowerGapTent_midpoint_pos :
    0 < primePowerGapTent ((Real.log 2 + Real.log 3) / 2) := by
  apply gapTent_pos_of_mem
  constructor <;> linarith [log_two_lt_log_three]

/-- The explicit sampling-kernel witness is detected positively by the actual archimedean
theta seam. -/
theorem archimedeanThetaSeamFunctional_gapTent_pos :
    0 < archimedeanThetaSeamFunctional primePowerGapTent := by
  exact archimedeanThetaSeamFunctionalOn_gapTent_pos log_two_lt_log_three

/-- The actual positive-half archimedean theta seam does not factor through prime-power
logarithmic samples on continuous real test functions, even through an arbitrary nonlinear
post-processing of those samples. -/
theorem archimedeanThetaSeamFunctional_not_factors_through_primePowerSamples :
    ¬ ∃ F : (ℕ → ℝ) → ℝ, ∀ φ : ℝ → ℝ, Continuous φ →
      archimedeanThetaSeamFunctional φ = F (primePowerSamples φ) := by
  exact archimedeanThetaSeamFunctionalOn_not_factors_through_maskedSamples
    log_two_lt_log_three (fun n hpp => primePowerLog_not_mem_first_gap hpp)

end RHTower
