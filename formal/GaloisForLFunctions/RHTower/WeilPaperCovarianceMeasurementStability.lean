import GaloisForLFunctions.RHTower.WeilPaperCovarianceToleranceContinuity

/-!
# Stability under changes in finite covariance measurements

The original compensated energy budget bounds the oscillation of the gamma
objective. At positive tolerance this gives a uniform sensitivity bound,
independent of the number of measurements, and joint continuity under changes
to measured law, tolerance, and bounded spectral penalty.
-/

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal BoundedContinuousFunction
noncomputable section
namespace RHTower.WeilWorkPBAP
open WeilOneSided
variable {ι : Type*}

/-- The paid budget gives a uniform oscillation allowance for gamma energy
with a bounded spectral penalty. -/
def paperCovarianceEnergyOscillation (c : ComplexNullMixture) (G : ℝ →ᵇ ℝ) : ℝ≥0 :=
  ⟨paperPoleCompensatedEnergy c.1 + 2 * ‖G‖,
    add_nonneg (paperPoleCompensatedEnergy_nonneg c.1) (by positivity)⟩

/-- Every finite-window certificate stays within the same paid oscillation
allowance above the global minimum. -/
theorem paperCovarianceGammaCertificate_gap_le_oscillation
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) (G : ℝ →ᵇ ℝ)
    (μ : PaperObservedSpectralCompletion c F)
    (s : Finset (LogIndex × LogIndex × Bool)) (r : ℝ≥0) :
    paperCovarianceGammaCertificate c F G μ s r - paperObservedGammaValue c F G ≤
      paperCovarianceEnergyOscillation c G := by
  let ν := paperObservedGammaMinimizer c F G
  have hu := paperObservedSpectralCompletion_gammaCost_le c F μ
  have hl := paperCompletedGammaExpectation_lower (paperPoleCompensatedEnergy c.1)
    ⟨ν.1, paperObservedSpectralCompletion_subset_budget c F ν.2⟩
  have hi := G.norm_integral_le_norm (μ.1 : Measure ℝ)
  have hj := G.norm_integral_le_norm (ν.1 : Measure ℝ)
  rw [Real.norm_eq_abs] at hi hj
  have hc := paperCovarianceGammaCertificate_le_target c F G μ s r
  change _ - paperPerturbedGammaExpectation G ν.1 ≤ paperPoleCompensatedEnergy c.1 + 2 * ‖G‖
  unfold paperPerturbedGammaExpectation at hc ⊢
  linarith [(abs_le.mp hi).2, (abs_le.mp hj).1]

/-- A uniform precision sensitivity constant, depending only on the original
energy budget, the penalty size, and a positive tolerance floor. -/
def paperCovarianceUniformSlopeBound (c : ComplexNullMixture) (G : ℝ →ᵇ ℝ)
    (a : {r : ℝ≥0 // 0 < r}) : ℝ≥0 := paperCovarianceEnergyOscillation c G / a.1

/-- The same tolerance Lipschitz constant works for every completed law and
every finite measurement selection. -/
theorem lipschitzOnWith_paperCovarianceGammaCertificate_uniform
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) (G : ℝ →ᵇ ℝ)
    (μ : PaperObservedSpectralCompletion c F)
    (s : Finset (LogIndex × LogIndex × Bool)) (a : {r : ℝ≥0 // 0 < r}) :
    LipschitzOnWith (paperCovarianceUniformSlopeBound c G a)
      (paperCovarianceGammaCertificate c F G μ s) (Ici a.1) := by
  have hK : (paperCovarianceToleranceSlopeBound c F G μ s a : ℝ) ≤
      paperCovarianceUniformSlopeBound c G a :=
    div_le_div_of_nonneg_right (paperCovarianceGammaCertificate_gap_le_oscillation c F G μ s 0) a.1.2
  apply lipschitzOnWith_iff_dist_le_mul.mpr
  intro r hr q hq
  exact ((lipschitzOnWith_paperCovarianceGammaCertificate_tolerance c F G μ s a).dist_le_mul r hr q hq).trans
    (mul_le_mul_of_nonneg_right hK dist_nonneg)

/-- Largest discrepancy between the selected real covariance channels. -/
def paperFiniteCovarianceError
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ)
    (s : Finset (LogIndex × LogIndex × Bool)) (μ ν : PaperObservedSpectralCompletion c F) : ℝ≥0 :=
  nndist (paperFiniteCovarianceData c F s μ) (paperFiniteCovarianceData c F s ν)

/-- Changing the measured law enlarges the compatible window by at most the
maximum selected covariance discrepancy. -/
theorem paperCovarianceWindow_subset_of_center_shift
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ)
    (s : Finset (LogIndex × LogIndex × Bool)) (μ ν : PaperObservedSpectralCompletion c F) (r : ℝ≥0) :
    paperCovarianceWindow c F μ s r ⊆
      paperCovarianceWindow c F ν s (r + paperFiniteCovarianceError c F s μ ν) := by
  intro η hη k hk
  have hc : |paperObservedPhaseCovariances c F μ k - paperObservedPhaseCovariances c F ν k| ≤
      (paperFiniteCovarianceError c F s μ ν : ℝ) := by
    simpa only [paperFiniteCovarianceData, ContinuousMap.coe_mk, Real.dist_eq,
      paperFiniteCovarianceError, coe_nndist] using
      dist_le_pi_dist (paperFiniteCovarianceData c F s μ) (paperFiniteCovarianceData c F s ν) ⟨k, hk⟩
  exact (abs_sub_le (paperObservedPhaseCovariances c F η k) (paperObservedPhaseCovariances c F μ k)
    (paperObservedPhaseCovariances c F ν k)).trans (add_le_add (hη k hk) hc)

/-- The corresponding energy certificates obey the same enlarged-window comparison. -/
theorem paperCovarianceGammaCertificate_center_shift
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) (G : ℝ →ᵇ ℝ)
    (s : Finset (LogIndex × LogIndex × Bool)) (μ ν : PaperObservedSpectralCompletion c F) (r : ℝ≥0) :
    paperCovarianceGammaCertificate c F G ν s (r + paperFiniteCovarianceError c F s μ ν) ≤
      paperCovarianceGammaCertificate c F G μ s r :=
  paperCovarianceGammaCertificate_le c F G ν s _
    ⟨paperCovarianceWindowGammaMinimizer c F G μ s r,
      paperCovarianceWindow_subset_of_center_shift c F s μ ν r
        (paperCovarianceWindowGammaMinimizer_mem c F G μ s r)⟩

private theorem center_gap_bound
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) (G : ℝ →ᵇ ℝ)
    (s : Finset (LogIndex × LogIndex × Bool)) (μ ν : PaperObservedSpectralCompletion c F)
    (r : {r : ℝ≥0 // 0 < r}) :
    paperCovarianceGammaCertificate c F G μ s r.1 - paperCovarianceGammaCertificate c F G ν s r.1 ≤
      paperCovarianceUniformSlopeBound c G r * (paperFiniteCovarianceError c F s μ ν : ℝ) := by
  let e := paperFiniteCovarianceError c F s ν μ
  have hs := paperCovarianceGammaCertificate_center_shift c F G s ν μ r.1
  have hL := (lipschitzOnWith_paperCovarianceGammaCertificate_uniform c F G μ s r).dist_le_mul
    r.1 (by change r.1 ≤ r.1; exact le_rfl) (r.1 + e) (by simp)
  have hd : dist r.1 (r.1 + e) = (e : ℝ) := by
    rw [NNReal.dist_eq, NNReal.coe_add]
    calc
      _ = |-(e : ℝ)| := congrArg abs (by ring)
      _ = (e : ℝ) := (abs_neg _).trans (abs_of_nonneg e.2)
  rw [Real.dist_eq, hd] at hL
  have he : e = paperFiniteCovarianceError c F s μ ν := nndist_comm _ _
  have hb := (le_abs_self (paperCovarianceGammaCertificate c F G μ s r.1 -
    paperCovarianceGammaCertificate c F G μ s (r.1 + e))).trans hL
  rw [he] at hb
  change paperCovarianceGammaCertificate c F G μ s (r.1 + e) ≤ _ at hs
  rw [he] at hs
  linarith

/-- At positive tolerance, gamma certificates have an explicit Lipschitz
bound in the finite covariance data, independent of the number of channels. -/
theorem abs_paperCovarianceGammaCertificate_center_sub_le
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) (G : ℝ →ᵇ ℝ)
    (s : Finset (LogIndex × LogIndex × Bool)) (μ ν : PaperObservedSpectralCompletion c F)
    (r : {r : ℝ≥0 // 0 < r}) :
    |paperCovarianceGammaCertificate c F G μ s r.1 - paperCovarianceGammaCertificate c F G ν s r.1| ≤
      paperCovarianceUniformSlopeBound c G r * (paperFiniteCovarianceError c F s μ ν : ℝ) := by
  apply abs_le.mpr
  constructor
  · have h := center_gap_bound c F G s ν μ r
    have he : paperFiniteCovarianceError c F s ν μ = paperFiniteCovarianceError c F s μ ν := nndist_comm _ _
    rw [he] at h
    linarith
  · exact center_gap_bound c F G s μ ν r

/-- Measured laws and positive tolerances may vary simultaneously without
creating a discontinuity in the certified gamma energy. -/
theorem continuous_paperCovarianceGammaCertificate_measurement_tolerance
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) (G : ℝ →ᵇ ℝ)
    (s : Finset (LogIndex × LogIndex × Bool)) :
    Continuous (fun p : PaperObservedSpectralCompletion c F × {r : ℝ≥0 // 0 < r} =>
      paperCovarianceGammaCertificate c F G p.1 s p.2.1) := by
  apply continuous_iff_continuousAt.mpr
  intro p₀
  let D (p : PaperObservedSpectralCompletion c F × {r : ℝ≥0 // 0 < r}) : ℝ :=
    paperCovarianceUniformSlopeBound c G p.2 *
      dist (paperFiniteCovarianceData c F s p.1) (paperFiniteCovarianceData c F s p₀.1) +
      dist (paperCovarianceGammaCertificate c F G p₀.1 s p.2.1)
        (paperCovarianceGammaCertificate c F G p₀.1 s p₀.2.1)
  have hK : Continuous (fun p : PaperObservedSpectralCompletion c F × {r : ℝ≥0 // 0 < r} =>
      (paperCovarianceUniformSlopeBound c G p.2 : ℝ)) := by
    change Continuous (fun p : PaperObservedSpectralCompletion c F × {r : ℝ≥0 // 0 < r} =>
      (paperCovarianceEnergyOscillation c G : ℝ) / (p.2.1 : ℝ))
    exact continuous_const.div
      ((NNReal.continuous_coe.comp continuous_subtype_val).comp continuous_snd)
      (fun p => by exact_mod_cast (ne_of_gt p.2.2))
  have hD : Continuous D :=
    (hK.mul (((paperFiniteCovarianceData c F s).continuous.comp continuous_fst).dist continuous_const)).add
      (((continuous_paperCovarianceGammaCertificate_tolerance c F G p₀.1 s).comp
        (continuous_subtype_val.comp continuous_snd)).dist continuous_const)
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero (fun _ => dist_nonneg) (fun p => ?_)
    (by simpa [D] using hD.tendsto p₀)
  have hc := abs_paperCovarianceGammaCertificate_center_sub_le c F G s p.1 p₀.1 p.2
  calc
    _ ≤ dist (paperCovarianceGammaCertificate c F G p.1 s p.2.1)
        (paperCovarianceGammaCertificate c F G p₀.1 s p.2.1) +
        dist (paperCovarianceGammaCertificate c F G p₀.1 s p.2.1)
          (paperCovarianceGammaCertificate c F G p₀.1 s p₀.2.1) := dist_triangle _ _ _
    _ ≤ D p := add_le_add (by simpa only [Real.dist_eq, paperFiniteCovarianceError, coe_nndist] using hc) le_rfl

/-- Bounded penalty, measured law, and positive tolerance may all vary jointly. -/
theorem continuous_paperCovarianceGammaCertificate_all_parameters
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ)
    (s : Finset (LogIndex × LogIndex × Bool)) :
    Continuous (fun p : (ℝ →ᵇ ℝ) × (PaperObservedSpectralCompletion c F × {r : ℝ≥0 // 0 < r}) =>
      paperCovarianceGammaCertificate c F p.1 p.2.1 s p.2.2.1) := by
  apply continuous_iff_continuousAt.mpr
  intro p₀
  let D (p : (ℝ →ᵇ ℝ) × (PaperObservedSpectralCompletion c F × {r : ℝ≥0 // 0 < r})) : ℝ :=
    ‖p.1 - p₀.1‖ + dist (paperCovarianceGammaCertificate c F p₀.1 p.2.1 s p.2.2.1)
      (paperCovarianceGammaCertificate c F p₀.1 p₀.2.1 s p₀.2.2.1)
  have hD : Continuous D :=
    (continuous_fst.sub continuous_const).norm.add
      (((continuous_paperCovarianceGammaCertificate_measurement_tolerance c F p₀.1 s).comp
        continuous_snd).dist continuous_const)
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero (fun _ => dist_nonneg) (fun p => ?_)
    (by simpa [D] using hD.tendsto p₀)
  calc
    _ ≤ dist (paperCovarianceGammaCertificate c F p.1 p.2.1 s p.2.2.1)
        (paperCovarianceGammaCertificate c F p₀.1 p.2.1 s p.2.2.1) +
        dist (paperCovarianceGammaCertificate c F p₀.1 p.2.1 s p.2.2.1)
          (paperCovarianceGammaCertificate c F p₀.1 p₀.2.1 s p₀.2.2.1) := dist_triangle _ _ _
    _ ≤ D p := add_le_add
      (by simpa only [Real.dist_eq] using abs_paperCovarianceGammaCertificate_sub_le c F p.1 p₀.1 p.2.1 s p.2.2.1)
      le_rfl

end RHTower.WeilWorkPBAP
