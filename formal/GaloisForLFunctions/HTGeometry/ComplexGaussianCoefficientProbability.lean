import GaloisForLFunctions.HTGeometry.BoundedComplexCoefficientProbability

/-!
# The standard complex Gaussian coefficient law

Two independent standard real Gaussians, transported through the measurable equivalence
`ℝ × ℝ ≃ ℂ`, give a complex probability law that is absolutely continuous with respect to planar
Lebesgue measure and has a quadratically decaying tail.  This is the coefficient law of the planar
Gaussian entire function.
-/

open MeasureTheory ProbabilityTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The standard complex Gaussian law on `ℂ`. -/
def complexGaussianProbability : Measure ℂ :=
  Measure.map Complex.measurableEquivRealProd.symm
    ((gaussianReal 0 1).prod (gaussianReal 0 1))

instance complexGaussianProbability_isProbabilityMeasure :
    IsProbabilityMeasure complexGaussianProbability := by
  refine ⟨?_⟩
  rw [complexGaussianProbability,
    Measure.map_apply_of_aemeasurable
      Complex.measurableEquivRealProd.symm.measurable.aemeasurable MeasurableSet.univ]
  simp

theorem gaussianReal_absolutelyContinuous :
    (gaussianReal 0 1) ≪ (volume : Measure ℝ) := by
  rw [gaussianReal_of_var_ne_zero _ (by norm_num)]
  exact withDensity_absolutelyContinuous _ _

theorem complexGaussianProbability_absolutelyContinuous :
    complexGaussianProbability ≪ (volume : Measure ℂ) := by
  have hprod0 : (gaussianReal 0 1).prod (gaussianReal 0 1) ≪
      (volume : Measure ℝ).prod (volume : Measure ℝ) :=
    gaussianReal_absolutelyContinuous.prod gaussianReal_absolutelyContinuous
  have hvol : (volume : Measure ℝ).prod (volume : Measure ℝ) =
      (volume : Measure (ℝ × ℝ)) := rfl
  have hprod : (gaussianReal 0 1).prod (gaussianReal 0 1) ≪ (volume : Measure (ℝ × ℝ)) := by
    simpa only [hvol] using hprod0
  have hmap := hprod.map Complex.measurableEquivRealProd.symm.measurable
  rw [(Complex.volume_preserving_equiv_real_prod.symm
    Complex.measurableEquivRealProd).map_eq] at hmap
  exact hmap

/-- Every finite independent complex Gaussian packet has a Lebesgue absolutely continuous law. -/
theorem pi_complexGaussianProbability_absolutelyContinuous (M : ℕ) :
    Measure.pi (fun _ : Fin M => complexGaussianProbability) ≪
      (volume : Measure (Fin M → ℂ)) := by
  rw [volume_pi]
  exact pi_absolutelyContinuous_pi M _ _
    (fun _ => complexGaussianProbability_absolutelyContinuous)

/-! ### The coefficient tail -/

theorem measure_abs_ge_le {c : ℝ} (hc : 0 < c) :
    (gaussianReal 0 1) {t : ℝ | c ≤ |t|} ≤ ENNReal.ofReal ((c ^ 2)⁻¹) := by
  have hmem : MemLp id 2 (gaussianReal 0 1) := memLp_id_gaussianReal 2
  have hmean : ∫ x : ℝ, id x ∂(gaussianReal 0 1) = 0 := integral_id_gaussianReal
  have h := meas_ge_le_variance_div_sq (μ := gaussianReal 0 1) (X := id) hmem hc
  rw [hmean] at h
  simpa using h

theorem measure_norm_ge_le {c : ℝ} (hc : 0 < c) :
    complexGaussianProbability {z : ℂ | c ≤ ‖z‖}
      ≤ ENNReal.ofReal (((c / 2) ^ 2)⁻¹)
        + ENNReal.ofReal (((c / 2) ^ 2)⁻¹) := by
  have hsub : {z : ℂ | c ≤ ‖z‖} ⊆
      {z : ℂ | c / 2 ≤ |z.re|} ∪ {z : ℂ | c / 2 ≤ |z.im|} := by
    intro z hz
    by_contra hcon
    rw [Set.mem_union] at hcon
    push Not at hcon
    obtain ⟨h1, h2⟩ := hcon
    have h1' : |z.re| < c / 2 := by simpa using h1
    have h2' : |z.im| < c / 2 := by simpa using h2
    have := Complex.norm_le_abs_re_add_abs_im z
    have hz' : c ≤ ‖z‖ := hz
    linarith
  refine le_trans (measure_mono hsub) (le_trans (measure_union_le _ _) ?_)
  have hre : complexGaussianProbability {z : ℂ | c / 2 ≤ |z.re|}
      ≤ ENNReal.ofReal (((c / 2) ^ 2)⁻¹) := by
    have hmapre : Measure.map Complex.re complexGaussianProbability = gaussianReal 0 1 := by
      rw [complexGaussianProbability, Measure.map_map Complex.measurable_re
        Complex.measurableEquivRealProd.symm.measurable]
      have hcomp : Complex.re ∘ Complex.measurableEquivRealProd.symm
          = (Prod.fst : ℝ × ℝ → ℝ) := by
        funext p
        simp [Complex.measurableEquivRealProd_symm_apply]
      rw [hcomp, Measure.map_fst_prod]
      simp
    have hmeasSet : MeasurableSet {t : ℝ | c / 2 ≤ |t|} :=
      measurableSet_le measurable_const measurable_id.abs
    have := measure_abs_ge_le (c := c / 2) (by positivity)
    rw [← hmapre, Measure.map_apply Complex.measurable_re hmeasSet] at this
    exact this
  have him : complexGaussianProbability {z : ℂ | c / 2 ≤ |z.im|}
      ≤ ENNReal.ofReal (((c / 2) ^ 2)⁻¹) := by
    have hmapim : Measure.map Complex.im complexGaussianProbability = gaussianReal 0 1 := by
      rw [complexGaussianProbability, Measure.map_map Complex.measurable_im
        Complex.measurableEquivRealProd.symm.measurable]
      have hcomp : Complex.im ∘ Complex.measurableEquivRealProd.symm
          = (Prod.snd : ℝ × ℝ → ℝ) := by
        funext p
        simp [Complex.measurableEquivRealProd_symm_apply]
      rw [hcomp, Measure.map_snd_prod]
      simp
    have hmeasSet : MeasurableSet {t : ℝ | c / 2 ≤ |t|} :=
      measurableSet_le measurable_const measurable_id.abs
    have := measure_abs_ge_le (c := c / 2) (by positivity)
    rw [← hmapim, Measure.map_apply Complex.measurable_im hmeasSet] at this
    exact this
  exact add_le_add hre him

end

end GaloisForLFunctions.HTGeometry
