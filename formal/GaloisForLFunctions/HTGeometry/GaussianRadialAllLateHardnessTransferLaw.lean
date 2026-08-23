import GaloisForLFunctions.HTGeometry.GaussianAngularPolarDisintegrationLaw

/-!
# Gaussian radial all-late hardness transfer

For a homogeneous static Hamiltonian family, Gaussian radius is an internal
clock: radial rescaling of the coefficients is exactly time rescaling.  This
module proves the measure-theoretic step needed to turn an asymptotic hardness
bound on every sufficiently late angular time into an asymptotic bound at every
sufficiently late laboratory time under Gaussian coefficient sampling.

The proof is not a subsequence extraction.  Positive radial scale sends every
laboratory-time net tending to infinity to an angular-time net tending to
infinity; dominated convergence then retains the full `atTop` filter.
-/

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Positive random dilation preserves a bounded `limsup` after averaging.
The subtracted excess converges to zero along the full late-time filter. -/
theorem tendsto_lintegral_dilated_excess_zero
    {X : Type*} [MeasurableSpace X]
    (mu : Measure X) [IsProbabilityMeasure mu]
    (a : ℝ → ℝ≥0∞) (ha : Measurable a) (ha_one : ∀ t, a t ≤ 1)
    (scale : X → ℝ) (hscale : Measurable scale)
    (hscale_pos : ∀ᵐ x ∂mu, 0 < scale x)
    (b : ℝ≥0∞)
    (hlim : limsup a atTop ≤ b) :
    Tendsto (fun T : ℝ => ∫⁻ x, a (scale x * T) - b ∂mu) atTop (𝓝 0) := by
  have hconv := tendsto_lintegral_filter_of_dominated_convergence
    (μ := mu) (l := atTop)
    (F := fun T x => a (scale x * T) - b) (f := fun _ => 0) (fun _ => 1)
    (Eventually.of_forall fun T =>
      (ha.comp (hscale.mul_const T)).sub measurable_const)
    (Eventually.of_forall fun T => ae_of_all mu fun x =>
      (tsub_le_self.trans (ha_one (scale x * T))))
    (by simp)
    (by
      filter_upwards [hscale_pos] with x hx
      apply ENNReal.tendsto_nhds_zero.2
      intro eps heps
      have htime : Tendsto (fun T : ℝ => scale x * T) atTop atTop :=
        (tendsto_const_mul_atTop_of_pos hx).2 tendsto_id
      have hcomp : limsup (fun T : ℝ => a (scale x * T)) atTop ≤ b := by
        exact (htime.limsup_comp_le_limsup (u := a)).trans hlim
      have hexcess : limsup (fun T : ℝ => a (scale x * T) - b) atTop ≤ 0 := by
        rw [ENNReal.limsup_sub_const]
        exact (tsub_eq_zero_of_le hcomp).le
      have hlt : limsup (fun T : ℝ => a (scale x * T) - b) atTop < eps :=
        hexcess.trans_lt heps
      exact (eventually_lt_of_limsup_lt hlt).mono fun _ h => h.le)
  simpa using hconv

/-- Every sufficiently late averaged dilation obeys the original asymptotic
ceiling, up to an arbitrarily prescribed positive error. -/
theorem eventually_lintegral_dilation_le
    {X : Type*} [MeasurableSpace X]
    (mu : Measure X) [IsProbabilityMeasure mu]
    (a : ℝ → ℝ≥0∞) (ha : Measurable a) (ha_one : ∀ t, a t ≤ 1)
    (scale : X → ℝ) (hscale : Measurable scale)
    (hscale_pos : ∀ᵐ x ∂mu, 0 < scale x)
    (b : ℝ≥0∞) (hlim : limsup a atTop ≤ b)
    {eta : ℝ≥0∞} (heta : 0 < eta) :
    ∀ᶠ T : ℝ in atTop, (∫⁻ x, a (scale x * T) ∂mu) ≤ b + eta := by
  have hconv := tendsto_lintegral_dilated_excess_zero
    mu a ha ha_one scale hscale hscale_pos b hlim
  have hevent : ∀ᶠ T : ℝ in atTop,
      (∫⁻ x, a (scale x * T) - b ∂mu) ≤ eta :=
    ENNReal.tendsto_nhds_zero.1 hconv eta heta
  filter_upwards [hevent] with T hT
  calc
    (∫⁻ x, a (scale x * T) ∂mu) ≤
        ∫⁻ x, b + (a (scale x * T) - b) ∂mu :=
      lintegral_mono fun x => le_add_tsub
    _ = (∫⁻ _x : X, b ∂mu) + (∫⁻ x, a (scale x * T) - b ∂mu) :=
      lintegral_add_left measurable_const _
    _ = b + (∫⁻ x, a (scale x * T) - b ∂mu) := by simp
    _ ≤ b + eta := add_le_add (le_refl b) hT

/-- The normalized angular factor in Gaussian polar coordinates has unit mass. -/
theorem gaussianAngularMeasure_univ {m : ℕ} (hm : 0 < m) :
    gaussianAngularMeasure m Set.univ = 1 := by
  rw [gaussianAngularMeasure, withDensity_apply _ MeasurableSet.univ]
  rw [setLIntegral_const]
  apply (ENNReal.toReal_eq_one_iff _).mp
  rw [ENNReal.toReal_mul]
  rw [ENNReal.toReal_ofReal]
  · exact gaussianAngularNormalization_mul_sphereMass hm
  · unfold gaussianAngularNormalization
    positivity

/-- The independent angular-radius Gaussian product has unit mass. -/
theorem gaussianPolarProduct_univ {m : ℕ} (hm : 0 < m) :
    ((gaussianAngularMeasure m).prod (gaussianRadiusMeasure m)) Set.univ = 1 := by
  apply (ENNReal.toReal_eq_one_iff _).mp
  change ((gaussianAngularMeasure m).prod (gaussianRadiusMeasure m)).real Set.univ = 1
  have h := integral_stdGaussian_independent_polar hm
    (fun _ : EuclideanSpace ℝ (Fin m) => (1 : ℝ))
  simpa [integral_const] using h.symm

/-- The chi-radius factor in Gaussian polar coordinates has unit mass. -/
theorem gaussianRadiusMeasure_univ {m : ℕ} (hm : 0 < m) :
    gaussianRadiusMeasure m Set.univ = 1 := by
  letI : SFinite (gaussianRadiusMeasure m) := by
    unfold gaussianRadiusMeasure
    infer_instance
  have hprod := gaussianPolarProduct_univ hm
  have hangular := gaussianAngularMeasure_univ hm
  rw [show (Set.univ : Set
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1 × Ioi (0 : ℝ))) =
      Set.univ ×ˢ Set.univ by ext; simp,
    Measure.prod_prod, hangular, one_mul] at hprod
  exact hprod

/-- Gaussian-radius specialization of the all-late dilation law.  In a
homogeneous static Hamiltonian family, `r * T` is exactly the angular evolution
time produced by a coefficient vector of radius `r`. -/
theorem eventually_gaussianRadius_lintegral_dilation_le
    {m : ℕ} (hm : 0 < m)
    (a : ℝ → ℝ≥0∞) (ha : Measurable a) (ha_one : ∀ t, a t ≤ 1)
    (b : ℝ≥0∞) (hlim : limsup a atTop ≤ b)
    {eta : ℝ≥0∞} (heta : 0 < eta) :
    ∀ᶠ T : ℝ in atTop,
      (∫⁻ r : Ioi (0 : ℝ), a (r.1 * T) ∂(gaussianRadiusMeasure m)) ≤ b + eta := by
  letI : IsProbabilityMeasure (gaussianRadiusMeasure m) :=
    IsProbabilityMeasure.mk (gaussianRadiusMeasure_univ hm)
  exact eventually_lintegral_dilation_le
    (gaussianRadiusMeasure m) a ha ha_one
    (fun r : Ioi (0 : ℝ) => r.1) measurable_subtype_coe
    (ae_of_all _ fun r => r.2) b hlim heta

end

end GaloisForLFunctions.HTGeometry
