import GaloisForLFunctions.RHTower.SteinhausAffineCircleMeasure
import GaloisForLFunctions.RHTower.SteinhausDensityEventCost
import GaloisForLFunctions.HTGeometry.GaussianShiftInformation

open MeasureTheory
open scoped ENNReal

noncomputable section
namespace RHTower
open SteinhausModel

/-- Original independent uniform phases on a literal finite coordinate set. -/
def steinhausFinitePhaseMeasure (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ => volume.restrict (Set.Icc (0 : ℝ) 1))

instance isProbabilityMeasure_steinhausFinitePhaseMeasure (n : ℕ) :
    IsProbabilityMeasure (steinhausFinitePhaseMeasure n) := by
  unfold steinhausFinitePhaseMeasure
  infer_instance

/-- Product of the concrete affine circle densities. -/
def steinhausFiniteAffineDensity {n : ℕ} (m : Fin n → ℂ) (x : Fin n → ℝ) : ℝ≥0∞ :=
  ∏ i, ENNReal.ofReal (steinhausAffineCircleWeight (m i) (x i))

/-- Independent circle phases with the prescribed coordinate means. -/
def steinhausFiniteAffineMeasure {n : ℕ} (m : Fin n → ℂ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun i => steinhausAffineCircleMeasure (m i))

theorem measurable_steinhausFiniteAffineDensity {n : ℕ} (m : Fin n → ℂ) :
    Measurable (steinhausFiniteAffineDensity m) :=
  Finset.measurable_prod _ fun i _ =>
    ((continuous_steinhausAffineCircleWeight (m i)).measurable.ennreal_ofReal).comp
      (measurable_pi_apply i)

theorem isProbabilityMeasure_steinhausFiniteAffineMeasure {n : ℕ} {m : Fin n → ℂ}
    (hm : ∀ i, ‖m i‖ ≤ 1 / 2) : IsProbabilityMeasure (steinhausFiniteAffineMeasure m) := by
  letI (i : Fin n) : IsProbabilityMeasure (steinhausAffineCircleMeasure (m i)) :=
    isProbabilityMeasure_steinhausAffineCircleMeasure (hm i)
  unfold steinhausFiniteAffineMeasure
  infer_instance

/-- The product law is exactly the displayed density relative to the original finite phases. -/
theorem steinhausFiniteAffineMeasure_eq_withDensity {n : ℕ} (m : Fin n → ℂ) :
    steinhausFiniteAffineMeasure m =
      (steinhausFinitePhaseMeasure n).withDensity (steinhausFiniteAffineDensity m) := by
  exact (GaloisForLFunctions.HTGeometry.pi_withDensity
    (fun _ : Fin n => volume.restrict (Set.Icc (0 : ℝ) 1))
    (fun i => (continuous_steinhausAffineCircleWeight (m i)).measurable.ennreal_ofReal)).symm

/-- Exact factorization of the squared product-density cost. -/
theorem lintegral_sq_steinhausFiniteAffineDensity {n : ℕ} {m : Fin n → ℂ}
    (hm : ∀ i, ‖m i‖ ≤ 1 / 2) :
    (∫⁻ x, steinhausFiniteAffineDensity m x ^ 2 ∂steinhausFinitePhaseMeasure n) =
      ENNReal.ofReal (∏ i, (1 + 2 * ‖m i‖ ^ 2)) := by
  have hcoord (i : Fin n) :
      (∫⁻ x, ENNReal.ofReal (steinhausAffineCircleWeight (m i) x) ^ 2
        ∂(volume.restrict (Set.Icc (0 : ℝ) 1))) =
        ENNReal.ofReal (1 + 2 * ‖m i‖ ^ 2) := by
    have hs : Integrable (fun x => steinhausAffineCircleWeight (m i) x ^ 2)
        (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
      ((continuous_steinhausAffineCircleWeight (m i)).pow 2).integrableOn_Icc
    simp_rw [← ENNReal.ofReal_pow (steinhausAffineCircleWeight_nonneg (hm i) _) 2]
    rw [← ofReal_integral_eq_lintegral_ofReal hs
      (Filter.Eventually.of_forall fun _ => sq_nonneg _),
      integral_sq_steinhausAffineCircleWeight]
  unfold steinhausFiniteAffineDensity steinhausFinitePhaseMeasure
  simp_rw [← Finset.prod_pow]
  rw [GaloisForLFunctions.HTGeometry.lintegral_pi_prod _ (fun i =>
    ((continuous_steinhausAffineCircleWeight (m i)).measurable.ennreal_ofReal).pow_const 2)]
  simp_rw [hcoord]
  exact (ENNReal.ofReal_prod_of_nonneg (fun i _ => by positivity)).symm

/-- The only exponential cost is twice the total squared prescribed bias. -/
theorem lintegral_sq_steinhausFiniteAffineDensity_le {n : ℕ} {m : Fin n → ℂ}
    (hm : ∀ i, ‖m i‖ ≤ 1 / 2) :
    (∫⁻ x, steinhausFiniteAffineDensity m x ^ 2 ∂steinhausFinitePhaseMeasure n) ≤
      ENNReal.ofReal (Real.exp (2 * ∑ i, ‖m i‖ ^ 2)) := by
  rw [lintegral_sq_steinhausFiniteAffineDensity hm]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ ∏ i, Real.exp (2 * ‖m i‖ ^ 2) := by
      apply Finset.prod_le_prod (fun i _ => by positivity)
      intro i _
      simpa only [add_comm] using Real.add_one_le_exp (2 * ‖m i‖ ^ 2)
    _ = _ := by rw [← Real.exp_sum, Finset.mul_sum]

/-- Any event with half the biased probability has the explicit positive original probability. -/
theorem measureReal_event_ge_steinhausFiniteAffineCost {n : ℕ} {m : Fin n → ℂ}
    (hm : ∀ i, ‖m i‖ ≤ 1 / 2) {E : Set (Fin n → ℝ)} (hE : MeasurableSet E)
    (hmass : ENNReal.ofReal (1 / 2 : ℝ) ≤ steinhausFiniteAffineMeasure m E) :
    (1 / 4 : ℝ) * Real.exp (-(2 * ∑ i, ‖m i‖ ^ 2)) ≤
      (steinhausFinitePhaseMeasure n).real E := by
  apply measureReal_event_ge_quarter_exp_neg_densityCost (steinhausFinitePhaseMeasure n)
    (measurable_steinhausFiniteAffineDensity m) hE (2 * ∑ i, ‖m i‖ ^ 2)
  · rwa [← steinhausFiniteAffineMeasure_eq_withDensity m]
  · exact lintegral_sq_steinhausFiniteAffineDensity_le hm

end RHTower
