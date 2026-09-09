import GaloisForLFunctions.HTGeometry.GomesPolynomialExponentialMoments

/-!
# Complete moment observations on polynomial L² spaces

The entire exponential window discharges the existing real polynomial-density theorem.
For every finite raw polynomial profile, and for every total normalized profile, the
full sequence of polynomial moments is an injective linear observation of L² vectors.
The normalized infinite-mass case is correctly retained as the zero L² space.
-/

noncomputable section
open Polynomial MeasureTheory Filter
open scoped Topology NNReal ENNReal SchwartzMap

namespace GaloisForLFunctions.HTGeometry

/-- Every polynomial moment of a finite raw L² vector is an actual integrable observable. -/
theorem gomesPolynomialMeasure_L2_moment_integrable (P : GomesFinitePolynomialProfile)
    (g : Lp ℝ 2 (gomesDilatonMeasure P.val)) (n : ℕ) :
    Integrable (fun x : ℝ => x ^ n * g x) (gomesDilatonMeasure P.val) :=
  memLp_one_iff_integrable.mp ((Lp.memLp g).mul' (gomesPolynomialMeasure_pow_memLp_two P n))

/-- Polynomial moments detect zero exactly in the finite raw L² space. -/
theorem gomesPolynomialMeasure_L2_moments_zero_iff (P : GomesFinitePolynomialProfile)
    (g : Lp ℝ 2 (gomesDilatonMeasure P.val)) :
    (∀ n : ℕ, ∫ x : ℝ, x ^ n * g x ∂(gomesDilatonMeasure P.val) = 0) ↔ g = 0 := by
  letI : IsFiniteMeasure (gomesDilatonMeasure P.val) := P.property
  constructor
  · intro h
    have hz := RHTower.ae_eq_zero_of_all_moments_of_entireExponentialMoments
      (gomesPolynomialMeasure_entireExponentialMoments P) (Lp.stronglyMeasurable g).measurable (Lp.memLp g) h
    apply Lp.ext
    filter_upwards [hz, Lp.coeFn_zero ℝ 2 (gomesDilatonMeasure P.val)] with x hx hzero
    exact hx.trans hzero.symm
  · rintro rfl n
    apply integral_eq_zero_of_ae
    filter_upwards [Lp.coeFn_zero ℝ 2 (gomesDilatonMeasure P.val)] with x hx
    change x ^ n * (0 : Lp ℝ 2 (gomesDilatonMeasure P.val)) x = 0
    rw [hx]
    exact mul_zero _

/-- Polynomial observables have dense span in every finite raw L² space. -/
theorem gomesPolynomialMeasure_L2_polynomial_dense (P : GomesFinitePolynomialProfile) :
    (RHTower.realMonomialSpan (gomesDilatonMeasure P.val)
      (gomesPolynomialMeasure_entireExponentialMoments P)).topologicalClosure = ⊤ := by
  letI : IsFiniteMeasure (gomesDilatonMeasure P.val) := P.property
  exact RHTower.realMonomialSpan_closure_eq_top _ (gomesPolynomialMeasure_entireExponentialMoments P)

/-- The complete polynomial moment record is a real linear observation. -/
def gomesPolynomialMeasureMomentMap (P : GomesFinitePolynomialProfile) :
    Lp ℝ 2 (gomesDilatonMeasure P.val) →ₗ[ℝ] (ℕ → ℝ) where
  toFun g n := ∫ x : ℝ, x ^ n * g x ∂(gomesDilatonMeasure P.val)
  map_add' g k := by
    funext n
    change (∫ x : ℝ, x ^ n * (g + k) x ∂(gomesDilatonMeasure P.val)) =
      (∫ x : ℝ, x ^ n * g x ∂(gomesDilatonMeasure P.val)) +
        (∫ x : ℝ, x ^ n * k x ∂(gomesDilatonMeasure P.val))
    rw [← integral_add (gomesPolynomialMeasure_L2_moment_integrable P g n)
      (gomesPolynomialMeasure_L2_moment_integrable P k n)]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_add g k] with x hx
    change x ^ n * (g + k) x = x ^ n * g x + x ^ n * k x
    rw [hx]
    exact mul_add _ _ _
  map_smul' c g := by
    funext n
    change (∫ x : ℝ, x ^ n * (c • g) x ∂(gomesDilatonMeasure P.val)) =
      c * (∫ x : ℝ, x ^ n * g x ∂(gomesDilatonMeasure P.val))
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_smul c g] with x hx
    change x ^ n * (c • g) x = c * (x ^ n * g x)
    rw [hx]
    change x ^ n * (c * g x) = c * (x ^ n * g x)
    ring

/-- No nonzero L² direction is invisible to the full finite raw moment record. -/
theorem gomesPolynomialMeasureMomentMap_injective (P : GomesFinitePolynomialProfile) :
    Function.Injective (gomesPolynomialMeasureMomentMap P) := by
  intro g k h
  apply sub_eq_zero.mp
  apply (gomesPolynomialMeasure_L2_moments_zero_iff P (g - k)).mp
  intro n
  have hz : gomesPolynomialMeasureMomentMap P (g - k) = 0 := by
    rw [map_sub, h, sub_self]
  exact congrFun hz n

/-- Every polynomial moment of a total normalized L² vector is an actual integrable observable. -/
theorem gomesPolynomialNormalized_L2_moment_integrable (H : ℝ[X])
    (g : Lp ℝ 2 (gomesDilatonMassNormalized H)) (n : ℕ) :
    Integrable (fun x : ℝ => x ^ n * g x) (gomesDilatonMassNormalized H) :=
  memLp_one_iff_integrable.mp ((Lp.memLp g).mul' (gomesPolynomialNormalized_pow_memLp_two H n))

/-- Polynomial moments detect zero exactly in the total normalized L² space. -/
theorem gomesPolynomialNormalized_L2_moments_zero_iff (H : ℝ[X])
    (g : Lp ℝ 2 (gomesDilatonMassNormalized H)) :
    (∀ n : ℕ, ∫ x : ℝ, x ^ n * g x ∂(gomesDilatonMassNormalized H) = 0) ↔ g = 0 := by
  letI : IsFiniteMeasure (gomesDilatonMassNormalized H) := gomesPolynomialNormalized_finite H
  constructor
  · intro h
    have hz := RHTower.ae_eq_zero_of_all_moments_of_entireExponentialMoments
      (gomesPolynomialNormalized_entireExponentialMoments H) (Lp.stronglyMeasurable g).measurable (Lp.memLp g) h
    apply Lp.ext
    filter_upwards [hz, Lp.coeFn_zero ℝ 2 (gomesDilatonMassNormalized H)] with x hx hzero
    exact hx.trans hzero.symm
  · rintro rfl n
    apply integral_eq_zero_of_ae
    filter_upwards [Lp.coeFn_zero ℝ 2 (gomesDilatonMassNormalized H)] with x hx
    change x ^ n * (0 : Lp ℝ 2 (gomesDilatonMassNormalized H)) x = 0
    rw [hx]
    exact mul_zero _

/-- Polynomial observables have dense span in every total normalized L² space. -/
theorem gomesPolynomialNormalized_L2_polynomial_dense (H : ℝ[X]) :
    (RHTower.realMonomialSpan (gomesDilatonMassNormalized H)
      (gomesPolynomialNormalized_entireExponentialMoments H)).topologicalClosure = ⊤ := by
  letI : IsFiniteMeasure (gomesDilatonMassNormalized H) := gomesPolynomialNormalized_finite H
  exact RHTower.realMonomialSpan_closure_eq_top _ (gomesPolynomialNormalized_entireExponentialMoments H)

/-- The complete polynomial moment record is a real linear observation. -/
def gomesPolynomialNormalizedMomentMap (H : ℝ[X]) :
    Lp ℝ 2 (gomesDilatonMassNormalized H) →ₗ[ℝ] (ℕ → ℝ) where
  toFun g n := ∫ x : ℝ, x ^ n * g x ∂(gomesDilatonMassNormalized H)
  map_add' g k := by
    funext n
    change (∫ x : ℝ, x ^ n * (g + k) x ∂(gomesDilatonMassNormalized H)) =
      (∫ x : ℝ, x ^ n * g x ∂(gomesDilatonMassNormalized H)) +
        (∫ x : ℝ, x ^ n * k x ∂(gomesDilatonMassNormalized H))
    rw [← integral_add (gomesPolynomialNormalized_L2_moment_integrable H g n)
      (gomesPolynomialNormalized_L2_moment_integrable H k n)]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_add g k] with x hx
    change x ^ n * (g + k) x = x ^ n * g x + x ^ n * k x
    rw [hx]
    exact mul_add _ _ _
  map_smul' c g := by
    funext n
    change (∫ x : ℝ, x ^ n * (c • g) x ∂(gomesDilatonMassNormalized H)) =
      c * (∫ x : ℝ, x ^ n * g x ∂(gomesDilatonMassNormalized H))
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_smul c g] with x hx
    change x ^ n * (c • g) x = c * (x ^ n * g x)
    rw [hx]
    change x ^ n * (c * g x) = c * (x ^ n * g x)
    ring

/-- No nonzero L² direction is invisible to the full total normalized moment record. -/
theorem gomesPolynomialNormalizedMomentMap_injective (H : ℝ[X]) :
    Function.Injective (gomesPolynomialNormalizedMomentMap H) := by
  intro g k h
  apply sub_eq_zero.mp
  apply (gomesPolynomialNormalized_L2_moments_zero_iff H (g - k)).mp
  intro n
  have hz : gomesPolynomialNormalizedMomentMap H (g - k) = 0 := by
    rw [map_sub, h, sub_self]
  exact congrFun hz n

end GaloisForLFunctions.HTGeometry
