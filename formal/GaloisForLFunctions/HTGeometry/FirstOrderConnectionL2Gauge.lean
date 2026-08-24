import GaloisForLFunctions.HTGeometry.FirstOrderConnectionGauge
import GaloisForLFunctions.HTGeometry.L2OperatorFamilyIsometry

/-!
# The first-order Carathéodory gauge as an L² unitary

The pointwise finite-dimensional gauge and its adjoint define mutually inverse multiplication
operators on vector-valued `L²(ℝ)`. Thus the formal pointwise gauge law is implemented by a genuine
Hilbert-space unitary `M_G`, even for merely locally integrable self-adjoint potentials.
-/

noncomputable section

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace

namespace GaloisForLFunctions.HTGeometry

abbrev ConnectionLineL2 (E : Type*) [NormedAddCommGroup E] :=
  Lp E 2 (volume : Measure ℝ)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [FiniteDimensional ℂ E]

def caratheodoryGaugeAdjointFamily
    (c : ℝ) (V : ℝ → E →L[ℂ] E) (t : ℝ) : E →L[ℂ] E :=
  star (GaloisForLFunctions.HTGeometry.caratheodoryGauge c V t)

omit [FiniteDimensional ℂ E] in
theorem continuous_caratheodoryGaugeAdjointFamily
    {c : ℝ} {V : ℝ → E →L[ℂ] E} (hV : LocallyIntegrable V volume) :
    Continuous (caratheodoryGaugeAdjointFamily c V) := by
  exact (GaloisForLFunctions.HTGeometry.continuous_caratheodoryGauge hV).star

theorem caratheodoryGaugeAdjointFamily_apply_eq_unitary_symm
    {c : ℝ} (hc : c ≠ 0) {V : ℝ → E →L[ℂ] E} (hV : LocallyIntegrable V volume)
    (hVstar : ∀ t, IsSelfAdjoint (V t)) (t : ℝ) (x : E) :
    caratheodoryGaugeAdjointFamily c V t x =
      (GaloisForLFunctions.HTGeometry.caratheodoryGaugeUnitary hc hV hVstar t).symm x := by
  let U := GaloisForLFunctions.HTGeometry.caratheodoryGaugeUnitary hc hV hVstar t
  apply ext_inner_right ℂ
  intro y
  calc
    inner ℂ (caratheodoryGaugeAdjointFamily c V t x) y =
        inner ℂ x (GaloisForLFunctions.HTGeometry.caratheodoryGauge c V t y) := by
      rw [caratheodoryGaugeAdjointFamily,
        ContinuousLinearMap.star_eq_adjoint,
        ContinuousLinearMap.adjoint_inner_left]
    _ = inner ℂ x (U y) := rfl
    _ = inner ℂ (U (U.symm x)) (U y) := by rw [U.apply_symm_apply]
    _ = inner ℂ (U.symm x) y := U.inner_map_map _ _

theorem norm_caratheodoryGaugeAdjointFamily_apply
    {c : ℝ} (hc : c ≠ 0) {V : ℝ → E →L[ℂ] E} (hV : LocallyIntegrable V volume)
    (hVstar : ∀ t, IsSelfAdjoint (V t)) (t : ℝ) (x : E) :
    ‖caratheodoryGaugeAdjointFamily c V t x‖ = ‖x‖ := by
  rw [caratheodoryGaugeAdjointFamily_apply_eq_unitary_symm hc hV hVstar]
  exact (GaloisForLFunctions.HTGeometry.caratheodoryGaugeUnitary hc hV hVstar t).symm.norm_map x

theorem caratheodoryGauge_apply_adjointFamily
    {c : ℝ} (hc : c ≠ 0) {V : ℝ → E →L[ℂ] E} (hV : LocallyIntegrable V volume)
    (hVstar : ∀ t, IsSelfAdjoint (V t)) (t : ℝ) (x : E) :
    GaloisForLFunctions.HTGeometry.caratheodoryGauge c V t
        (caratheodoryGaugeAdjointFamily c V t x) = x := by
  rw [caratheodoryGaugeAdjointFamily_apply_eq_unitary_symm hc hV hVstar]
  exact (GaloisForLFunctions.HTGeometry.caratheodoryGaugeUnitary hc hV hVstar t).apply_symm_apply x

noncomputable def l2CaratheodoryGaugeUnitary
    {c : ℝ} (hc : c ≠ 0) {V : ℝ → E →L[ℂ] E} (hV : LocallyIntegrable V volume)
    (hVstar : ∀ t, IsSelfAdjoint (V t)) :
    ConnectionLineL2 E ≃ₗᵢ[ℂ] ConnectionLineL2 E :=
  GaloisForLFunctions.HTGeometry.lpOperatorFamilyIsometryEquiv
    (GaloisForLFunctions.HTGeometry.continuous_caratheodoryGauge hV).aestronglyMeasurable
    (continuous_caratheodoryGaugeAdjointFamily hV).aestronglyMeasurable
    (GaloisForLFunctions.HTGeometry.caratheodoryGauge_norm_preserved hc hV hVstar)
    (norm_caratheodoryGaugeAdjointFamily_apply hc hV hVstar)
    (caratheodoryGauge_apply_adjointFamily hc hV hVstar)

theorem l2CaratheodoryGaugeUnitary_coeFn
    {c : ℝ} (hc : c ≠ 0) {V : ℝ → E →L[ℂ] E} (hV : LocallyIntegrable V volume)
    (hVstar : ∀ t, IsSelfAdjoint (V t)) (f : ConnectionLineL2 E) :
    ((l2CaratheodoryGaugeUnitary hc hV hVstar f : ConnectionLineL2 E) : ℝ → E) =ᵐ[volume]
      fun t => GaloisForLFunctions.HTGeometry.caratheodoryGauge c V t
        ((f : ℝ → E) t) := by
  exact GaloisForLFunctions.HTGeometry.lpOperatorFamilyIsometry_coeFn
    (GaloisForLFunctions.HTGeometry.continuous_caratheodoryGauge hV).aestronglyMeasurable
    (GaloisForLFunctions.HTGeometry.caratheodoryGauge_norm_preserved hc hV hVstar) f

end GaloisForLFunctions.HTGeometry
