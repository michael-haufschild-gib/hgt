import GaloisForLFunctions.RHTower.BurnolBaseFirstJetAdmission

/-!
# Exact coefficient coordinates for the original Burnol synthesis

Counting-measure `L²` and `lp` have different implementations. The canonical isometry below
identifies them pointwise and transports the existing Bochner synthesis, preserving every
literal column. This makes the first-jet admission a statement about the original source.
-/

open MeasureTheory Filter Topology
open scoped InnerProductSpace

namespace RHTower
open GaloisForLFunctions.HTGeometry
noncomputable section

local instance : MeasurableSpace RoutePPrimitiveIndex := ⊤
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩

local notation "CSource" => Lp ℂ 2 (Measure.count : Measure RoutePPrimitiveIndex)
local notation "LSource" => lp (fun _ : RoutePPrimitiveIndex => ℂ) 2

private theorem integrable_sq_countSource (f : CSource) :
    Integrable (fun pe => ‖f pe‖ ^ 2) Measure.count :=
  (memLp_two_iff_integrable_sq_norm (Lp.memLp f).aestronglyMeasurable).mp (Lp.memLp f)

private theorem summable_sq_countSource (f : CSource) :
    Summable (fun pe => ‖f pe‖ ^ 2) := by
  have h := integrable_count_iff.mp (integrable_sq_countSource f)
  simpa only [Real.norm_eq_abs, abs_sq] using h

private def burnolCountCoordinatesLinear : CSource →ₗ[ℂ] LSource where
  toFun f := ⟨fun pe => f pe, memℓp_gen <| by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using summable_sq_countSource f⟩
  map_add' f g := by
    apply lp.ext
    funext pe
    exact (Measure.ae_count_iff.mp (Lp.coeFn_add f g)) pe
  map_smul' z f := by
    apply lp.ext
    funext pe
    exact (Measure.ae_count_iff.mp (Lp.coeFn_smul z f)) pe

private theorem norm_burnolCountCoordinatesLinear (f : CSource) :
    ‖burnolCountCoordinatesLinear f‖ = ‖f‖ := by
  have hsquare : ‖burnolCountCoordinatesLinear f‖ ^ 2 = ‖f‖ ^ 2 := by
    rw [HilbertSchmidt.lp_norm_sq_eq, HTGeometry.norm_l2_sq_eq_integral_norm_sq,
      integral_countable (integrable_sq_countSource f)]
    simp [burnolCountCoordinatesLinear, measureReal_def]
  nlinarith [norm_nonneg (burnolCountCoordinatesLinear f), norm_nonneg f]

private def burnolCountCoordinatesIsometry : CSource →ₗᵢ[ℂ] LSource :=
  { burnolCountCoordinatesLinear with norm_map' := norm_burnolCountCoordinatesLinear }

private theorem burnolCountCoordinates_surjective :
    Function.Surjective burnolCountCoordinatesIsometry := by
  intro x
  have hx : MemLp (fun pe => (x : RoutePPrimitiveIndex → ℂ) pe) 2 Measure.count := by
    apply (memLp_two_iff_integrable_sq_norm measurable_from_top.aestronglyMeasurable).mpr
    rw [integrable_count_iff]
    simpa only [Real.norm_eq_abs, abs_sq] using summable_norm_sq_lp x
  refine ⟨hx.toLp _, ?_⟩
  apply lp.ext
  funext pe
  exact (Measure.ae_count_iff.mp hx.coeFn_toLp) pe

/-- Canonical, coefficient-preserving identification of the original counting-measure source. -/
def burnolBaseCountCoordinates : CSource ≃ₗᵢ[ℂ] LSource :=
  LinearIsometryEquiv.ofSurjective burnolCountCoordinatesIsometry burnolCountCoordinates_surjective

@[simp] theorem burnolBaseCountCoordinates_apply (f : CSource) (pe : RoutePPrimitiveIndex) :
    (burnolBaseCountCoordinates f : RoutePPrimitiveIndex → ℂ) pe = f pe := rfl

@[simp] theorem burnolBaseCountCoordinates_symm_apply (x : LSource) (pe : RoutePPrimitiveIndex) :
    burnolBaseCountCoordinates.symm x pe = (x : RoutePPrimitiveIndex → ℂ) pe := by
  have h := congrArg (fun y : LSource => (y : RoutePPrimitiveIndex → ℂ) pe)
    (burnolBaseCountCoordinates.apply_symm_apply x)
  exact h

/-- The original Bochner synthesis in its canonical coefficient coordinates. -/
def burnolBaseCoefficientSynthesis : LSource →L[ℂ] routePBurnolHalfLineL2 :=
  routePPrimitiveBurnolBaseSynthesis ∘L
    burnolBaseCountCoordinates.symm.toLinearIsometry.toContinuousLinearMap

private theorem burnolBaseFieldLp_apply (pe : RoutePPrimitiveIndex) :
    routePPrimitiveBurnolBaseFieldLp pe = routePPrimitiveBurnolBaseField pe :=
  (Measure.ae_count_iff.mp memLp_two_routePPrimitiveBurnolBaseField.coeFn_toLp) pe

theorem hasSum_burnolBaseCoefficientSynthesis (x : LSource) :
    HasSum (fun pe => (x : RoutePPrimitiveIndex → ℂ) pe • routePPrimitiveBurnolBaseField pe)
      (burnolBaseCoefficientSynthesis x) := by
  let f : CSource := burnolBaseCountCoordinates.symm x
  have hint : Integrable (fun pe => f pe • routePPrimitiveBurnolBaseFieldLp pe) Measure.count :=
    memLp_one_iff_integrable.mp
      (MemLp.smul (𝕜 := ℂ) (p := 2) (q := 2) (r := 1)
        (Lp.memLp routePPrimitiveBurnolBaseFieldLp) (Lp.memLp f))
  have hs : Summable (fun pe => f pe • routePPrimitiveBurnolBaseFieldLp pe) :=
    Summable.of_norm (integrable_count_iff.mp hint)
  have hval : burnolBaseCoefficientSynthesis x =
      ∑' pe, f pe • routePPrimitiveBurnolBaseFieldLp pe := by
    change l2Synthesis Measure.count routePPrimitiveBurnolBaseFieldLp f = _
    rw [l2Synthesis_apply]
    simpa [measureReal_def] using! integral_countable hint
  rw [hval]
  simpa only [f, burnolBaseCountCoordinates_symm_apply, burnolBaseFieldLp_apply] using hs.hasSum

theorem burnolBaseCoefficientSynthesis_single (pe : RoutePPrimitiveIndex) (z : ℂ) :
    burnolBaseCoefficientSynthesis (lp.single 2 pe z) = z • routePPrimitiveBurnolBaseField pe := by
  rw [← (hasSum_burnolBaseCoefficientSynthesis (lp.single 2 pe z)).tsum_eq]
  simp [lp.single_apply, Pi.single_apply, ite_smul]

theorem isCompactOperator_burnolBaseCoefficientSynthesis :
    IsCompactOperator burnolBaseCoefficientSynthesis :=
  routePPrimitiveBurnolBaseSynthesis_isHilbertSchmidt.isCompactOperator.comp_clm _

/-- Exact source identity; the coordinate conversion introduces no new amplitude. -/
theorem burnolBaseCoefficientSynthesis_countCoordinates (f : CSource) :
    burnolBaseCoefficientSynthesis (burnolBaseCountCoordinates f) =
      routePPrimitiveBurnolBaseSynthesis f := by
  simp [burnolBaseCoefficientSynthesis]

end
end RHTower
