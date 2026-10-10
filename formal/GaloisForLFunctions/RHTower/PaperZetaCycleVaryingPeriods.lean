import GaloisForLFunctions.RHTower.PaperZetaCycleFourierReconstruction
import GaloisForLFunctions.HTGeometry.PaperFourierCircleTransport

/-! # Simultaneous arithmetic reconstruction across varying cycle periods

Rescaling each orbit to the unit circle retains its exact ζ-times-Mellin
coefficients. Countably many periods and caps share one exceptional set.
-/

namespace RHTower
noncomputable section
open MeasureTheory Filter Topology Set
open GaloisForLFunctions.HTGeometry
open scoped BigOperators SchwartzMap

/-- The literal orbit trace expressed at unit-circle phase. -/
def paperZetaCycleUnitTrace (L : CCMZetaCircleLength) (f : DeningerMeyerCap) :
    C(UnitAddCircle, ℂ) :=
  ⟨fun x => ccmZetaCycleTrace L f (paperCircleRescale 1 (L : ℝ) x),
    (continuous_ccmZetaCycleTrace L f).comp (paperCircleRescale 1 (L : ℝ)).continuous⟩

/-- Arithmetic coefficients retain their original period-dependent normalization. -/
def paperZetaCycleUnitArithmeticSum (L : CCMZetaCircleLength) (f : DeningerMeyerCap)
    (N : ℕ) (x : UnitAddCircle) : ℂ :=
  ∑ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
    ((1 / (L : ℝ)) • (riemannZeta (ccmZetaCircleCriticalPoint L m) *
      mellin (f : 𝓢(ℝ, ℂ)) (ccmZetaCircleCriticalPoint L m))) * fourier m x

theorem paperZetaCycleUnitTrace_fourierCoeff (L : CCMZetaCircleLength)
    (f : DeningerMeyerCap) (m : ℤ) :
    fourierCoeff (paperZetaCycleUnitTrace L f) m =
      fourierCoeff (ccmZetaCycleTrace L f) m :=
  fourierCoeff_paperCircleRescale 1 (L : ℝ) (ccmZetaCycleTrace L f) m

theorem paperZetaCycleUnitArithmeticSum_rescale (L : CCMZetaCircleLength)
    (f : DeningerMeyerCap) (N : ℕ) (x : UnitAddCircle) :
    paperZetaCycleUnitArithmeticSum L f N x =
      paperZetaCycleArithmeticSum L f N (paperCircleRescale 1 (L : ℝ) x) := by
  simp only [paperZetaCycleUnitArithmeticSum, paperZetaCycleArithmeticSum,
    fourier_paperCircleRescale]

theorem paperZetaCycleUnitArithmeticSum_eq (L : CCMZetaCircleLength)
    (f : DeningerMeyerCap) (N : ℕ) (x : UnitAddCircle) :
    paperZetaCycleUnitArithmeticSum L f N x =
      paperCircleFourierPartialSum 1 (paperZetaCycleUnitTrace L f) N x := by
  simp only [paperZetaCycleUnitArithmeticSum, paperCircleFourierPartialSum,
    paperZetaCycleUnitTrace_fourierCoeff,
    fourierCoeff_ccmZetaCycleTrace_eq_zeta_mul_mellin]

/-- A common physical height corresponds to the period-dependent phase `t / L`. -/
theorem paperZetaCycleUnitTrace_physical_height (L : CCMZetaCircleLength)
    (f : DeningerMeyerCap) (t : ℝ) :
    paperZetaCycleUnitTrace L f ((t / (L : ℝ) : ℝ) : UnitAddCircle) =
      ccmZetaCycleTrace L f (t : AddCircle (L : ℝ)) := by
  change ccmZetaCycleTrace L f
    (((t / (L : ℝ)) * ((1 : ℝ)⁻¹ * (L : ℝ)) : ℝ) : AddCircle (L : ℝ)) = _
  simp [L.property.ne']

/-- One null set works before selecting a period, cap, or finite complex mixture. -/
theorem paperZetaCycle_varying_periods_common_reconstruction
    {κ : Type*} [Countable κ] (L : κ → CCMZetaCircleLength)
    (f : κ → DeningerMeyerCap) :
    ∃ E : Set UnitAddCircle, MeasurableSet E ∧ AddCircle.haarAddCircle E = 0 ∧
      ∀ x ∉ E, ∀ j,
        Tendsto (fun N => paperZetaCycleUnitArithmeticSum (L j) (f j) N x)
          atTop (𝓝 (paperZetaCycleUnitTrace (L j) (f j) x)) := by
  simpa only [paperZetaCycleUnitArithmeticSum_eq] using
    paperCircleContinuous_common_convergence 1
      (fun j => paperZetaCycleUnitTrace (L j) (f j))

theorem paperZetaCycle_varying_periods_common_span_reconstruction
    {κ : Type*} [Countable κ] (L : κ → CCMZetaCircleLength)
    (f : κ → DeningerMeyerCap) :
    ∃ E : Set UnitAddCircle, MeasurableSet E ∧ AddCircle.haarAddCircle E = 0 ∧
      ∀ x ∉ E, ∀ (S : Finset κ) (c : κ → ℂ),
        Tendsto (fun N => ∑ j ∈ S, c j * paperZetaCycleUnitArithmeticSum (L j) (f j) N x)
          atTop (𝓝 (∑ j ∈ S, c j * paperZetaCycleUnitTrace (L j) (f j) x)) := by
  obtain ⟨E, hm, hz, hc⟩ := paperZetaCycle_varying_periods_common_reconstruction L f
  exact ⟨E, hm, hz, fun x hx S c =>
    tendsto_finsetSum S (fun j _ => (hc x hx j).const_mul (c j))⟩

/-- Prescribed countable flows share the same exceptional set across all periods. -/
theorem paperZetaCycle_varying_periods_flow_common_span_reconstruction
    {κ ι : Type*} [Countable κ] [Countable ι]
    (L : κ → CCMZetaCircleLength) (f : κ → DeningerMeyerCap) (a : ι → ℝ) :
    ∃ E : Set UnitAddCircle, MeasurableSet E ∧ AddCircle.haarAddCircle E = 0 ∧
      ∀ x ∉ E, ∀ (S : Finset (κ × ι)) (c : κ × ι → ℂ),
        Tendsto (fun N => ∑ j ∈ S, c j * paperZetaCycleUnitArithmeticSum (L j.1)
          (deningerMeyerCapFlow (a j.2) (f j.1)) N x)
          atTop (𝓝 (∑ j ∈ S, c j * ((Real.exp (a j.2 / 2) : ℝ) : ℂ) *
            ccmZetaCycleTrace (L j.1) (f j.1)
              (paperCircleRescale 1 (L j.1 : ℝ) x - (a j.2 : AddCircle (L j.1 : ℝ))))) := by
  simpa only [paperZetaCycleUnitTrace, ContinuousMap.coe_mk,
    ccmZetaCycleTrace_capFlow, mul_assoc] using
    paperZetaCycle_varying_periods_common_span_reconstruction
      (fun j : κ × ι => L j.1) (fun j => deningerMeyerCapFlow (a j.2) (f j.1))

end
end RHTower
