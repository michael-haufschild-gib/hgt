import GaloisForLFunctions.HTGeometry.PaperCirclePhysicalHeight
import GaloisForLFunctions.RHTower.PaperZetaCycleFourierReconstruction

/-! # Arithmetic reconstruction at a shared physical height

The varying orbit periods are retained. Outside one Lebesgue-null set, every
trace in a countable family is reconstructed at the same real height, together
with every finite complex mixture and every prescribed countable scaling flow.
-/

namespace RHTower
noncomputable section
open MeasureTheory Filter Topology Set
open GaloisForLFunctions.HTGeometry
open scoped BigOperators

theorem paperZetaCycle_common_physical_reconstruction
    {κ : Type*} [Countable κ] (L : κ → CCMZetaCircleLength)
    (f : κ → DeningerMeyerCap) :
    ∃ E : Set ℝ, MeasurableSet E ∧ volume E = 0 ∧
      ∀ t ∉ E, ∀ j,
        Tendsto (fun N => paperZetaCycleArithmeticSum (L j) (f j) N (t : AddCircle (L j : ℝ)))
          atTop (𝓝 (ccmZetaCycleTrace (L j) (f j) (t : AddCircle (L j : ℝ)))) := by
  simpa only [paperZetaCycleArithmeticSum_eq, ccmZetaCycleTraceContinuous,
    ContinuousMap.coe_mk] using
    paperCircleContinuous_common_physical_convergence (fun j => (L j : ℝ))
      (fun j => ccmZetaCycleTraceContinuous (L j) (f j))

theorem paperZetaCycle_common_physical_span_reconstruction
    {κ : Type*} [Countable κ] (L : κ → CCMZetaCircleLength)
    (f : κ → DeningerMeyerCap) :
    ∃ E : Set ℝ, MeasurableSet E ∧ volume E = 0 ∧
      ∀ t ∉ E, ∀ (S : Finset κ) (c : κ → ℂ),
        Tendsto (fun N => ∑ j ∈ S, c j *
          paperZetaCycleArithmeticSum (L j) (f j) N (t : AddCircle (L j : ℝ)))
          atTop (𝓝 (∑ j ∈ S, c j * ccmZetaCycleTrace (L j) (f j)
            (t : AddCircle (L j : ℝ)))) := by
  obtain ⟨E, hm, hz, hc⟩ := paperZetaCycle_common_physical_reconstruction L f
  exact ⟨E, hm, hz, fun t ht S c =>
    tendsto_finsetSum S (fun j _ => (hc t ht j).const_mul (c j))⟩

/-- At shared height, the native cap flow translates by the same real amount. -/
theorem paperZetaCycle_flow_common_physical_span_reconstruction
    {κ ι : Type*} [Countable κ] [Countable ι]
    (L : κ → CCMZetaCircleLength) (f : κ → DeningerMeyerCap) (a : ι → ℝ) :
    ∃ E : Set ℝ, MeasurableSet E ∧ volume E = 0 ∧
      ∀ t ∉ E, ∀ (S : Finset (κ × ι)) (c : κ × ι → ℂ),
        Tendsto (fun N => ∑ j ∈ S, c j * paperZetaCycleArithmeticSum (L j.1)
          (deningerMeyerCapFlow (a j.2) (f j.1)) N (t : AddCircle (L j.1 : ℝ)))
          atTop (𝓝 (∑ j ∈ S, c j * ((Real.exp (a j.2 / 2) : ℝ) : ℂ) *
            ccmZetaCycleTrace (L j.1) (f j.1) ((t - a j.2 : ℝ) : AddCircle (L j.1 : ℝ)))) := by
  simpa only [ccmZetaCycleTrace_capFlow, mul_assoc, AddCircle.coe_sub] using
    paperZetaCycle_common_physical_span_reconstruction
      (fun j : κ × ι => L j.1) (fun j => deningerMeyerCapFlow (a j.2) (f j.1))

end
end RHTower
