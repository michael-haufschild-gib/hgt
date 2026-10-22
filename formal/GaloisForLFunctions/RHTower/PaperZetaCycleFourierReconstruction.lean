import GaloisForLFunctions.HTGeometry.PaperFourierLiteralConvergence
import GaloisForLFunctions.RHTower.CCM.CCMConnesConsaniZetaCycles

/-! # Literal cycle traces from arithmetic Fourier coefficients

The paper endpoint reconstructs actual Connes--Consani cycle traces from the
existing ζ-times-Mellin coefficients. A single exceptional set covers countable
cap families, their prescribed scaling flows, and every finite complex mixture.
-/

namespace RHTower
noncomputable section
open MeasureTheory Filter Topology Set
open GaloisForLFunctions.HTGeometry
open scoped BigOperators SchwartzMap

/-- The symmetric arithmetic reconstruction, using only the native coefficient formula. -/
def paperZetaCycleArithmeticSum (L : CCMZetaCircleLength) (f : DeningerMeyerCap)
    (N : ℕ) (x : AddCircle (L : ℝ)) : ℂ :=
  ∑ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
    ((1 / (L : ℝ)) • (riemannZeta (ccmZetaCircleCriticalPoint L m) *
      mellin (f : 𝓢(ℝ, ℂ)) (ccmZetaCircleCriticalPoint L m))) * fourier m x

theorem paperZetaCycleArithmeticSum_eq (L : CCMZetaCircleLength)
    (f : DeningerMeyerCap) (N : ℕ) (x : AddCircle (L : ℝ)) :
    paperZetaCycleArithmeticSum L f N x =
      paperCircleFourierPartialSum (L : ℝ) (ccmZetaCycleTrace L f) N x := by
  simp only [paperZetaCycleArithmeticSum, paperCircleFourierPartialSum,
    fourierCoeff_ccmZetaCycleTrace_eq_zeta_mul_mellin]

/-- The entire symmetric sequence recovers the literal trace for a countable cap family. -/
theorem paperZetaCycle_common_reconstruction (L : CCMZetaCircleLength)
    {κ : Type*} [Countable κ] (f : κ → DeningerMeyerCap) :
    ∃ E : Set (AddCircle (L : ℝ)), MeasurableSet E ∧ AddCircle.haarAddCircle E = 0 ∧
      ∀ x ∉ E, ∀ j, Tendsto (fun N => paperZetaCycleArithmeticSum L (f j) N x)
        atTop (𝓝 (ccmZetaCycleTrace L (f j) x)) := by
  simpa [paperZetaCycleArithmeticSum_eq, ccmZetaCycleTraceContinuous] using
    paperCircleContinuous_common_convergence (L : ℝ)
      (fun j => ccmZetaCycleTraceContinuous L (f j))

/-- The exceptional set is chosen before every finite support and every complex weight. -/
theorem paperZetaCycle_common_span_reconstruction (L : CCMZetaCircleLength)
    {κ : Type*} [Countable κ] (f : κ → DeningerMeyerCap) :
    ∃ E : Set (AddCircle (L : ℝ)), MeasurableSet E ∧ AddCircle.haarAddCircle E = 0 ∧
      ∀ x ∉ E, ∀ (S : Finset κ) (c : κ → ℂ),
        Tendsto (fun N => ∑ j ∈ S, c j * paperZetaCycleArithmeticSum L (f j) N x)
          atTop (𝓝 (∑ j ∈ S, c j * ccmZetaCycleTrace L (f j) x)) := by
  obtain ⟨E, hm, hz, hc⟩ := paperZetaCycle_common_reconstruction L f
  exact ⟨E, hm, hz, fun x hx S c =>
    tendsto_finsetSum S (fun j _ => (hc x hx j).const_mul (c j))⟩

/-- Scaling flows are reconstructed simultaneously, including all finite mixtures of translates. -/
theorem paperZetaCycle_flow_common_span_reconstruction (L : CCMZetaCircleLength)
    {κ ι : Type*} [Countable κ] [Countable ι]
    (f : κ → DeningerMeyerCap) (a : ι → ℝ) :
    ∃ E : Set (AddCircle (L : ℝ)), MeasurableSet E ∧ AddCircle.haarAddCircle E = 0 ∧
      ∀ x ∉ E, ∀ (S : Finset (κ × ι)) (c : κ × ι → ℂ),
        Tendsto (fun N => ∑ j ∈ S, c j *
          paperZetaCycleArithmeticSum L (deningerMeyerCapFlow (a j.2) (f j.1)) N x)
          atTop (𝓝 (∑ j ∈ S, c j * ((Real.exp (a j.2 / 2) : ℝ) : ℂ) *
            ccmZetaCycleTrace L (f j.1) (x - (a j.2 : AddCircle (L : ℝ))))) := by
  simpa only [ccmZetaCycleTrace_capFlow, mul_assoc] using
    paperZetaCycle_common_span_reconstruction L
      (fun j : κ × ι => deningerMeyerCapFlow (a j.2) (f j.1))

end
end RHTower
