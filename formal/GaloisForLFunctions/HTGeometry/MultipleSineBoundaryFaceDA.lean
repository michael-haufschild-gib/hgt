import GaloisForLFunctions.HTGeometry.MultipleSineOrderOneSourceDA
import GaloisForLFunctions.HTGeometry.MultipleSineFacePacket

/-!
# Boundary face packets are differentially algebraic

A face retaining at most one period is below the hypertranscendental range: its packet is either
empty or consists of translates of the order-one source, which is a period cotangent up to a
rational function and hence differentially algebraic over the constants.
-/

open Filter Set Topology Complex
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

attribute [local instance] relativeGaugeDomain relativeGaugeDifferential
  relativeGaugeRatFuncAlgebra relativeGaugeRatFuncDifferential relativeGaugeDifferentialAlgebra
  relativeGaugeCharZeroBase relativeGaugeCharZero relativeGaugeComplexAlgebra
  relativeGaugeComplexAlgebraAnalytic

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **The packet of a face retaining one period is differentially algebraic.** -/
theorem differentialAlgebraicOver_facePacket_of_compl_card_one (ω : ι → ℂ)
    (hω : ∀ k, 0 < (ω k).im) {L : Finset ι} (hL : (Lᶜ : Finset ι).card = 1)
    {y : meroField (Set.univ : Set ℂ)} (hy : y ∈ facePacket ω hω L) :
    DifferentialAlgebraicOver ℂ y := by
  classical
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hL
  have hne : (Lᶜ : Finset ι).Nonempty := ⟨a, by rw [ha]; simp⟩
  have hsingle : ({a} : Finset ι).Nonempty := ⟨a, by simp⟩
  have hsrc : frameSourceMero ω hω (Lᶜ : Finset ι) hne
      = frameSourceMero ω hω ({a} : Finset ι) hsingle :=
    frameSourceMero_congr ω hω ha hne hsingle
  rw [facePacket_eq ω hω hne] at hy
  obtain ⟨α, rfl⟩ := hy
  rw [hsrc]
  refine differentialAlgebraicOver_complex_of_ratFunc ?_
  exact differentialAlgebraicOver_addTranslationMeroEquiv _
    (differentialAlgebraicOver_frameSourceMero_singleton ω hω a hsingle)

/-- **Every boundary face packet is differentially algebraic.** -/
theorem differentialAlgebraicOver_facePacket_of_compl_lt_two (ω : ι → ℂ)
    (hω : ∀ k, 0 < (ω k).im) {L : Finset ι} (hL : (Lᶜ : Finset ι).card < 2)
    {y : meroField (Set.univ : Set ℂ)} (hy : y ∈ facePacket ω hω L) :
    DifferentialAlgebraicOver ℂ y := by
  classical
  by_cases h0 : (Lᶜ : Finset ι).card = 0
  · have hempty : ¬ (Lᶜ : Finset ι).Nonempty := by
      rw [← Finset.card_pos, h0]
      omega
    rw [facePacket, dif_neg hempty] at hy
    exact absurd hy (Set.notMem_empty _)
  · exact differentialAlgebraicOver_facePacket_of_compl_card_one ω hω (by omega) hy

end

end GaloisForLFunctions.HTGeometry
