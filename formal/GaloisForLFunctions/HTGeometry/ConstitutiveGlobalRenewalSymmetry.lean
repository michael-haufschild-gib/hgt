import GaloisForLFunctions.HTGeometry.ConstitutiveCofinalRenewalGeometry

/-!
# Global-renewal symmetry neutrality

A measurable involution is packaged as a measurable equivalence.  If it preserves the baseline
law and the formation-height observable, it preserves both global KL action and renewed height
expectation exactly.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Real InformationTheory

noncomputable section

variable {X : Type*} [MeasurableSpace X]

/-- A measurable involution as a measurable self-equivalence. -/
def measurableEquivOfInvolution (R : X → X) (hR : Measurable R)
    (hinv : Function.Involutive R) : X ≃ᵐ X where
  toEquiv :=
    { toFun := R
      invFun := R
      left_inv := hinv
      right_inv := hinv }
  measurable_toFun := hR
  measurable_invFun := hR

/-- A baseline-preserving measurable involution is an exact global-KL isometry. -/
theorem klDiv_map_involution_eq
    (mu nu : Measure X) [IsFiniteMeasure mu] [IsFiniteMeasure nu]
    (R : X → X) (hR : Measurable R) (hinv : Function.Involutive R)
    (hmu : mu.map R = mu) :
    klDiv (nu.map R) mu = klDiv nu mu := by
  calc
    klDiv (nu.map R) mu = klDiv (nu.map R) (mu.map R) := by rw [hmu]
    _ = klDiv nu mu := by
      simpa [measurableEquivOfInvolution] using
        klDiv_map_measurableEmbedding
          (measurableEquivOfInvolution R hR hinv).measurableEmbedding nu mu

/-- A pointwise invariant height has exactly invariant expectation under measurable reversal. -/
theorem integral_map_involution_eq
    (nu : Measure X) (R : X → X) (hR : Measurable R)
    (N : X → ℝ) (hN : Measurable N) (hNR : ∀ x, N (R x) = N x) :
    (∫ x, N x ∂nu.map R) = ∫ x, N x ∂nu := by
  rw [integral_map hR.aemeasurable hN.aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards with x
  exact hNR x

/-- `(GRG.20)`--`(GRG.21)`: functional-equation reversal is simultaneously action-neutral and
height-neutral. -/
theorem globalRenewal_involution_action_height_invariant
    (mu nu : Measure X) [IsFiniteMeasure mu] [IsFiniteMeasure nu]
    (R : X → X) (hR : Measurable R) (hinv : Function.Involutive R)
    (hmu : mu.map R = mu)
    (N : X → ℝ) (hN : Measurable N) (hNR : ∀ x, N (R x) = N x) :
    klDiv (nu.map R) mu = klDiv nu mu ∧
      (∫ x, N x ∂nu.map R) = ∫ x, N x ∂nu :=
  ⟨klDiv_map_involution_eq mu nu R hR hinv hmu,
    integral_map_involution_eq nu R hR N hN hNR⟩

end

end GaloisForLFunctions.HTGeometry
