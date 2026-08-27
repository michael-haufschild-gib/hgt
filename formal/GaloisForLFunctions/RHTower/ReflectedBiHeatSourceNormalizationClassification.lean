import GaloisForLFunctions.RHTower.ReflectedBiHeatMultiplicityLeadingJetBalance

/-!
# Reflected bi-heat source-normalization classification

Every fixed linear reporter on the two reflected scale orders has reflection defect

`(a - b) * (Re z - 1/2)`.

Consequently its symmetric component is identically reflection-blind, while every nonzero
antisymmetric component is an exact critical-wall detector.  At the level of actual first
surviving Xi jets, any common nonzero source normalization cancels from norm balance and cannot
produce the missing equality.  This classifies fixed linear/common-scalar RBH normalizations:
they supply exact receivers but no unconditional producer.

`[NEW] [CLASSIFICATION] [NO-GO] [EXACT RECEIVER] [PAPER-PROVED] [LEAN-PROVED]`
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- Fixed linear reporter on the two reflected bi-heat scale orders. -/
def reflectedBiHeatLinearScaleReporter (a b : ℝ) (z : ℂ) : ℝ :=
  a * reflectedBiHeatLeftScaleOrder z + b * reflectedBiHeatRightScaleOrder z

/-- Reflection defect of every fixed linear scale reporter is its antisymmetric coefficient
times the centered real coordinate. -/
theorem reflectedBiHeatLinearScaleReporter_reflectionDefect
    (a b : ℝ) (z : ℂ) :
    reflectedBiHeatLinearScaleReporter a b z -
        reflectedBiHeatLinearScaleReporter a b (1 - z) =
      (a - b) * (z.re - 1 / 2) := by
  rw [reflectedBiHeatLinearScaleReporter,
    reflectedBiHeatLinearScaleReporter,
    reflectedBiHeat_scaleOrders_reflect_left,
    reflectedBiHeat_scaleOrders_reflect_right]
  rw [reflectedBiHeatLeftScaleOrder, reflectedBiHeatRightScaleOrder]
  ring

/-- Complete classification of equality locus of fixed linear reporter and its reflection. -/
theorem reflectedBiHeatLinearScaleReporter_eq_reflection_iff
    (a b : ℝ) (z : ℂ) :
    reflectedBiHeatLinearScaleReporter a b z =
        reflectedBiHeatLinearScaleReporter a b (1 - z) ↔
      a = b ∨ z.re = 1 / 2 := by
  calc
    reflectedBiHeatLinearScaleReporter a b z =
          reflectedBiHeatLinearScaleReporter a b (1 - z) ↔
        reflectedBiHeatLinearScaleReporter a b z -
            reflectedBiHeatLinearScaleReporter a b (1 - z) = 0 := sub_eq_zero.symm
    _ ↔ (a - b) * (z.re - 1 / 2) = 0 := by
      rw [reflectedBiHeatLinearScaleReporter_reflectionDefect]
    _ ↔ a - b = 0 ∨ z.re - 1 / 2 = 0 := mul_eq_zero
    _ ↔ a = b ∨ z.re = 1 / 2 := by rw [sub_eq_zero, sub_eq_zero]

/-- Every asymmetric fixed linear reporter is exact pointwise wall detector. -/
theorem reflectedBiHeatLinearScaleReporter_eq_reflection_iff_of_ne
    {a b : ℝ} (hab : a ≠ b) (z : ℂ) :
    reflectedBiHeatLinearScaleReporter a b z =
        reflectedBiHeatLinearScaleReporter a b (1 - z) ↔
      z.re = 1 / 2 := by
  rw [reflectedBiHeatLinearScaleReporter_eq_reflection_iff]
  simp [hab]

/-- Multiplying both actual multiplicity-leading channels by same nonzero source normalization
does not change their balance locus. -/
theorem reflectedBiHeatCommonNormalizedLeadingJetNorms_two_eq_iff
    (rho : XiDivisorSupport) (c : ℂ) (hc : c ≠ 0) :
    ‖c * iteratedDeriv (xiSupportMultiplicity rho)
          (reflectedBiHeatLeftResponse 2) (rho : ℂ)‖ =
        ‖c * iteratedDeriv (xiSupportMultiplicity rho)
          (reflectedBiHeatRightResponse 2) (rho : ℂ)‖ ↔
      (rho : ℂ).re = 1 / 2 := by
  rw [norm_mul, norm_mul]
  have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc
  constructor
  · intro h
    apply (reflectedBiHeatMultiplicityLeadingJetNorms_two_eq_iff rho).mp
    exact mul_left_cancel₀ hcpos.ne' h
  · intro hre
    rw [(reflectedBiHeatMultiplicityLeadingJetNorms_two_eq_iff rho).mpr hre]

/-- For asymmetric fixed source weights, reflection balance at every actual Xi divisor is exactly
RH.  Symmetric weights are excluded by classification because they are identically blind. -/
theorem riemannHypothesis_iff_reflectedBiHeatLinearScaleReporter_eq_reflection
    {a b : ℝ} (hab : a ≠ b) :
    RiemannHypothesis ↔
      ∀ rho : XiDivisorSupport,
        reflectedBiHeatLinearScaleReporter a b (rho : ℂ) =
          reflectedBiHeatLinearScaleReporter a b (1 - (rho : ℂ)) := by
  constructor
  · intro hRH rho
    exact (reflectedBiHeatLinearScaleReporter_eq_reflection_iff_of_ne hab (rho : ℂ)).mpr
      (xi_divisor_support_re_eq_half_of_rh hRH rho)
  · intro h
    exact riemannHypothesis_of_forall_xiDivisorSupport_re_eq_half fun rho =>
      (reflectedBiHeatLinearScaleReporter_eq_reflection_iff_of_ne hab (rho : ℂ)).mp (h rho)

end

end RHTower
