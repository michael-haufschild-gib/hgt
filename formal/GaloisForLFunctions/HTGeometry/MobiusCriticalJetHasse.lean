import GaloisForLFunctions.HTGeometry.GammaCommonInverseCollar

/-!
# Hasse reconstruction from critical Möbius jets

The complete normalized derivative profile of a tangent Möbius germ determines its parameter.
This file packages that analytic local-to-global statement as an equivalence with the realized jet
range and an all-order Hasse congruence.  In this family the principle is stronger than expected:
the normalized derivative of order two already reconstructs the global chart.

This gives jet-based and analytic-continuation routes a lossless finite detector.  It does not prove
that an RH source family lies in this one-parameter Möbius class.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- Möbius parameters are equivalent to the complete critical-jet profiles they realize. -/
noncomputable def mobiusCriticalJetProfileHasseEquivRange :
    ℂ ≃ Set.range mobiusCriticalJetProfile :=
  Equiv.ofInjective mobiusCriticalJetProfile mobiusCriticalJetProfile_injective

@[simp]
theorem mobiusCriticalJetProfileHasseEquivRange_apply (a : ℂ) :
    (mobiusCriticalJetProfileHasseEquivRange a : ℕ → ℂ) =
      mobiusCriticalJetProfile a := rfl

/-- Two Möbius charts agree exactly when all normalized critical jets agree. -/
theorem mobiusCriticalJet_congr_hasse_iff (a b : ℂ) :
    a = b ↔ ∀ k : ℕ, mobiusCriticalJetProfile a k = mobiusCriticalJetProfile b k := by
  constructor
  · rintro rfl
    exact fun _ ↦ rfl
  · intro h
    exact mobiusCriticalJetProfile_injective (funext h)

/-- The normalized second derivative alone reconstructs a tangent Möbius chart. -/
theorem mobiusCriticalJet_congr_secondOrder_hasse_iff (a b : ℂ) :
    a = b ↔ mobiusCriticalJetProfile a 1 = mobiusCriticalJetProfile b 1 := by
  simp

/-- Vanishing of the normalized second derivative detects the zero Möbius parameter. -/
theorem mobiusCriticalJet_eq_zero_secondOrder_hasse_iff (a : ℂ) :
    a = 0 ↔ mobiusCriticalJetProfile a 1 = 0 := by
  simp

/-- Distinct tangent Möbius charts already separate at normalized derivative order two. -/
theorem mobiusCriticalJet_secondOrder_ne_of_ne {a b : ℂ} (hab : a ≠ b) :
    mobiusCriticalJetProfile a 1 ≠ mobiusCriticalJetProfile b 1 := by
  exact fun h ↦ hab ((mobiusCriticalJet_congr_secondOrder_hasse_iff a b).2 h)

end GaloisForLFunctions.HTGeometry
