import GaloisForLFunctions.HTGeometry.HasseFamily
import GaloisForLFunctions.HTGeometry.ObserverTimeFourierValuationAtlasLaw

/-!
# Positive-scale sinc Hasse principle

The response `sinc (τ a)` at all positive observation scales is a complete local profile of the
positive activation magnitude `a`.  Thus unequal magnitudes are separated by at least one positive
scale.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Positive observation scales form a Hasse family for positive sinc activation magnitudes. -/
noncomputable def positiveSincScaleHasseFamily :
    HasseFamily PositiveObservationPrefactor PositiveObservationPrefactor where
  Local _ := ℝ
  profile a τ := Real.sinc (τ.1 * a.1)
  profile_injective := by
    intro a b h
    apply Subtype.ext
    exact real_sinc_positive_scale_injective a.2 b.2 fun τ hτ =>
      congrFun h ⟨τ, hτ⟩

/-- Positive activation magnitudes agree exactly when every positive-scale sinc response agrees. -/
theorem positiveSincScale_congr_hasse_iff
    (a b : PositiveObservationPrefactor) :
    (∀ τ : PositiveObservationPrefactor,
      Real.sinc (τ.1 * a.1) = Real.sinc (τ.1 * b.1)) ↔ a = b :=
  positiveSincScaleHasseFamily.pointwise_eq_iff a b

/-- Unequal positive activation magnitudes are separated at one positive scale. -/
theorem positiveSincScale_ne_iff_exists_local_ne
    (a b : PositiveObservationPrefactor) :
    a ≠ b ↔ ∃ τ : PositiveObservationPrefactor,
      Real.sinc (τ.1 * a.1) ≠ Real.sinc (τ.1 * b.1) :=
  positiveSincScaleHasseFamily.ne_iff_exists_local_ne a b

end

end GaloisForLFunctions.HTGeometry
