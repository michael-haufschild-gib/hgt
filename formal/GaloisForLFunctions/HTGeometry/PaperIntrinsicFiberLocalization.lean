import GaloisForLFunctions.HTGeometry.PaperNativeInvariantLocalization
import GaloisForLFunctions.HTGeometry.PaperIntrinsicFiberClocks

/-!
# Localization of the complete intrinsic clock frame

On every actual scalar fibre of the source polynomial, the three intrinsic
clocks survive a principal localization as locally nilpotent derivations
simultaneously exactly when its denominator is a complex scalar. Inverting
one intrinsic coordinate preserves precisely the other two clocks.
-/

namespace GaloisForLFunctions.HTGeometry

open StableCoordinate

noncomputable section

local instance fiberLocalizationDomain (t : ℂ) : IsDomain (FiberRing t) :=
  Function.Injective.isDomain (exactFiberEquiv t).toRingHom (exactFiberEquiv t).injective

local instance fiberLocalizationCharZero (t : ℂ) : CharZero (FiberRing t) :=
  ⟨fun m n h => Nat.cast_injective
    (by simpa only [map_natCast] using congrArg (exactFiberEquiv t) h)⟩

/-- Native quotient-rule extension of each actual intrinsic clock. -/
def paperIntrinsicLocalizedClock (t : ℂ) (i : Fin 3) (a : FiberRing t) :
    Derivation ℂ (Localization.Away a) (Localization.Away a) :=
  paperNativeLocalization (Submonoid.powers a) (paperIntrinsicFiberClock t i)

/-- The exact denominator criterion holds on every scalar fibre. -/
theorem paperIntrinsicLocalizedClock_iff (t : ℂ) (i : Fin 3) (a : FiberRing t) :
    IsLocallyNilpotent (paperIntrinsicLocalizedClock t i a) ↔
      paperIntrinsicFiberClock t i a = 0 :=
  paperNativeAway_locallyNilpotent_iff (paperIntrinsicFiberClock t i)
    (paperIntrinsicFiberClock_locallyNilpotent t i) a

/-- Only scalar denominators preserve the entire locally nilpotent clock frame. -/
theorem paperIntrinsicLocalizedClocks_all_iff (t : ℂ) (a : FiberRing t) :
    (∀ i, IsLocallyNilpotent (paperIntrinsicLocalizedClock t i a)) ↔
      ∃ c : ℂ, a = algebraMap ℂ (FiberRing t) c := by
  simp only [paperIntrinsicLocalizedClock_iff]
  exact paperIntrinsicFiberClock_common_kernel t a

/-- Inverting one coordinate preserves exactly the two transverse clocks. -/
theorem paperIntrinsicLocalizedClock_coordinate_iff (t : ℂ) (i j : Fin 3) :
    IsLocallyNilpotent
      (paperIntrinsicLocalizedClock t i (paperIntrinsicFiberCoordinate t j)) ↔ i ≠ j := by
  rw [paperIntrinsicLocalizedClock_iff, paperIntrinsicFiberClock_coordinate]
  simp

/-- Every nonconstant denominator destroys at least one clock's local nilpotence. -/
theorem paperIntrinsicLocalizedClocks_failure_iff (t : ℂ) (a : FiberRing t) :
    (∃ i, ¬ IsLocallyNilpotent (paperIntrinsicLocalizedClock t i a)) ↔
      ∀ c : ℂ, a ≠ algebraMap ℂ (FiberRing t) c := by
  have h := not_congr (paperIntrinsicLocalizedClocks_all_iff t a)
  push Not at h
  exact h

/-- The preceding failure is an actual nonterminating orbit of a native derivation. -/
theorem paperIntrinsicLocalizedClocks_nontermination_iff (t : ℂ) (a : FiberRing t) :
    (∃ i, ∃ z : Localization.Away a, ∀ n : ℕ,
      ((paperIntrinsicLocalizedClock t i a)^[n]) z ≠ 0) ↔
        ∀ c : ℂ, a ≠ algebraMap ℂ (FiberRing t) c := by
  have h := paperIntrinsicLocalizedClocks_failure_iff t a
  unfold IsLocallyNilpotent at h
  push Not at h
  exact h

end

end GaloisForLFunctions.HTGeometry
