import GaloisForLFunctions.HTGeometry.PaperTerminatingCore
import GaloisForLFunctions.HTGeometry.PaperNativeInvariantLocalization

/-!
# Units and localization of the maximal terminating algebra

The proven unit rigidity of locally nilpotent derivations applies on the
entire terminating core. Its units are exactly ambient units fixed by the
original derivation. The inverse direction uses the ambient Leibniz rule,
so the classification does not require local nilpotence on the ambient ring.
-/

namespace GaloisForLFunctions.HTGeometry

open StableCoordinate

noncomputable section

attribute [local instance 2000] Algebra.toModule
attribute [local instance 2100] Semiring.toModule

variable {k A : Type*} [Field k] [CharZero k] [CommRing A] [IsDomain A] [Algebra k A]

local instance (D : Derivation k A A) : CharZero (paperTerminatingCore D) :=
  charZero_of_injective_algebraMap (algebraMap k (paperTerminatingCore D)).injective

/-- A core element is invertible precisely when it is an ambient invariant unit. -/
theorem paperTerminatingCore_isUnit_iff (D : Derivation k A A)
    (a : paperTerminatingCore D) :
    IsUnit a ↔ IsUnit (a : A) ∧ D (a : A) = 0 := by
  constructor
  · intro ha
    refine ⟨ha.map (paperTerminatingCore D).val, ?_⟩
    obtain ⟨u, hu⟩ := ha
    have h := paperLocallyNilpotent_kills_unit (k := k) (A := paperTerminatingCore D)
      (paperTerminatingClock D) (paperTerminatingClock_locallyNilpotent D) u
    rw [hu] at h
    exact congrArg Subtype.val h
  · rintro ⟨⟨u, hu⟩, ha⟩
    have hinv : D (↑u⁻¹ : A) = 0 := by
      change D u.inv = 0
      rw [D.leibniz_of_mul_eq_one u.inv_val, hu, ha, smul_zero]
    let b : paperTerminatingCore D :=
      ⟨(↑u⁻¹ : A), (paperTerminatingCore_mem_iff D _).mpr ⟨1, hinv⟩⟩
    refine ⟨⟨a, b, Subtype.ext ?_, Subtype.ext ?_⟩, rfl⟩
    · change (a : A) * (↑u⁻¹ : A) = 1
      rw [← hu]
      exact u.val_inv
    · change (↑u⁻¹ : A) * (a : A) = 1
      rw [← hu]
      exact u.inv_val

/-- An ambient unit and its inverse terminate together exactly when they are fixed. -/
theorem paperTerminatingCore_unit_and_inverse_iff (D : Derivation k A A) (u : Aˣ) :
    ((u : A) ∈ paperTerminatingCore D ∧ (↑u⁻¹ : A) ∈ paperTerminatingCore D) ↔
      D (u : A) = 0 := by
  constructor
  · rintro ⟨hu, hi⟩
    let v : (paperTerminatingCore D)ˣ :=
      ⟨⟨u, hu⟩, ⟨↑u⁻¹, hi⟩, Subtype.ext u.val_inv, Subtype.ext u.inv_val⟩
    exact ((paperTerminatingCore_isUnit_iff D (v : paperTerminatingCore D)).mp v.isUnit).2
  · intro h
    refine ⟨(paperTerminatingCore_mem_iff D _).mpr ⟨1, h⟩, ?_⟩
    apply (paperTerminatingCore_mem_iff D _).mpr
    refine ⟨1, ?_⟩
    change D u.inv = 0
    rw [D.leibniz_of_mul_eq_one u.inv_val, h, smul_zero]

/-- The core clock survives native localization exactly at invariant denominators. -/
theorem paperTerminatingCore_localization_iff (D : Derivation k A A)
    (a : paperTerminatingCore D) :
    IsLocallyNilpotent
      (paperNativeLocalization (S := Localization.Away a) (Submonoid.powers a)
        (paperTerminatingClock D)) ↔ D (a : A) = 0 := by
  have h := paperNativeAway_locallyNilpotent_iff (k := k) (A := paperTerminatingCore D)
    (paperTerminatingClock D) (paperTerminatingClock_locallyNilpotent D) a
  exact h.trans ⟨fun ha => congrArg Subtype.val ha, fun ha => Subtype.ext ha⟩

end

end GaloisForLFunctions.HTGeometry
