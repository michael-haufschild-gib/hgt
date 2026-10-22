import GaloisForLFunctions.RHTower.Deninger.DeningerKummerReciprocityQuotient

/-!
# Placewise Hasse principle for reciprocal Kummer currents

The product-formula current of a number-field unit determines its class modulo roots of unity.
Here that bundled injectivity is sharpened to a literal placewise Hasse principle: two Kummer
classes agree exactly when their current values agree at every place, and every nontrivial class is
detected at one place.  Every current already known to be globally realized has a unique global
Kummer ancestor.

This is the injective and realized-range part of a Kummer local--global classification.  It does not
assert that every sum-zero local current is globally realized.
-/

namespace RHTower

noncomputable section

/-- Additive local current carried by a global Kummer class modulo roots of unity. -/
noncomputable def deningerKummerQuotientLocalCurrent
    (K : Type*) [Field K] [NumberField K] (x : deningerKummerGroup K) :
    LinearMap.ker (deningerPlaceSum K) :=
  Multiplicative.toAdd (deningerKummerReciprocityQuotientHom K x)

@[simp] theorem deningerKummerQuotientLocalCurrent_one
    (K : Type*) [Field K] [NumberField K] :
    deningerKummerQuotientLocalCurrent K (1 : deningerKummerGroup K) = 0 := by
  unfold deningerKummerQuotientLocalCurrent
  rw [map_one]
  rfl

/-- Value of a quotient Kummer current at one place. -/
noncomputable def deningerKummerQuotientLocalValue
    (K : Type*) [Field K] [NumberField K] (x : deningerKummerGroup K)
    (v : DeningerPlace K) : ℝ :=
  deningerKummerQuotientLocalCurrent K x |>.1.1 v

@[simp] theorem deningerKummerQuotientLocalValue_one
    (K : Type*) [Field K] [NumberField K] (v : DeningerPlace K) :
    deningerKummerQuotientLocalValue K (1 : deningerKummerGroup K) v = 0 := by
  rw [deningerKummerQuotientLocalValue,
    deningerKummerQuotientLocalCurrent_one]
  rfl

/-- Placewise Hasse congruence for global units modulo roots of unity. -/
theorem deningerKummerQuotient_congr_placewise_hasse_iff
    (K : Type*) [Field K] [NumberField K] (x y : deningerKummerGroup K) :
    x = y ↔ ∀ v : DeningerPlace K,
      deningerKummerQuotientLocalValue K x v =
        deningerKummerQuotientLocalValue K y v := by
  constructor
  · rintro rfl
    exact fun _ ↦ rfl
  · intro h
    apply deningerKummerReciprocityQuotientHom_injective K
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    apply Subtype.ext
    funext v
    exact h v

/-- A Kummer class is trivial exactly when every local logarithmic current vanishes. -/
theorem deningerKummerQuotient_eq_one_placewise_hasse_iff
    (K : Type*) [Field K] [NumberField K] (x : deningerKummerGroup K) :
    x = 1 ↔ ∀ v : DeningerPlace K,
      deningerKummerQuotientLocalValue K x v = 0 := by
  rw [deningerKummerQuotient_congr_placewise_hasse_iff]
  simp

/-- Every nontrivial global Kummer class is detected at one place. -/
theorem exists_deningerPlace_current_ne_zero_of_kummerQuotient_ne_one
    (K : Type*) [Field K] [NumberField K] (x : deningerKummerGroup K)
    (hx : x ≠ 1) :
    ∃ v : DeningerPlace K, deningerKummerQuotientLocalValue K x v ≠ 0 := by
  by_contra h
  push Not at h
  exact hx ((deningerKummerQuotient_eq_one_placewise_hasse_iff K x).2 h)

/-- Every globally realized reciprocal local current has one unique global Kummer class. -/
theorem deningerKummerRealizedCurrent_existsUnique_global
    (K : Type*) [Field K] [NumberField K]
    (c : MonoidHom.mrange (deningerKummerReciprocityQuotientHom K)) :
    ∃! x : deningerKummerGroup K,
      deningerKummerReciprocityQuotientHom K x = c.1 := by
  obtain ⟨x, hx⟩ := c.2
  refine ⟨x, hx, ?_⟩
  intro y hy
  exact deningerKummerReciprocityQuotientHom_injective K (hy.trans hx.symm)

end

end RHTower
