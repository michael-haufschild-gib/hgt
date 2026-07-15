import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Tactic.Ring

/-!
# Characters forced by multiplicative translation cocycles

An automorphism compatible with every translation can only rescale a nonvanishing multiplicative
translation cocycle by a character.  Conversely, scaling by a translation-fixed character preserves
the cocycle.  This is the abstract algebraic core of the elliptic-gamma holographic Galois
correspondence; it does not assert that every character extends to an automorphism of a concrete
meromorphic differential field.
-/

namespace GaloisForLFunctions

noncomputable section

/-- Scalars by which a translation-compatible automorphism acts on a nonvanishing
multiplicative translation cocycle obey the character law. -/
theorem multiplicativeTranslationCocycle_scalars_mul
    {A L : Type*} [AddCommGroup A] [Field L]
    (translation : A → L ≃+* L) (R : A → L) (gamma : L ≃+* L) (c : A → Lˣ)
    (hR : ∀ a, R a ≠ 0)
    (hcocycle : ∀ a b, R (a + b) = R a * translation a (R b))
    (hcomm : ∀ a x, gamma (translation a x) = translation a (gamma x))
    (hfixed : ∀ a b, translation a (c b : L) = c b)
    (hscale : ∀ a, gamma (R a) = (c a : L) * R a)
    (a b : A) : c (a + b) = c a * c b := by
  apply Units.ext
  apply mul_right_cancel₀ (hR (a + b))
  calc
    (c (a + b) : L) * R (a + b) = gamma (R (a + b)) := (hscale (a + b)).symm
    _ = gamma (R a * translation a (R b)) := by rw [← hcocycle a b]
    _ = gamma (R a) * gamma (translation a (R b)) := map_mul gamma _ _
    _ = ((c a : L) * R a) * translation a (gamma (R b)) := by
      rw [hscale a, hcomm a]
    _ = ((c a : L) * R a) * translation a ((c b : L) * R b) := by
      rw [hscale b]
    _ = ((c a : L) * R a) * ((c b : L) * translation a (R b)) := by
      rw [map_mul, hfixed a b]
    _ = ((c a * c b : Lˣ) : L) * R (a + b) := by
      rw [Units.val_mul, hcocycle]
      ring

/-- A character is constant on cosets of every subgroup on which it is trivial. -/
theorem multiplicativeCharacter_eq_of_sub_mem
    {A L : Type*} [AddCommGroup A] [Field L]
    (c : A → Lˣ) (hmul : ∀ a b, c (a + b) = c a * c b)
    (H : AddSubgroup A) (hH : ∀ h ∈ H, c h = 1)
    {a b : A} (hab : a - b ∈ H) : c a = c b := by
  have h := hmul (a - b) b
  rw [sub_add_cancel, hH (a - b) hab, one_mul] at h
  exact h

/-- Scaling a multiplicative translation cocycle by a translation-fixed character preserves its
cocycle law. -/
theorem characterScale_preserves_multiplicativeTranslationCocycle
    {A L : Type*} [AddCommGroup A] [Field L]
    (translation : A → L ≃+* L) (R : A → L) (c : A → Lˣ)
    (hcocycle : ∀ a b, R (a + b) = R a * translation a (R b))
    (hmul : ∀ a b, c (a + b) = c a * c b)
    (hfixed : ∀ a b, translation a (c b : L) = c b)
    (a b : A) :
    (c (a + b) : L) * R (a + b) =
      ((c a : L) * R a) * translation a ((c b : L) * R b) := by
  rw [hmul, Units.val_mul, hcocycle, map_mul, hfixed]
  ring

end

end GaloisForLFunctions
