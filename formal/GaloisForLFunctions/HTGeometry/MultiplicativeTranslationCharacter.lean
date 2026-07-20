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

/-- **Zero-or-nowhere-zero law for multiplicative translation cocycles.** A cocycle valued in a
field and transported by field automorphisms is either identically zero or nonzero at every
translation parameter. If its value at zero vanishes, the cocycle law at `(0,a)` kills every
value; if it does not, the law at `(a,-a)` prevents any value from vanishing. No action law for
the family of translations is needed. -/
theorem multiplicativeTranslationCocycle_eq_zero_or_forall_ne_zero
    {A L : Type*} [AddCommGroup A] [Field L]
    (translation : A → L ≃+* L) (R : A → L)
    (hcocycle : ∀ a b, R (a + b) = R a * translation a (R b)) :
    (∀ a, R a = 0) ∨ ∀ a, R a ≠ 0 := by
  by_cases h0 : R 0 = 0
  · left
    intro a
    simpa [h0] using hcocycle 0 a
  · right
    intro a ha
    have h := hcocycle a (-a)
    rw [add_neg_cancel, ha, zero_mul] at h
    exact h0 h

/-- A single nonzero cocycle value forces global nonvanishing. This is the useful Prop interface
of the zero-or-nowhere-zero dichotomy. -/
theorem multiplicativeTranslationCocycle_forall_ne_zero_of_exists
    {A L : Type*} [AddCommGroup A] [Field L]
    (translation : A → L ≃+* L) (R : A → L)
    (hcocycle : ∀ a b, R (a + b) = R a * translation a (R b))
    (hR : ∃ a, R a ≠ 0) :
    ∀ a, R a ≠ 0 := by
  rcases multiplicativeTranslationCocycle_eq_zero_or_forall_ne_zero
      translation R hcocycle with hzero | hne
  · obtain ⟨a, ha⟩ := hR
    exact (ha (hzero a)).elim
  · exact hne

/-- Scalars by which a translation-compatible automorphism acts on a multiplicative translation
cocycle obey the character law at `a,b` as soon as the single value `R (a+b)` is nonzero. No
global nonvanishing hypothesis on the cocycle is needed. This pointwise premise is sharp: if the
value being cancelled vanishes, the scaling relation contains no information about the scalar. -/
theorem multiplicativeTranslationCocycle_scalars_mul
    {A L : Type*} [AddCommGroup A] [Field L]
    (translation : A → L ≃+* L) (R : A → L) (gamma : L ≃+* L) (c : A → Lˣ)
    (hcocycle : ∀ a b, R (a + b) = R a * translation a (R b))
    (hcomm : ∀ a x, gamma (translation a x) = translation a (gamma x))
    (hfixed : ∀ a b, translation a (c b : L) = c b)
    (hscale : ∀ a, gamma (R a) = (c a : L) * R a)
    (a b : A) (hR : R (a + b) ≠ 0) : c (a + b) = c a * c b := by
  apply Units.ext
  apply mul_right_cancel₀ hR
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

/-- **A nontrivial multiplicative cocycle forces a global scalar character.** One nonzero value of
`R` is enough: the cocycle dichotomy supplies every pointwise nonvanishing premise, so the scaling
units multiply at all parameter pairs. -/
theorem multiplicativeTranslationCocycle_scalars_mul_of_exists_ne_zero
    {A L : Type*} [AddCommGroup A] [Field L]
    (translation : A → L ≃+* L) (R : A → L) (gamma : L ≃+* L) (c : A → Lˣ)
    (hcocycle : ∀ a b, R (a + b) = R a * translation a (R b))
    (hcomm : ∀ a x, gamma (translation a x) = translation a (gamma x))
    (hfixed : ∀ a b, translation a (c b : L) = c b)
    (hscale : ∀ a, gamma (R a) = (c a : L) * R a)
    (hR : ∃ a, R a ≠ 0) :
    ∀ a b, c (a + b) = c a * c b := by
  have hne := multiplicativeTranslationCocycle_forall_ne_zero_of_exists
    translation R hcocycle hR
  intro a b
  exact multiplicativeTranslationCocycle_scalars_mul
    translation R gamma c hcocycle hcomm hfixed hscale a b (hne (a + b))

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
