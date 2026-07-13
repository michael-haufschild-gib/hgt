import Mathlib

/-!
# Finite commuting-shift peeling bridge

Abstract form of the many-shift rational-or-hypertranscendental dichotomy.  Given the one-shift
dichotomy — if a single shift-difference `Δ i f` lands in the rational class `R`, then `f` is
rational or hypertranscendental — together with downward descent of differential algebraicity
through shift-differences, any composite word of shift-differences that lands `f` in `R` forces `f`
itself to be rational or hypertranscendental.

The one-shift dichotomy is the Adamczewski–Dreyfus–Hardouin Laurent-series shift theorem; it enters
here as the hypothesis `dich`.  The descent `htDown` is the elementary closure of differential
algebraicity under shift-differences.  Everything else — the induction over the shift word — is
unconditional.
-/

namespace HTGeometry

variable {X : Type*} {n : ℕ}

/-- Composition of the shift-difference operators `Δ` indexed by a word `w`. -/
def shiftWord (Δ : Fin n → X → X) (w : List (Fin n)) (f : X) : X :=
  w.foldr (fun i g => Δ i g) f

@[simp] theorem shiftWord_nil (Δ : Fin n → X → X) (f : X) : shiftWord Δ [] f = f := rfl

@[simp] theorem shiftWord_cons (Δ : Fin n → X → X) (i : Fin n) (w : List (Fin n)) (f : X) :
    shiftWord Δ (i :: w) f = Δ i (shiftWord Δ w f) := rfl

/-- Differential algebraicity descends through shift-differences: if a shifted word of `f` is
hypertranscendental, so is `f`. -/
theorem ht_of_ht_shiftWord {Δ : Fin n → X → X} {H : X → Prop}
    (htDown : ∀ (i : Fin n) (g : X), H (Δ i g) → H g)
    (w : List (Fin n)) (f : X) (h : H (shiftWord Δ w f)) : H f := by
  induction w with
  | nil => simpa using h
  | cons i w ih =>
    rw [shiftWord_cons] at h
    exact ih (htDown i _ h)

/-- Finite commuting-shift peeling bridge.  Given the one-shift dichotomy (`Δ i g` rational forces
`g` rational or hypertranscendental) and downward descent of differential algebraicity, any word of
shift-differences that lands `f` in the rational class `R` forces `f` itself rational or
hypertranscendental. -/
theorem shiftWord_dichotomy {Δ : Fin n → X → X} {R H : X → Prop}
    (dich : ∀ (i : Fin n) (g : X), R (Δ i g) → R g ∨ H g)
    (htDown : ∀ (i : Fin n) (g : X), H (Δ i g) → H g)
    (w : List (Fin n)) (f : X) (h : R (shiftWord Δ w f)) : R f ∨ H f := by
  induction w with
  | nil => exact Or.inl (by simpa using h)
  | cons i w ih =>
    rw [shiftWord_cons] at h
    rcases dich i _ h with hg | hg
    · exact ih hg
    · exact Or.inr (ht_of_ht_shiftWord htDown w f hg)

end HTGeometry
