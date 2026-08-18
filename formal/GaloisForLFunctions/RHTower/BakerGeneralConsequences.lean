import GaloisForLFunctions.RHTower.BakerGeneralProof.BakerGeneralCapstone

/-!
# Consequences of the general Baker theorem

Restricting the `Option`-indexed independent family gives homogeneous independence of the
logarithms.  Adjoining `1` is what upgrades that to the transcendence of every nonzero
algebraic-coefficient linear form: an algebraic value of the form would be an algebraic
coefficient for the constant member of the family.
-/

open scoped Classical
open BigOperators

namespace GaloisForLFunctions.RHTower

/-- **Every nonzero algebraic linear form in `ℚ`-linearly independent logarithms of algebraic
numbers is transcendental.** -/
theorem baker_linearForm_transcendental
    {n : ℕ} (lambda : Fin n → ℂ) (beta : Fin n → ℂ)
    (halg : ∀ i, IsLogarithmOfAlgebraic (lambda i))
    (hind : LinearIndependent ℚ lambda)
    (hbeta : ∀ i, IsAlgebraic ℚ (beta i))
    (hne : ∃ i, beta i ≠ 0) :
    ¬ IsAlgebraic ℚ (∑ i, beta i * lambda i) := by
  intro hform
  have hfull := bakerTheorem_holds n lambda halg hind
  rw [Fintype.linearIndependent_iff] at hfull
  set L : ℂ := ∑ i, beta i * lambda i with hL
  let g : Option (Fin n) → algebraicClosure ℚ ℂ := fun j =>
    match j with
    | none => ⟨-L, mem_algebraicClosure_iff.mpr hform.neg⟩
    | some i => ⟨beta i, mem_algebraicClosure_iff.mpr (hbeta i)⟩
  have hsum : ∑ j : Option (Fin n), g j •
      (match j with | none => (1 : ℂ) | some i => lambda i) = 0 := by
    rw [Fintype.sum_option]
    have hnone : (g none : ℂ) = -L := rfl
    have hsome : ∀ i, (g (some i) : ℂ) = beta i := fun i => rfl
    simp only [IntermediateField.smul_def, smul_eq_mul, hnone, hsome, mul_one]
    rw [hL]
    ring
  obtain ⟨i, hi⟩ := hne
  apply hi
  have := hfull g hsum (some i)
  exact congrArg Subtype.val this

end GaloisForLFunctions.RHTower
