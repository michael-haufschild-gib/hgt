import GaloisForLFunctions.RHTower.Deninger.DeningerCycReassemble

/-!
# The base case of the cyclic reduction recursion

A word which is already cyclically reduced, or which is a single letter, is its own cyclically
reduced part, with empty conjugator and itself as tail.

* `deningerCycData_of_cycRed` : the base case.
-/

namespace RHTower

open Monoid Monoid.PushoutI Monoid.CoprodI

variable {ι : Type*} {G : ι → Type*} {H : Type*} [∀ i, Group (G i)] [Group H]
  {φ : ∀ i, H →* G i}

/-- **The base case.** -/
theorem deningerCycData_of_cycRed (L : List (Σ i, G i)) (hne : L ≠ [])
    (hred : ∀ p ∈ L, p.2 ∉ (φ p.1).range)
    (halt : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) L)
    (hyp : L.length ≤ 1 ∨ ∀ p ∈ L.getLast?, ∀ q ∈ L.head?, p.1 ≠ q.1) :
    ∃ C R V : List (Σ i, G i),
      L = C ++ R ∧ R ≠ [] ∧ V ≠ [] ∧
      (∀ p ∈ V, p.2 ∉ (φ p.1).range) ∧
      List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) V ∧
      V.head?.map Sigma.fst = R.head?.map Sigma.fst ∧
      deningerLetterProd (φ := φ) R =
        deningerLetterProd (φ := φ) V * (deningerLetterProd (φ := φ) C)⁻¹ ∧
      (V.length ≤ 1 ∨ ∀ p ∈ V.getLast?, ∀ q ∈ V.head?, p.1 ≠ q.1) :=
  ⟨[], L, L, by simp, hne, hne, hred, halt, rfl,
    by rw [deningerLetterProd_nil, inv_one, mul_one], hyp⟩

end RHTower
