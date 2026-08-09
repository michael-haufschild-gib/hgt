import GaloisForLFunctions.HTGeometry.NonidentityPauliWordCount

/-!
# The diagonal `Z` strings of a qubit register

The `Z` string supported on a set of qubits is diagonal in the computational basis, with the sign
determined by the parity of the occupied sites inside its support.  Its weight is the size of that
support, and distinct supports give distinct strings.

These are the terms of the diagonal centre of a fixed-locality Pauli ensemble.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {n : ℕ}

/-- The `Z` string supported on a set of qubits. -/
def pauliZSetLabel (S : Finset (Fin n)) : Fin n → Option (Fin 3) :=
  fun s => if s ∈ S then some 2 else none

/-- The diagonal sign a `Z` string assigns to a computational configuration. -/
def zSetSign (S : Finset (Fin n)) (x : Fin n → Bool) : ℝ :=
  ∏ s ∈ S, (if x s then (-1 : ℝ) else 1)

@[simp] theorem pauliSupport_pauliZSetLabel (S : Finset (Fin n)) :
    pauliSupport (pauliZSetLabel S) = S := by
  ext s
  simp [pauliZSetLabel]

theorem pauliWeight_pauliZSetLabel (S : Finset (Fin n)) :
    pauliWeight (pauliZSetLabel S) = S.card := by
  rw [pauliWeight_eq_card_pauliSupport, pauliSupport_pauliZSetLabel]

theorem pauliZSetLabel_injective : Function.Injective (pauliZSetLabel (n := n)) := by
  intro S T h
  have := congrArg pauliSupport h
  simpa using this

/-- A string all of whose entries are `Z` or trivial is the `Z` string of its support. -/
theorem pauliZSetLabel_pauliSupport_of_forall {P : Fin n → Option (Fin 3)}
    (hP : ∀ s, P s = none ∨ P s = some 2) :
    pauliZSetLabel (pauliSupport P) = P := by
  funext s
  rcases hP s with h | h
  · rw [pauliZSetLabel, if_neg (by simp [h])]
    exact h.symm
  · rw [pauliZSetLabel, if_pos (by simp [h])]
    exact h.symm

theorem forall_pauliZSetLabel_eq (S : Finset (Fin n)) (s : Fin n) :
    pauliZSetLabel S s = none ∨ pauliZSetLabel S s = some 2 := by
  by_cases hs : s ∈ S <;> simp [pauliZSetLabel, hs]

/-- **A `Z` string is diagonal with its configuration sign.** -/
theorem finitePauliMatrix_pauliZSetLabel (S : Finset (Fin n)) (x y : Fin n → Bool) :
    finitePauliMatrix (pauliZSetLabel S) x y
      = if x = y then ((zSetSign S x : ℝ) : ℂ) else 0 := by
  classical
  by_cases hxy : x = y
  · subst hxy
    rw [if_pos rfl]
    have hentry : ∀ s : Fin n,
        boolPauliOptionEntry (pauliZSetLabel S s) (x s, x s)
          = if s ∈ S then ((if x s then (-1 : ℝ) else 1 : ℝ) : ℂ) else 1 := by
      intro s
      by_cases hs : s ∈ S
      · rw [pauliZSetLabel, if_pos hs, boolPauliOptionEntry_z, if_pos rfl, if_pos hs, zSign]
        by_cases hxs : x s = true <;> simp [hxs]
      · rw [pauliZSetLabel, if_neg hs, boolPauliOptionEntry_none, if_pos rfl, if_neg hs]
    calc finitePauliMatrix (pauliZSetLabel S) x x
        = ∏ s, boolPauliOptionEntry (pauliZSetLabel S s) (x s, x s) := rfl
      _ = ∏ s, if s ∈ S then ((if x s then (-1 : ℝ) else 1 : ℝ) : ℂ) else 1 :=
          Finset.prod_congr rfl fun s _ => hentry s
      _ = ∏ s ∈ Finset.univ.filter fun s => s ∈ S,
            ((if x s then (-1 : ℝ) else 1 : ℝ) : ℂ) := (Finset.prod_filter _ _).symm
      _ = ∏ s ∈ S, ((if x s then (-1 : ℝ) else 1 : ℝ) : ℂ) := by
          congr 1
          ext s
          simp
      _ = ((zSetSign S x : ℝ) : ℂ) := by
          rw [zSetSign, Complex.ofReal_prod]
  · rw [if_neg hxy]
    obtain ⟨s, hs⟩ : ∃ s, x s ≠ y s := Function.ne_iff.mp hxy
    refine Finset.prod_eq_zero (Finset.mem_univ s) ?_
    by_cases hsS : s ∈ S
    · rw [pauliZSetLabel, if_pos hsS, boolPauliOptionEntry_z, if_neg hs]
    · rw [pauliZSetLabel, if_neg hsS, boolPauliOptionEntry_none, if_neg hs]

theorem abs_zSetSign (S : Finset (Fin n)) (x : Fin n → Bool) : |zSetSign S x| = 1 := by
  rw [zSetSign, Finset.abs_prod]
  refine Finset.prod_eq_one fun s _ => ?_
  by_cases hs : x s = true <;> simp [hs]

theorem zSetSign_le_one (S : Finset (Fin n)) (x : Fin n → Bool) : zSetSign S x ≤ 1 :=
  (le_abs_self _).trans (le_of_eq (abs_zSetSign S x))

theorem neg_one_le_zSetSign (S : Finset (Fin n)) (x : Fin n → Bool) : -1 ≤ zSetSign S x := by
  have := abs_le.mp (le_of_eq (abs_zSetSign S x))
  exact this.1

theorem zSetSign_singleton (i : Fin n) (x : Fin n → Bool) :
    zSetSign {i} x = if x i then -1 else 1 := by
  rw [zSetSign, Finset.prod_singleton]

theorem zSetSign_eq_one_of_forall_false {x : Fin n → Bool} (hx : ∀ s, x s = false)
    (S : Finset (Fin n)) : zSetSign S x = 1 := by
  rw [zSetSign]
  refine Finset.prod_eq_one fun s _ => ?_
  simp [hx s]

end

end GaloisForLFunctions.HTGeometry
