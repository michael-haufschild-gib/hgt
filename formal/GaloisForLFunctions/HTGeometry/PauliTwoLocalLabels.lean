import GaloisForLFunctions.HTGeometry.FiniteQubitPauliBasisLaw
import GaloisForLFunctions.HTGeometry.BooleanHypercubeTranspositionLaw

/-!
# The two-local Pauli labels in the computational basis

A Pauli string acts on a computational configuration factorwise, so a string supported on one or two
qubits has an entry which is a single product with all but one or two factors equal to a Kronecker
delta.  Evaluating those products gives closed forms: the `Z` strings are diagonal with the sign
pattern of the occupied qubits, and an `X` string on one qubit is the adjacency matrix of that
qubit's hypercube edges.

These are the labels a two-local Ising Hamiltonian with a transverse field is built from.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {n : ℕ}

/-- Sign of one qubit in a computational configuration. -/
def zSign (b : Bool) : ℂ := if b then -1 else 1

/-- Weight of a Pauli string: the number of qubits it acts on. -/
def pauliWeight (P : Fin n → Option (Fin 3)) : ℕ :=
  (Finset.univ.filter fun s => P s ≠ none).card

/-- The identity Pauli string. -/
def pauliIdentityLabel (n : ℕ) : Fin n → Option (Fin 3) := fun _ => none

/-- The `Z` string of one qubit. -/
def pauliZLabel (i : Fin n) : Fin n → Option (Fin 3) := fun s => if s = i then some 2 else none

/-- The `Z Z` string of two qubits. -/
def pauliZZLabel (i j : Fin n) : Fin n → Option (Fin 3) :=
  fun s => if s = i ∨ s = j then some 2 else none

/-- The `X` string of one qubit. -/
def pauliXLabel (i : Fin n) : Fin n → Option (Fin 3) := fun s => if s = i then some 0 else none

theorem pauliWeight_pauliIdentityLabel : pauliWeight (pauliIdentityLabel n) = 0 := by
  simp [pauliWeight, pauliIdentityLabel]

theorem pauliWeight_pauliZLabel (i : Fin n) : pauliWeight (pauliZLabel i) = 1 := by
  classical
  have hfilter : (Finset.univ.filter fun s => pauliZLabel i s ≠ none) = {i} := by
    ext s
    simp [pauliZLabel]
  rw [pauliWeight, hfilter, Finset.card_singleton]

theorem pauliWeight_pauliXLabel (i : Fin n) : pauliWeight (pauliXLabel i) = 1 := by
  classical
  have hfilter : (Finset.univ.filter fun s => pauliXLabel i s ≠ none) = {i} := by
    ext s
    simp [pauliXLabel]
  rw [pauliWeight, hfilter, Finset.card_singleton]

theorem pauliWeight_pauliZZLabel_le (i j : Fin n) : pauliWeight (pauliZZLabel i j) ≤ 2 := by
  classical
  have hsubset : (Finset.univ.filter fun s => pauliZZLabel i j s ≠ none) ⊆ {i, j} := by
    intro s hs
    simp only [Finset.mem_filter, pauliZZLabel] at hs
    by_cases hij : s = i ∨ s = j
    · rcases hij with h | h <;> simp [h]
    · exact absurd (by simp [hij] at hs) hs.2
  calc pauliWeight (pauliZZLabel i j) ≤ ({i, j} : Finset (Fin n)).card :=
        Finset.card_le_card hsubset
    _ ≤ 2 := Finset.card_insert_le _ _ |>.trans (by simp)

/-- Off the identity factor, a Pauli-string entry vanishes wherever the configurations differ. -/
theorem boolPauliOptionEntry_none (x y : Bool) :
    boolPauliOptionEntry none (x, y) = if x = y then 1 else 0 := by
  simp [boolPauliOptionEntry, boolPauliOption, Matrix.one_apply]

theorem boolPauliOptionEntry_z (x y : Bool) :
    boolPauliOptionEntry (some 2) (x, y) = if x = y then zSign x else 0 := by
  simp only [boolPauliOptionEntry, boolPauliOption, finiteQubitPauli, zSign]
  by_cases hxy : x = y <;> cases x <;> simp_all

theorem boolPauliOptionEntry_x (x y : Bool) :
    boolPauliOptionEntry (some 0) (x, y) = if x = y then 0 else 1 := by
  simp only [boolPauliOptionEntry, boolPauliOption, finiteQubitPauli]
  by_cases hxy : x = y <;> simp [hxy]

/-- Away from the support of a Pauli string the entries force the configurations to agree. -/
theorem finitePauliMatrix_eq_zero_of_ne_off_support {P : Fin n → Option (Fin 3)}
    {x y : Fin n → Bool} {s : Fin n} (hs : P s = none) (hxy : x s ≠ y s) :
    finitePauliMatrix P x y = 0 := by
  classical
  refine Finset.prod_eq_zero (Finset.mem_univ s) ?_
  rw [hs, boolPauliOptionEntry_none, if_neg hxy]

/-- The identity string is the identity matrix. -/
theorem finitePauliMatrix_pauliIdentityLabel (x y : Fin n → Bool) :
    finitePauliMatrix (pauliIdentityLabel n) x y = if x = y then 1 else 0 := by
  classical
  by_cases hxy : x = y
  · subst hxy
    rw [if_pos rfl]
    refine Finset.prod_eq_one fun s _ => ?_
    rw [pauliIdentityLabel, boolPauliOptionEntry_none, if_pos rfl]
  · rw [if_neg hxy]
    obtain ⟨s, hs⟩ : ∃ s, x s ≠ y s := Function.ne_iff.mp hxy
    exact finitePauliMatrix_eq_zero_of_ne_off_support (P := pauliIdentityLabel n) rfl hs

/-- A `Z` string is diagonal with the sign of its qubit. -/
theorem finitePauliMatrix_pauliZLabel (i : Fin n) (x y : Fin n → Bool) :
    finitePauliMatrix (pauliZLabel i) x y = if x = y then zSign (x i) else 0 := by
  classical
  by_cases hxy : x = y
  · subst hxy
    rw [if_pos rfl]
    refine (Finset.prod_eq_single i ?_ ?_).trans ?_
    · intro s _ hs
      rw [pauliZLabel, if_neg hs, boolPauliOptionEntry_none, if_pos rfl]
    · intro h
      exact absurd (Finset.mem_univ i) h
    · rw [pauliZLabel, if_pos rfl, boolPauliOptionEntry_z, if_pos rfl]
  · rw [if_neg hxy]
    obtain ⟨s, hs⟩ : ∃ s, x s ≠ y s := Function.ne_iff.mp hxy
    refine Finset.prod_eq_zero (Finset.mem_univ s) ?_
    by_cases hsi : s = i
    · subst hsi
      rw [pauliZLabel, if_pos rfl, boolPauliOptionEntry_z, if_neg hs]
    · rw [pauliZLabel, if_neg hsi, boolPauliOptionEntry_none, if_neg hs]

/-- A `Z Z` string is diagonal with the product of the signs of its qubits. -/
theorem finitePauliMatrix_pauliZZLabel {i j : Fin n} (hij : i ≠ j) (x y : Fin n → Bool) :
    finitePauliMatrix (pauliZZLabel i j) x y
      = if x = y then zSign (x i) * zSign (x j) else 0 := by
  classical
  by_cases hxy : x = y
  · subst hxy
    rw [if_pos rfl]
    have hsplit : (∏ s, boolPauliOptionEntry (pauliZZLabel i j s) (x s, x s))
        = boolPauliOptionEntry (pauliZZLabel i j i) (x i, x i) *
          ∏ s ∈ Finset.univ.erase i, boolPauliOptionEntry (pauliZZLabel i j s) (x s, x s) :=
      (Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)).symm
    rw [show finitePauliMatrix (pauliZZLabel i j) x x
        = ∏ s, boolPauliOptionEntry (pauliZZLabel i j s) (x s, x s) from rfl, hsplit]
    rw [show pauliZZLabel i j i = some 2 by simp [pauliZZLabel], boolPauliOptionEntry_z,
      if_pos rfl]
    congr 1
    refine (Finset.prod_eq_single j ?_ ?_).trans ?_
    · intro s hs hsj
      have hsi : s ≠ i := (Finset.mem_erase.mp hs).1
      rw [show pauliZZLabel i j s = none by simp [pauliZZLabel, hsi, hsj],
        boolPauliOptionEntry_none, if_pos rfl]
    · intro h
      exact absurd (Finset.mem_erase.mpr ⟨fun hcon => hij hcon.symm, Finset.mem_univ j⟩) h
    · rw [show pauliZZLabel i j j = some 2 by simp [pauliZZLabel], boolPauliOptionEntry_z,
        if_pos rfl]
  · rw [if_neg hxy]
    obtain ⟨s, hs⟩ : ∃ s, x s ≠ y s := Function.ne_iff.mp hxy
    refine Finset.prod_eq_zero (Finset.mem_univ s) ?_
    by_cases hsupp : s = i ∨ s = j
    · rw [show pauliZZLabel i j s = some 2 by simp [pauliZZLabel, hsupp],
        boolPauliOptionEntry_z, if_neg hs]
    · rw [show pauliZZLabel i j s = none by simp [pauliZZLabel, hsupp],
        boolPauliOptionEntry_none, if_neg hs]

/-- An `X` string is the adjacency matrix of the hypercube edges of its qubit. -/
theorem finitePauliMatrix_pauliXLabel (i : Fin n) (x y : Fin n → Bool) :
    finitePauliMatrix (pauliXLabel i) x y = if y = boolToggle x i then 1 else 0 := by
  classical
  by_cases hy : y = boolToggle x i
  · subst hy
    rw [if_pos rfl]
    refine (Finset.prod_eq_single i ?_ ?_).trans ?_
    · intro s _ hs
      rw [pauliXLabel, if_neg hs, boolPauliOptionEntry_none, if_pos ?_]
      rw [boolToggle, Function.update_of_ne hs]
    · intro h
      exact absurd (Finset.mem_univ i) h
    · rw [pauliXLabel, if_pos rfl, boolPauliOptionEntry_x, if_neg ?_]
      rw [boolToggle, Function.update_self]
      exact fun hcon => (Bool.not_ne_self (x i)) hcon.symm
  · rw [if_neg hy]
    by_cases hoff : ∀ s, s ≠ i → x s = y s
    · have hi : x i = y i := by
        by_contra hne
        refine hy (funext fun s => ?_)
        by_cases hs : s = i
        · subst hs
          rw [boolToggle, Function.update_self]
          rcases Bool.eq_false_or_eq_true (x s) with hx | hx <;>
            rcases Bool.eq_false_or_eq_true (y s) with hyv | hyv <;>
              simp [hx, hyv] at hne ⊢
        · rw [boolToggle, Function.update_of_ne hs, hoff s hs]
      refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
      rw [pauliXLabel, if_pos rfl, boolPauliOptionEntry_x, if_pos hi]
    · push Not at hoff
      obtain ⟨s, hsi, hs⟩ := hoff
      refine Finset.prod_eq_zero (Finset.mem_univ s) ?_
      rw [pauliXLabel, if_neg hsi, boolPauliOptionEntry_none, if_neg hs]

end

end GaloisForLFunctions.HTGeometry
