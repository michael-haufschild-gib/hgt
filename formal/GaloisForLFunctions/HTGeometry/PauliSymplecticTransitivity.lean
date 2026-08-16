import Mathlib

/-!
# Transitivity of the binary symplectic group on nonzero vectors

The commutation form of the `n`-qubit Pauli labels is a nondegenerate alternating form over the
field with two elements.  Its symplectic transvections are involutive form-preserving additive
bijections, and one or two of them carry any nonzero label to any other: if two labels fail to
commute a single transvection suffices, and otherwise a common noncommuting partner exists because
two nonzero linear functionals over the field with two elements jointly take the value one.
-/

open Finset

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

variable {n : ℕ}

/-- Binary symplectic labels of `n` qubits: an `X` part and a `Z` part at each site. -/
abbrev PauliSymp (n : ℕ) := Fin n → (ZMod 2 × ZMod 2)

theorem zmodTwo_add_self (z : ZMod 2) : z + z = 0 := by
  revert z
  decide

theorem pauliSymp_add_self (u : PauliSymp n) : u + u = 0 := by
  funext i
  show u i + u i = 0
  refine Prod.ext ?_ ?_
  · rw [Prod.fst_add]
    exact zmodTwo_add_self _
  · rw [Prod.snd_add]
    exact zmodTwo_add_self _

/-- The commutation form of two Pauli labels. -/
def symForm (u v : PauliSymp n) : ZMod 2 :=
  ∑ i, ((u i).1 * (v i).2 + (u i).2 * (v i).1)

theorem symForm_comm (u v : PauliSymp n) : symForm u v = symForm v u := by
  rw [symForm, symForm]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem symForm_add_left (u v w : PauliSymp n) :
    symForm (u + v) w = symForm u w + symForm v w := by
  rw [symForm, symForm, symForm, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.add_apply, Prod.fst_add, Prod.snd_add]
  ring

theorem symForm_add_right (u v w : PauliSymp n) :
    symForm u (v + w) = symForm u v + symForm u w := by
  rw [symForm_comm, symForm_add_left, symForm_comm v u, symForm_comm w u]

theorem symForm_self (u : PauliSymp n) : symForm u u = 0 := by
  rw [symForm]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [mul_comm ((u i).2) ((u i).1)]
  exact zmodTwo_add_self _

theorem symForm_zero_left (v : PauliSymp n) : symForm 0 v = 0 := by
  rw [symForm]
  refine Finset.sum_eq_zero fun i _ => ?_
  simp

theorem symForm_smul_left (c : ZMod 2) (u v : PauliSymp n) :
    symForm (c • u) v = c * symForm u v := by
  rw [symForm, symForm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.smul_apply, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

theorem symForm_smul_right (c : ZMod 2) (u v : PauliSymp n) :
    symForm u (c • v) = c * symForm u v := by
  rw [symForm_comm, symForm_smul_left, symForm_comm v u]

/-- The form on a pair of shifted labels. -/
theorem symForm_shift (a x y : PauliSymp n) (c d : ZMod 2) :
    symForm (x + c • a) (y + d • a) =
      symForm x y + d * symForm x a + c * symForm a y := by
  simp only [symForm_add_left, symForm_add_right, symForm_smul_left, symForm_smul_right,
    symForm_self, mul_zero]
  ring

/-- **Nondegeneracy.**  Every nonzero label fails to commute with some label. -/
theorem exists_symForm_eq_one {u : PauliSymp n} (hu : u ≠ 0) :
    ∃ x : PauliSymp n, symForm u x = 1 := by
  classical
  obtain ⟨i, hi⟩ : ∃ i : Fin n, u i ≠ 0 := by
    by_contra hcon
    exact hu (funext fun i => not_not.mp fun h => hcon ⟨i, h⟩)
  by_cases h1 : (u i).1 = 0
  · have h2 : (u i).2 = 1 := by
      have hne : (u i).2 ≠ 0 := fun h => hi (Prod.ext h1 h)
      revert hne
      generalize (u i).2 = a
      revert a
      decide
    refine ⟨Pi.single i (1, 0), ?_⟩
    rw [symForm, Finset.sum_eq_single i]
    · rw [Pi.single_eq_same, h1, h2]
      norm_num
    · intro j _ hj
      rw [Pi.single_eq_of_ne hj]
      simp
    · intro hcon
      exact absurd (Finset.mem_univ i) hcon
  · have h1' : (u i).1 = 1 := by
      revert h1
      generalize (u i).1 = a
      revert a
      decide
    refine ⟨Pi.single i (0, 1), ?_⟩
    rw [symForm, Finset.sum_eq_single i]
    · rw [Pi.single_eq_same, h1']
      norm_num
    · intro j _ hj
      rw [Pi.single_eq_of_ne hj]
      simp
    · intro hcon
      exact absurd (Finset.mem_univ i) hcon

/-- **A common noncommuting partner.**  Two nonzero labels both fail to commute with a common
label. -/
theorem exists_symForm_eq_one_pair {u v : PauliSymp n} (hu : u ≠ 0) (hv : v ≠ 0) :
    ∃ x : PauliSymp n, symForm u x = 1 ∧ symForm v x = 1 := by
  classical
  obtain ⟨a, ha⟩ := exists_symForm_eq_one hu
  obtain ⟨b, hb⟩ := exists_symForm_eq_one hv
  by_cases hva : symForm v a = 1
  · exact ⟨a, ha, hva⟩
  · by_cases hub : symForm u b = 1
    · exact ⟨b, hub, hb⟩
    · have hva0 : symForm v a = 0 := by
        revert hva
        generalize symForm v a = z
        revert z
        decide
      have hub0 : symForm u b = 0 := by
        revert hub
        generalize symForm u b = z
        revert z
        decide
      refine ⟨a + b, ?_, ?_⟩
      · rw [symForm_add_right, ha, hub0, add_zero]
      · rw [symForm_add_right, hva0, hb, zero_add]

/-- The symplectic transvection attached to a label. -/
def transvection (a : PauliSymp n) (x : PauliSymp n) : PauliSymp n :=
  x + symForm a x • a

theorem transvection_add (a x y : PauliSymp n) :
    transvection a (x + y) = transvection a x + transvection a y := by
  rw [transvection, transvection, transvection, symForm_add_right, add_smul]
  abel

theorem transvection_involutive (a : PauliSymp n) :
    Function.Involutive (transvection a (n := n)) := by
  intro x
  rw [transvection, transvection, symForm_add_right, symForm_smul_right, symForm_self, mul_zero,
    add_zero, add_assoc, ← add_smul, zmodTwo_add_self, zero_smul, add_zero]

theorem symForm_transvection (a x y : PauliSymp n) :
    symForm (transvection a x) (transvection a y) = symForm x y := by
  rw [transvection, transvection, symForm_shift, symForm_comm x a]
  have h : symForm a y * symForm a x + symForm a x * symForm a y = 0 := by
    rw [mul_comm (symForm a y) (symForm a x)]
    exact zmodTwo_add_self _
  linear_combination h

/-- The transvection as a bijection of labels. -/
def transvectionEquiv (a : PauliSymp n) : PauliSymp n ≃ PauliSymp n :=
  Function.Involutive.toPerm _ (transvection_involutive a)

theorem transvectionEquiv_apply (a x : PauliSymp n) :
    transvectionEquiv a x = transvection a x := rfl

theorem transvection_of_symForm_eq_one {a b : PauliSymp n} (h : symForm b a = 1) :
    transvection (a + b) a = b := by
  rw [transvection, symForm_add_left, symForm_self, zero_add, h, one_smul, ← add_assoc,
    pauliSymp_add_self, zero_add]

/-- **Transitivity on nonzero labels.**  Any nonzero Pauli label is carried to any other by a
form-preserving additive bijection. -/
theorem exists_symplectic_equiv_map {u v : PauliSymp n} (hu : u ≠ 0) (hv : v ≠ 0) :
    ∃ T : PauliSymp n ≃ PauliSymp n,
      (∀ x y, T (x + y) = T x + T y) ∧
        (∀ x y, symForm (T x) (T y) = symForm x y) ∧ T u = v := by
  classical
  by_cases hform : symForm v u = 1
  · exact ⟨transvectionEquiv (u + v), fun x y => transvection_add _ x y,
      fun x y => symForm_transvection _ x y, transvection_of_symForm_eq_one hform⟩
  · obtain ⟨w, hw1, hw2⟩ := exists_symForm_eq_one_pair hu hv
    have hstep1 : transvection (u + w) u = w := by
      refine transvection_of_symForm_eq_one ?_
      rw [symForm_comm]
      exact hw1
    have hstep2 : transvection (w + v) w = v := by
      refine transvection_of_symForm_eq_one ?_
      exact hw2
    refine ⟨(transvectionEquiv (u + w)).trans (transvectionEquiv (w + v)),
      fun x y => ?_, fun x y => ?_, ?_⟩
    · simp only [Equiv.trans_apply, transvectionEquiv_apply]
      rw [transvection_add, transvection_add]
    · simp only [Equiv.trans_apply, transvectionEquiv_apply]
      rw [symForm_transvection, symForm_transvection]
    · simp only [Equiv.trans_apply, transvectionEquiv_apply]
      rw [hstep1, hstep2]

end GaloisForLFunctions.HTGeometry
