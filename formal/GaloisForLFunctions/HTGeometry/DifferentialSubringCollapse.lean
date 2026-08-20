import GaloisForLFunctions.HTGeometry.AdditiveDifferentialSubgroupLinear
import GaloisForLFunctions.HTGeometry.DifferentialConstantsCollapse

/-!
# A subring inside a differential algebraic set consists of constants

A nonzero linear relation among the jets can be normalised to a monic one by dividing by the
coefficient of the highest jet that occurs.  Applied to the additive relation carried by a subgroup
lying in the zero set of a nonzero differential polynomial, this puts every element of the subgroup
in the solution set of one monic linear differential equation; if the subgroup is a ring, the powers
of any of its elements solve it too, so the element is algebraic over the constants, hence — the
constants being algebraically closed — constant.

The consequence recorded here is the hypothesis Cassidy's matrix classification consumes: the
scalars `x` with `x • 1` in a multiplicatively closed module of matrices are constants as soon as
they lie in a proper differential algebraic set.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped Differential
open GaloisForLFunctions

variable {C : Type*} [Field C] [CharZero C] [Differential C]

omit [CharZero C] in
/-- **A nonzero linear jet relation can be taken monic.** -/
theorem exists_monic_jet_relation (V : Set C) :
    ∀ (n : ℕ) (c : Fin (n + 1) → C), (∃ i, c i ≠ 0) →
    (∀ v ∈ V, ∑ i : Fin (n + 1), c i * differentialJet (i : ℕ) v = 0) →
    ∃ (m : ℕ) (a : Fin m → C), ∀ v ∈ V,
      differentialJet m v = ∑ i : Fin m, a i * differentialJet (i : ℕ) v := by
  intro n
  induction n with
  | zero =>
      intro c hc hrel
      obtain ⟨i, hi⟩ := hc
      haveI : Subsingleton (Fin (0 + 1)) := inferInstanceAs (Subsingleton (Fin 1))
      have hi0 : c 0 ≠ 0 := by
        rwa [Subsingleton.elim i 0] at hi
      refine ⟨0, Fin.elim0, fun v hv => ?_⟩
      have h := hrel v hv
      rw [Fin.sum_univ_one] at h
      have hv0 : v = 0 := by
        rw [Fin.val_zero, differentialJet_zero] at h
        rcases mul_eq_zero.mp h with h0 | h0
        · exact absurd h0 hi0
        · exact h0
      rw [differentialJet_zero, hv0, Finset.univ_eq_empty, Finset.sum_empty]
  | succ n ih =>
      intro c hc hrel
      by_cases hlast : c (Fin.last (n + 1)) = 0
      · refine ih (fun i : Fin (n + 1) => c i.castSucc) ?_ ?_
        · obtain ⟨i, hi⟩ := hc
          rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
          · exact ⟨j, hi⟩
          · exact absurd hlast hi
        · intro v hv
          have h := hrel v hv
          rw [Fin.sum_univ_castSucc, hlast, zero_mul, add_zero] at h
          simpa only [Fin.val_castSucc] using h
      · refine ⟨n + 1, fun i : Fin (n + 1) => -(c i.castSucc) / c (Fin.last (n + 1)),
          fun v hv => ?_⟩
        have h := hrel v hv
        rw [Fin.sum_univ_castSucc] at h
        simp only [Fin.val_castSucc, Fin.val_last] at h
        have hsum : ∑ i : Fin (n + 1),
            (-(c i.castSucc) / c (Fin.last (n + 1))) * differentialJet ((i : ℕ)) v
            = (-(∑ i : Fin (n + 1), c i.castSucc * differentialJet ((i : ℕ)) v))
              / c (Fin.last (n + 1)) := by
          rw [Finset.sum_congr rfl (fun (i : Fin (n + 1)) _ => div_mul_eq_mul_div
            (-(c i.castSucc)) (c (Fin.last (n + 1))) (differentialJet ((i : ℕ)) v))]
          rw [← Finset.sum_div]
          congr 1
          rw [← Finset.sum_neg_distrib]
          exact Finset.sum_congr rfl fun (i : Fin (n + 1)) _ => neg_mul _ _
        rw [hsum, eq_div_iff hlast]
        linear_combination h

/-- **The collapse.**  A subring of a differential field lying in the zero set of a nonzero
differential polynomial consists of constants, when the constants are algebraically closed.

The subgroup satisfies a nonzero linear relation among its jets, which can be taken monic; the
powers of one of its elements all satisfy that one equation, so the element is algebraic over the
constants, hence constant. -/
theorem deriv_eq_zero_of_subring_of_zeroSet [IsAlgClosed (differentialConstants C)]
    (V : AddSubgroup C) (hone : (1 : C) ∈ V) (hmul : ∀ x ∈ V, ∀ y ∈ V, x * y ∈ V)
    {P : DifferentialPolynomial Unit C} (hP : P ≠ 0)
    (hPV : ∀ v ∈ V, differentialPolynomialEvalOver (K := C) (fun _ : Unit => v) P = 0) :
    ∀ x ∈ V, Differential.deriv x = 0 := by
  obtain ⟨n, c, hc, hrel⟩ := exists_nonzero_linear_jet_relation_of_addSubgroup V hP hPV
  obtain ⟨m, a, hmonic⟩ := exists_monic_jet_relation (V : Set C) n c hc hrel
  intro x hx
  have hpow : ∀ k : ℕ, x ^ k ∈ V := by
    intro k
    induction k with
    | zero => simpa using hone
    | succ k ih =>
        rw [pow_succ]
        exact hmul _ ih _ hx
  exact deriv_eq_zero_of_solution_powers a (fun k => hmonic (x ^ k) (hpow k))

/-- The scalars whose multiples of the identity lie in a submodule of matrices. -/
def scalarStabilizer (A : Submodule (differentialConstants C) (Matrix (Fin 2) (Fin 2) C)) :
    AddSubgroup C where
  carrier := {x : C | x • (1 : Matrix (Fin 2) (Fin 2) C) ∈ A}
  zero_mem' := by
    show (0 : C) • (1 : Matrix (Fin 2) (Fin 2) C) ∈ A
    rw [zero_smul]
    exact A.zero_mem
  add_mem' := by
    intro x y hx hy
    show (x + y) • (1 : Matrix (Fin 2) (Fin 2) C) ∈ A
    rw [add_smul]
    exact A.add_mem hx hy
  neg_mem' := by
    intro x hx
    show (-x) • (1 : Matrix (Fin 2) (Fin 2) C) ∈ A
    rw [neg_smul]
    exact A.neg_mem hx

omit [CharZero C] in
@[simp] theorem mem_scalarStabilizer
    {A : Submodule (differentialConstants C) (Matrix (Fin 2) (Fin 2) C)} {x : C} :
    x ∈ scalarStabilizer A ↔ x • (1 : Matrix (Fin 2) (Fin 2) C) ∈ A := Iff.rfl

/-- **The scalar stabiliser of a multiplicatively closed module of matrices collapses to the
constants** as soon as it lies in the zero set of a nonzero differential polynomial. -/
theorem eq_algebraMap_of_scalarStabilizer_of_zeroSet [IsAlgClosed (differentialConstants C)]
    (A : Submodule (differentialConstants C) (Matrix (Fin 2) (Fin 2) C))
    (hone : (1 : Matrix (Fin 2) (Fin 2) C) ∈ A)
    (hmulA : ∀ a ∈ A, ∀ b ∈ A, a * b ∈ A)
    {P : DifferentialPolynomial Unit C} (hP : P ≠ 0)
    (hPV : ∀ v ∈ scalarStabilizer A,
      differentialPolynomialEvalOver (K := C) (fun _ : Unit => v) P = 0) :
    ∀ x : C, x • (1 : Matrix (Fin 2) (Fin 2) C) ∈ A →
      ∃ x₀ : differentialConstants C, x = algebraMap (differentialConstants C) C x₀ := by
  have honeV : (1 : C) ∈ scalarStabilizer A := by
    show (1 : C) • (1 : Matrix (Fin 2) (Fin 2) C) ∈ A
    rwa [one_smul]
  have hmulV : ∀ x ∈ scalarStabilizer A, ∀ y ∈ scalarStabilizer A,
      x * y ∈ scalarStabilizer A := by
    intro x hx y hy
    show (x * y) • (1 : Matrix (Fin 2) (Fin 2) C) ∈ A
    have hprod := hmulA _ hx _ hy
    rwa [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul] at hprod
  have hconst := deriv_eq_zero_of_subring_of_zeroSet (scalarStabilizer A) honeV hmulV hP hPV
  intro x hx
  exact ⟨⟨x, hconst x hx⟩, rfl⟩

end

end GaloisForLFunctions.HTGeometry
