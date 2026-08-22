import GaloisForLFunctions.HTGeometry.AdditiveDifferentialSubgroupLinear
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# The unipotent parameter set of a matrix group

`u(t) = [[1, t], [0, 1]]` satisfies `u(t)·u(t') = u(t + t')`, so for any multiplicative subgroup `G`
of `2×2` matrices the set of parameters `t` with `u(t) ∈ G` is an additive subgroup of the
coefficients.  Substituting `u(X)` into a differential polynomial in the four matrix entries
produces a differential polynomial in one indeterminate whose zero set contains that parameter set,
because the entries `1` and `0` are differential constants: all their jets above order zero vanish.

So a differential-algebraic constraint on the group becomes a differential-algebraic constraint on
the parameter set, and Cassidy's additive classification — already in the tree as
`exists_nonzero_linear_jet_relation_of_addSubgroup` — turns it into one nonzero *linear*
differential relation.  That is the shape the isomonodromy endgame consumes.

The one thing this cannot decide is whether the substituted polynomial is nonzero: it is exactly
the statement that the group does not contain every upper unipotent.

* `unipotentUpper`, `unipotentUpper_mul`, `unipotentUpper_zero`, `unipotentUpper_inv`;
* `unipotentParams` — the additive subgroup of parameters;
* `unipotentSubstHom`, `unipotentSubst`, `evalOver_unipotentSubst`;
* `exists_nonzero_linear_jet_relation_of_unipotentParams`.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped Differential
open GaloisForLFunctions

variable {U : Type*} [Field U] [CharZero U] [Differential U]

/-- The upper unipotent with parameter `t`. -/
def unipotentUpper (t : U) : Matrix (Fin 2) (Fin 2) U := !![1, t; 0, 1]

omit [CharZero U] [Differential U] in
@[simp] theorem unipotentUpper_zero : unipotentUpper (0 : U) = 1 := by
  rw [unipotentUpper]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

omit [CharZero U] [Differential U] in
theorem unipotentUpper_mul (t t' : U) :
    unipotentUpper t * unipotentUpper t' = unipotentUpper (t + t') := by
  rw [unipotentUpper, unipotentUpper, unipotentUpper]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]

omit [CharZero U] [Differential U] in
theorem unipotentUpper_inv (t : U) :
    unipotentUpper t * unipotentUpper (-t) = 1 := by
  rw [unipotentUpper_mul, add_neg_cancel, unipotentUpper_zero]

/-- The parameters of the upper unipotents that lie in a multiplicative subgroup. -/
def unipotentParams (G : Set (Matrix (Fin 2) (Fin 2) U))
    (hone : (1 : Matrix (Fin 2) (Fin 2) U) ∈ G)
    (hmul : ∀ g ∈ G, ∀ h ∈ G, g * h ∈ G)
    (hinv : ∀ g ∈ G, ∀ h, g * h = 1 → h ∈ G) : AddSubgroup U where
  carrier := {t | unipotentUpper t ∈ G}
  zero_mem' := by
    simp only [Set.mem_setOf_eq, unipotentUpper_zero]
    exact hone
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [← unipotentUpper_mul]
    exact hmul _ ha _ hb
  neg_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    exact hinv _ ha _ (unipotentUpper_inv a)

omit [CharZero U] [Differential U] in
@[simp] theorem mem_unipotentParams {G : Set (Matrix (Fin 2) (Fin 2) U)}
    {hone hmul hinv} {t : U} :
    t ∈ unipotentParams G hone hmul hinv ↔ unipotentUpper t ∈ G := Iff.rfl

/-- Substituting `u(X)` into a differential polynomial in the four matrix entries. -/
def unipotentSubstHom :
    DifferentialPolynomial (Fin 2 × Fin 2) U →ₐ[U] DifferentialPolynomial Unit U :=
  MvPolynomial.aeval
    (fun q : (Fin 2 × Fin 2) × ℕ =>
      if q.1 = (0, 1) then MvPolynomial.X ((), q.2)
      else if q.1 = (1, 0) then 0
      else if q.2 = 0 then 1 else 0)

/-- The substituted differential polynomial in one indeterminate. -/
def unipotentSubst (P : DifferentialPolynomial (Fin 2 × Fin 2) U) :
    DifferentialPolynomial Unit U := unipotentSubstHom P

omit [CharZero U] in
theorem differentialJet_one (n : ℕ) :
    differentialJet (n + 1) (1 : U) = 0 := by
  induction n with
  | zero =>
      rw [differentialJet_succ, differentialJet_zero]
      exact Differential.deriv.map_one_eq_zero
  | succ n ih => rw [differentialJet_succ, ih, map_zero]

omit [CharZero U] in
private theorem differentialJet_zero_elt (n : ℕ) : differentialJet n (0 : U) = 0 :=
  differentialJet_apply_zero n

omit [CharZero U] in
/-- **The substitution computes the value at the unipotent.** -/
theorem evalOver_unipotentSubst (P : DifferentialPolynomial (Fin 2 × Fin 2) U) (t : U) :
    differentialPolynomialEvalOver (K := U) (fun _ : Unit => t) (unipotentSubst P)
      = differentialPolynomialEvalOver (K := U)
          (fun q : Fin 2 × Fin 2 => unipotentUpper t q.1 q.2) P := by
  have key : (differentialPolynomialEvalOver (K := U) (fun _ : Unit => t)).comp
        (unipotentSubstHom (U := U))
      = differentialPolynomialEvalOver (K := U)
          (fun q : Fin 2 × Fin 2 => unipotentUpper t q.1 q.2) := by
    refine MvPolynomial.algHom_ext fun q => ?_
    obtain ⟨⟨i, j⟩, n⟩ := q
    rw [AlgHom.comp_apply, unipotentSubstHom, MvPolynomial.aeval_X,
      differentialPolynomialEvalOver_X]
    by_cases h1 : ((i, j) : Fin 2 × Fin 2) = ((0 : Fin 2), (1 : Fin 2))
    · rw [if_pos h1]
      have hij : unipotentUpper t i j = t := by
        rw [(Prod.mk.injEq .. ▸ h1 : i = 0 ∧ j = 1).1, (Prod.mk.injEq .. ▸ h1 : i = 0 ∧ j = 1).2,
          unipotentUpper]
        simp
      rw [hij, differentialPolynomialEvalOver_X]
    · rw [if_neg h1]
      by_cases h2 : ((i, j) : Fin 2 × Fin 2) = ((1 : Fin 2), (0 : Fin 2))
      · rw [if_pos h2, map_zero]
        have hij : unipotentUpper t i j = 0 := by
          rw [(Prod.mk.injEq .. ▸ h2 : i = 1 ∧ j = 0).1, (Prod.mk.injEq .. ▸ h2 : i = 1 ∧ j = 0).2,
            unipotentUpper]
          simp
        rw [hij, differentialJet_zero_elt]
      · rw [if_neg h2]
        have hij : unipotentUpper t i j = 1 := by
          rw [unipotentUpper]
          fin_cases i <;> fin_cases j <;> simp_all
        rw [hij]
        by_cases h3 : n = 0
        · subst h3
          rw [if_pos rfl, map_one, differentialJet_zero]
        · rw [if_neg h3, map_zero]
          obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
          rw [differentialJet_one]
  exact congrArg (fun f => f P) key

/-- **The unipotent parameters of a differential-algebraic group satisfy a nonzero linear jet
relation.**  The one input is that the substituted polynomial is nonzero — exactly the statement
that the group does not contain every upper unipotent. -/
theorem exists_nonzero_linear_jet_relation_of_unipotentParams
    {G : Set (Matrix (Fin 2) (Fin 2) U)} {hone hmul hinv}
    {P : DifferentialPolynomial (Fin 2 × Fin 2) U} (hsub : unipotentSubst P ≠ 0)
    (hPG : ∀ g ∈ G, differentialPolynomialEvalOver (K := U)
      (fun q : Fin 2 × Fin 2 => g q.1 q.2) P = 0) :
    ∃ (n : ℕ) (c : Fin (n + 1) → U), (∃ i, c i ≠ 0) ∧
      ∀ t ∈ unipotentParams G hone hmul hinv,
        ∑ i : Fin (n + 1), c i * differentialJet (i : ℕ) t = 0 := by
  refine exists_nonzero_linear_jet_relation_of_addSubgroup
    (unipotentParams G hone hmul hinv) hsub ?_
  intro t ht
  rw [evalOver_unipotentSubst]
  exact hPG _ ht

end

end GaloisForLFunctions.HTGeometry
