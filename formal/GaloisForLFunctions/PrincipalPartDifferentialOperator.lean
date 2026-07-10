import GaloisForLFunctions.OrbitResidueVector

/-!
# Differential operators on simple Laurent principal parts

The `n`th derivative of a simple pole with coefficient `c` has top Laurent coefficient
`(-1)^n n! c` at order `n+1`.  This file packages the action of a constant-coefficient
differential operator on that formal principal part and proves that a nonzero operator cannot
annihilate a nonzero simple pole in characteristic zero.  Combined with orbit-residue vectors, two
opposite simple poles on distinct translation orbits remain a non-coboundary after every nonzero
constant-coefficient differential operator.
-/

namespace GaloisForLFunctions
noncomputable section

/-- The formal Laurent principal part obtained by applying `L` to a simple pole of coefficient
`c`; index `m` records the coefficient of the pole of order `m`. -/
def simplePoleDifferentialOperator
    {C : Type*} [Field C] (L : Polynomial C) (c : C) : ℕ →₀ C :=
  L.sum fun n a =>
    Finsupp.single (n + 1) (a * ((-1 : C) ^ n * (n.factorial : C)) * c)

/-- The top coefficient comes only from the leading differential term. -/
theorem simplePoleDifferentialOperator_coeff_succ_natDegree
    {C : Type*} [Field C] (L : Polynomial C) (c : C) :
    simplePoleDifferentialOperator L c (L.natDegree + 1) =
      L.leadingCoeff * ((-1 : C) ^ L.natDegree * (L.natDegree.factorial : C)) * c := by
  classical
  by_cases hL : L = 0
  · subst L
    simp [simplePoleDifferentialOperator]
  have hNmem := Polynomial.natDegree_mem_support_of_nonzero hL
  rw [simplePoleDifferentialOperator, Polynomial.sum_def]
  rw [Finset.sum_apply']
  rw [Finset.sum_eq_single_of_mem L.natDegree hNmem]
  · simp
  · intro b hb hne
    simp only [Finsupp.single_apply]
    split_ifs with h
    · omega
    · rfl

/-- A nonzero constant-coefficient differential operator preserves a nonzero top principal part
of a simple pole. -/
theorem simplePoleDifferentialOperator_ne_zero
    {C : Type*} [Field C] [CharZero C]
    {L : Polynomial C} (hL : L ≠ 0) {c : C} (hc : c ≠ 0) :
    simplePoleDifferentialOperator L c ≠ 0 := by
  intro hzero
  have hcoeff := congrArg (fun P : ℕ →₀ C => P (L.natDegree + 1)) hzero
  change simplePoleDifferentialOperator L c (L.natDegree + 1) = 0 at hcoeff
  rw [simplePoleDifferentialOperator_coeff_succ_natDegree] at hcoeff
  exact mul_ne_zero
    (mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hL)
      (mul_ne_zero (pow_ne_zero _ (by norm_num))
        (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)))) hc hcoeff

/-- The formal principal-part field of two opposite simple poles after applying `L`. -/
def simplePolePairDifferentialOperator
    {G C : Type*} [AddCommGroup G] [Field C]
    (L : Polynomial C) (c : C) (x y : G) : G →₀ (ℕ →₀ C) :=
  Finsupp.single x (simplePoleDifferentialOperator L c) -
    Finsupp.single y (simplePoleDifferentialOperator L c)

/-- **Differential orbital-residue obstruction.** Two opposite nonzero simple poles on distinct
translation orbits remain outside the finite coboundary image after every nonzero
constant-coefficient differential operator. -/
theorem simplePolePairDifferentialOperator_ne_finiteOrbitCoboundary
    {G C : Type*} [AddCommGroup G] [Field C] [CharZero C]
    (q x y : G) {L : Polynomial C} (hL : L ≠ 0) {c : C} (hc : c ≠ 0)
    (hxy : (x : G ⧸ AddSubgroup.zmultiples q) ≠
      (y : G ⧸ AddSubgroup.zmultiples q))
    (E : G →₀ (ℕ →₀ C)) :
    simplePolePairDifferentialOperator L c x y ≠ finiteOrbitCoboundary q E := by
  exact single_sub_single_ne_finiteOrbitCoboundary_of_orbit_ne q x y
    (simplePoleDifferentialOperator_ne_zero hL hc) hxy E

end
end GaloisForLFunctions
