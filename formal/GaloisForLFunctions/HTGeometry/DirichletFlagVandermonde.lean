import GaloisForLFunctions.HTGeometry.GammaShiftCasoratian

open scoped BigOperators

namespace GaloisForLFunctions

open Matrix

noncomputable section

def dirichletFlagPositiveProduct (q : ℕ) : ℝ :=
  ∏ i : Fin q, ∏ j ∈ Finset.Ioi i,
    (dirichletReciprocalNode i - dirichletReciprocalNode j) *
      (dirichletLogNode i - dirichletLogNode j)

theorem dirichletFlagVandermonde_eq_positiveProduct (q : ℕ) :
    dirichletFlagVandermonde q = dirichletFlagPositiveProduct q := by
  rw [dirichletFlagVandermonde, Matrix.det_vandermonde, Matrix.det_vandermonde,
    dirichletFlagPositiveProduct]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  ring

theorem dirichletReciprocalNode_sub_pos {q : ℕ} {i j : Fin q} (hij : i < j) :
    0 < dirichletReciprocalNode i - dirichletReciprocalNode j := by
  rw [sub_pos]
  have hab : ((((i : ℕ) + 1 : ℕ) : ℝ)) < (((j : ℕ) + 1 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.add_lt_add_right hij 1)
  simpa [dirichletReciprocalNode, one_div] using
    (one_div_lt_one_div_of_lt (α := ℝ) (by positivity) hab)

theorem dirichletLogNode_sub_pos {q : ℕ} {i j : Fin q} (hij : i < j) :
    0 < dirichletLogNode i - dirichletLogNode j := by
  rw [sub_pos]
  change -Real.log (((j : ℕ) + 1 : ℕ) : ℝ) <
    -Real.log (((i : ℕ) + 1 : ℕ) : ℝ)
  rw [neg_lt_neg_iff]
  have hab : ((((i : ℕ) + 1 : ℕ) : ℝ)) < (((j : ℕ) + 1 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.add_lt_add_right hij 1)
  have hai : 0 < ((((i : ℕ) + 1 : ℕ) : ℝ)) := by positivity
  have haj : 0 < ((((j : ℕ) + 1 : ℕ) : ℝ)) := by positivity
  exact Real.strictMonoOn_log hai haj hab

/-- Equation (D3): the double Vandermonde of the initial Dirichlet flag is positive. -/
theorem dirichletFlagVandermonde_pos (q : ℕ) :
    0 < dirichletFlagVandermonde q := by
  rw [dirichletFlagVandermonde_eq_positiveProduct, dirichletFlagPositiveProduct]
  apply Finset.prod_pos
  intro i _
  apply Finset.prod_pos
  intro j hj
  exact mul_pos (dirichletReciprocalNode_sub_pos (Finset.mem_Ioi.mp hj))
    (dirichletLogNode_sub_pos (Finset.mem_Ioi.mp hj))

end
end GaloisForLFunctions
