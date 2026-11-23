import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.Stability.OccupationGaps
import GaloisForLFunctions.HTGeometry.IndexedDiagonalApproximation

/-! # Approximation numbers of squared critical heat -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open ContinuousLinearMap

/-- The decreasing singular values of squared critical heat are the occupation weights. -/
theorem squareHeat_approxNumber (k : ℕ) :
    _root_.RHTower.approxNumber squareHeat.val k = occupationWeight k := by
  let e : ℕ ≃ ℕ+ := Equiv.ofBijective number ⟨number_injective,number_surjective⟩
  let m (i : ℕ+) : ℂ := (occupationWeight (e.symm i):ℝ)
  have hm (i : ℕ+) : ‖m i‖ = occupationWeight (e.symm i) :=
    (Complex.norm_real _).trans (Real.norm_of_nonneg (occupationWeight_pos _).le)
  have h := _root_.HTGeometry.approxNumber_ellTwoDiagonal_reindex_eq e hm
    (fun j => (occupationWeight_pos j).le) (fun {_ _} hij => occupationWeight_antitone hij) k
  have hop : squareHeat.val = _root_.HTGeometry.ellTwoDiagonal m
      (fun i => (hm i).trans_le (occupationWeight_antitone (Nat.zero_le _))) := by
    apply ContinuousLinearMap.ext
    intro f
    apply lp.ext
    funext i
    obtain ⟨j,rfl⟩ := e.surjective i
    change criticalOperator (criticalOperator f) (e j) = m (e j)*f (e j)
    rw [critical_apply,critical_apply]
    simp only [m,e.symm_apply_apply,occupationWeight,pow_two,Complex.ofReal_mul,mul_assoc]
    rfl
  rw [hop]
  exact h

/-- Total squared occupation weight of the first r modes. -/
def traceCeiling (r : ℕ) : ℝ := ∑ k ∈ Finset.range r, occupationWeight k ^ 2

theorem traceCeiling_succ (r : ℕ) : traceCeiling (r+1)-traceCeiling r = (((r:ℝ)+1)⁻¹)^2 := by
  rw [traceCeiling,Finset.sum_range_succ,traceCeiling,add_sub_cancel_left,occupationWeight_eq]

#print axioms squareHeat_approxNumber
#print axioms traceCeiling_succ

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
