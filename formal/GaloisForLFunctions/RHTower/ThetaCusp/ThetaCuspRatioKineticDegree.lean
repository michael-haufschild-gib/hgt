import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticModel
import Mathlib.Tactic.ComputeDegree
import Mathlib.Algebra.Polynomial.Eval.Degree
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity

theorem kineticBlockTerm_degree (d j : ℕ) (c : Poly) :
    (kineticBlockTerm d j c).natDegree≤j+1 := by
  unfold kineticBlockTerm
  apply Polynomial.natDegree_add_le_of_degree_le
  · apply Polynomial.natDegree_add_le_of_degree_le
    · exact Polynomial.natDegree_C_mul_X_pow_le _ _
    · exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (by omega)
  · exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (by omega)

theorem kineticMoment2_degree : kineticMoment2.natDegree≤2 := by
  unfold kineticMoment2
  exact (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_C_mul_X_pow_le clearMoment2KineticCoeff0 0).trans (show 0≤2 by omega)) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_C_mul_X_pow_le clearMoment2KineticCoeff1 1).trans (show 1≤2 by omega)) ((Polynomial.natDegree_C_mul_X_pow_le clearMoment2KineticCoeff2 2).trans (show 2≤2 by omega))))

theorem kineticBlock2_degree : kineticBlock2.natDegree≤2+1 := by
  unfold kineticBlock2
  exact (Polynomial.natDegree_add_le_of_degree_le ((kineticBlockTerm_degree 3 0 clearMoment2KineticCoeff0).trans (show 0+1≤2+1 by omega)) (Polynomial.natDegree_add_le_of_degree_le ((kineticBlockTerm_degree 3 1 clearMoment2KineticCoeff1).trans (show 1+1≤2+1 by omega)) ((kineticBlockTerm_degree 3 2 clearMoment2KineticCoeff2).trans (show 2+1≤2+1 by omega))))

theorem kineticMoment4_degree : kineticMoment4.natDegree≤4 := by
  unfold kineticMoment4
  exact (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_C_mul_X_pow_le clearMoment4KineticCoeff0 0).trans (show 0≤4 by omega)) ((Polynomial.natDegree_C_mul_X_pow_le clearMoment4KineticCoeff1 1).trans (show 1≤4 by omega))) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_C_mul_X_pow_le clearMoment4KineticCoeff2 2).trans (show 2≤4 by omega)) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_C_mul_X_pow_le clearMoment4KineticCoeff3 3).trans (show 3≤4 by omega)) ((Polynomial.natDegree_C_mul_X_pow_le clearMoment4KineticCoeff4 4).trans (show 4≤4 by omega)))))

theorem kineticBlock4_degree : kineticBlock4.natDegree≤4+1 := by
  unfold kineticBlock4
  exact (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le ((kineticBlockTerm_degree 5 0 clearMoment4KineticCoeff0).trans (show 0+1≤4+1 by omega)) ((kineticBlockTerm_degree 5 1 clearMoment4KineticCoeff1).trans (show 1+1≤4+1 by omega))) (Polynomial.natDegree_add_le_of_degree_le ((kineticBlockTerm_degree 5 2 clearMoment4KineticCoeff2).trans (show 2+1≤4+1 by omega)) (Polynomial.natDegree_add_le_of_degree_le ((kineticBlockTerm_degree 5 3 clearMoment4KineticCoeff3).trans (show 3+1≤4+1 by omega)) ((kineticBlockTerm_degree 5 4 clearMoment4KineticCoeff4).trans (show 4+1≤4+1 by omega)))))

theorem kineticMoment6_degree : kineticMoment6.natDegree≤6 := by
  unfold kineticMoment6
  exact (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_C_mul_X_pow_le clearMoment6KineticCoeff0 0).trans (show 0≤6 by omega)) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_C_mul_X_pow_le clearMoment6KineticCoeff1 1).trans (show 1≤6 by omega)) ((Polynomial.natDegree_C_mul_X_pow_le clearMoment6KineticCoeff2 2).trans (show 2≤6 by omega)))) (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_C_mul_X_pow_le clearMoment6KineticCoeff3 3).trans (show 3≤6 by omega)) ((Polynomial.natDegree_C_mul_X_pow_le clearMoment6KineticCoeff4 4).trans (show 4≤6 by omega))) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_C_mul_X_pow_le clearMoment6KineticCoeff5 5).trans (show 5≤6 by omega)) ((Polynomial.natDegree_C_mul_X_pow_le clearMoment6KineticCoeff6 6).trans (show 6≤6 by omega)))))

theorem kineticBlock6_degree : kineticBlock6.natDegree≤6+1 := by
  unfold kineticBlock6
  exact (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le ((kineticBlockTerm_degree 7 0 clearMoment6KineticCoeff0).trans (show 0+1≤6+1 by omega)) (Polynomial.natDegree_add_le_of_degree_le ((kineticBlockTerm_degree 7 1 clearMoment6KineticCoeff1).trans (show 1+1≤6+1 by omega)) ((kineticBlockTerm_degree 7 2 clearMoment6KineticCoeff2).trans (show 2+1≤6+1 by omega)))) (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le ((kineticBlockTerm_degree 7 3 clearMoment6KineticCoeff3).trans (show 3+1≤6+1 by omega)) ((kineticBlockTerm_degree 7 4 clearMoment6KineticCoeff4).trans (show 4+1≤6+1 by omega))) (Polynomial.natDegree_add_le_of_degree_le ((kineticBlockTerm_degree 7 5 clearMoment6KineticCoeff5).trans (show 5+1≤6+1 by omega)) ((kineticBlockTerm_degree 7 6 clearMoment6KineticCoeff6).trans (show 6+1≤6+1 by omega)))))

theorem kineticMoment8_degree : kineticMoment8.natDegree≤8 := by
  unfold kineticMoment8
  exact (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_C_mul_X_pow_le clearMoment8KineticCoeff0 0).trans (show 0≤8 by omega)) ((Polynomial.natDegree_C_mul_X_pow_le clearMoment8KineticCoeff1 1).trans (show 1≤8 by omega))) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_C_mul_X_pow_le clearMoment8KineticCoeff2 2).trans (show 2≤8 by omega)) ((Polynomial.natDegree_C_mul_X_pow_le clearMoment8KineticCoeff3 3).trans (show 3≤8 by omega)))) (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_C_mul_X_pow_le clearMoment8KineticCoeff4 4).trans (show 4≤8 by omega)) ((Polynomial.natDegree_C_mul_X_pow_le clearMoment8KineticCoeff5 5).trans (show 5≤8 by omega))) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_C_mul_X_pow_le clearMoment8KineticCoeff6 6).trans (show 6≤8 by omega)) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_C_mul_X_pow_le clearMoment8KineticCoeff7 7).trans (show 7≤8 by omega)) ((Polynomial.natDegree_C_mul_X_pow_le clearMoment8KineticCoeff8 8).trans (show 8≤8 by omega))))))

theorem kineticBlock8_degree : kineticBlock8.natDegree≤8+1 := by
  unfold kineticBlock8
  exact (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le ((kineticBlockTerm_degree 9 0 clearMoment8KineticCoeff0).trans (show 0+1≤8+1 by omega)) ((kineticBlockTerm_degree 9 1 clearMoment8KineticCoeff1).trans (show 1+1≤8+1 by omega))) (Polynomial.natDegree_add_le_of_degree_le ((kineticBlockTerm_degree 9 2 clearMoment8KineticCoeff2).trans (show 2+1≤8+1 by omega)) ((kineticBlockTerm_degree 9 3 clearMoment8KineticCoeff3).trans (show 3+1≤8+1 by omega)))) (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le ((kineticBlockTerm_degree 9 4 clearMoment8KineticCoeff4).trans (show 4+1≤8+1 by omega)) ((kineticBlockTerm_degree 9 5 clearMoment8KineticCoeff5).trans (show 5+1≤8+1 by omega))) (Polynomial.natDegree_add_le_of_degree_le ((kineticBlockTerm_degree 9 6 clearMoment8KineticCoeff6).trans (show 6+1≤8+1 by omega)) (Polynomial.natDegree_add_le_of_degree_le ((kineticBlockTerm_degree 9 7 clearMoment8KineticCoeff7).trans (show 7+1≤8+1 by omega)) ((kineticBlockTerm_degree 9 8 clearMoment8KineticCoeff8).trans (show 8+1≤8+1 by omega))))))

theorem kineticMoment10_degree : kineticMoment10.natDegree≤10 := by
  unfold kineticMoment10
  exact (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_C_mul_X_pow_le clearMoment10KineticCoeff0 0).trans (show 0≤10 by omega)) ((Polynomial.natDegree_C_mul_X_pow_le clearMoment10KineticCoeff1 1).trans (show 1≤10 by omega))) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_C_mul_X_pow_le clearMoment10KineticCoeff2 2).trans (show 2≤10 by omega)) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_C_mul_X_pow_le clearMoment10KineticCoeff3 3).trans (show 3≤10 by omega)) ((Polynomial.natDegree_C_mul_X_pow_le clearMoment10KineticCoeff4 4).trans (show 4≤10 by omega))))) (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_C_mul_X_pow_le clearMoment10KineticCoeff5 5).trans (show 5≤10 by omega)) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_C_mul_X_pow_le clearMoment10KineticCoeff6 6).trans (show 6≤10 by omega)) ((Polynomial.natDegree_C_mul_X_pow_le clearMoment10KineticCoeff7 7).trans (show 7≤10 by omega)))) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_C_mul_X_pow_le clearMoment10KineticCoeff8 8).trans (show 8≤10 by omega)) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_C_mul_X_pow_le clearMoment10KineticCoeff9 9).trans (show 9≤10 by omega)) ((Polynomial.natDegree_C_mul_X_pow_le clearMoment10KineticCoeff10 10).trans (show 10≤10 by omega))))))

theorem kineticBlock10_degree : kineticBlock10.natDegree≤10+1 := by
  unfold kineticBlock10
  exact (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le ((kineticBlockTerm_degree 11 0 clearMoment10KineticCoeff0).trans (show 0+1≤10+1 by omega)) ((kineticBlockTerm_degree 11 1 clearMoment10KineticCoeff1).trans (show 1+1≤10+1 by omega))) (Polynomial.natDegree_add_le_of_degree_le ((kineticBlockTerm_degree 11 2 clearMoment10KineticCoeff2).trans (show 2+1≤10+1 by omega)) (Polynomial.natDegree_add_le_of_degree_le ((kineticBlockTerm_degree 11 3 clearMoment10KineticCoeff3).trans (show 3+1≤10+1 by omega)) ((kineticBlockTerm_degree 11 4 clearMoment10KineticCoeff4).trans (show 4+1≤10+1 by omega))))) (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le ((kineticBlockTerm_degree 11 5 clearMoment10KineticCoeff5).trans (show 5+1≤10+1 by omega)) (Polynomial.natDegree_add_le_of_degree_le ((kineticBlockTerm_degree 11 6 clearMoment10KineticCoeff6).trans (show 6+1≤10+1 by omega)) ((kineticBlockTerm_degree 11 7 clearMoment10KineticCoeff7).trans (show 7+1≤10+1 by omega)))) (Polynomial.natDegree_add_le_of_degree_le ((kineticBlockTerm_degree 11 8 clearMoment10KineticCoeff8).trans (show 8+1≤10+1 by omega)) (Polynomial.natDegree_add_le_of_degree_le ((kineticBlockTerm_degree 11 9 clearMoment10KineticCoeff9).trans (show 9+1≤10+1 by omega)) ((kineticBlockTerm_degree 11 10 clearMoment10KineticCoeff10).trans (show 10+1≤10+1 by omega))))))

theorem completeKineticSlope_degree : completeKineticSlope.natDegree≤19 := by
  have h2 := kineticMoment2_degree
  have h4 := kineticMoment4_degree
  have h6 := kineticMoment6_degree
  have h8 := kineticMoment8_degree
  have h10 := kineticMoment10_degree
  have b2 := kineticBlock2_degree
  have b4 := kineticBlock4_degree
  have b6 := kineticBlock6_degree
  have b8 := kineticBlock8_degree
  have b10 := kineticBlock10_degree
  unfold completeKineticSlope cof2_75 cof4_75 cof6_75 cof8_75 cof10_75
  compute_degree!
  omega

theorem completeKineticSlope_expansion : clearSlope=
    ∑ j ∈ Finset.range 20, completeKineticSlope.coeff j*(X Coord.J)^j := by
  rw [←completeKineticSlope_read]
  change completeKineticSlope.eval (X Coord.J)=_
  exact Polynomial.eval_eq_sum_range' (by have := completeKineticSlope_degree; omega) _

end
end HTGeometry.ThetaRatioKineticContraction
