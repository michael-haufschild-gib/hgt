import GaloisForLFunctions.HTGeometry.ChronologicalTensor.RecoverySurgeryCoefficients

/-!
# Sharp recovery-coefficient duality on finite alternation grids

Interpolation at positive shifted Chebyshev nodes represents the missing
coefficient by alternating weights. Their absolute mass is exactly the
Chebyshev coefficient, giving a sharp bound from these node values alone.
-/

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section
open Polynomial


def recoveryDualWeight (k i : ℕ) : ℝ :=
  (Lagrange.basis (Finset.range (k+2)) (fun j => 2+Chebyshev.node (k+1) j) i).coeff k

theorem recoveryDualWeight_formula (k i : ℕ) (hi : i ≤ k+1) :
    recoveryDualWeight k i =
      (∏ j ∈ (Finset.range (k+2)).erase i, (Chebyshev.node (k+1) i-Chebyshev.node (k+1) j))⁻¹ *
        (-(∑ j ∈ (Finset.range (k+2)).erase i, (2+Chebyshev.node (k+1) j))) := by
  have hi' : i ∈ Finset.range (k+2) := Finset.mem_range.mpr (by omega)
  have hf : Lagrange.basis (Finset.range (k+2)) (fun j => 2+Chebyshev.node (k+1) j) i =
      C ((∏ j ∈ (Finset.range (k+2)).erase i,
        (Chebyshev.node (k+1) i-Chebyshev.node (k+1) j))⁻¹) *
      ∏ j ∈ (Finset.range (k+2)).erase i, (X-C (2+Chebyshev.node (k+1) j)) := by
    simp only [Lagrange.basis, Lagrange.basisDivisor, Finset.prod_mul_distrib,
      ← map_prod, ← Finset.prod_inv_distrib]
    congr 2
    apply Finset.prod_congr rfl
    intro j _
    congr 1
    ring
  have hd : (∏ j ∈ (Finset.range (k+2)).erase i,
      (X-C (2+Chebyshev.node (k+1) j))).natDegree = k+1 := by
    rw [natDegree_finsetProd_X_sub_C_eq_card, Finset.card_erase_of_mem hi', Finset.card_range]
    omega
  have hn := nextCoeff_of_natDegree_pos (p := ∏ j ∈ (Finset.range (k+2)).erase i,
    (X-C (2+Chebyshev.node (k+1) j))) (by rw [hd]; omega)
  rw [hd, Nat.add_sub_cancel] at hn
  rw [recoveryDualWeight, hf, coeff_C_mul, ← hn, prod_X_sub_C_nextCoeff]

theorem recoveryDualWeight_sign (k i : ℕ) (hi : i ≤ k+1) :
    (-1 : ℝ)^i*recoveryDualWeight k i ≤ 0 := by
  have hs : 0 ≤ ∑ j ∈ (Finset.range (k+2)).erase i, (2+Chebyshev.node (k+1) j) := by
    apply Finset.sum_nonneg
    intro j _
    have h := Chebyshev.node_mem_Icc (n := k+1) (i := j)
    linarith [h.1]
  have hd := inv_pos.mpr (Chebyshev.zero_lt_prod_node_sub_node hi)
  simp only [mul_inv_rev, ← inv_pow, inv_neg, inv_one] at hd
  rw [recoveryDualWeight_formula k i hi]
  have hh := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hd) (neg_nonpos.mpr hs)
  nlinarith

theorem recoveryDualWeight_abs (k i : ℕ) (hi : i ≤ k+1) :
    |recoveryDualWeight k i| = -((-1 : ℝ)^i*recoveryDualWeight k i) := by
  have h := abs_of_nonpos (recoveryDualWeight_sign k i hi)
  rwa [abs_mul, abs_neg_one_pow, one_mul] at h

theorem recoveryCoefficient_interpolation (k : ℕ) (P : ℝ[X]) (hP : P.natDegree ≤ k+1) :
    P.coeff k = ∑ i ∈ Finset.range (k+2),
      P.eval (2+Chebyshev.node (k+1) i)*recoveryDualWeight k i := by
  have hv : Set.InjOn (fun j => 2+Chebyshev.node (k+1) j) (Finset.range (k+2)) := by
    intro i hi j hj he
    apply (Chebyshev.strictAntiOn_node (k+1)).injOn hi hj
    linarith
  have hd : P.degree < (Finset.range (k+2)).card := by
    rw [Finset.card_range]
    exact (degree_le_of_natDegree_le hP).trans_lt (by exact_mod_cast (show k+1<k+2 by omega))
  have h := congrArg (fun Q : ℝ[X] => Q.coeff k) (Lagrange.eq_interpolate hv hd)
  simpa only [recoveryDualWeight, Lagrange.interpolate_apply, finsetSum_coeff, coeff_C_mul] using h

theorem recoveryChebyshev_shifted_node (k i : ℕ) (hi : i ≤ k+1) :
    (taylor (-2 : ℝ) (Chebyshev.T ℝ ((k+1 : ℕ) : ℤ))).eval
      (2+Chebyshev.node (k+1) i) = (-1 : ℝ)^i := by
  rw [taylor_eval]
  have he : 2+Chebyshev.node (k+1) i+(-2) = Chebyshev.node (k+1) i := by ring
  rw [he, Chebyshev.eval_T_real_node (Finset.mem_Iic.mpr hi)]

theorem recoveryDualWeight_mass (k : ℕ) :
    ∑ i ∈ Finset.range (k+2), |recoveryDualWeight k i| = (k+1 : ℝ)*(2 : ℝ)^(k+1) := by
  have hs := recoveryCoefficient_interpolation k
    (taylor (-2 : ℝ) (Chebyshev.T ℝ ((k+1 : ℕ) : ℤ)))
    (by rw [natDegree_taylor, Chebyshev.natDegree_T, Int.natAbs_natCast])
  rw [recoveryChebyshev_shifted_penultimate] at hs
  have he : (∑ i ∈ Finset.range (k+2), |recoveryDualWeight k i|) =
      -(∑ i ∈ Finset.range (k+2),
        (taylor (-2 : ℝ) (Chebyshev.T ℝ ((k+1 : ℕ) : ℤ))).eval
          (2+Chebyshev.node (k+1) i)*recoveryDualWeight k i) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    have hi' : i ≤ k+1 := by simp only [Finset.mem_range] at hi; omega
    rw [recoveryChebyshev_shifted_node k i hi', recoveryDualWeight_abs k i hi']
  rw [he, ← hs]
  ring

theorem recoveryCoefficient_grid_bound (k : ℕ) (P : ℝ[X]) (hP : P.natDegree ≤ k+1)
    (b : ℝ) (hb : ∀ i ≤ k+1, |P.eval (2+Chebyshev.node (k+1) i)| ≤ b) :
    |P.coeff k| ≤ b*((k+1 : ℝ)*(2 : ℝ)^(k+1)) := by
  rw [recoveryCoefficient_interpolation k P hP, ← recoveryDualWeight_mass]
  calc
    _ ≤ ∑ i ∈ Finset.range (k+2),
        |P.eval (2+Chebyshev.node (k+1) i)*recoveryDualWeight k i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range (k+2), b*|recoveryDualWeight k i| := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hb i (by simp only [Finset.mem_range] at hi; omega))
        (abs_nonneg _)
    _ = _ := (Finset.mul_sum _ _ _).symm

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
