import GaloisForLFunctions.HTGeometry.ChronologicalTensor.CubicHomogeneousCoordinates

/-!
# The physical homogeneous norm is a weighted polynomial norm

Exact coefficient coordinates give a univariate polynomial R of degree at
most k. On the realized edge, the observation is c^k R(c/2-c^2/4).
The physical capacity is precisely the weighted supremum on [0,1], with
no division by c and no exception at the origin.
-/

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section
open Set Polynomial
open scoped BigOperators


def cubicDehomogeneousPolynomial (k : ℕ) (α : Fin (k+1) → ℝ) : Polynomial ℝ :=
  ∑ i : Fin (k+1), Polynomial.monomial i.val (α i)

theorem cubicDehomogeneousPolynomial_coefficient (k : ℕ) (α : Fin (k+1) → ℝ) (i : Fin (k+1)) :
    (cubicDehomogeneousPolynomial k α).coeff i.val=α i := by
  unfold cubicDehomogeneousPolynomial
  rw [Polynomial.finsetSum_coeff,Finset.sum_eq_single i]
  · simp
  · intro j hj hji
    have hn : j.val ≠ i.val := fun h => hji (Fin.ext h)
    simp [Polynomial.coeff_monomial,hn]
  · simp

theorem cubicDehomogeneousPolynomial_degree (k : ℕ) (α : Fin (k+1) → ℝ) :
    (cubicDehomogeneousPolynomial k α).natDegree ≤ k := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro n hn
  unfold cubicDehomogeneousPolynomial
  rw [Polynomial.finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro i hi
  have hne : i.val ≠ n := by omega
  simp [Polynomial.coeff_monomial,hne]

theorem cubicDehomogeneousPolynomial_evaluation (k : ℕ) (α : Fin (k+1) → ℝ) (r : ℝ) :
    (cubicDehomogeneousPolynomial k α).eval r=∑ i : Fin (k+1), α i*r^i.val := by
  simp only [cubicDehomogeneousPolynomial,Polynomial.eval_finsetSum,Polynomial.eval_monomial]

def cubicEdgeRatio (c : ℝ) : ℝ := c/2-c^2/4

theorem cubicHomogeneousPolynomial_edge (k : ℕ) (α : Fin (k+1) → ℝ) (c : ℝ) :
    cubicEdgeProfile (cubicHomogeneousPolynomial k α) c=
      c^k*(cubicDehomogeneousPolynomial k α).eval (cubicEdgeRatio c) := by
  unfold cubicHomogeneousPolynomial cubicEdgeProfile
  rw [Polynomial.eval₂_finsetSum,cubicDehomogeneousPolynomial_evaluation,Finset.mul_sum]
  simp only [Polynomial.eval₂_monomial,Polynomial.coe_evalRingHom,Polynomial.eval_monomial]
  apply Finset.sum_congr rfl
  intro i hi
  have hL : cubicRecoveryLower c=c*cubicEdgeRatio c := by
    unfold cubicRecoveryLower cubicEdgeRatio
    ring
  rw [hL,mul_pow]
  have he : i.val+(k-i.val)=k := by omega
  calc
    α i*(c^i.val*cubicEdgeRatio c^i.val)*c^(k-i.val)=
        α i*(c^i.val*c^(k-i.val))*cubicEdgeRatio c^i.val := by ring
    _=c^k*(α i*cubicEdgeRatio c^i.val) := by rw [← pow_add,he]; ring

def cubicWeightedPolynomialNorm (k : ℕ) (α : Fin (k+1) → ℝ) : ℝ :=
  sSup ((fun c : ℝ => c^k*|(cubicDehomogeneousPolynomial k α).eval (cubicEdgeRatio c)|) '' Icc 0 1)

theorem cubicHomogeneousCapacity_weighted (k : ℕ) (α : Fin (k+1) → ℝ) :
    cubicHomogeneousCapacity k ((cubicHomogeneousCoordinatesEquiv k).symm α)=
      cubicWeightedPolynomialNorm k α := by
  rw [cubicHomogeneousCapacity_edgeSup]
  change sSup ((fun c : ℝ => |cubicEdgeProfile (cubicHomogeneousPolynomial k α) c|) '' Icc 0 1)=_
  unfold cubicWeightedPolynomialNorm
  congr 1
  apply Set.image_congr
  intro c hc
  rw [cubicHomogeneousPolynomial_edge,abs_mul,abs_of_nonneg (pow_nonneg hc.1 k)]

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
