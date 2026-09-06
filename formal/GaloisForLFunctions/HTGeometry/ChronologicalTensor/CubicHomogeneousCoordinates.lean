import GaloisForLFunctions.HTGeometry.ChronologicalTensor.CubicHomogeneousNorm

/-!
# Exact coordinates for every physical scaling weight

The weight-k space is linearly equivalent to k+1 real coefficients, indexed
by the power of the first mode u. The inverse constructs the corresponding
homogeneous polynomial in u and c. At positive weight k+1, cusp membership
is exactly vanishing of coefficient k, the coefficient of u^k c.
-/

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section
open Polynomial
open scoped BigOperators


def cubicHomogeneousPolynomial (k : ℕ) (α : Fin (k+1) → ℝ) : Polynomial (Polynomial ℝ) :=
  ∑ i : Fin (k+1), Polynomial.monomial (k-i.val) (Polynomial.monomial i.val (α i))

theorem cubicHomogeneousPolynomial_diagonal (k : ℕ) (α : Fin (k+1) → ℝ) (i : Fin (k+1)) :
    ((cubicHomogeneousPolynomial k α).coeff (k-i.val)).coeff i.val=α i := by
  unfold cubicHomogeneousPolynomial
  rw [Polynomial.finsetSum_coeff,Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j hj hji
    have hn : j.val ≠ i.val := fun h => hji (Fin.ext h)
    simp only [Polynomial.coeff_monomial]
    split_ifs <;> simp [Polynomial.coeff_monomial,hn]
  · simp

theorem cubicHomogeneousPolynomial_offDiagonal (k : ℕ) (α : Fin (k+1) → ℝ) :
    ∀ m n : ℕ, m+n ≠ k → ((cubicHomogeneousPolynomial k α).coeff m).coeff n=0 := by
  intro m n hmn
  unfold cubicHomogeneousPolynomial
  rw [Polynomial.finsetSum_coeff,Polynomial.finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro i hi
  by_cases hm : k-i.val=m
  · have hn : i.val ≠ n := by
      intro he
      have hki : i.val ≤ k := by omega
      have h := Nat.sub_add_cancel hki
      exact hmn (by omega)
    simp [Polynomial.coeff_monomial,hm,hn]
  · simp [Polynomial.coeff_monomial,hm]

theorem cubicHomogeneousPolynomial_mem (k : ℕ) (α : Fin (k+1) → ℝ) :
    cubicHomogeneousPolynomial k α ∈ cubicHomogeneousSpace k := by
  rw [cubicHomogeneousSpace_mem,cubicPolynomialFlow_halfWeight]
  exact cubicHomogeneousPolynomial_offDiagonal k α

def cubicHomogeneousCoordinates (k : ℕ) (P : cubicHomogeneousSpace k) : Fin (k+1) → ℝ :=
  fun i => (P.val.coeff (k-i.val)).coeff i.val

theorem cubicHomogeneousCoordinates_reconstruct (k : ℕ) (P : cubicHomogeneousSpace k) :
    cubicHomogeneousPolynomial k (cubicHomogeneousCoordinates k P)=P.val := by
  have hP := (cubicPolynomialFlow_halfWeight P.val k).mp
    ((cubicHomogeneousSpace_mem k P.val).mp P.property)
  ext m n
  by_cases hmn : m+n=k
  · have hn : n<k+1 := by omega
    have hm : k-n=m := by omega
    have h := cubicHomogeneousPolynomial_diagonal k (cubicHomogeneousCoordinates k P) ⟨n,hn⟩
    simpa only [cubicHomogeneousCoordinates,hm] using h
  · rw [cubicHomogeneousPolynomial_offDiagonal k _ m n hmn,hP m n hmn]

def cubicHomogeneousCoordinatesEquiv (k : ℕ) :
    cubicHomogeneousSpace k ≃ₗ[ℝ] (Fin (k+1) → ℝ) where
  toFun := cubicHomogeneousCoordinates k
  invFun α := ⟨cubicHomogeneousPolynomial k α,cubicHomogeneousPolynomial_mem k α⟩
  left_inv P := Subtype.ext (cubicHomogeneousCoordinates_reconstruct k P)
  right_inv α := by
    funext i
    exact cubicHomogeneousPolynomial_diagonal k α i
  map_add' P Q := by
    funext i
    change ((P.val+Q.val).coeff (k-i.val)).coeff i.val=
      (P.val.coeff (k-i.val)).coeff i.val+(Q.val.coeff (k-i.val)).coeff i.val
    rw [Polynomial.coeff_add,Polynomial.coeff_add]
  map_smul' r P := by
    funext i
    change ((r • P.val).coeff (k-i.val)).coeff i.val=r*((P.val.coeff (k-i.val)).coeff i.val)
    rw [Polynomial.coeff_smul,Polynomial.coeff_smul,smul_eq_mul]


theorem cubicHomogeneousSpace_finrank (k : ℕ) : Module.finrank ℝ (cubicHomogeneousSpace k)=k+1 := by
  rw [(cubicHomogeneousCoordinatesEquiv k).finrank_eq,Module.finrank_fin_fun]

theorem cubicHomogeneousCoordinates_cusp (k : ℕ) (P : cubicHomogeneousSpace (k+1)) :
    P.val ∈ cubicCuspAlgebra ↔ cubicHomogeneousCoordinates (k+1) P ⟨k,by omega⟩=0 := by
  have hk : k+1-k=1 := by omega
  change P.val.coeff 1=0 ↔ (P.val.coeff (k+1-k)).coeff k=0
  rw [hk]
  constructor
  · intro h
    rw [h,Polynomial.coeff_zero]
  · intro h
    have hP := (cubicPolynomialFlow_halfWeight P.val (k+1)).mp
      ((cubicHomogeneousSpace_mem (k+1) P.val).mp P.property)
    ext n
    by_cases hn : n=k
    · subst n
      simpa only [Polynomial.coeff_zero] using h
    · simpa only [Polynomial.coeff_zero] using hP 1 n (by omega)

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
