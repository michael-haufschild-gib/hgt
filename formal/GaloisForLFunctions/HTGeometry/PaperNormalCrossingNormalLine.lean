import GaloisForLFunctions.HTGeometry.PaperVeroneseNormalLine
import GaloisForLFunctions.HTGeometry.CofaceBoundaryReconstruction

/-!
# Polynomial normal directions for source criticalization and coface constraints

The native normal-crossing Jacobian ideal equals the squarefree Veronese
ideal and the weighted coface boundary's maximal-minor ideal. Apply the
paper's exact Rees kernel to an actual gradient component and actual
boundary minor. Both native interfaces acquire polynomial normal lines,
with exact ideal order in every power over every field.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial GaloisForLFunctions.VeroneseIdeal

noncomputable section

variable (K : Type*) [Field K]

/-- Actual gradient and weight proofs supply the normal-crossing normal-line data. -/
def paperNormalCrossingNormalData (r : ℕ) :
    PaperHomogeneousNormalData K (Fin (r + 1 + 1))
      (normalCrossingJacobianIdeal (F := K) (r + 1)) where
  generator := cofaceMonomial (r + 1) 0
  degree := r + 1
  degree_pos := Nat.succ_pos r
  generator_mem := by
    rw [← pderiv_normalCrossingPolynomial (F := K) (r + 1) 0]
    exact Ideal.subset_span ⟨0, rfl⟩
  generator_ne_zero := by
    rw [cofaceMonomial, Finset.prod_ne_zero_iff]
    exact fun j _ => MvPolynomial.X_ne_zero j
  homogeneous := by
    have hh := paperSquarefreeProduct_homogeneous K
      ((Finset.univ : Finset (Fin (r + 1 + 1))).erase 0)
    have hcard : ((Finset.univ : Finset (Fin (r + 1 + 1))).erase 0).card = r + 1 := by simp
    rw [hcard] at hh
    exact paperIsWeightedHomogeneous_int hh
  order_bound := by
    rw [normalCrossingJacobianIdeal_eq_veroneseIdeal]
    exact paperVeroneseIdeal_weightOrder K _ _

/-- Each power of the chosen source gradient component has exact Jacobian-ideal order. -/
theorem paperNormalCrossingCoface_pow_exact (r n : ℕ) :
    cofaceMonomial (F := K) (r + 1) 0 ^ n ∈
        normalCrossingJacobianIdeal (F := K) (r + 1) ^ n ∧
    cofaceMonomial (F := K) (r + 1) 0 ^ n ∉
        normalCrossingJacobianIdeal (F := K) (r + 1) ^ (n + 1) :=
  ⟨(paperNormalCrossingNormalData K r).pow_mem n, (paperNormalCrossingNormalData K r).pow_not_mem_succ n⟩

/-- Polynomial substitution into the source criticalization associated graded ring. -/
def paperNormalCrossingNormalPolynomialMap (r : ℕ) :
    Polynomial K →+* PaperIdealAssociatedGraded (normalCrossingJacobianIdeal (F := K) (r + 1)) :=
  (paperNormalCrossingNormalData K r).polynomialMap

/-- Source criticalization retains an actual polynomial normal direction. -/
theorem paperNormalCrossingNormalPolynomialMap_injective (r : ℕ) :
    Function.Injective (paperNormalCrossingNormalPolynomialMap K r) :=
  (paperNormalCrossingNormalData K r).polynomialMap_injective

/-- The native coface boundary minor ideal inherits the same fully paid data. -/
def paperCofaceBoundaryNormalData (r : ℕ) :
    PaperHomogeneousNormalData K (Fin (r + 1 + 1))
      (cofaceBoundaryMaximalMinorIdeal (F := K) (r + 1)) := by
  rw [cofaceBoundaryMaximalMinorIdeal_eq_normalCrossingJacobianIdeal]
  exact paperNormalCrossingNormalData K r

/-- The actual weighted boundary determinant has exact order in every determinantal power. -/
theorem paperCofaceBoundaryMinor_pow_exact (r n : ℕ) :
    cofaceBoundaryMaximalMinor (F := K) (r + 1) 0 ^ n ∈
        cofaceBoundaryMaximalMinorIdeal (F := K) (r + 1) ^ n ∧
    cofaceBoundaryMaximalMinor (F := K) (r + 1) 0 ^ n ∉
        cofaceBoundaryMaximalMinorIdeal (F := K) (r + 1) ^ (n + 1) := by
  simpa only [cofaceBoundaryMaximalMinor_zero,
    cofaceBoundaryMaximalMinorIdeal_eq_normalCrossingJacobianIdeal]
      using paperNormalCrossingCoface_pow_exact K r n

/-- Polynomial substitution into the native weighted coface associated graded ring. -/
def paperCofaceBoundaryNormalPolynomialMap (r : ℕ) :
    Polynomial K →+* PaperIdealAssociatedGraded (cofaceBoundaryMaximalMinorIdeal (F := K) (r + 1)) :=
  (paperCofaceBoundaryNormalData K r).polynomialMap

/-- The weighted coface boundary ideal retains a polynomial normal direction in every dimension. -/
theorem paperCofaceBoundaryNormalPolynomialMap_injective (r : ℕ) :
    Function.Injective (paperCofaceBoundaryNormalPolynomialMap K r) :=
  (paperCofaceBoundaryNormalData K r).polynomialMap_injective

end

end GaloisForLFunctions.HTGeometry
