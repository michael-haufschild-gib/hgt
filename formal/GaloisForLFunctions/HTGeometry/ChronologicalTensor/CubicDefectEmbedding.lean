import GaloisForLFunctions.HTGeometry.ChronologicalTensor.CubicDefectHilbert
import GaloisForLFunctions.HTGeometry.ChronologicalTensor.CubicCuspQuotient

/-!
# Dense embedding of the actual normalization defect into its graded Hilbert sum

The monomial-basis construction embeds the already identified quotient B/A.
Its coordinate maps recover exactly the missing outer-linear coefficients,
so the embedding is injective and has the explicit physical weighted norm.
Every single-grade vector is in its range, which proves density by grade sums.
-/

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section
open Set Polynomial

attribute [local instance] cubicGradedLineNormedGroup cubicGradedLineInnerProductSpace
  cubicGradedLine_complete


def cubicGradedCoordinateLinearEquiv (k : ℕ) : cubicGradedDefect k ≃ₗ[ℝ] ℝ where
  toEquiv := cubicGradedDefectEquiv k
  map_add' x y := by
    have h := (cubicGradedLineLinearEquiv k).map_add x y
    change cubicGradedRecoveryGap k*cubicGradedDefectCoordinate k (x+y)=
      cubicGradedRecoveryGap k*cubicGradedDefectCoordinate k x+
      cubicGradedRecoveryGap k*cubicGradedDefectCoordinate k y at h
    rw [← mul_add] at h
    exact mul_left_cancel₀ (cubicGradedRecoveryGap_positive k).ne' h
  map_smul' r x := by
    have h := (cubicGradedLineLinearEquiv k).map_smul r x
    change cubicGradedRecoveryGap k*cubicGradedDefectCoordinate k (r • x)=
      r*(cubicGradedRecoveryGap k*cubicGradedDefectCoordinate k x) at h
    rw [mul_left_comm r] at h
    exact mul_left_cancel₀ (cubicGradedRecoveryGap_positive k).ne' h

def cubicDefectHilbertCoefficient (k : ℕ) : cubicDefectHilbert →ₗ[ℝ] ℝ :=
  (cubicGradedCoordinateLinearEquiv k).toLinearMap.comp (lp.evalₗ cubicGradedDefect 2 k)

theorem cubicDefectHilbertCoefficient_apply (k : ℕ) (x : cubicDefectHilbert) :
    cubicDefectHilbertCoefficient k x=cubicGradedDefectCoordinate k (x k) := rfl

def cubicDefectHilbertPolynomial : Polynomial ℝ →ₗ[ℝ] cubicDefectHilbert :=
  (Polynomial.basisMonomials ℝ).constr ℝ (fun k =>
    cubicDefectHilbertSingle k (cubicGradedDefectMk k (cubicHomogeneousMissing k)))

theorem cubicDefectHilbertPolynomial_basis (k : ℕ) :
    cubicDefectHilbertPolynomial ((Polynomial.basisMonomials ℝ) k)=
      cubicDefectHilbertSingle k (cubicGradedDefectMk k (cubicHomogeneousMissing k)) :=
  (Polynomial.basisMonomials ℝ).constr_basis ℝ _ k

theorem cubicDefectHilbertCoefficient_generator (i k : ℕ) :
    cubicDefectHilbertCoefficient i
      (cubicDefectHilbertSingle k (cubicGradedDefectMk k (cubicHomogeneousMissing k)))=
      if i=k then 1 else 0 := by
  by_cases h : i=k
  · subst k
    rw [cubicDefectHilbertCoefficient_apply,cubicDefectHilbertSingle,lp.single_apply_self,
      cubicGradedDefectCoordinate_mk,cubicGradedCoefficient_missing,if_pos rfl]
  · rw [cubicDefectHilbertCoefficient_apply,cubicDefectHilbertSingle,
      lp.single_apply_ne 2 k _ h,if_neg h]
    exact (cubicGradedCoordinateLinearEquiv i).map_zero

theorem cubicDefectHilbertPolynomial_coefficient (k : ℕ) (p : Polynomial ℝ) :
    cubicDefectHilbertCoefficient k (cubicDefectHilbertPolynomial p)=p.coeff k := by
  have h : (cubicDefectHilbertCoefficient k).comp cubicDefectHilbertPolynomial=
      Polynomial.lcoeff ℝ k := by
    apply (Polynomial.basisMonomials ℝ).ext
    intro n
    rw [LinearMap.comp_apply,cubicDefectHilbertPolynomial_basis,
      cubicDefectHilbertCoefficient_generator]
    simp [Polynomial.coe_basisMonomials,Polynomial.coeff_monomial,eq_comm]
  exact congrArg (fun f : Polynomial ℝ →ₗ[ℝ] ℝ => f p) h

theorem cubicDefectHilbertPolynomial_injective : Function.Injective cubicDefectHilbertPolynomial := by
  intro p q h
  apply Polynomial.ext
  intro k
  have hk := congrArg (cubicDefectHilbertCoefficient k) h
  simpa only [cubicDefectHilbertPolynomial_coefficient] using hk

def cubicDefectHilbertEmbedding :
    (Polynomial (Polynomial ℝ) ⧸ cubicCuspAlgebra.toSubmodule) →ₗ[ℝ] cubicDefectHilbert :=
  cubicDefectHilbertPolynomial.comp cubicCuspDefectEquiv.toLinearMap

theorem cubicDefectHilbertEmbedding_injective : Function.Injective cubicDefectHilbertEmbedding :=
  cubicDefectHilbertPolynomial_injective.comp cubicCuspDefectEquiv.injective

theorem cubicDefectHilbertEmbedding_coefficient
    (x : Polynomial (Polynomial ℝ) ⧸ cubicCuspAlgebra.toSubmodule) (k : ℕ) :
    cubicDefectHilbertCoefficient k (cubicDefectHilbertEmbedding x)=
      (cubicCuspDefectEquiv x).coeff k :=
  cubicDefectHilbertPolynomial_coefficient k (cubicCuspDefectEquiv x)

theorem cubicDefectHilbertEmbedding_norm_sq
    (x : Polynomial (Polynomial ℝ) ⧸ cubicCuspAlgebra.toSubmodule) :
    ‖cubicDefectHilbertEmbedding x‖^(2 : ℕ)=∑' k, (cubicGradedRecoveryGap k)^(2 : ℕ) *
      ((cubicCuspDefectEquiv x).coeff k)^(2 : ℕ) := by
  rw [cubicDefectHilbert_norm_sq]
  congr 1
  funext k
  rw [← cubicDefectHilbertCoefficient_apply,cubicDefectHilbertEmbedding_coefficient]


theorem cubicDefectHilbertEmbedding_single_mem_range (k : ℕ) (x : cubicGradedDefect k) :
    cubicDefectHilbertSingle k x ∈ LinearMap.range cubicDefectHilbertEmbedding := by
  let r := cubicGradedDefectCoordinate k x
  have hx : r • cubicGradedDefectMk k (cubicHomogeneousMissing k)=x := by
    apply (cubicGradedCoordinateLinearEquiv k).injective
    rw [map_smul]
    change r*cubicGradedCoefficient k (cubicHomogeneousMissing k)=r
    rw [cubicGradedCoefficient_missing,mul_one]
  refine ⟨cubicCuspDefectEquiv.symm (r • (Polynomial.basisMonomials ℝ) k),?_⟩
  change cubicDefectHilbertPolynomial
    (cubicCuspDefectEquiv (cubicCuspDefectEquiv.symm (r • (Polynomial.basisMonomials ℝ) k)))=_
  rw [LinearEquiv.apply_symm_apply,map_smul,cubicDefectHilbertPolynomial_basis]
  change r • lp.single 2 k (cubicGradedDefectMk k (cubicHomogeneousMissing k))=lp.single 2 k x
  rw [← lp.single_smul,hx]

theorem cubicDefectHilbertEmbedding_denseRange : DenseRange cubicDefectHilbertEmbedding := by
  intro x
  let S := LinearMap.range cubicDefectHilbertEmbedding
  have hs : ∀ t : Finset ℕ, ∑ k ∈ t, cubicDefectHilbertSingle k (x k) ∈
      closure (S : Set cubicDefectHilbert) := by
    intro t
    exact S.le_topologicalClosure (S.sum_mem (fun k _ =>
      cubicDefectHilbertEmbedding_single_mem_range k (x k)))
  exact isClosed_closure.mem_of_tendsto (cubicDefectHilbert_hasSum x)
    (Filter.Eventually.of_forall hs)

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
