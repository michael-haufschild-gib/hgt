import GaloisForLFunctions.HTGeometry.ChronologicalTensor.CubicRecoveryMultiplier
import GaloisForLFunctions.HTGeometry.ChronologicalTensor.CubicHilbertBasis

/-!
# Multiplication by the physical first mode on the actual cusp quotient

The quotient map is exactly [P] ↦ [u P]. It shifts the original monomial classes,
intertwines the physical flow with one additional factor, and is bounded by one
quarter in the graded physical norm. The bound follows from the proved optimal
recovery gaps, with infinite sums justified by finite polynomial support.
-/


namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section
open Set Polynomial
attribute [local instance] cubicGradedLineNormedGroup cubicGradedLineInnerProductSpace
  cubicGradedLine_complete

def cubicCuspDefectMultiplyFirst :
    (Polynomial (Polynomial ℝ) ⧸ cubicCuspAlgebra.toSubmodule) →ₗ[ℝ]
      (Polynomial (Polynomial ℝ) ⧸ cubicCuspAlgebra.toSubmodule) :=
  cubicCuspDefectEquiv.symm.toLinearMap.comp
    ((LinearMap.mulLeft ℝ (Polynomial.X : Polynomial ℝ)).comp cubicCuspDefectEquiv.toLinearMap)

theorem cubicCuspDefectMultiplyFirst_coordinate
    (x : Polynomial (Polynomial ℝ) ⧸ cubicCuspAlgebra.toSubmodule) :
    cubicCuspDefectEquiv (cubicCuspDefectMultiplyFirst x)=
      Polynomial.X*cubicCuspDefectEquiv x := by
  exact cubicCuspDefectEquiv.apply_symm_apply _

theorem cubicCuspDefectMultiplyFirst_mk (P : Polynomial (Polynomial ℝ)) :
    cubicCuspDefectMultiplyFirst (Submodule.Quotient.mk P)=
      Submodule.Quotient.mk (Polynomial.C Polynomial.X*P) := by
  apply cubicCuspDefectEquiv.injective
  rw [cubicCuspDefectMultiplyFirst_coordinate,cubicCuspDefectEquiv_mk,
    cubicCuspDefectEquiv_mk,Polynomial.coeff_C_mul]

theorem cubicCuspDefectMultiplyFirst_basis (k : ℕ) :
    cubicCuspDefectMultiplyFirst (cubicCuspDefectBasis k)=cubicCuspDefectBasis (k+1) := by
  rw [cubicCuspDefectBasis_apply,cubicCuspDefectMultiplyFirst_mk,cubicCuspDefectBasis_apply]
  congr 1
  rw [← mul_assoc,← map_mul,pow_succ]
  congr 2
  ring

theorem cubicCuspDefectMultiplyFirst_flow (q : ℝ)
    (x : Polynomial (Polynomial ℝ) ⧸ cubicCuspAlgebra.toSubmodule) :
    cubicCuspDefectFlow q (cubicCuspDefectMultiplyFirst x)=
      q • cubicCuspDefectMultiplyFirst (cubicCuspDefectFlow q x) := by
  have h : (cubicCuspDefectFlow q).comp cubicCuspDefectMultiplyFirst=
      q • cubicCuspDefectMultiplyFirst.comp (cubicCuspDefectFlow q) := by
    apply cubicCuspDefectBasis.ext
    intro k
    simp only [LinearMap.comp_apply,LinearMap.smul_apply,cubicCuspDefectMultiplyFirst_basis,
      cubicCuspDefectFlow_spectrum,map_smul,smul_smul,pow_succ]
    congr 1
    ring
  exact congrArg (fun f => f x) h

theorem cubicPolynomialWeightedCoefficients_summable (w : ℕ → ℝ) (p : Polynomial ℝ) :
    Summable (fun k : ℕ => w k*(p.coeff k)^(2:ℕ)) := by
  apply summable_of_ne_finset_zero (s := p.support)
  intro k hk
  have hc : p.coeff k=0 := by simpa only [Polynomial.mem_support_iff,not_not] using hk
  rw [hc,zero_pow (show (2:ℕ)≠0 by omega),mul_zero]

theorem cubicPolynomialWeightedShift_tsum (w : ℕ → ℝ) (p : Polynomial ℝ) :
    (∑' k : ℕ, w k*((Polynomial.X*p).coeff k)^(2:ℕ))=∑' k : ℕ, w (k+1)*(p.coeff k)^(2:ℕ) := by
  let f : ℕ → ℝ := fun k : ℕ => w k*((Polynomial.X*p).coeff k)^(2:ℕ)
  have hs : Summable (fun k : ℕ => f (k+1)) := by
    simp only [f,Polynomial.coeff_X_mul]
    exact cubicPolynomialWeightedCoefficients_summable _ _
  have hh := tsum_eq_zero_add' (f := f) hs
  simpa only [f,Polynomial.coeff_X_mul_zero,zero_pow (show (2:ℕ)≠0 by omega),mul_zero,zero_add,
    Polynomial.coeff_X_mul] using hh

theorem cubicCuspDefectMultiplyFirst_norm_sq
    (x : Polynomial (Polynomial ℝ) ⧸ cubicCuspAlgebra.toSubmodule) :
    ‖cubicDefectHilbertEmbedding (cubicCuspDefectMultiplyFirst x)‖^(2:ℕ)=
      ∑' k : ℕ, (cubicGradedRecoveryGap (k+1))^(2:ℕ)*((cubicCuspDefectEquiv x).coeff k)^(2:ℕ) := by
  rw [cubicDefectHilbertEmbedding_norm_sq,cubicCuspDefectMultiplyFirst_coordinate]
  exact cubicPolynomialWeightedShift_tsum _ _

theorem cubicCuspDefectMultiplyFirst_bound
    (x : Polynomial (Polynomial ℝ) ⧸ cubicCuspAlgebra.toSubmodule) :
    ‖cubicDefectHilbertEmbedding (cubicCuspDefectMultiplyFirst x)‖ ≤
      (1/4:ℝ)*‖cubicDefectHilbertEmbedding x‖ := by
  have hsq : ‖cubicDefectHilbertEmbedding (cubicCuspDefectMultiplyFirst x)‖^(2:ℕ) ≤
      (1/4:ℝ)^(2:ℕ)*‖cubicDefectHilbertEmbedding x‖^(2:ℕ) := by
    rw [cubicCuspDefectMultiplyFirst_norm_sq,cubicDefectHilbertEmbedding_norm_sq,← tsum_mul_left]
    apply Summable.tsum_le_tsum _ (cubicPolynomialWeightedCoefficients_summable _ _)
      ((cubicPolynomialWeightedCoefficients_summable _ _).mul_left _)
    intro k
    have hd := cubicGradedRecoveryGap_successor_bound k
    have hδ := cubicGradedRecoveryGap_positive k
    have hw : (cubicGradedRecoveryGap (k+1))^(2:ℕ) ≤ (1/4:ℝ)^(2:ℕ)*(cubicGradedRecoveryGap k)^(2:ℕ) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hd.2)
        (show 0 ≤ cubicGradedRecoveryGap k/4+cubicGradedRecoveryGap (k+1) by linarith [hd.1])]
    have h := mul_le_mul_of_nonneg_right hw (sq_nonneg ((cubicCuspDefectEquiv x).coeff k))
    nlinarith
  nlinarith [norm_nonneg (cubicDefectHilbertEmbedding (cubicCuspDefectMultiplyFirst x)),
    norm_nonneg (cubicDefectHilbertEmbedding x)]

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
