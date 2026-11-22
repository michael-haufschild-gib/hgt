import GaloisForLFunctions.HTGeometry.PrimeHodgeSteinGramian

/-!
# Hilbert–Schmidt loss under isometric compression

The loss consists of two squared norms in the orthogonal complement of
the isometry's range. Equality detects the support of a self-adjoint input.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Projection on the missing output directions. -/
def omitted (U : H →ₗᵢ[ℂ] H) : H →L[ℂ] H :=
  1-U.toContinuousLinearMap*star U.toContinuousLinearMap

theorem omitted_self (U : H →ₗᵢ[ℂ] H) : star (omitted U) = omitted U := by
  simp only [omitted,star_sub,star_one,star_mul,star_star]

theorem omitted_idempotent (U : H →ₗᵢ[ℂ] H) : omitted U*omitted U = omitted U := by
  let V := U.toContinuousLinearMap
  have hi : star V*V = 1 := U.adjoint_comp_self
  let P := V*star V
  have hP : P*P = P := by
    change (V*star V)*(V*star V) = _
    rw [mul_assoc V,← mul_assoc (star V),hi,one_mul]
  change (1-P)*(1-P) = 1-P
  calc
    _ = 1-P-P+P*P := by noncomm_ring
    _ = _ := by rw [hP]; abel

private theorem omitted_loss (U : H →ₗᵢ[ℂ] H) {B : H →L[ℂ] H} (hB : B.IsHilbertSchmidt) :
    hsNormSq (omitted U*B) = hsNormSq B-hsNormSq (star U.toContinuousLinearMap*B) := by
  apply HTGeometry.hsNormSq_defect_comp (C := star U.toContinuousLinearMap) _ hB
  change star (omitted U)*omitted U = 1-star (star U.toContinuousLinearMap)*star U.toContinuousLinearMap
  rw [omitted_self,omitted_idempotent,star_star]
  rfl

abbrev HSObservable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] :=
  {A : H →L[ℂ] H // IsSelfAdjoint A ∧ A.IsHilbertSchmidt}

/-- Exact two-term defect of compressing an observable by an isometry. -/
theorem compression_loss (U : H →ₗᵢ[ℂ] H) (A : HSObservable H) :
    hsNormSq A.val-hsNormSq (star U.toContinuousLinearMap*(A.val*U.toContinuousLinearMap)) =
      hsNormSq (omitted U*A.val)+hsNormSq (omitted U*(A.val*U.toContinuousLinearMap)) := by
  let V := U.toContinuousLinearMap
  have hAV : (A.val*V).IsHilbertSchmidt := A.property.2.comp_right V
  have hsym : hsNormSq (star V*A.val) = hsNormSq (A.val*V) := by
    have h := hAV.hsNormSq_adjoint
    change hsNormSq (star (A.val*V)) = _ at h
    rwa [star_mul,A.property.1.star_eq] at h
  rw [omitted_loss U A.property.2,omitted_loss U hAV]
  change hsNormSq A.val-hsNormSq (star V*(A.val*V)) =
    (hsNormSq A.val-hsNormSq (star V*A.val))+(hsNormSq (A.val*V)-hsNormSq (star V*(A.val*V)))
  rw [hsym]; abel

/-- Loss vanishes precisely when the range of the isometry contains the range of the observable. -/
theorem compression_eq_iff (U : H →ₗᵢ[ℂ] H) (A : HSObservable H) :
    hsNormSq (star U.toContinuousLinearMap*(A.val*U.toContinuousLinearMap)) = hsNormSq A.val ↔
      omitted U*A.val = 0 := by
  have h := compression_loss U A
  constructor
  · intro he
    rw [he,sub_self] at h
    apply (hsNormSq_eq_zero_iff (A.property.2.comp_left (omitted U))).mp
    change hsNormSq (omitted U*A.val) = 0
    linarith only [h,hsNormSq_nonneg (omitted U*A.val),
      hsNormSq_nonneg (omitted U*(A.val*U.toContinuousLinearMap))]
  · intro hz
    rw [← mul_assoc (omitted U),hz,zero_mul,hsNormSq_zero,add_zero] at h
    exact (sub_eq_zero.mp h).symm

#print axioms compression_loss
#print axioms compression_eq_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
