import GaloisForLFunctions.HTGeometry.HilbertSchmidtRankOne

/-!
# The exact Hilbert–Schmidt trace defect

The average squared Hilbert–Schmidt norm of two operators dominates both signs
of the real trace of their product. The excess is exactly half the squared
distance from either operator to the signed adjoint of the other.
-/

noncomputable section
open ContinuousLinearMap
namespace GaloisForLFunctions.HTGeometry

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem real_hsInner_comm (A B : H →L[ℂ] H) :
    (hsInner A B).re = (hsInner B A).re := by
  rw [hsInner_conj_symm A B]
  rfl

/-- Subtraction changes only the sign of the real mixed Hilbert–Schmidt pairing. -/
theorem hsNormSq_sub_eq_real_inner {A B : H →L[ℂ] H}
    (hA : A.IsHilbertSchmidt) (hB : B.IsHilbertSchmidt) :
    hsNormSq (A - B) = hsNormSq A - 2 * (hsInner A B).re + hsNormSq B := by
  have hneg : hsInner A (-B) = -hsInner A B := by
    rw [← neg_one_smul ℂ B, hsInner_smul_right, neg_one_mul]
  rw [sub_eq_add_neg, hsNormSq_add hA hB.neg,
    hsNormSq_neg_eq_self, hneg, Complex.neg_re]
  ring

private theorem real_hsInner_adjoint_eq_trace {A B : H →L[ℂ] H}
    (hA : A.IsHilbertSchmidt) (hB : B.IsHilbertSchmidt) :
    (hsInner A (adjoint B)).re = (opTrace (A.comp B)).re := by
  calc
    _ = (hsInner (adjoint B) A).re := real_hsInner_comm _ _
    _ = (opTrace (B.comp A)).re := congrArg Complex.re (opTrace_comp_eq_hsInner B A).symm
    _ = _ := congrArg Complex.re (opTrace_comp_comm hB hA)

/-- The exact nonnegative excess of Hilbert–Schmidt mass over the real product trace. -/
theorem half_hsNormSq_sum_sub_re_trace {A B : H →L[ℂ] H}
    (hA : A.IsHilbertSchmidt) (hB : B.IsHilbertSchmidt) :
    (hsNormSq A + hsNormSq B) / 2 - (opTrace (A.comp B)).re =
      hsNormSq (A - adjoint B) / 2 := by
  rw [hsNormSq_sub_eq_real_inner hA hB.adjoint,
    hB.hsNormSq_adjoint, real_hsInner_adjoint_eq_trace hA hB]
  ring

/-- The companion square controls the opposite sign of the same trace. -/
theorem half_hsNormSq_sum_add_re_trace {A B : H →L[ℂ] H}
    (hA : A.IsHilbertSchmidt) (hB : B.IsHilbertSchmidt) :
    (hsNormSq A + hsNormSq B) / 2 + (opTrace (A.comp B)).re =
      hsNormSq (A + adjoint B) / 2 := by
  rw [hsNormSq_add hA hB.adjoint,
    hB.hsNormSq_adjoint, real_hsInner_adjoint_eq_trace hA hB]
  ring

/-- Equality in the positive trace bound is exactly adjoint compatibility. -/
theorem half_hsNormSq_sum_le_re_trace_iff {A B : H →L[ℂ] H}
    (hA : A.IsHilbertSchmidt) (hB : B.IsHilbertSchmidt) :
    (hsNormSq A + hsNormSq B) / 2 ≤ (opTrace (A.comp B)).re ↔
      A = adjoint B := by
  have hid := half_hsNormSq_sum_sub_re_trace hA hB
  constructor
  · intro h
    have hz : hsNormSq (A - adjoint B) = 0 := by
      linarith only [hid, h, hsNormSq_nonneg (A - adjoint B)]
    exact sub_eq_zero.mp ((hsNormSq_eq_zero_iff (hA.sub hB.adjoint)).mp hz)
  · rintro rfl
    rw [sub_self] at hid
    have hzero : hsNormSq (0 : H →L[ℂ] H) = 0 := by simp [hsNormSq]
    rw [hzero] at hid
    linarith only [hid]

end GaloisForLFunctions.HTGeometry

