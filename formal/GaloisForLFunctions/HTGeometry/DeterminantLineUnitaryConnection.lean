import GaloisForLFunctions.HTGeometry.DeterminantLineFillingHolonomy

/-!
# The determinant-line connection is unitary and of Chern type

For the frame `w = Q + Y` with Gram operator `Ĝ` the connection form is
`α(w)[Ẏ] = Tr(Ĝ⁻¹ w† Ẏ)`.

* `detConnection_smul`: `α` is complex linear in `Ẏ`, so along holomorphic frames it has type
  `(1, 0)`.
* `two_re_detConnection`: along admissible variations `2 Re α = Tr(Ĝ⁻¹(Ẏ†w + w†Ẏ))`, half the
  logarithmic derivative of the Quillen density: the connection preserves the Quillen metric.
* `norm_edgeHol_of_fills`: the holonomy of every filled path has modulus one.
-/

set_option autoImplicit false

open ContinuousLinearMap

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {Q Pp : H →L[ℂ] H}

/-- **The connection form is complex linear in the frame variation**: `α(w)[c Ẏ] = c α(w)[Ẏ]`.
Along a holomorphic family of frames it is therefore of type `(1, 0)`. -/
theorem detConnection_smul (Y Ydot : HSpace ℂ H) (c : ℂ) :
    detConnection Q Y (c • Ydot) = c * detConnection Q Y Ydot := by
  rw [detConnection, detConnection, HSpace.op_smul, mul_smul_comm, opTrace_smul']

/-- **The connection is unitary**: along an admissible variation `Ẏ` of the frame `w = Q + Y`,
`2 Re α(w)[Ẏ] = Tr(Ĝ⁻¹ Ĝ̇)` with `Ĝ̇ = Ẏ†w + w†Ẏ` the variation of the Gram operator, i.e. the real
part of the connection form is half the logarithmic derivative of the Quillen density `det Ĝ`. -/
theorem two_re_detConnection (hQ : IsStarProjection Q) {V : Submodule ℂ H} [FiniteDimensional ℂ V]
    {Y Ydot : HSpace ℂ H} (hunit : IsUnit (frameGram Q (frameOf Q Y))) (hY : QPartIn Q V Ydot) :
    ((2 * (detConnection Q Y Ydot).re : ℝ) : ℂ) =
      opTrace (Ring.inverse (frameGram Q (frameOf Q Y)) *
        (adjoint Ydot.op * frameOf Q Y + adjoint (frameOf Q Y) * Ydot.op)) := by
  set R := Ring.inverse (frameGram Q (frameOf Q Y))
  set w := frameOf Q Y
  have hRs : IsSelfAdjoint R :=
    frameInv_isSelfAdjoint hQ.isSelfAdjoint (Ring.mul_inverse_cancel _ hunit)
  have hmem : adjoint w * Ydot.op ∈ hsTraceIdeal H := by
    rw [adjoint_frameOf hQ.isSelfAdjoint, HSpace.op_adjointL, add_mul]
    exact add_mem (mem_hsTraceIdeal_of_range_le (V := V) fun x => hY x)
      (mul_mem_hsTraceIdeal Y.isHS.adjoint Ydot.isHS)
  have hmem' : adjoint Ydot.op * w ∈ hsTraceIdeal H := by
    have := hsTraceIdeal_adjoint hmem
    rwa [← star_eq_adjoint, star_mul, star_eq_adjoint, star_eq_adjoint, adjoint_adjoint] at this
  have hadj : adjoint (R * (adjoint w * Ydot.op)) = adjoint Ydot.op * w * R := by
    rw [← star_eq_adjoint, star_mul, star_mul, hRs.star_eq, star_eq_adjoint, star_eq_adjoint,
      adjoint_adjoint]
  have hconj : (starRingEnd ℂ) (detConnection Q Y Ydot) = opTrace (R * (adjoint Ydot.op * w)) := by
    rw [detConnection, ← opTrace_adjoint, mul_assoc, hadj, ← opTrace_mul_comm_of_mem hmem' R]
  rw [mul_add, opTrace_add_of_mem (hsTraceIdeal_mul_left hmem' R) (hsTraceIdeal_mul_left hmem R),
    ← hconj, detConnection, ← mul_assoc, add_comm, Complex.add_conj]

/-- **Unitary holonomy**: the holonomy of a path filled by a chain has modulus one. -/
theorem norm_edgeHol_of_fills (hQ : IsStarProjection Q) (c : GrChain Pp) {γ : ℝ → SLSpace H}
    (hγ : ¬ IsDegeneratePath γ) (hc : c.Fills γ)
    (hγsec : ∃ u, IsAdmissibleFrame Q u (Pp + (γ 0).op)) : ‖edgeHol Q Pp γ‖ = 1 := by
  rw [edgeHol_eq_exp_kahlerIntegral hQ c hγ hc hγsec,
    show 2 * Real.pi * Complex.I * (c.kahlerIntegral : ℂ) =
      ((2 * Real.pi * c.kahlerIntegral : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I]

end

end GaloisForLFunctions.HTGeometry
