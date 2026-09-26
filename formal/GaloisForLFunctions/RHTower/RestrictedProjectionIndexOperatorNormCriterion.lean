import GaloisForLFunctions.RHTower.RestrictedProjectionCubicRelativeIndex
import GaloisForLFunctions.RHTower.RestrictedUnitaryCubicIndex
import GaloisForLFunctions.RHTower.RestrictedUnitaryCubicContinuity
import GaloisForLFunctions.RHTower.TraceClassOperatorTrace

/-!
# The cubic relative index needs only an operator-norm bound on the forward seam

For orthogonal projections `R, P` with Hilbert–Schmidt displacement `D = R - P`, the cubic trace
`Tr D³` is the relative index `dim ker(D - 1) - dim ker(D + 1)`
(`opTrace_restrictedProjectionCubicDefect_eq_relativeIndex`).  The `+1` eigenspace of `D` is
`Ran R ∩ Ker P`.  So the index is `≤ 0` as soon as the forward seam `(1 - P) R` has operator norm
below one: a vector of `Ran R ∩ Ker P` is fixed by `(1 - P) R`.

Every sub-unit budget on the forward seam in any Schatten norm implies this operator-norm bound.
For route 1 (`docs/reports/route-proposals/route1.md`), whose fallback asks for `Tr T_(D,x) ≤ B_base < 1`
on the relative cubic defect, the sharp form of the budget is therefore `‖(1 - P) R‖ < 1`, with no
trace-class content.  For the Hardy projections of two unimodular boundary phases this is the
Nehari / Toeplitz-invertibility condition on their quotient.

In the corpus carrier `RestrictedUnitaryDatum` (`R = U†PU`), the adjoint seam `(1-P)U†P` bounds
`(1-P)R`, and the forward seam `(1-P)UP` bounds `(1-R)P`.  So both oriented Hankel seams being strict
contractions forces the cubic relative index to vanish (`relativeIndex_eq_zero_of_seams`).
-/

noncomputable section

namespace RHTower

open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The `+1` eigenvectors of `R - P` lie in `Ran R ∩ Ker P`. -/
theorem restrictedProjectionDisplacement_eq_self_imp
    (R P : H →L[ℂ] H) (hR : IsIdempotentElem R) (hP : IsIdempotentElem P)
    (hRadj : adjoint R = R) (hPadj : adjoint P = P) {x : H}
    (hx : restrictedProjectionDisplacement R P x = x) : R x = x ∧ P x = 0 := by
  have hx1 : restrictedProjectionDisplacement R P x = ((1 : ℝ) : ℂ) • x := by
    rw [hx]; simp
  have hCC := restrictedProjectionComplement_sq_apply_eigenvector R P hR hP 1 hx1
  norm_num at hCC
  set C := restrictedProjectionComplement R P with hCdef
  have hCadj : adjoint C = C := by
    simp [hCdef, restrictedProjectionComplement, map_sub, hRadj, hPadj]
  have hCx : C x = 0 := by
    have hinner : inner ℂ (C x) (C x) = 0 := by
      calc inner ℂ (C x) (C x) = inner ℂ (adjoint C (C x)) x := by
            rw [ContinuousLinearMap.adjoint_inner_left]
        _ = 0 := by rw [hCadj, hCC, inner_zero_left]
    exact inner_self_eq_zero.mp hinner
  have hsum : x = R x + P x := by
    have := hCx
    simp only [hCdef, restrictedProjectionComplement, sub_apply,
      one_apply_eq_self] at this
    rw [sub_sub, sub_eq_zero] at this
    exact this
  have hdiff : R x - P x = x := by
    simpa [restrictedProjectionDisplacement] using hx
  have hPx : P x = 0 := by
    have h2 : (2 : ℂ) • P x = 0 := by
      have : R x + P x - (R x - P x) = x - x := by rw [← hsum, hdiff]
      rw [two_smul]
      simpa [sub_self, add_sub_sub_cancel] using this
    exact (smul_eq_zero.mp h2).resolve_left two_ne_zero
  refine ⟨?_, hPx⟩
  rw [hPx, sub_zero] at hdiff
  exact hdiff

/-- **Operator-norm criterion.**  If the forward seam `(1 - P) R` is a strict contraction, the
`+1` eigenspace of `R - P` is trivial. -/
theorem eigenspace_restrictedProjectionDisplacement_one_eq_bot
    (R P : H →L[ℂ] H) (hR : IsIdempotentElem R) (hP : IsIdempotentElem P)
    (hRadj : adjoint R = R) (hPadj : adjoint P = P)
    (hnorm : ‖(1 - P) ∘L R‖ < 1) :
    Module.End.eigenspace (restrictedProjectionDisplacement R P : H →ₗ[ℂ] H) (1 : ℂ) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Module.End.mem_eigenspace_iff, one_smul] at hx
  have hx' : restrictedProjectionDisplacement R P x = x := hx
  obtain ⟨hRx, hPx⟩ :=
    restrictedProjectionDisplacement_eq_self_imp R P hR hP hRadj hPadj hx'
  have hfix : ((1 - P) ∘L R) x = x := by
    simp [hRx, hPx]
  rw [Submodule.mem_bot]
  by_contra hne
  have hpos : 0 < ‖x‖ := norm_pos_iff.mpr hne
  have hle : ‖x‖ ≤ ‖(1 - P) ∘L R‖ * ‖x‖ := by
    calc ‖x‖ = ‖((1 - P) ∘L R) x‖ := by rw [hfix]
      _ ≤ ‖(1 - P) ∘L R‖ * ‖x‖ := ContinuousLinearMap.le_opNorm _ _
  have : ‖(1 - P) ∘L R‖ * ‖x‖ < ‖x‖ := by
    calc ‖(1 - P) ∘L R‖ * ‖x‖ < 1 * ‖x‖ := mul_lt_mul_of_pos_right hnorm hpos
      _ = ‖x‖ := one_mul _
  linarith

/-- **The relative index is nonpositive under a sub-unit forward seam.** -/
theorem restrictedProjectionRelativeIndex_nonpos_of_norm_lt_one
    (R P : H →L[ℂ] H) (hR : IsIdempotentElem R) (hP : IsIdempotentElem P)
    (hRadj : adjoint R = R) (hPadj : adjoint P = P)
    (hnorm : ‖(1 - P) ∘L R‖ < 1) :
    restrictedProjectionRelativeIndex R P ≤ 0 := by
  unfold restrictedProjectionRelativeIndex
  rw [eigenspace_restrictedProjectionDisplacement_one_eq_bot R P hR hP hRadj hPadj hnorm,
    finrank_bot]
  simp

/-- **Cubic form.**  Under a Hilbert–Schmidt displacement and a sub-unit forward seam, the cubic
trace (the relative index) is a nonpositive integer. -/
theorem re_opTrace_restrictedProjectionCubicDefect_nonpos_of_norm_lt_one
    (R P : H →L[ℂ] H) (hR : IsIdempotentElem R) (hP : IsIdempotentElem P)
    (hRadj : adjoint R = R) (hPadj : adjoint P = P)
    (hDelta : (restrictedProjectionDisplacement R P).IsHilbertSchmidt)
    (hnorm : ‖(1 - P) ∘L R‖ < 1) :
    (ContinuousLinearMap.opTrace (restrictedProjectionCubicDefect R P)).re ≤ 0 := by
  rw [opTrace_restrictedProjectionCubicDefect_eq_relativeIndex R P hR hP hRadj hPadj hDelta]
  have := restrictedProjectionRelativeIndex_nonpos_of_norm_lt_one R P hR hP hRadj hPadj hnorm
  simp only [Complex.intCast_re]
  exact_mod_cast this

/-! ## The restricted-unitary carrier: both Hankel seams below one force index zero -/

/-- The adjoint Hankel seam controls `(1 - P) ∘ U†PU`. -/
theorem RestrictedUnitaryDatum.norm_sub_projection_comp_conjugate_le (D : RestrictedUnitaryDatum H) :
    ‖(1 - D.projection) ∘L D.conjugateProjection‖ ≤ ‖D.adjointHankelSeam‖ := by
  have hU := norm_unitary_le_one D.unitary D.adjoint_mul_unitary
  have heq : (1 - D.projection) ∘L D.conjugateProjection = D.adjointHankelSeam ∘L D.unitary := by
    change (1 - D.projection) * D.conjugateProjection = D.adjointHankelSeam * D.unitary
    simp only [RestrictedUnitaryDatum.conjugateProjection, RestrictedUnitaryDatum.adjointHankelSeam]
    noncomm_ring
  rw [heq]
  calc ‖D.adjointHankelSeam ∘L D.unitary‖ ≤ ‖D.adjointHankelSeam‖ * ‖D.unitary‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖D.adjointHankelSeam‖ * 1 := by gcongr
    _ = ‖D.adjointHankelSeam‖ := mul_one _

/-- The forward Hankel seam controls `(1 - U†PU) ∘ P`. -/
theorem RestrictedUnitaryDatum.norm_sub_conjugate_comp_projection_le (D : RestrictedUnitaryDatum H) :
    ‖(1 - D.conjugateProjection) ∘L D.projection‖ ≤ ‖D.forwardHankelSeam‖ := by
  have hU' : ContinuousLinearMap.adjoint (ContinuousLinearMap.adjoint D.unitary) *
      ContinuousLinearMap.adjoint D.unitary = 1 := by
    rw [ContinuousLinearMap.adjoint_adjoint, D.unitary_mul_adjoint]
  have hUa := norm_unitary_le_one (ContinuousLinearMap.adjoint D.unitary) hU'
  have heq : (1 - D.conjugateProjection) ∘L D.projection =
      ContinuousLinearMap.adjoint D.unitary ∘L D.forwardHankelSeam := by
    change (1 - D.conjugateProjection) * D.projection =
      ContinuousLinearMap.adjoint D.unitary * D.forwardHankelSeam
    simp only [RestrictedUnitaryDatum.conjugateProjection, RestrictedUnitaryDatum.forwardHankelSeam]
    have h1 : ContinuousLinearMap.adjoint D.unitary * ((1 - D.projection) * D.unitary * D.projection) =
        ContinuousLinearMap.adjoint D.unitary * D.unitary * D.projection -
          ContinuousLinearMap.adjoint D.unitary * D.projection * D.unitary * D.projection := by
      noncomm_ring
    rw [h1, D.adjoint_mul_unitary, one_mul]
    noncomm_ring
  rw [heq]
  calc ‖ContinuousLinearMap.adjoint D.unitary ∘L D.forwardHankelSeam‖
      ≤ ‖ContinuousLinearMap.adjoint D.unitary‖ * ‖D.forwardHankelSeam‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * ‖D.forwardHankelSeam‖ := by gcongr
    _ = ‖D.forwardHankelSeam‖ := one_mul _

/-- **Adjoint seam below one.**  The cubic trace of the datum is `≤ 0`. -/
theorem RestrictedUnitaryDatum.re_opTrace_cubicDefect_nonpos_of_adjointSeam
    (D : RestrictedUnitaryDatum H) (h : ‖D.adjointHankelSeam‖ < 1) :
    (ContinuousLinearMap.opTrace
      (restrictedProjectionCubicDefect D.conjugateProjection D.projection)).re ≤ 0 :=
  re_opTrace_restrictedProjectionCubicDefect_nonpos_of_norm_lt_one _ _
    D.conjugateProjection_idempotent D.projection_idempotent D.conjugateProjection_adjoint
    D.projection_adjoint D.displacement_isHilbertSchmidt
    ((D.norm_sub_projection_comp_conjugate_le).trans_lt h)

/-- **Forward seam below one.**  The cubic trace of the datum is `≥ 0`. -/
theorem RestrictedUnitaryDatum.re_opTrace_cubicDefect_nonneg_of_forwardSeam
    (D : RestrictedUnitaryDatum H) (h : ‖D.forwardHankelSeam‖ < 1) :
    0 ≤ (ContinuousLinearMap.opTrace
      (restrictedProjectionCubicDefect D.conjugateProjection D.projection)).re := by
  have hHS : (restrictedProjectionDisplacement D.projection D.conjugateProjection).IsHilbertSchmidt := by
    have heq : restrictedProjectionDisplacement D.projection D.conjugateProjection =
        -restrictedProjectionDisplacement D.conjugateProjection D.projection := by
      simp only [restrictedProjectionDisplacement, neg_sub]
    rw [heq]
    exact D.displacement_isHilbertSchmidt.neg
  have hle := re_opTrace_restrictedProjectionCubicDefect_nonpos_of_norm_lt_one D.projection
    D.conjugateProjection D.projection_idempotent D.conjugateProjection_idempotent
    D.projection_adjoint D.conjugateProjection_adjoint hHS
    ((D.norm_sub_conjugate_comp_projection_le).trans_lt h)
  rw [restrictedProjectionCubicDefect_swap, opTrace_neg, Complex.neg_re] at hle
  linarith

/-- **Both seams below one: the relative index vanishes.**  Route 1's fallback and frontier TG ask
for `Tr T ≤ B < 1`.  Operator-norm contraction of the two oriented Hankel seams already forces the
cubic index to be zero, with no trace-class budget. -/
theorem RestrictedUnitaryDatum.relativeIndex_eq_zero_of_seams (D : RestrictedUnitaryDatum H)
    (hadj : ‖D.adjointHankelSeam‖ < 1) (hfwd : ‖D.forwardHankelSeam‖ < 1) :
    restrictedProjectionRelativeIndex D.conjugateProjection D.projection = 0 := by
  have h1 := D.re_opTrace_cubicDefect_nonpos_of_adjointSeam hadj
  have h2 := D.re_opTrace_cubicDefect_nonneg_of_forwardSeam hfwd
  rw [D.opTrace_cubicDefect_eq_relativeIndex, Complex.intCast_re] at h1 h2
  exact_mod_cast le_antisymm (by exact_mod_cast h1) (by exact_mod_cast h2)

end RHTower
