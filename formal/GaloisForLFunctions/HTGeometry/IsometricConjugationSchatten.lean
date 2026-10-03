import GaloisForLFunctions.RHTower.TraceClassCyclicity
import GaloisForLFunctions.RHTower.TraceClassOperatorTrace

/-!
# Schatten invariants under isometric corner embedding

For an isometry `V : E → F` (`V*V = 1`) the corner map `X ↦ V X V*` preserves operator norm and every
approximation number: a rank-`n` approximant of `X` maps to one of `VXV*`, and a rank-`n` approximant
`G` of `VXV*` pulls back to the rank-`n` approximant `V*GV` of `X`.  Consequently Schatten membership,
the trace norm and the operator trace are invariant, and positivity is preserved.
-/

open ContinuousLinearMap
open scoped InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open _root_.RHTower

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- The corner embedding `X ↦ V X V*`. -/
def cornerConj (V : E →L[ℂ] F) (X : E →L[ℂ] E) : F →L[ℂ] F := V ∘L X ∘L adjoint V

variable {V : E →L[ℂ] F} (hV : adjoint V ∘L V = ContinuousLinearMap.id ℂ E)
include hV

theorem norm_apply_of_isometry (x : E) : ‖V x‖ = ‖x‖ := by
  have h : ⟪V x, V x⟫_ℂ = ⟪x, x⟫_ℂ := by
    rw [← adjoint_inner_right, ← comp_apply, hV, id_apply]
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  have h2 : ‖V x‖ ^ 2 = ‖x‖ ^ 2 := by exact_mod_cast h
  exact le_antisymm (by nlinarith [norm_nonneg (V x), norm_nonneg x])
    (by nlinarith [norm_nonneg (V x), norm_nonneg x])

theorem norm_le_one_of_isometry : ‖V‖ ≤ 1 :=
  opNorm_le_bound _ zero_le_one fun x => by rw [norm_apply_of_isometry hV x, one_mul]

theorem adjoint_comp_cornerConj_comp (X : E →L[ℂ] E) : adjoint V ∘L cornerConj V X ∘L V = X := by
  rw [cornerConj, ← comp_assoc, ← comp_assoc, hV, id_comp, comp_assoc, hV, comp_id]

theorem norm_cornerConj (X : E →L[ℂ] E) : ‖cornerConj V X‖ = ‖X‖ := by
  have h1 : ‖V‖ ≤ 1 := norm_le_one_of_isometry hV
  have h2 : ‖adjoint V‖ ≤ 1 := by rw [adjoint.norm_map]; exact h1
  refine le_antisymm ?_ ?_
  · calc ‖cornerConj V X‖ ≤ ‖V‖ * (‖X‖ * ‖adjoint V‖) :=
          (opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_left (opNorm_comp_le _ _) (norm_nonneg _))
      _ ≤ 1 * (‖X‖ * 1) := by gcongr
      _ = ‖X‖ := by ring
  · conv_lhs => rw [← adjoint_comp_cornerConj_comp hV X]
    calc ‖adjoint V ∘L cornerConj V X ∘L V‖ ≤ ‖adjoint V‖ * (‖cornerConj V X‖ * ‖V‖) :=
          (opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_left (opNorm_comp_le _ _) (norm_nonneg _))
      _ ≤ 1 * (‖cornerConj V X‖ * 1) := by gcongr
      _ = ‖cornerConj V X‖ := by ring

omit hV [CompleteSpace E] [CompleteSpace F] in
theorem hasRankLE_comp_comp {X : E →L[ℂ] E} {n : ℕ} (hX : HasRankLE X n) (A : E →L[ℂ] F)
    (B : F →L[ℂ] E) : HasRankLE (A ∘L X ∘L B) n := by
  obtain ⟨W, hW, hWn, hXW⟩ := hX
  refine ⟨W.map (A : E →ₗ[ℂ] F), inferInstance, (Submodule.finrank_map_le _ _).trans hWn,
    fun y => ?_⟩
  exact Submodule.mem_map_of_mem (hXW (B y))

theorem approxNumber_cornerConj (X : E →L[ℂ] E) (n : ℕ) :
    approxNumber (cornerConj V X) n = approxNumber X n := by
  refine le_antisymm ?_ ?_
  · refine le_csInf (approxNumber_set_nonempty X n) ?_
    rintro r ⟨G, hG, rfl⟩
    have h := approxNumber_le (cornerConj V X) n (cornerConj V G) (hasRankLE_comp_comp hG _ _)
    have heq : cornerConj V X - cornerConj V G = cornerConj V (X - G) := by
      simp only [cornerConj, comp_sub, sub_comp]
    rwa [heq, norm_cornerConj hV] at h
  · refine le_csInf (approxNumber_set_nonempty _ n) ?_
    rintro r ⟨G, hG, rfl⟩
    have h := approxNumber_le X n (adjoint V ∘L G ∘L V) (hasRankLE_comp_comp hG _ _)
    refine h.trans ?_
    conv_lhs => rw [← adjoint_comp_cornerConj_comp hV X]
    rw [← comp_sub, ← sub_comp]
    calc ‖adjoint V ∘L (cornerConj V X - G) ∘L V‖ ≤ ‖adjoint V‖ * (‖cornerConj V X - G‖ * ‖V‖) :=
          (opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_left (opNorm_comp_le _ _) (norm_nonneg _))
      _ ≤ 1 * (‖cornerConj V X - G‖ * 1) := by
          gcongr
          · rw [adjoint.norm_map]; exact norm_le_one_of_isometry hV
          · exact norm_le_one_of_isometry hV
      _ = ‖cornerConj V X - G‖ := by ring

theorem memSchattenClass_cornerConj_iff {p : ℝ} (X : E →L[ℂ] E) :
    MemSchattenClass p (cornerConj V X) ↔ MemSchattenClass p X := by
  unfold MemSchattenClass
  simp_rw [approxNumber_cornerConj hV]

theorem traceNorm_cornerConj (X : E →L[ℂ] E) : traceNorm F (cornerConj V X) = traceNorm E X := by
  unfold traceNorm
  simp_rw [approxNumber_cornerConj hV]

/-- The corner embedding preserves the trace of a trace-class operator: with `X = SU`
(Hilbert–Schmidt factors), `tr_F (VS)(UV*) = tr_E (UV*)(VS) = tr_E (US) = tr_E X`. -/
theorem opTrace_cornerConj {X : E →L[ℂ] E} (hX : MemSchattenClass 1 X) :
    opTrace (cornerConj V X) = opTrace X := by
  obtain ⟨S, U, hS, hU, rfl⟩ := hX.one_isTraceClass
  have h1 : cornerConj V (S ∘L U) = (V ∘L S) ∘L (U ∘L adjoint V) := by
    simp only [cornerConj, comp_assoc]
  have h2 : (U ∘L adjoint V) ∘L (V ∘L S) = U ∘L S := by
    rw [comp_assoc, ← comp_assoc (adjoint V), hV, id_comp]
  rw [h1, ← opTrace_comp_comm (hU.comp_right (adjoint V)) (hS.comp_left V), h2,
    opTrace_comp_comm hU hS]

omit hV in
theorem cornerConj_isPositive {X : E →L[ℂ] E} (hX : X.IsPositive) : (cornerConj V X).IsPositive :=
  hX.conj_adjoint V

end GaloisForLFunctions.HTGeometry
