import GaloisForLFunctions.HTGeometry.CompactPerturbationTopEigenvalue

/-!
# The top eigenvalue on an invariant orthogonal complement

A symmetric operator `L` that preserves a subspace `V` also preserves `Vᗮ`.  Compressing
`L = K + B` to `W = Vᗮ` by the orthogonal projection keeps `K` compact and does not increase `‖B‖`,
while on `W` the compression of `L` is `L` itself.  So the top-eigenvalue theorem applies inside `W`:
if `re⟪Lf, f⟫ > b‖f‖²` for some `f ∈ Vᗮ`, the supremum `M > b` of the numerical range of `L` on
`Vᗮ` is an eigenvalue of `L` with an eigenvector in `Vᗮ`
(`exists_eigenvector_of_compact_add_orthogonal`).  In applications `V` is a space of trivial
eigenvectors (the constants), and the theorem produces a nontrivial one.
-/

open RCLike ContinuousLinearMap

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local notation "⟪" x ", " y "⟫" => inner ℂ x y

omit [CompleteSpace H] in
/-- A symmetric operator preserving `V` preserves `Vᗮ`. -/
theorem map_mem_orthogonal_of_invariant {L : H →L[ℂ] H} (hL : (L : H →ₗ[ℂ] H).IsSymmetric)
    {V : Submodule ℂ H} (hV : ∀ v ∈ V, L v ∈ V) {w : H} (hw : w ∈ Vᗮ) : L w ∈ Vᗮ := by
  rw [Submodule.mem_orthogonal] at hw ⊢
  intro u hu
  have := hL u w
  simp only [ContinuousLinearMap.coe_coe] at this
  rw [← this]
  exact hw _ (hV u hu)

variable {L K B : H →L[ℂ] H}

/-- **The top eigenvalue on `Vᗮ`.**  Let `L = K + B` be symmetric with `K` compact and `‖B‖ ≤ b`, and
let `L` preserve `V`.  If `re⟪Lf, f⟫ > b‖f‖²` for some `f ∈ Vᗮ`, then some `M > b` bounds the numerical
range of `L` on `Vᗮ` and is an eigenvalue of `L` with an eigenvector in `Vᗮ`. -/
theorem exists_eigenvector_of_compact_add_orthogonal (hL : (L : H →ₗ[ℂ] H).IsSymmetric)
    (hK : IsCompactOperator K) (hLKB : L = K + B) {b : ℝ} (hb : 0 ≤ b) (hB : ‖B‖ ≤ b)
    {V : Submodule ℂ H} (hV : ∀ v ∈ V, L v ∈ V) {f : H} (hfV : f ∈ Vᗮ)
    (hf : b * ‖f‖ ^ 2 < re ⟪L f, f⟫) :
    ∃ M : ℝ, b < M ∧ (∀ x ∈ Vᗮ, re ⟪L x, x⟫ ≤ M * ‖x‖ ^ 2) ∧
      ∃ x ∈ Vᗮ, x ≠ 0 ∧ L x = (M : ℂ) • x := by
  set W : Submodule ℂ H := Vᗮ with hW
  set P : H →L[ℂ] W := W.orthogonalProjectionOnto
  set ιW : W →L[ℂ] H := W.subtypeL
  have hLW : ∀ w : W, L (w : H) ∈ W := fun w => map_mem_orthogonal_of_invariant hL hV w.2
  have hP : ∀ w : W, P (L (w : H)) = ⟨L w, hLW w⟩ := fun w =>
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (K := W) ⟨L w, hLW w⟩
  set LW : W →L[ℂ] W := P ∘L L ∘L ιW
  set KW : W →L[ℂ] W := P ∘L K ∘L ιW
  set BW : W →L[ℂ] W := P ∘L B ∘L ιW
  have hLW_apply : ∀ w : W, (LW w : H) = L w := fun w => by
    change ((P (L (w : H)) : W) : H) = L w
    rw [hP]
  have hsym : (LW : W →ₗ[ℂ] W).IsSymmetric := by
    intro x y
    simp only [ContinuousLinearMap.coe_coe]
    rw [Submodule.coe_inner, Submodule.coe_inner, hLW_apply, hLW_apply]
    exact hL x y
  have hKW : IsCompactOperator KW := by
    rw [ContinuousLinearMap.coe_comp, ContinuousLinearMap.coe_comp]
    exact (hK.comp_clm ιW).clm_comp P
  have hLKBW : LW = KW + BW := by
    simp only [LW, KW, BW, hLKB, ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add]
  have hBW : ‖BW‖ ≤ b := by
    calc ‖BW‖ ≤ ‖P‖ * (‖B‖ * ‖ιW‖) := by
          refine (opNorm_comp_le _ _).trans ?_
          gcongr
          exact opNorm_comp_le _ _
      _ ≤ 1 * (‖B‖ * 1) := by
          gcongr
          · exact Submodule.orthogonalProjectionOnto_norm_le W
          · exact Submodule.norm_subtypeL_le W
      _ ≤ b := by rw [one_mul, mul_one]; exact hB
  have hfW : b * ‖(⟨f, hfV⟩ : W)‖ ^ 2 < re ⟪LW ⟨f, hfV⟩, (⟨f, hfV⟩ : W)⟫ := by
    rw [Submodule.coe_inner, hLW_apply]
    exact hf
  obtain ⟨M, hbM, hbound, x, hx0, hx⟩ :=
    exists_eigenvector_of_compact_add hsym hKW hLKBW hb hBW hfW
  refine ⟨M, hbM, fun y hy => ?_, x, x.2, fun h => hx0 (Subtype.ext h), ?_⟩
  · have := hbound ⟨y, hy⟩
    rwa [Submodule.coe_inner, hLW_apply] at this
  · have := congrArg (fun w : W => (w : H)) hx
    simp only [hLW_apply, Submodule.coe_smul] at this
    exact this

end

end GaloisForLFunctions.HTGeometry
