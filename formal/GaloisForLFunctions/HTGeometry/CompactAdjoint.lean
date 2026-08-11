import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Basic

/-!
# Compactness of rectangular Hilbert-space adjoints

Mathlib's compact-operator API is stable under bounded pre- and postcomposition, but does not
currently expose the Schauder theorem for a rectangular continuous linear map.  This module proves
the needed complex-Hilbert-space form by finite-dimensional orthogonal cuts.
-/

open ContinuousLinearMap Metric Module Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- Orthogonal projection onto a finite-dimensional complex subspace is compact. -/
theorem isCompactOperator_starProjection_finiteDimensional
    (V : Submodule ℂ F) [FiniteDimensional ℂ V] :
    IsCompactOperator V.starProjection := by
  refine ⟨Subtype.val '' closedBall (0 : V) 1,
    (isCompact_closedBall 0 1).image continuous_subtype_val, ?_⟩
  refine Filter.mem_of_superset (ball_mem_nhds 0 one_pos) ?_
  intro x hx
  refine ⟨V.orthogonalProjectionOnto x, ?_, (V.starProjection_apply x).symm⟩
  rw [mem_closedBall_zero_iff]
  calc
    ‖V.orthogonalProjectionOnto x‖ = ‖V.starProjection x‖ := rfl
    _ ≤ ‖x‖ := V.norm_starProjection_apply_le x
    _ ≤ 1 := le_of_lt (mem_ball_zero_iff.mp hx)

/-- A finite-dimensional target cut makes a compact rectangular map uniformly small. -/
private theorem exists_finset_norm_orthogonalCut_comp_le
    {C : E →L[ℂ] F} (hC : IsCompactOperator C) {eps : ℝ} (heps : 0 < eps) :
    ∃ s : Finset F, ∀ t : Finset F, s ⊆ t →
      ‖(1 - (Submodule.span ℂ (t : Set F)).starProjection).comp C‖ ≤ eps := by
  have htb : TotallyBounded (C '' closedBall 0 1) :=
    (hC.isCompact_closure_image_closedBall 1).totallyBounded.subset subset_closure
  obtain ⟨t0, ht0fin, ht0cov⟩ :=
    Metric.totallyBounded_iff.mp htb (eps / 2) (by positivity)
  refine ⟨ht0fin.toFinset, fun t hst => ?_⟩
  set V := Submodule.span ℂ (t : Set F) with hV
  refine opNorm_le_of_shell
    (f := (1 - V.starProjection).comp C) one_pos heps.le
      (c := (2 : ℂ)) (by norm_num) ?_
  intro x hx1 hx2
  have hxball : x ∈ closedBall (0 : E) 1 := by
    rw [mem_closedBall_zero_iff]
    exact hx2.le
  have hCx : C x ∈ ⋃ y ∈ t0, ball y (eps / 2) := ht0cov ⟨x, hxball, rfl⟩
  obtain ⟨y, hyt0, hy⟩ := Set.mem_iUnion₂.mp hCx
  have hyV : y ∈ V := by
    apply Submodule.subset_span
    have hmem : y ∈ ht0fin.toFinset := ht0fin.mem_toFinset.mpr hyt0
    exact_mod_cast hst hmem
  have hmin : ‖C x - V.starProjection (C x)‖ ≤ ‖C x - y‖ := by
    rw [Submodule.starProjection_minimal]
    exact ciInf_le ⟨0, by rintro r ⟨v, rfl⟩; positivity⟩ (⟨y, hyV⟩ : V)
  have hnormx : (1 : ℝ) / ‖(2 : ℂ)‖ = 1 / 2 := by norm_num
  calc
    ‖((1 - V.starProjection).comp C) x‖ =
        ‖C x - V.starProjection (C x)‖ := by
      simp [ContinuousLinearMap.comp_apply, _root_.sub_apply]
    _ ≤ ‖C x - y‖ := hmin
    _ ≤ eps / 2 := le_of_lt (by simpa [dist_eq_norm] using hy)
    _ ≤ eps * ‖x‖ := by
      rw [hnormx] at hx1
      nlinarith

/-- **Rectangular Schauder theorem.** Adjoint of compact continuous linear map between complex
Hilbert spaces is compact. -/
theorem isCompactOperator_adjoint_rectangular
    [CompleteSpace E] [CompleteSpace F]
    (T : E →L[ℂ] F) (hT : IsCompactOperator T) :
    IsCompactOperator T.adjoint := by
  have hmem : T.adjoint ∈ closure {W : F →L[ℂ] E | IsCompactOperator W} := by
    rw [Metric.mem_closure_iff]
    intro delta hdelta
    obtain ⟨s, hs⟩ :=
      exists_finset_norm_orthogonalCut_comp_le hT (half_pos hdelta)
    let V := Submodule.span ℂ ((s : Finset F) : Set F)
    let P := V.starProjection
    have hcut : ‖(1 - P).comp T‖ ≤ delta / 2 := hs s (Finset.Subset.refl s)
    have hPadj : P.adjoint = P := (isSelfAdjoint_starProjection V).star_eq
    have hAdjOneSub : (1 - P).adjoint = 1 - P := by
      change star (1 - P) = 1 - P
      rw [star_sub, star_one]
      exact congrArg (fun W => (1 : F →L[ℂ] F) - W) hPadj
    refine ⟨T.adjoint.comp P,
      (isCompactOperator_starProjection_finiteDimensional V).clm_comp T.adjoint, ?_⟩
    have heq : T.adjoint - T.adjoint.comp P =
        ((1 - P).comp T).adjoint := by
      rw [ContinuousLinearMap.adjoint_comp, hAdjOneSub]
      ext y
      simp [ContinuousLinearMap.comp_apply, _root_.sub_apply]
    rw [dist_eq_norm]
    calc
      ‖T.adjoint - T.adjoint.comp P‖ = ‖((1 - P).comp T).adjoint‖ :=
        congrArg norm heq
      _ = ‖(1 - P).comp T‖ := LinearIsometryEquiv.norm_map _ _
      _ < delta := hcut.trans_lt (half_lt_self hdelta)
  exact isClosed_setOf_isCompactOperator.closure_subset hmem

end

end GaloisForLFunctions.HTGeometry
