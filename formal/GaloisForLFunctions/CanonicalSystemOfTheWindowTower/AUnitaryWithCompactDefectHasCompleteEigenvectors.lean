import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-!
# Unitaries with compact defect have complete eigenvectors

Let `V` be a unitary with `V - 1` compact. The commuting operators `V + V⁻¹ - 2` and
`i(V - V⁻¹)` are compact and self-adjoint, so on any nonzero closed subspace invariant under `V`
and `V⁻¹` they have a common eigenvector, which is an eigenvector of `V`. Hence the eigenspaces of
`V` have trivial orthogonal complement.

A linear map bounded by a compact one is compact; this is used to obtain the compact defect.
-/

open Module.End
open scoped InnerProduct

noncomputable section

namespace GaloisForLFunctions.CanonicalSystemOfTheWindowTower

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A compact symmetric operator has an eigenvector in every nonzero closed invariant subspace. -/
theorem exists_eigenvector_on_invariant {S : H →L[ℂ] H} (hS : IsCompactOperator S)
    (hs : (S : H →ₗ[ℂ] H).IsSymmetric) (W : Submodule ℂ H) (hW : IsClosed (W : Set H))
    (hinv : ∀ x ∈ W, S x ∈ W) (hne : W ≠ ⊥) :
    ∃ y ∈ W, y ≠ 0 ∧ ∃ c : ℂ, S y = c • y := by
  haveI : CompleteSpace W := hW.completeSpace_coe
  let T : W →L[ℂ] W := S.restrict hinv
  have hTc : IsCompactOperator T := hS.restrict' hinv
  have hTs : (T : W →ₗ[ℂ] W).IsSymmetric := hs.restrict_invariant hinv
  have hbot := ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot hTc hTs
  by_contra hno
  have heig (μ : ℂ) : eigenspace (T : Module.End ℂ W) μ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [mem_eigenspace_iff] at hx
    rw [Submodule.mem_bot]
    by_contra hx0
    refine hno ⟨x, x.2, fun h => hx0 (Subtype.ext h), μ, ?_⟩
    exact congrArg Subtype.val hx
  simp only [heig, iSup_bot, Submodule.bot_orthogonal_eq_top] at hbot
  apply hne
  rw [eq_bot_iff]
  intro x hx
  have hmem : (⟨x, hx⟩ : W) ∈ (⊤ : Submodule ℂ W) := Submodule.mem_top
  rw [hbot, Submodule.mem_bot] at hmem
  simpa using congrArg Subtype.val hmem

/-- **Spectral theorem for unitaries with compact defect.** -/
theorem orthogonal_iSup_eigenspaces_of_unitary (V : H ≃ₗᵢ[ℂ] H)
    (hV : IsCompactOperator (((V.toContinuousLinearEquiv : H →L[ℂ] H) - 1 : H →L[ℂ] H) : H → H)) :
    (⨆ μ : ℂ, eigenspace (V.toLinearEquiv.toLinearMap : Module.End ℂ H) μ)ᗮ = ⊥ := by
  set M := ⨆ μ : ℂ, eigenspace (V.toLinearEquiv.toLinearMap : Module.End ℂ H) μ with hM
  let U : H →L[ℂ] H := V.toContinuousLinearEquiv
  let Ui : H →L[ℂ] H := V.symm.toContinuousLinearEquiv
  have hU (x : H) : U x = V x := rfl
  have hUi (x : H) : Ui x = V.symm x := rfl
  have hadj : ContinuousLinearMap.adjoint U = Ui := by
    apply ContinuousLinearMap.ext
    intro y
    apply ext_inner_right ℂ
    intro x
    rw [ContinuousLinearMap.adjoint_inner_left, hU, hUi]
    calc
      inner ℂ y (V x) = inner ℂ (V (V.symm y)) (V x) := by
        rw [LinearIsometryEquiv.apply_symm_apply]
      _ = inner ℂ (V.symm y) x := V.inner_map_map _ _
  -- The eigenspace sum is invariant under `V` and `V⁻¹`.
  have hstep (μ : ℂ) (m : H) (hm : V m = μ • m) :
      V m ∈ M ∧ V.symm m ∈ M := by
    have hmem : m ∈ M := Submodule.mem_iSup_of_mem μ (mem_eigenspace_iff.mpr hm)
    refine ⟨by rw [hm]; exact M.smul_mem μ hmem, ?_⟩
    by_cases hm0 : m = 0
    · simp [hm0]
    have hμ : μ ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hm
      exact hm0 (by simpa using congrArg V.symm hm)
    have hsymm : V.symm m = μ⁻¹ • m := by
      apply V.injective
      rw [LinearIsometryEquiv.apply_symm_apply, map_smul, hm, smul_smul, inv_mul_cancel₀ hμ,
        one_smul]
    rw [hsymm]
    exact M.smul_mem _ hmem
  have hMV : M ≤ M.comap V.toLinearEquiv.toLinearMap := by
    refine iSup_le fun μ m hm => ?_
    exact (hstep μ m (mem_eigenspace_iff.mp hm)).1
  have hMVi : M ≤ M.comap V.symm.toLinearEquiv.toLinearMap := by
    refine iSup_le fun μ m hm => ?_
    exact (hstep μ m (mem_eigenspace_iff.mp hm)).2
  have hNV (x : H) (hx : x ∈ Mᗮ) : V x ∈ Mᗮ := by
    rw [Submodule.mem_orthogonal] at hx ⊢
    intro m hm
    have h := hx (V.symm m) (hMVi hm)
    calc
      inner ℂ m (V x) = inner ℂ (V (V.symm m)) (V x) := by
        rw [LinearIsometryEquiv.apply_symm_apply]
      _ = inner ℂ (V.symm m) x := V.inner_map_map _ _
      _ = 0 := h
  have hNVi (x : H) (hx : x ∈ Mᗮ) : V.symm x ∈ Mᗮ := by
    rw [Submodule.mem_orthogonal] at hx ⊢
    intro m hm
    have h := hx (V m) (hMV hm)
    calc
      inner ℂ m (V.symm x) = inner ℂ (V m) (V (V.symm x)) := (V.inner_map_map _ _).symm
      _ = inner ℂ (V m) x := by rw [LinearIsometryEquiv.apply_symm_apply]
      _ = 0 := h
  -- The real and imaginary parts of the defect are compact and self-adjoint.
  let K : H →L[ℂ] H := U - 1
  have hK : IsCompactOperator K := hV
  have hKadj : ContinuousLinearMap.adjoint K = Ui - 1 := by
    simp only [K, map_sub, hadj]
    congr 1
    exact ContinuousLinearMap.adjoint_id
  have hKs : IsCompactOperator (Ui - 1 : H →L[ℂ] H) := by
    have hc := hK.clm_comp (-Ui)
    have hfun : ((Ui - 1 : H →L[ℂ] H) : H → H) = (-Ui : H →L[ℂ] H) ∘ K := by
      funext x
      change Ui x - x = -Ui (U x - x)
      rw [map_sub, hU, hUi, hUi, LinearIsometryEquiv.symm_apply_apply]
      abel
    rw [hfun]
    exact hc
  let B : H →L[ℂ] H := K + (Ui - 1)
  let C : H →L[ℂ] H := (Complex.I : ℂ) • (K - (Ui - 1))
  have hBc : IsCompactOperator B := hK.add hKs
  have hCc : IsCompactOperator C := (hK.sub hKs).smul (Complex.I : ℂ)
  have hBs : (B : H →ₗ[ℂ] H).IsSymmetric := by
    have hb : IsSelfAdjoint B := by
      rw [ContinuousLinearMap.isSelfAdjoint_iff']
      simp only [B, map_add, hKadj]
      rw [show ContinuousLinearMap.adjoint (Ui - 1) = K by
        rw [← hKadj, ContinuousLinearMap.adjoint_adjoint]]
      abel
    exact hb.isSymmetric
  have hCs : (C : H →ₗ[ℂ] H).IsSymmetric := by
    have hb : IsSelfAdjoint C := by
      rw [ContinuousLinearMap.isSelfAdjoint_iff']
      have hK2 : ContinuousLinearMap.adjoint (Ui - 1) = K := by
        rw [← hKadj, ContinuousLinearMap.adjoint_adjoint]
      simp only [C]
      rw [show ContinuousLinearMap.adjoint ((Complex.I : ℂ) • (K - (Ui - 1))) =
          (starRingEnd ℂ) Complex.I • ContinuousLinearMap.adjoint (K - (Ui - 1)) from
        LinearIsometryEquiv.map_smulₛₗ _ _ _]
      rw [map_sub, hKadj, hK2, Complex.conj_I, neg_smul, ← smul_neg, neg_sub]
    exact hb.isSymmetric
  have hBapply (x : H) : B x = V x + V.symm x - (2 : ℂ) • x := by
    change (U x - x) + (Ui x - x) = _
    rw [hU, hUi, two_smul]
    abel
  have hCapply (x : H) : C x = (Complex.I : ℂ) • (V x - V.symm x) := by
    change (Complex.I : ℂ) • ((U x - x) - (Ui x - x)) = _
    rw [hU, hUi, sub_sub_sub_cancel_right]
  have hcomm (x : H) : B (C x) = C (B x) := by
    simp only [hBapply, hCapply, map_smul, map_sub, map_add,
      LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.symm_apply_apply]
    simp only [smul_sub, smul_add, smul_smul, mul_comm]
    abel
  by_contra hne
  have hNclosed : IsClosed ((Mᗮ : Submodule ℂ H) : Set H) := Submodule.isClosed_orthogonal M
  have hNB (x : H) (hx : x ∈ Mᗮ) : B x ∈ Mᗮ := by
    rw [hBapply]
    exact Submodule.sub_mem _ (Submodule.add_mem _ (hNV x hx) (hNVi x hx))
      (Submodule.smul_mem _ _ hx)
  have hNC (x : H) (hx : x ∈ Mᗮ) : C x ∈ Mᗮ := by
    rw [hCapply]
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (hNV x hx) (hNVi x hx))
  obtain ⟨x₀, hx₀, hx₀0, c, hc⟩ := exists_eigenvector_on_invariant hBc hBs Mᗮ hNclosed hNB hne
  -- Fix a real-part eigenspace inside the complement and diagonalize the imaginary part on it.
  let W : Submodule ℂ H := Mᗮ ⊓ LinearMap.ker (B - c • (1 : H →L[ℂ] H)).toLinearMap
  have hWclosed : IsClosed (W : Set H) := by
    have h2 : IsClosed
        ((LinearMap.ker (B - c • (1 : H →L[ℂ] H)).toLinearMap : Submodule ℂ H) : Set H) :=
      (B - c • (1 : H →L[ℂ] H)).isClosed_ker
    simpa [W] using hNclosed.inter h2
  have hWmem (x : H) : x ∈ W ↔ x ∈ Mᗮ ∧ B x = c • x := by
    simp only [W, Submodule.mem_inf, LinearMap.mem_ker]
    change _ ∧ (B x - c • x = 0) ↔ _
    rw [sub_eq_zero]
  have hWC (x : H) (hx : x ∈ W) : C x ∈ W := by
    obtain ⟨hxN, hxB⟩ := (hWmem x).mp hx
    refine (hWmem _).mpr ⟨hNC x hxN, ?_⟩
    rw [hcomm, hxB, map_smul]
  have hWne : W ≠ ⊥ := by
    intro h
    have hmem : x₀ ∈ W := (hWmem x₀).mpr ⟨hx₀, hc⟩
    rw [h, Submodule.mem_bot] at hmem
    exact hx₀0 hmem
  obtain ⟨y, hyW, hy0, d, hd⟩ := exists_eigenvector_on_invariant hCc hCs W hWclosed hWC hWne
  obtain ⟨hyN, hyB⟩ := (hWmem y).mp hyW
  -- `2V = B - iC + 2`, so the common eigenvector is an eigenvector of `V`.
  have hVy : V y = (1 + (c - Complex.I * d) / 2) • y := by
    have h1 := hBapply y
    have h2 := hCapply y
    rw [hyB] at h1
    rw [hd] at h2
    have h3 : V y - V.symm y = (-Complex.I * d) • y := by
      have h4 := congrArg (fun v : H => (-Complex.I : ℂ) • v) h2
      simp only [smul_smul] at h4
      rw [show (-Complex.I * Complex.I : ℂ) = 1 by
        rw [neg_mul, Complex.I_mul_I, neg_neg], one_smul] at h4
      exact h4.symm
    have h5 : (2 : ℂ) • V y = ((2 : ℂ) + c + -Complex.I * d) • y := by
      have h6 : V y + V.symm y = (c + 2) • y := by
        rw [add_smul, h1]
        abel
      calc
        (2 : ℂ) • V y = (V y + V.symm y) + (V y - V.symm y) := by
          rw [two_smul]
          abel
        _ = _ := by
          rw [h6, h3, ← add_smul]
          congr 1
          ring
    have h7 := congrArg (fun v : H => (2⁻¹ : ℂ) • v) h5
    simp only [smul_smul] at h7
    rw [inv_mul_cancel₀ (two_ne_zero), one_smul] at h7
    rw [h7]
    congr 1
    ring
  have hyM : y ∈ M := Submodule.mem_iSup_of_mem _ (mem_eigenspace_iff.mpr hVy)
  have hzero := (Submodule.mem_orthogonal _ _).mp hyN y hyM
  exact hy0 (inner_self_eq_zero.mp hzero)

/-- A linear map dominated by a compact one is compact. -/
theorem isCompactOperator_of_norm_le {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedAddCommGroup G] [NormedSpace ℂ G]
    [CompleteSpace G] {A : E →L[ℂ] F} {T : E →L[ℂ] G} (hA : IsCompactOperator A) {C : ℝ}
    (hT : ∀ x, ‖T x‖ ≤ C * ‖A x‖) : IsCompactOperator T := by
  have hball := hA.isCompact_closure_image_closedBall (1 : ℝ)
  have htb : TotallyBounded (A '' Metric.closedBall (0 : E) 1) :=
    hball.totallyBounded.subset subset_closure
  rw [show (T : E → G) = (T : E →ₗ[ℂ] G) from rfl,
    isCompactOperator_iff_isCompact_closure_image_closedBall (T : E →ₗ[ℂ] G) one_pos]
  refine (TotallyBounded.closure ?_).isCompact_of_isClosed isClosed_closure
  rw [Metric.totallyBounded_iff]
  intro ε hε
  let d : ℝ := ε / (|C| + 1)
  have hd : 0 < d := div_pos hε (by positivity)
  obtain ⟨t, htA, htf, hcov⟩ := Metric.finite_approx_of_totallyBounded htb d hd
  choose! p hp using fun y (hy : y ∈ t) => htA hy
  refine ⟨T '' (p '' t), (htf.image p).image T, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (hcov (Set.mem_image_of_mem A hx))
  refine Set.mem_iUnion₂.mpr ⟨T (p y), Set.mem_image_of_mem T (Set.mem_image_of_mem p hy), ?_⟩
  have hpy := (hp y hy).2
  rw [Metric.mem_ball, dist_eq_norm] at hxy ⊢
  change ‖T x - T (p y)‖ < ε
  rw [← map_sub]
  have hbound : ‖A (x - p y)‖ < d := by
    rw [map_sub, hpy]
    exact hxy
  calc
    ‖T (x - p y)‖ ≤ C * ‖A (x - p y)‖ := hT _
    _ ≤ |C| * ‖A (x - p y)‖ := mul_le_mul_of_nonneg_right (le_abs_self C) (norm_nonneg _)
    _ ≤ |C| * d := mul_le_mul_of_nonneg_left hbound.le (abs_nonneg C)
    _ < ε := by
      have hpos : 0 < |C| + 1 := by positivity
      have : |C| * d = ε * (|C| / (|C| + 1)) := by
        simp only [d]
        field_simp
      rw [this]
      have hlt : |C| / (|C| + 1) < 1 := (div_lt_one hpos).mpr (by linarith)
      nlinarith only [hlt, hε]

end GaloisForLFunctions.CanonicalSystemOfTheWindowTower

#print axioms GaloisForLFunctions.CanonicalSystemOfTheWindowTower.orthogonal_iSup_eigenspaces_of_unitary
#print axioms GaloisForLFunctions.CanonicalSystemOfTheWindowTower.isCompactOperator_of_norm_le
