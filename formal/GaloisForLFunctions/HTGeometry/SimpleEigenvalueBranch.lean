import Mathlib

/-!
# The branch of a simple isolated eigenvalue of a compact self-adjoint operator

A compact self-adjoint operator `A` with a simple eigenvalue `μ ≠ 0` and unit eigenvector `u`
restricts to an operator on `uᗮ` for which `μ` is not an eigenvalue; the Fredholm alternative for
compact operators therefore makes `μ - A` invertible there.  Solving the eigenvalue equation for
`A + tB` in the splitting `H = ℂu ⊕ uᗮ` turns it into a contraction fixed-point problem for the
`uᗮ`-component, whose solution is `O(t)`.  Consequently the eigenvalue branch is differentiable at
`t = 0` with derivative `⟪u, B u⟫`, the first-order perturbation formula.
-/

namespace HTGeometry

open scoped InnerProductSpace

section SimpleBranch

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A simple isolated eigenpair of a compact self-adjoint operator. -/
structure IsSimpleEigenpair (A : H →L[ℂ] H) (μ : ℂ) (u : H) : Prop where
  /-- The operator is compact. -/
  compact : IsCompactOperator A
  /-- The operator is self-adjoint. -/
  selfAdjoint : IsSelfAdjoint A
  /-- The eigenvalue is nonzero. -/
  ne_zero : μ ≠ 0
  /-- The eigenvalue equation. -/
  apply_eq : A u = μ • u
  /-- The eigenvector is normalized. -/
  norm_eq : ‖u‖ = 1
  /-- The eigenvalue is simple. -/
  simple : ∀ v : H, A v = μ • v → v ∈ (ℂ ∙ u)

/-- **First-order perturbation of a simple eigenvalue.**  For a compact self-adjoint `A` with a
simple nonzero eigenvalue `μ` and unit eigenvector `u`, the affine family `A + tB` has a local
eigenvalue branch through `μ` whose derivative at `0` is `⟪u, B u⟫`. -/
theorem exists_eigenBranch {A : H →L[ℂ] H} {μ : ℂ} {u : H}
    (hp : IsSimpleEigenpair A μ u) (B : H →L[ℂ] H) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ lam : ℝ → ℂ, ∃ v : ℝ → H,
      lam 0 = μ ∧ v 0 = u ∧
      (∀ t : ℝ, |t| < δ → (A + (t : ℂ) • B) (v t) = lam t • v t) ∧
      (∀ t : ℝ, |t| < δ → v t ≠ 0) ∧
      HasDerivAt lam (inner ℂ u (B u)) 0 := by
  classical
  haveI hcs : CompleteSpace ((ℂ ∙ u)ᗮ : Submodule ℂ H) :=
    ((ℂ ∙ u).isClosed_orthogonal).completeSpace_coe
  set S : Submodule ℂ H := (ℂ ∙ u)ᗮ with hSdef
  -- the orthogonal projection onto `uᗮ`, written without the projection API
  set pr : H →L[ℂ] H := ContinuousLinearMap.id ℂ H - (innerSL ℂ u).smulRight u with hpr
  have hpr_apply : ∀ y : H, pr y = y - (inner ℂ u y) • u := fun y => rfl
  have huu : (inner ℂ u u : ℂ) = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hp.norm_eq]
    norm_num
  have hprmem : ∀ y : H, pr y ∈ S := by
    intro y
    rw [hSdef, Submodule.mem_orthogonal_singleton_iff_inner_right, hpr_apply,
      inner_sub_right, inner_smul_right, huu, mul_one, sub_self]
  set P : H →L[ℂ] S := pr.codRestrict S hprmem with hP
  set ι : S →L[ℂ] H := S.subtypeL with hι
  have hPcoe : ∀ y : H, ((P y : S) : H) = y - (inner ℂ u y) • u := fun y => rfl
  have hιcoe : ∀ w : S, (ι w : H) = (w : H) := fun w => rfl
  have hinner_mem : ∀ w : S, (inner ℂ u (w : H) : ℂ) = 0 := fun w =>
    (Submodule.mem_orthogonal_singleton_iff_inner_right).mp w.2
  have hPι : ∀ w : S, P (ι w) = w := by
    intro w
    apply Subtype.ext
    rw [hPcoe, hιcoe, hinner_mem w, zero_smul, sub_zero]
  have hdecomp : ∀ y : H, y = (inner ℂ u y) • u + (P y : H) := by
    intro y
    rw [hPcoe]
    abel
  have hPnorm : ∀ y : H, ‖P y‖ ≤ 2 * ‖y‖ := by
    intro y
    have h1 : ‖(P y : H)‖ ≤ ‖y‖ + ‖(inner ℂ u y : ℂ) • u‖ := by
      rw [hPcoe]
      exact norm_sub_le _ _
    have h2 : ‖(inner ℂ u y : ℂ) • u‖ ≤ ‖y‖ := by
      rw [norm_smul, hp.norm_eq, mul_one]
      simpa [hp.norm_eq] using norm_inner_le_norm (𝕜 := ℂ) u y
    have h3 : ‖P y‖ = ‖(P y : H)‖ := rfl
    rw [h3]
    linarith
  -- the restriction of `A` to `uᗮ`
  set A' : S →L[ℂ] S := P ∘L (A ∘L ι) with hA'
  have hAmem : ∀ w : S, A (w : H) ∈ S := by
    intro w
    have hgoal : A (w : H) ∈ (ℂ ∙ u)ᗮ := by
      rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
      have h1 : (inner ℂ u (A (w : H)) : ℂ)
          = inner ℂ ((ContinuousLinearMap.adjoint A) u) (w : H) :=
        (ContinuousLinearMap.adjoint_inner_left A (w : H) u).symm
      rw [h1, hp.selfAdjoint.adjoint_eq, hp.apply_eq, inner_smul_left, hinner_mem w, mul_zero]
    exact hgoal
  have hA'coe : ∀ w : S, ((A' w : S) : H) = A (w : H) := by
    intro w
    have h1 : (inner ℂ u (A (w : H)) : ℂ) = 0 :=
      (Submodule.mem_orthogonal_singleton_iff_inner_right).mp (hAmem w)
    show ((P (A (ι w)) : S) : H) = A (w : H)
    rw [hPcoe, hιcoe, h1, zero_smul, sub_zero]
  have hA'compact : IsCompactOperator A' := by
    have h := (hp.compact.comp_clm ι).clm_comp P
    exact h
  have hnoteig : ¬ Module.End.HasEigenvalue (A' : Module.End ℂ S) μ := by
    intro h
    obtain ⟨w, hmem, hne⟩ := h.exists_hasEigenvector
    have heq : A' w = μ • w := Module.End.mem_eigenspace_iff.mp hmem
    have hH : A (w : H) = μ • (w : H) := by
      rw [← hA'coe w, heq]
      rfl
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hp.simple (w : H) hH)
    have h0 : (inner ℂ u (w : H) : ℂ) = 0 := hinner_mem w
    rw [← hc, inner_smul_right, huu, mul_one] at h0
    exact hne (Subtype.ext (by rw [← hc, h0, zero_smul]; rfl))
  have hres : μ ∈ resolventSet ℂ A' :=
    (hA'compact.hasEigenvalue_or_mem_resolventSet hp.ne_zero).resolve_left hnoteig
  obtain ⟨Uu, hUu⟩ := spectrum.mem_resolventSet_iff.mp hres
  set R : S →L[ℂ] S := ((Uu⁻¹ : (S →L[ℂ] S)ˣ) : S →L[ℂ] S) with hR
  have hRleft : ∀ y : S, R (μ • y - A' y) = y := by
    intro y
    have h : (R * ((algebraMap ℂ (S →L[ℂ] S)) μ - A')) = 1 := by
      rw [hR, hUu]
      exact Uu.inv_mul
    have := congrArg (fun T : S →L[ℂ] S => T y) h
    simpa [ContinuousLinearMap.mul_apply, Algebra.algebraMap_eq_smul_one] using this
  have hRright : ∀ y : S, μ • R y - A' (R y) = y := by
    intro y
    have h : (((algebraMap ℂ (S →L[ℂ] S)) μ - A') * R) = 1 := by
      rw [hR, hUu]
      exact Uu.mul_inv
    have := congrArg (fun T : S →L[ℂ] S => T y) h
    simpa [ContinuousLinearMap.mul_apply, Algebra.algebraMap_eq_smul_one] using this
  -- the fixed-point map
  set C : ℝ := ‖R‖ * ‖B‖ with hC
  have hC0 : 0 ≤ C := by positivity
  set δ : ℝ := (8 * (C + 1))⁻¹ with hδ
  have hδ0 : 0 < δ := by rw [hδ]; positivity
  set Φ : ℝ → S → S := fun t w =>
    (t : ℂ) • R (P (B (u + (w : H))) - (inner ℂ u (B (u + (w : H)))) • w) with hΦ
  have hΦnorm : ∀ (t : ℝ) (w : S), ‖w‖ ≤ 1 → ‖Φ t w‖ ≤ |t| * (6 * C) := by
    intro t w hw
    have hv : ‖u + (w : H)‖ ≤ 2 := by
      have := norm_add_le u (w : H)
      rw [hp.norm_eq] at this
      have hw' : ‖(w : H)‖ ≤ 1 := hw
      linarith
    have hB : ‖B (u + (w : H))‖ ≤ 2 * ‖B‖ := by
      have := B.le_opNorm (u + (w : H))
      nlinarith [norm_nonneg B, hv]
    have h1 : ‖P (B (u + (w : H)))‖ ≤ 4 * ‖B‖ := by
      have := hPnorm (B (u + (w : H)))
      linarith
    have h2 : ‖(inner ℂ u (B (u + (w : H))) : ℂ) • w‖ ≤ 2 * ‖B‖ := by
      rw [norm_smul]
      have hi : ‖(inner ℂ u (B (u + (w : H))) : ℂ)‖ ≤ 2 * ‖B‖ := by
        have := norm_inner_le_norm (𝕜 := ℂ) u (B (u + (w : H)))
        rw [hp.norm_eq, one_mul] at this
        linarith
      nlinarith [norm_nonneg (w : S), norm_nonneg B, hi]
    have h3 : ‖P (B (u + (w : H))) - (inner ℂ u (B (u + (w : H)))) • w‖ ≤ 6 * ‖B‖ := by
      have := norm_sub_le (P (B (u + (w : H))))
        ((inner ℂ u (B (u + (w : H))) : ℂ) • w)
      linarith
    have h4 : ‖R (P (B (u + (w : H))) - (inner ℂ u (B (u + (w : H)))) • w)‖ ≤ ‖R‖ * (6 * ‖B‖) := by
      refine le_trans (R.le_opNorm _) ?_
      exact mul_le_mul_of_nonneg_left h3 (norm_nonneg R)
    rw [hΦ]
    simp only
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
    calc |t| * ‖R (P (B (u + (w : H))) - (inner ℂ u (B (u + (w : H)))) • w)‖
        ≤ |t| * (‖R‖ * (6 * ‖B‖)) := mul_le_mul_of_nonneg_left h4 (abs_nonneg t)
      _ = |t| * (6 * C) := by rw [hC]; ring
  have hΦlip : ∀ (t : ℝ) (w₁ w₂ : S), ‖w₁‖ ≤ 1 → ‖w₂‖ ≤ 1 →
      ‖Φ t w₁ - Φ t w₂‖ ≤ |t| * (5 * C) * ‖w₁ - w₂‖ := by
    intro t w₁ w₂ hw₁ hw₂
    have hd : (u + (w₁ : H)) - (u + (w₂ : H)) = ((w₁ - w₂ : S) : H) := by
      push_cast
      abel
    have hPd : P (B (u + (w₁ : H))) - P (B (u + (w₂ : H))) = P (B ((w₁ - w₂ : S) : H)) := by
      rw [← map_sub, ← map_sub, hd]
    have hPdn : ‖P (B ((w₁ - w₂ : S) : H))‖ ≤ 2 * ‖B‖ * ‖w₁ - w₂‖ := by
      have h1 := hPnorm (B ((w₁ - w₂ : S) : H))
      have h2 := B.le_opNorm ((w₁ - w₂ : S) : H)
      have h3 : ‖((w₁ - w₂ : S) : H)‖ = ‖w₁ - w₂‖ := rfl
      rw [h3] at h2
      nlinarith [norm_nonneg (w₁ - w₂), norm_nonneg B]
    have hcd : (inner ℂ u (B (u + (w₁ : H))) : ℂ) - inner ℂ u (B (u + (w₂ : H)))
        = inner ℂ u (B ((w₁ - w₂ : S) : H)) := by
      rw [← inner_sub_right, ← map_sub, hd]
    have hcdn : ‖(inner ℂ u (B (u + (w₁ : H))) : ℂ) - inner ℂ u (B (u + (w₂ : H)))‖
        ≤ ‖B‖ * ‖w₁ - w₂‖ := by
      rw [hcd]
      have h1 := norm_inner_le_norm (𝕜 := ℂ) u (B ((w₁ - w₂ : S) : H))
      rw [hp.norm_eq, one_mul] at h1
      have h2 := B.le_opNorm ((w₁ - w₂ : S) : H)
      have h3 : ‖((w₁ - w₂ : S) : H)‖ = ‖w₁ - w₂‖ := rfl
      rw [h3] at h2
      linarith
    have hc1 : ‖(inner ℂ u (B (u + (w₁ : H))) : ℂ)‖ ≤ 2 * ‖B‖ := by
      have h1 := norm_inner_le_norm (𝕜 := ℂ) u (B (u + (w₁ : H)))
      rw [hp.norm_eq, one_mul] at h1
      have hv : ‖u + (w₁ : H)‖ ≤ 2 := by
        have := norm_add_le u (w₁ : H)
        rw [hp.norm_eq] at this
        have hw' : ‖(w₁ : H)‖ ≤ 1 := hw₁
        linarith
      have h2 := B.le_opNorm (u + (w₁ : H))
      nlinarith [norm_nonneg B]
    have hsplit : (inner ℂ u (B (u + (w₁ : H))) : ℂ) • w₁
          - (inner ℂ u (B (u + (w₂ : H))) : ℂ) • w₂
        = (inner ℂ u (B (u + (w₁ : H))) : ℂ) • (w₁ - w₂)
          + ((inner ℂ u (B (u + (w₁ : H))) : ℂ) - inner ℂ u (B (u + (w₂ : H)))) • w₂ := by
      rw [sub_smul, smul_sub]
      abel
    have hsplitn : ‖(inner ℂ u (B (u + (w₁ : H))) : ℂ) • w₁
          - (inner ℂ u (B (u + (w₂ : H))) : ℂ) • w₂‖ ≤ 3 * ‖B‖ * ‖w₁ - w₂‖ := by
      rw [hsplit]
      have hA := norm_add_le ((inner ℂ u (B (u + (w₁ : H))) : ℂ) • (w₁ - w₂))
        (((inner ℂ u (B (u + (w₁ : H))) : ℂ) - inner ℂ u (B (u + (w₂ : H)))) • w₂)
      rw [norm_smul, norm_smul] at hA
      nlinarith [norm_nonneg (w₁ - w₂), norm_nonneg B, hc1, hcdn, hw₂,
        norm_nonneg ((inner ℂ u (B (u + (w₂ : H))) : ℂ)), norm_nonneg w₂]
    have hinner : ‖(P (B (u + (w₁ : H))) - (inner ℂ u (B (u + (w₁ : H)))) • w₁)
        - (P (B (u + (w₂ : H))) - (inner ℂ u (B (u + (w₂ : H)))) • w₂)‖
        ≤ 5 * ‖B‖ * ‖w₁ - w₂‖ := by
      have hrw : (P (B (u + (w₁ : H))) - (inner ℂ u (B (u + (w₁ : H)))) • w₁)
          - (P (B (u + (w₂ : H))) - (inner ℂ u (B (u + (w₂ : H)))) • w₂)
          = (P (B (u + (w₁ : H))) - P (B (u + (w₂ : H))))
            - ((inner ℂ u (B (u + (w₁ : H))) : ℂ) • w₁
              - (inner ℂ u (B (u + (w₂ : H))) : ℂ) • w₂) := by abel
      rw [hrw, hPd]
      have := norm_sub_le (P (B ((w₁ - w₂ : S) : H)))
        ((inner ℂ u (B (u + (w₁ : H))) : ℂ) • w₁ - (inner ℂ u (B (u + (w₂ : H))) : ℂ) • w₂)
      linarith [hPdn, hsplitn]
    have hRd : ‖R ((P (B (u + (w₁ : H))) - (inner ℂ u (B (u + (w₁ : H)))) • w₁)
        - (P (B (u + (w₂ : H))) - (inner ℂ u (B (u + (w₂ : H)))) • w₂))‖
        ≤ ‖R‖ * (5 * ‖B‖ * ‖w₁ - w₂‖) := by
      refine le_trans (R.le_opNorm _) ?_
      exact mul_le_mul_of_nonneg_left hinner (norm_nonneg R)
    rw [hΦ]
    simp only
    rw [← smul_sub, ← map_sub, norm_smul, Complex.norm_real, Real.norm_eq_abs]
    calc |t| * ‖R ((P (B (u + (w₁ : H))) - (inner ℂ u (B (u + (w₁ : H)))) • w₁)
            - (P (B (u + (w₂ : H))) - (inner ℂ u (B (u + (w₂ : H)))) • w₂))‖
        ≤ |t| * (‖R‖ * (5 * ‖B‖ * ‖w₁ - w₂‖)) := mul_le_mul_of_nonneg_left hRd (abs_nonneg t)
      _ = |t| * (5 * C) * ‖w₁ - w₂‖ := by rw [hC]; ring
  sorry

end SimpleBranch

end HTGeometry
