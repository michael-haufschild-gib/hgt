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

set_option maxHeartbeats 1600000 in
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
      rw [hR, ← hUu]
      exact Uu.inv_mul
    have := congrArg (fun T : S →L[ℂ] S => T y) h
    simpa [mul_apply_eq_comp, Algebra.algebraMap_eq_smul_one] using this
  have hRright : ∀ y : S, μ • R y - A' (R y) = y := by
    intro y
    have h : (((algebraMap ℂ (S →L[ℂ] S)) μ - A') * R) = 1 := by
      rw [hR, ← hUu]
      exact Uu.mul_inv
    have := congrArg (fun T : S →L[ℂ] S => T y) h
    simpa [mul_apply_eq_comp, Algebra.algebraMap_eq_smul_one] using this
  -- the fixed-point map
  set C : ℝ := ‖R‖ * ‖B‖ with hC
  have hC0 : 0 ≤ C := by positivity
  set δ : ℝ := (8 * (C + 1))⁻¹ with hδ
  have hδ0 : 0 < δ := by rw [hδ]; positivity
  set Φ : ℝ → S → S := fun t w =>
    (t : ℂ) • R (P (B (u + (w : H))) - (inner ℂ u (B (u + (w : H)))) • w) with hΦ
  have hnormB : ∀ w : S, ‖w‖ ≤ 1 → ‖B (u + (w : H))‖ ≤ 2 * ‖B‖ := by
    intro w hw
    have hv : ‖u + (w : H)‖ ≤ 2 := by
      have h := norm_add_le u (w : H)
      rw [hp.norm_eq] at h
      have hw' : ‖(w : H)‖ ≤ 1 := hw
      linarith
    calc ‖B (u + (w : H))‖ ≤ ‖B‖ * ‖u + (w : H)‖ := B.le_opNorm _
      _ ≤ ‖B‖ * 2 := mul_le_mul_of_nonneg_left hv (norm_nonneg B)
      _ = 2 * ‖B‖ := by ring
  have hnormC : ∀ w : S, ‖w‖ ≤ 1 → ‖(inner ℂ u (B (u + (w : H))) : ℂ)‖ ≤ 2 * ‖B‖ := by
    intro w hw
    calc ‖(inner ℂ u (B (u + (w : H))) : ℂ)‖ ≤ ‖u‖ * ‖B (u + (w : H))‖ :=
          norm_inner_le_norm (𝕜 := ℂ) u (B (u + (w : H)))
      _ = ‖B (u + (w : H))‖ := by rw [hp.norm_eq, one_mul]
      _ ≤ 2 * ‖B‖ := hnormB w hw
  have hΦnorm : ∀ (t : ℝ) (w : S), ‖w‖ ≤ 1 → ‖Φ t w‖ ≤ |t| * (6 * C) := by
    intro t w hw
    have h1 : ‖P (B (u + (w : H)))‖ ≤ 4 * ‖B‖ := by
      calc ‖P (B (u + (w : H)))‖ ≤ 2 * ‖B (u + (w : H))‖ := hPnorm _
        _ ≤ 2 * (2 * ‖B‖) := by linarith [hnormB w hw]
        _ = 4 * ‖B‖ := by ring
    have h2 : ‖(inner ℂ u (B (u + (w : H))) : ℂ) • w‖ ≤ 2 * ‖B‖ := by
      rw [norm_smul]
      calc ‖(inner ℂ u (B (u + (w : H))) : ℂ)‖ * ‖w‖ ≤ (2 * ‖B‖) * 1 :=
            mul_le_mul (hnormC w hw) hw (norm_nonneg _) (by positivity)
        _ = 2 * ‖B‖ := by ring
    have h3 : ‖P (B (u + (w : H))) - (inner ℂ u (B (u + (w : H)))) • w‖ ≤ 6 * ‖B‖ := by
      have h := norm_sub_le (P (B (u + (w : H))))
        ((inner ℂ u (B (u + (w : H))) : ℂ) • w)
      linarith
    have h4 : ‖R (P (B (u + (w : H))) - (inner ℂ u (B (u + (w : H)))) • w)‖
        ≤ ‖R‖ * (6 * ‖B‖) :=
      le_trans (R.le_opNorm _) (mul_le_mul_of_nonneg_left h3 (norm_nonneg R))
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
    have hnd : ‖((w₁ - w₂ : S) : H)‖ = ‖w₁ - w₂‖ := rfl
    have hPd : P (B (u + (w₁ : H))) - P (B (u + (w₂ : H))) = P (B ((w₁ - w₂ : S) : H)) := by
      rw [← map_sub, ← map_sub, hd]
    have hPdn : ‖P (B ((w₁ - w₂ : S) : H))‖ ≤ 2 * ‖B‖ * ‖w₁ - w₂‖ := by
      calc ‖P (B ((w₁ - w₂ : S) : H))‖ ≤ 2 * ‖B ((w₁ - w₂ : S) : H)‖ := hPnorm _
        _ ≤ 2 * (‖B‖ * ‖((w₁ - w₂ : S) : H)‖) := by
            have h := B.le_opNorm ((w₁ - w₂ : S) : H); linarith
        _ = 2 * ‖B‖ * ‖w₁ - w₂‖ := by rw [hnd]; ring
    have hcd : (inner ℂ u (B (u + (w₁ : H))) : ℂ) - inner ℂ u (B (u + (w₂ : H)))
        = inner ℂ u (B ((w₁ - w₂ : S) : H)) := by
      rw [← inner_sub_right, ← map_sub, hd]
    have hcdn : ‖(inner ℂ u (B (u + (w₁ : H))) : ℂ) - inner ℂ u (B (u + (w₂ : H)))‖
        ≤ ‖B‖ * ‖w₁ - w₂‖ := by
      rw [hcd]
      calc ‖(inner ℂ u (B ((w₁ - w₂ : S) : H)) : ℂ)‖ ≤ ‖u‖ * ‖B ((w₁ - w₂ : S) : H)‖ :=
            norm_inner_le_norm (𝕜 := ℂ) u (B ((w₁ - w₂ : S) : H))
        _ = ‖B ((w₁ - w₂ : S) : H)‖ := by rw [hp.norm_eq, one_mul]
        _ ≤ ‖B‖ * ‖((w₁ - w₂ : S) : H)‖ := B.le_opNorm _
        _ = ‖B‖ * ‖w₁ - w₂‖ := by rw [hnd]
    have hsplit : (inner ℂ u (B (u + (w₁ : H))) : ℂ) • w₁
          - (inner ℂ u (B (u + (w₂ : H))) : ℂ) • w₂
        = (inner ℂ u (B (u + (w₁ : H))) : ℂ) • (w₁ - w₂)
          + ((inner ℂ u (B (u + (w₁ : H))) : ℂ) - inner ℂ u (B (u + (w₂ : H)))) • w₂ := by
      rw [sub_smul, smul_sub]
      abel
    have e1 : ‖(inner ℂ u (B (u + (w₁ : H))) : ℂ) • (w₁ - w₂)‖ ≤ 2 * ‖B‖ * ‖w₁ - w₂‖ := by
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_right (hnormC w₁ hw₁) (norm_nonneg _)
    have e2 : ‖((inner ℂ u (B (u + (w₁ : H))) : ℂ)
        - inner ℂ u (B (u + (w₂ : H)))) • w₂‖ ≤ ‖B‖ * ‖w₁ - w₂‖ := by
      rw [norm_smul]
      calc ‖(inner ℂ u (B (u + (w₁ : H))) : ℂ) - inner ℂ u (B (u + (w₂ : H)))‖ * ‖w₂‖
          ≤ (‖B‖ * ‖w₁ - w₂‖) * 1 :=
            mul_le_mul hcdn hw₂ (norm_nonneg _) (by positivity)
        _ = ‖B‖ * ‖w₁ - w₂‖ := by ring
    have hsplitn : ‖(inner ℂ u (B (u + (w₁ : H))) : ℂ) • w₁
          - (inner ℂ u (B (u + (w₂ : H))) : ℂ) • w₂‖ ≤ 3 * ‖B‖ * ‖w₁ - w₂‖ := by
      rw [hsplit]
      have hA := norm_add_le ((inner ℂ u (B (u + (w₁ : H))) : ℂ) • (w₁ - w₂))
        (((inner ℂ u (B (u + (w₁ : H))) : ℂ) - inner ℂ u (B (u + (w₂ : H)))) • w₂)
      linarith
    have hinner : ‖(P (B (u + (w₁ : H))) - (inner ℂ u (B (u + (w₁ : H)))) • w₁)
        - (P (B (u + (w₂ : H))) - (inner ℂ u (B (u + (w₂ : H)))) • w₂)‖
        ≤ 5 * ‖B‖ * ‖w₁ - w₂‖ := by
      have hrw : (P (B (u + (w₁ : H))) - (inner ℂ u (B (u + (w₁ : H)))) • w₁)
          - (P (B (u + (w₂ : H))) - (inner ℂ u (B (u + (w₂ : H)))) • w₂)
          = (P (B (u + (w₁ : H))) - P (B (u + (w₂ : H))))
            - ((inner ℂ u (B (u + (w₁ : H))) : ℂ) • w₁
              - (inner ℂ u (B (u + (w₂ : H))) : ℂ) • w₂) := by abel
      rw [hrw, hPd]
      have h := norm_sub_le (P (B ((w₁ - w₂ : S) : H)))
        ((inner ℂ u (B (u + (w₁ : H))) : ℂ) • w₁ - (inner ℂ u (B (u + (w₂ : H))) : ℂ) • w₂)
      linarith
    have hRd : ‖R ((P (B (u + (w₁ : H))) - (inner ℂ u (B (u + (w₁ : H)))) • w₁)
        - (P (B (u + (w₂ : H))) - (inner ℂ u (B (u + (w₂ : H)))) • w₂))‖
        ≤ ‖R‖ * (5 * ‖B‖ * ‖w₁ - w₂‖) :=
      le_trans (R.le_opNorm _) (mul_le_mul_of_nonneg_left hinner (norm_nonneg R))
    rw [hΦ]
    simp only
    rw [← smul_sub, ← map_sub, norm_smul, Complex.norm_real, Real.norm_eq_abs]
    calc |t| * ‖R ((P (B (u + (w₁ : H))) - (inner ℂ u (B (u + (w₁ : H)))) • w₁)
            - (P (B (u + (w₂ : H))) - (inner ℂ u (B (u + (w₂ : H)))) • w₂))‖
        ≤ |t| * (‖R‖ * (5 * ‖B‖ * ‖w₁ - w₂‖)) := mul_le_mul_of_nonneg_left hRd (abs_nonneg t)
      _ = |t| * (5 * C) * ‖w₁ - w₂‖ := by rw [hC]; ring
  -- numeric bounds coming from the choice of `δ`
  have hCpos : (0 : ℝ) < 8 * (C + 1) := by positivity
  have hbound6 : ∀ t : ℝ, |t| < δ → |t| * (6 * C) ≤ 3 / 4 := by
    intro t ht
    have h2 : |t| * (6 * C) ≤ δ * (6 * C) :=
      mul_le_mul_of_nonneg_right ht.le (by positivity)
    have h3 : δ * (6 * C) ≤ 3 / 4 := by
      rw [hδ, inv_mul_eq_div, div_le_iff₀ hCpos]
      nlinarith [hC0]
    linarith
  have hbound5 : ∀ t : ℝ, |t| < δ → |t| * (5 * C) ≤ 5 / 8 := by
    intro t ht
    have h2 : |t| * (5 * C) ≤ δ * (5 * C) :=
      mul_le_mul_of_nonneg_right ht.le (by positivity)
    have h3 : δ * (5 * C) ≤ 5 / 8 := by
      rw [hδ, inv_mul_eq_div, div_le_iff₀ hCpos]
      nlinarith [hC0]
    linarith
  -- the contraction fixed point
  have hfix : ∀ t : ℝ, ∃ w : S, ‖w‖ ≤ |t| * (6 * C) ∧ (|t| < δ → w = Φ t w) := by
    intro t
    by_cases ht : |t| < δ
    · haveI : Nonempty (Metric.closedBall (0 : S) 1) := ⟨⟨0, by simp⟩⟩
      haveI : CompleteSpace (Metric.closedBall (0 : S) 1) :=
        (Metric.isClosed_closedBall).completeSpace_coe
      have hmem : ∀ x : Metric.closedBall (0 : S) 1, ‖(x : S)‖ ≤ 1 := by
        intro x
        have hx := x.2
        rw [Metric.mem_closedBall, dist_zero_right] at hx
        exact hx
      have hmaps : Set.MapsTo (Φ t) (Metric.closedBall (0 : S) 1)
          (Metric.closedBall (0 : S) 1) := by
        intro x hx
        have hx1 : ‖x‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_zero_right] using hx
        have h := hΦnorm t x hx1
        have h2 := hbound6 t ht
        simp only [Metric.mem_closedBall, dist_zero_right]
        linarith
      have hlip : LipschitzWith (5 / 8 : NNReal) (hmaps.restrict _ _ _) := by
        refine LipschitzWith.of_dist_le_mul fun x y => ?_
        have h := hΦlip t (x : S) (y : S) (hmem x) (hmem y)
        have h5 := hbound5 t ht
        have hd : dist (hmaps.restrict _ _ _ x) (hmaps.restrict _ _ _ y)
            = ‖Φ t (x : S) - Φ t (y : S)‖ := by
          rw [Subtype.dist_eq, dist_eq_norm]
          rfl
        have hd2 : dist x y = ‖(x : S) - (y : S)‖ := by
          rw [Subtype.dist_eq, dist_eq_norm]
        rw [hd, hd2]
        have hk : ((5 / 8 : NNReal) : ℝ) = 5 / 8 := by norm_num
        rw [hk]
        have hn : (0 : ℝ) ≤ ‖(x : S) - (y : S)‖ := norm_nonneg _
        nlinarith [h, h5, hn]
      have hcw : ContractingWith (5 / 8 : NNReal) (hmaps.restrict _ _ _) :=
        ⟨by norm_num, hlip⟩
      set y := hcw.fixedPoint _ with hy
      have hfp : Function.IsFixedPt (hmaps.restrict _ _ _) y := hcw.fixedPoint_isFixedPt
      have hyeq : Φ t (y : S) = (y : S) := congrArg Subtype.val hfp
      refine ⟨(y : S), ?_, fun _ => hyeq.symm⟩
      rw [← hyeq]
      exact hΦnorm t (y : S) (hmem y)
    · exact ⟨0, by rw [norm_zero]; positivity, fun h => absurd h ht⟩
  choose w hwb hwfix using hfix
  have hw0 : w 0 = 0 := by
    have h := hwb 0
    simp only [abs_zero, zero_mul] at h
    exact norm_le_zero_iff.mp h
  refine ⟨δ, hδ0, fun t => μ + (t : ℂ) * inner ℂ u (B (u + (w t : H))),
    fun t => u + (w t : H), by simp, by simp [hw0], ?_, ?_, ?_⟩
  · intro t ht
    set c : ℂ := inner ℂ u (B (u + (w t : H))) with hc
    set vt : H := u + (w t : H) with hvt
    set zz : S := P (B vt) - c • (w t) with hzz
    have hkey : μ • (w t) - A' (w t) = (t : ℂ) • zz := by
      conv_lhs => rw [hwfix t ht]
      have h1 : μ • ((t : ℂ) • R zz) - A' ((t : ℂ) • R zz)
          = (t : ℂ) • (μ • R zz - A' (R zz)) := by
        rw [map_smul, smul_comm, smul_sub]
      rw [show Φ t (w t) = (t : ℂ) • R zz from rfl, h1, hRright zz]
    have hkeyH : μ • ((w t : S) : H) - A ((w t : S) : H)
        = (t : ℂ) • (((P (B vt) : S) : H) - c • ((w t : S) : H)) := by
      have h := congrArg (fun x : S => (x : H)) hkey
      simpa [hzz, hA'coe] using h
    have hAvt : A vt = μ • u + A ((w t : S) : H) := by
      rw [hvt, map_add, hp.apply_eq]
    have hBdec : B vt = c • u + ((P (B vt) : S) : H) := hdecomp (B vt)
    show (A + (t : ℂ) • B) vt = (μ + (t : ℂ) * c) • vt
    rw [add_apply, smul_apply, hAvt]
    rw [show B vt = c • u + ((P (B vt) : S) : H) from hBdec]
    have e : (μ + (t : ℂ) * c) • vt
          - (μ • u + A ((w t : S) : H) + (t : ℂ) • (c • u + ((P (B vt) : S) : H)))
        = (μ • ((w t : S) : H) - A ((w t : S) : H))
          - (t : ℂ) • (((P (B vt) : S) : H) - c • ((w t : S) : H)) := by
      rw [hvt]
      module
    have e0 : (μ • ((w t : S) : H) - A ((w t : S) : H))
        - (t : ℂ) • (((P (B vt) : S) : H) - c • ((w t : S) : H)) = 0 := by
      rw [hkeyH, sub_self]
    exact (sub_eq_zero.mp (e.trans e0)).symm
  · intro t ht
    have h1 : ‖((w t : S) : H)‖ ≤ 3 / 4 := le_trans (hwb t) (hbound6 t ht)
    intro hzero
    have h2 : ‖u‖ = ‖-((w t : S) : H)‖ := by
      rw [show u = -((w t : S) : H) from by
        have : u + ((w t : S) : H) = 0 := hzero
        linear_combination (norm := module) this]
    rw [hp.norm_eq, norm_neg] at h2
    linarith
  · rw [hasDerivAt_iff_tendsto_slope]
    have hwtend : Filter.Tendsto (fun t : ℝ => ((w t : S) : H)) (nhds 0) (nhds 0) := by
      refine squeeze_zero_norm (fun t => hwb t) ?_
      have : Filter.Tendsto (fun t : ℝ => |t| * (6 * C)) (nhds 0) (nhds (|(0:ℝ)| * (6 * C))) :=
        ((continuous_abs.tendsto 0).mul tendsto_const_nhds)
      simpa using this
    have hvtend : Filter.Tendsto (fun t : ℝ => u + ((w t : S) : H)) (nhds 0) (nhds u) := by
      have h : Filter.Tendsto (fun t : ℝ => u + ((w t : S) : H)) (nhds 0) (nhds (u + 0)) :=
        tendsto_const_nhds.add hwtend
      simpa using h
    have hctend : Filter.Tendsto (fun t : ℝ => (inner ℂ u (B (u + ((w t : S) : H))) : ℂ))
        (nhds 0) (nhds (inner ℂ u (B u))) := by
      have hcont : Continuous fun x : H => (inner ℂ u (B x) : ℂ) :=
        ((innerSL ℂ u).comp B).continuous
      exact (hcont.tendsto u).comp hvtend
    refine Filter.Tendsto.congr' ?_ (hctend.mono_left nhdsWithin_le_nhds)
    filter_upwards [self_mem_nhdsWithin] with t ht
    have htne : (t : ℝ) ≠ 0 := ht
    have htc : ((t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast htne
    have hs : slope (fun t : ℝ => μ + (t : ℂ) * inner ℂ u (B (u + (w t : H)))) 0 t
        = (inner ℂ u (B (u + (w t : H))) : ℂ) := by
      simp only [slope, vsub_eq_sub, sub_zero, Complex.ofReal_zero, zero_mul, add_zero,
        add_sub_cancel_left]
      rw [Complex.real_smul, Complex.ofReal_inv]
      field_simp
    exact hs.symm

end SimpleBranch

end HTGeometry
