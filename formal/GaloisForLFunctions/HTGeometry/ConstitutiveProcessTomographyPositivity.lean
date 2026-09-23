import Mathlib

/-!
# Interior positivity does not repair an incomplete experiment

A uniformly positive operator stays positive under any perturbation of operator norm smaller than
its positivity constant.  On a finite-dimensional space every positive definite operator has such a
constant — the least eigenvalue, obtained here as the minimum of the quadratic form on the unit
sphere — so both perturbations `W₀ ± εΔ` along a blind direction are positive definite, distinct,
and carry the same experimental record whenever `ε‖Δ‖` is below that constant.
-/

namespace GaloisForLFunctions.HTGeometry

open RCLike ContinuousLinearMap

noncomputable section

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-! ## The quadratic form of a perturbation -/

theorem reApplyInnerSelf_add (A B : E →L[𝕜] E) (x : E) :
    (A + B).reApplyInnerSelf x = A.reApplyInnerSelf x + B.reApplyInnerSelf x := by
  simp only [ContinuousLinearMap.reApplyInnerSelf_apply, add_apply,
    inner_add_left, map_add]

theorem reApplyInnerSelf_sub (A B : E →L[𝕜] E) (x : E) :
    (A - B).reApplyInnerSelf x = A.reApplyInnerSelf x - B.reApplyInnerSelf x := by
  simp only [ContinuousLinearMap.reApplyInnerSelf_apply, sub_apply,
    inner_sub_left, map_sub]

theorem abs_reApplyInnerSelf_le (D : E →L[𝕜] E) (x : E) :
    |D.reApplyInnerSelf x| ≤ ‖D‖ * ‖x‖ ^ (2 : ℕ) := by
  rw [ContinuousLinearMap.reApplyInnerSelf_apply]
  calc |RCLike.re (inner 𝕜 (D x) x)| ≤ ‖inner 𝕜 (D x) x‖ := RCLike.abs_re_le_norm _
    _ ≤ ‖D x‖ * ‖x‖ := norm_inner_le_norm _ _
    _ ≤ (‖D‖ * ‖x‖) * ‖x‖ := mul_le_mul_of_nonneg_right (D.le_opNorm x) (norm_nonneg x)
    _ = ‖D‖ * ‖x‖ ^ (2 : ℕ) := by ring

/-! ## Positivity survives a small perturbation -/

/-- **Equation (8), operator form.**  A uniformly positive operator stays positive definite under
both perturbations by an operator of smaller norm. -/
theorem reApplyInnerSelf_pos_of_perturb {W₀ D : E →L[𝕜] E} {c : ℝ}
    (hW₀ : ∀ x : E, c * ‖x‖ ^ (2 : ℕ) ≤ W₀.reApplyInnerSelf x) (hlt : ‖D‖ < c)
    {x : E} (hx : x ≠ 0) :
    0 < (W₀ + D).reApplyInnerSelf x ∧ 0 < (W₀ - D).reApplyInnerSelf x := by
  have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hxsq : 0 < ‖x‖ ^ (2 : ℕ) := by positivity
  have h1 := hW₀ x
  have habs := abs_le.mp (abs_reApplyInnerSelf_le D x)
  have hgap : ‖D‖ * ‖x‖ ^ (2 : ℕ) < c * ‖x‖ ^ (2 : ℕ) := by
    exact mul_lt_mul_of_pos_right hlt hxsq
  constructor
  · rw [reApplyInnerSelf_add]
    linarith [habs.1, habs.2]
  · rw [reApplyInnerSelf_sub]
    linarith [habs.1, habs.2]

/-- **Equation (8).**  Both `W₀ ± εΔ` are positive definite once `ε‖Δ‖` is below the positivity
constant of `W₀`. -/
theorem reApplyInnerSelf_pos_of_smul_perturb {W₀ Δ : E →L[𝕜] E} {c ε : ℝ}
    (hW₀ : ∀ x : E, c * ‖x‖ ^ (2 : ℕ) ≤ W₀.reApplyInnerSelf x) (hε : 0 < ε) (hlt : ε * ‖Δ‖ < c)
    {x : E} (hx : x ≠ 0) :
    0 < (W₀ + (ε : 𝕜) • Δ).reApplyInnerSelf x
      ∧ 0 < (W₀ - (ε : 𝕜) • Δ).reApplyInnerSelf x := by
  have hnorm : ‖(ε : 𝕜) • Δ‖ = ε * ‖Δ‖ := by
    rw [norm_smul, RCLike.norm_ofReal, abs_of_pos hε]
  refine reApplyInnerSelf_pos_of_perturb hW₀ ?_ hx
  rw [hnorm]
  exact hlt

/-! ## The two perturbations are distinct and have the same record -/

theorem perturb_ne {W₀ Δ : E →L[𝕜] E} {ε : ℝ} (hε : 0 < ε) (hΔ : Δ ≠ 0) :
    W₀ + (ε : 𝕜) • Δ ≠ W₀ - (ε : 𝕜) • Δ := by
  intro h
  have hzero : (2 : 𝕜) • ((ε : 𝕜) • Δ) = 0 := by
    have := sub_eq_zero.mpr h
    simp only [add_sub_sub_cancel] at this
    rw [two_smul]
    simpa using this
  have hε𝕜 : ((ε : 𝕜)) ≠ 0 := by
    simpa using hε.ne'
  have htwo : (2 : 𝕜) ≠ 0 := two_ne_zero
  rw [smul_eq_zero] at hzero
  rcases hzero with h2 | h3
  · exact htwo h2
  · rw [smul_eq_zero] at h3
    rcases h3 with h4 | h5
    · exact hε𝕜 h4
    · exact hΔ h5

theorem record_eq_of_blind {F : Type*} [AddCommGroup F] [Module 𝕜 F]
    (rec : (E →L[𝕜] E) →ₗ[𝕜] F) {W₀ Δ : E →L[𝕜] E} (hΔ : rec Δ = 0) (ε : 𝕜) :
    rec (W₀ + ε • Δ) = rec (W₀ - ε • Δ) := by
  rw [map_add, map_sub, map_smul, hΔ, smul_zero, add_zero, sub_zero]

/-! ## The positivity constant exists in finite dimension -/

theorem continuous_reApplyInnerSelf (W : E →L[𝕜] E) :
    Continuous fun x : E => W.reApplyInnerSelf x := by
  simp only [ContinuousLinearMap.reApplyInnerSelf_apply]
  exact RCLike.continuous_re.comp (continuous_inner.comp (W.continuous.prodMk continuous_id))

/-- **The least eigenvalue as a uniform positivity constant.**  On a finite-dimensional space a
positive definite operator dominates a positive multiple of the squared norm. -/
theorem exists_uniform_positive [FiniteDimensional 𝕜 E] {W : E →L[𝕜] E}
    (hW : ∀ x : E, x ≠ 0 → 0 < W.reApplyInnerSelf x) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : E, c * ‖x‖ ^ (2 : ℕ) ≤ W.reApplyInnerSelf x := by
  rcases subsingleton_or_nontrivial E with hs | hn
  · refine ⟨1, one_pos, fun x => ?_⟩
    have hx : x = 0 := Subsingleton.elim x 0
    subst hx
    simp [ContinuousLinearMap.reApplyInnerSelf_apply]
  · haveI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
    haveI : FiniteDimensional ℝ E := FiniteDimensional.trans ℝ 𝕜 E
    haveI : ProperSpace E := FiniteDimensional.proper ℝ E
    have hsph : IsCompact (Metric.sphere (0 : E) 1) := isCompact_sphere 0 1
    have hne : (Metric.sphere (0 : E) 1).Nonempty :=
      NormedSpace.sphere_nonempty.mpr zero_le_one
    obtain ⟨x₀, hx₀mem, hx₀⟩ :=
      hsph.exists_isMinOn hne (continuous_reApplyInnerSelf W).continuousOn
    have hx₀norm : ‖x₀‖ = 1 := by
      simpa using hx₀mem
    have hx₀ne : x₀ ≠ 0 := by
      intro h
      rw [h, norm_zero] at hx₀norm
      exact absurd hx₀norm (by norm_num)
    refine ⟨W.reApplyInnerSelf x₀, hW x₀ hx₀ne, fun x => ?_⟩
    rcases eq_or_ne x 0 with rfl | hx
    · simp [ContinuousLinearMap.reApplyInnerSelf_apply]
    · have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx
      set y : E := ((‖x‖⁻¹ : ℝ) : 𝕜) • x with hy
      have hcoe : ‖((‖x‖⁻¹ : ℝ) : 𝕜)‖ = ‖x‖⁻¹ := by
        rw [RCLike.norm_ofReal, abs_of_pos (inv_pos.mpr hxn)]
      have hynorm : ‖y‖ = 1 := by
        rw [hy, norm_smul, hcoe, inv_mul_cancel₀ hxn.ne']
      have hymem : y ∈ Metric.sphere (0 : E) 1 := by
        simpa using hynorm
      have hmin : W.reApplyInnerSelf x₀ ≤ W.reApplyInnerSelf y := hx₀ hymem
      have hscale : W.reApplyInnerSelf y = ‖x‖⁻¹ ^ (2 : ℕ) * W.reApplyInnerSelf x := by
        rw [hy, ContinuousLinearMap.reApplyInnerSelf_smul, hcoe]
      rw [hscale] at hmin
      have hsq : 0 < ‖x‖ ^ (2 : ℕ) := by positivity
      have hmul := mul_le_mul_of_nonneg_right hmin hsq.le
      have hcancel : ‖x‖⁻¹ ^ (2 : ℕ) * W.reApplyInnerSelf x * ‖x‖ ^ (2 : ℕ) = W.reApplyInnerSelf x := by
        field_simp
      rw [hcancel] at hmul
      exact hmul

/-! ## The blind sector survives interior positivity -/

/-- **Section 3 of the card.**  A positive definite process admits a threshold below which both
perturbations along any nonzero blind direction remain positive definite, stay distinct, and
produce the identical experimental record. -/
theorem interiorPositivity_blindDirection_persists [FiniteDimensional 𝕜 E]
    {F : Type*} [AddCommGroup F] [Module 𝕜 F] (rec : (E →L[𝕜] E) →ₗ[𝕜] F)
    {W₀ Δ : E →L[𝕜] E} (hW₀ : ∀ x : E, x ≠ 0 → 0 < W₀.reApplyInnerSelf x)
    (hΔ0 : Δ ≠ 0) (hΔrec : rec Δ = 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ ε : ℝ, 0 < ε → ε * ‖Δ‖ < c →
      (∀ x : E, x ≠ 0 → 0 < (W₀ + (ε : 𝕜) • Δ).reApplyInnerSelf x
          ∧ 0 < (W₀ - (ε : 𝕜) • Δ).reApplyInnerSelf x)
        ∧ W₀ + (ε : 𝕜) • Δ ≠ W₀ - (ε : 𝕜) • Δ
        ∧ rec (W₀ + (ε : 𝕜) • Δ) = rec (W₀ - (ε : 𝕜) • Δ) := by
  obtain ⟨c, hcpos, hc⟩ := exists_uniform_positive hW₀
  refine ⟨c, hcpos, fun ε hε hlt => ⟨fun x hx => ?_, perturb_ne hε hΔ0, ?_⟩⟩
  · exact reApplyInnerSelf_pos_of_smul_perturb hc hε hlt hx
  · exact record_eq_of_blind rec hΔrec ((ε : 𝕜))

end

end GaloisForLFunctions.HTGeometry
