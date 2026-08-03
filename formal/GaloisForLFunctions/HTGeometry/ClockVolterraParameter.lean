import GaloisForLFunctions.HTGeometry.ClockVolterraOperator

/-!
# Dependence of the Volterra operator on the characteristic parameter

The vector field of the characteristic ODE is `ξ ↦ A(ξ)`, and the Picard–Lindelöf structure of
mathlib asks for it to be continuous in `ξ` in the norm of the Banach space — that is, uniformly in
the second variable. This file supplies that, together with the uniform kernel bound on a compact
rectangle that the other two hypotheses need.

The estimates rest on two facts about a continuous kernel on a compact rectangle: it is bounded
there, and it is uniformly continuous there. Clamping both variables to the rectangle turns those
into global statements about the operator.
-/

namespace GaloisForLFunctions.HTGeometry

open Set Metric MeasureTheory

/-! ## The kernel on a compact rectangle -/

theorem continuous_kernel_slice {K : ℝ → ℝ → ℝ}
    (hK : Continuous fun p : ℝ × ℝ => K p.1 p.2) (a : ℝ) : Continuous (K a) :=
  hK.comp (continuous_const.prodMk continuous_id)

/-- **A continuous kernel is bounded on a compact rectangle.** -/
theorem exists_kernel_bound {K : ℝ → ℝ → ℝ} (hK : Continuous fun p : ℝ × ℝ => K p.1 p.2)
    (b b' c c' : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ ξ ∈ Icc c c', ∀ t ∈ Icc b b', |K ξ t| ≤ M := by
  obtain ⟨C, hC⟩ := ((isCompact_Icc (a := c) (b := c')).prod
    (isCompact_Icc (a := b) (b := b'))).exists_bound_of_continuousOn hK.continuousOn
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro ξ hξ t ht
  have h := hC (ξ, t) ⟨hξ, ht⟩
  rw [Real.norm_eq_abs] at h
  exact le_trans h (le_max_left _ _)

/-- **A continuous kernel is uniformly continuous on a compact rectangle**, in `ε`–`δ` form. -/
theorem exists_kernel_delta {K : ℝ → ℝ → ℝ} (hK : Continuous fun p : ℝ × ℝ => K p.1 p.2)
    (b b' c c' : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ ξ ∈ Icc c c', ∀ ξ' ∈ Icc c c', |ξ - ξ'| < δ →
      ∀ t ∈ Icc b b', |K ξ t - K ξ' t| ≤ ε := by
  have hcomp := (isCompact_Icc (a := c) (b := c')).prod (isCompact_Icc (a := b) (b := b'))
  have huc := hcomp.uniformContinuousOn_of_continuous hK.continuousOn
  obtain ⟨δ, hδ, hmain⟩ := Metric.uniformContinuousOn_iff.mp huc ε hε
  refine ⟨δ, hδ, ?_⟩
  intro ξ hξ ξ' hξ' hd t ht
  have hdist : dist ((ξ, t) : ℝ × ℝ) (ξ', t) < δ := by
    rw [Prod.dist_eq, dist_self, Real.dist_eq]
    exact max_lt hd hδ
  have h := hmain (ξ, t) ⟨hξ, ht⟩ (ξ', t) ⟨hξ', ht⟩ hdist
  rw [Real.dist_eq] at h
  exact le_of_lt h

/-! ## Clamping is nonexpansive -/

theorem abs_clampTo_sub_le (c c' ξ ξ' : ℝ) :
    |clampTo c c' ξ - clampTo c c' ξ'| ≤ |ξ - ξ'| := by
  have h1 := le_abs_self (ξ - ξ')
  have h2 := neg_abs_le (ξ - ξ')
  simp only [clampTo, min_def, max_def]
  rw [abs_le]
  constructor <;> · split_ifs <;> linarith

/-! ## Changing the kernel -/

/-- **Changing the kernel changes the operator by at most the kernel gap.** -/
theorem abs_volterraFun_kernel_sub_le {b b' : ℝ} (hbb : b ≤ b') {K₁ K₂ U : ℝ → ℝ} {ε C : ℝ}
    (hK₁ : Continuous K₁) (hK₂ : Continuous K₂) (hU : Continuous U)
    (hgap : ∀ t ∈ Icc b b', |K₁ t - K₂ t| ≤ ε) (hC : ∀ t, |U t| ≤ C)
    (hε0 : 0 ≤ ε) (hC0 : 0 ≤ C) (η : ℝ) :
    |volterraFun K₁ b b' U η - volterraFun K₂ b b' U η| ≤ ε * C * (b' - b) := by
  have hi₁ : IntervalIntegrable (fun t => K₁ t * U t) volume b (clampTo b b' η) :=
    (hK₁.mul hU).intervalIntegrable _ _
  have hi₂ : IntervalIntegrable (fun t => K₂ t * U t) volume b (clampTo b b' η) :=
    (hK₂.mul hU).intervalIntegrable _ _
  have hsub : volterraFun K₁ b b' U η - volterraFun K₂ b b' U η
      = ∫ t in b..clampTo b b' η, (K₁ t - K₂ t) * U t := by
    rw [volterraFun, volterraFun, ← intervalIntegral.integral_sub hi₁ hi₂]
    refine intervalIntegral.integral_congr ?_
    intro t _
    ring
  rw [hsub]
  have h := abs_volterraFun_le (b := b) (b' := b') hbb (K := fun t => K₁ t - K₂ t) (U := U)
    hgap hC hε0 hC0 η
  rw [volterraFun] at h
  exact h

/-! ## The vector field of the characteristic equation -/

/-- The vector field `ξ ↦ A(ξ)`, with both variables clamped to the rectangle so that the bounds
are global. -/
noncomputable def goursatBCF (K : ℝ → ℝ → ℝ) (b b' c c' M : ℝ)
    (hK : Continuous fun p : ℝ × ℝ => K p.1 p.2) (hbb : b ≤ b') (hcc : c ≤ c') (hM0 : 0 ≤ M)
    (hM : ∀ ξ ∈ Icc c c', ∀ t ∈ Icc b b', |K ξ t| ≤ M) (ξ : ℝ)
    (U : BoundedContinuousFunction ℝ ℝ) : BoundedContinuousFunction ℝ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (volterraFun (K (clampTo c c' ξ)) b b' U)
    (continuous_volterraFun (continuous_kernel_slice hK _) U.continuous b b')
    (M * ‖U‖ * (b' - b))
    (fun η => by
      rw [Real.norm_eq_abs]
      exact abs_volterraFun_le hbb (fun t ht => hM _ (clampTo_mem hcc ξ) t ht)
        (fun t => by
          rw [← Real.norm_eq_abs]
          exact U.norm_coe_le_norm t)
        hM0 (norm_nonneg U) η)

theorem goursatBCF_apply (K : ℝ → ℝ → ℝ) (b b' c c' M : ℝ)
    (hK : Continuous fun p : ℝ × ℝ => K p.1 p.2) (hbb : b ≤ b') (hcc : c ≤ c') (hM0 : 0 ≤ M)
    (hM : ∀ ξ ∈ Icc c c', ∀ t ∈ Icc b b', |K ξ t| ≤ M) (ξ : ℝ)
    (U : BoundedContinuousFunction ℝ ℝ) (η : ℝ) :
    goursatBCF K b b' c c' M hK hbb hcc hM0 hM ξ U η
      = volterraFun (K (clampTo c c' ξ)) b b' U η := rfl

/-- **The vector field is continuous in the characteristic parameter**, in the norm of the Banach
space — the hypothesis the Picard–Lindelöf structure requires. -/
theorem continuous_goursatBCF (K : ℝ → ℝ → ℝ) (b b' c c' M : ℝ)
    (hK : Continuous fun p : ℝ × ℝ => K p.1 p.2) (hbb : b ≤ b') (hcc : c ≤ c') (hM0 : 0 ≤ M)
    (hM : ∀ ξ ∈ Icc c c', ∀ t ∈ Icc b b', |K ξ t| ≤ M)
    (U : BoundedContinuousFunction ℝ ℝ) :
    Continuous fun ξ => goursatBCF K b b' c c' M hK hbb hcc hM0 hM ξ U := by
  rw [Metric.continuous_iff]
  intro ξ₀ ε hε
  have hlen : (0 : ℝ) ≤ b' - b := by linarith
  have hA0 : (0 : ℝ) < ‖U‖ * (b' - b) + 1 := by positivity
  have hε' : (0 : ℝ) < ε / (2 * (‖U‖ * (b' - b) + 1)) := by positivity
  obtain ⟨δ, hδ, hmain⟩ := exists_kernel_delta hK b b' c c' hε'
  refine ⟨δ, hδ, ?_⟩
  intro ξ hd
  have hgap : ∀ t ∈ Icc b b',
      |K (clampTo c c' ξ) t - K (clampTo c c' ξ₀) t| ≤ ε / (2 * (‖U‖ * (b' - b) + 1)) := by
    refine hmain _ (clampTo_mem hcc ξ) _ (clampTo_mem hcc ξ₀) ?_
    calc |clampTo c c' ξ - clampTo c c' ξ₀| ≤ |ξ - ξ₀| := abs_clampTo_sub_le c c' ξ ξ₀
      _ < δ := by rwa [← Real.dist_eq]
  have hpt : ∀ η : ℝ,
      ‖(goursatBCF K b b' c c' M hK hbb hcc hM0 hM ξ U
          - goursatBCF K b b' c c' M hK hbb hcc hM0 hM ξ₀ U) η‖
        ≤ ε / (2 * (‖U‖ * (b' - b) + 1)) * ‖U‖ * (b' - b) := by
    intro η
    have hval : (goursatBCF K b b' c c' M hK hbb hcc hM0 hM ξ U
        - goursatBCF K b b' c c' M hK hbb hcc hM0 hM ξ₀ U) η
        = volterraFun (K (clampTo c c' ξ)) b b' U η
          - volterraFun (K (clampTo c c' ξ₀)) b b' U η := rfl
    rw [hval, Real.norm_eq_abs]
    exact abs_volterraFun_kernel_sub_le hbb (continuous_kernel_slice hK _)
      (continuous_kernel_slice hK _) U.continuous hgap
      (fun t => by
        rw [← Real.norm_eq_abs]
        exact U.norm_coe_le_norm t)
      (le_of_lt hε') (norm_nonneg U) η
  have hnormle : ‖goursatBCF K b b' c c' M hK hbb hcc hM0 hM ξ U
      - goursatBCF K b b' c c' M hK hbb hcc hM0 hM ξ₀ U‖
      ≤ ε / (2 * (‖U‖ * (b' - b) + 1)) * ‖U‖ * (b' - b) :=
    (BoundedContinuousFunction.norm_le
      (by positivity)).2 hpt
  have hfinal : ε / (2 * (‖U‖ * (b' - b) + 1)) * ‖U‖ * (b' - b) < ε := by
    have hle : ‖U‖ * (b' - b) ≤ ‖U‖ * (b' - b) + 1 := by linarith
    have hstep : ε / (2 * (‖U‖ * (b' - b) + 1)) * (‖U‖ * (b' - b))
        ≤ ε / (2 * (‖U‖ * (b' - b) + 1)) * (‖U‖ * (b' - b) + 1) :=
      mul_le_mul_of_nonneg_left hle (le_of_lt hε')
    have hcalc : ε / (2 * (‖U‖ * (b' - b) + 1)) * (‖U‖ * (b' - b) + 1) = ε / 2 := by
      field_simp
    nlinarith [hstep, hcalc]
  rw [dist_eq_norm]
  exact lt_of_le_of_lt hnormle hfinal

end GaloisForLFunctions.HTGeometry
