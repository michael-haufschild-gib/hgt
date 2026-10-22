import GaloisForLFunctions.HTGeometry.KleinGordon.KleinGordonFullReconstruction

/-!
# A multiplication operator determines its potential

The corpus records that an almost-everywhere vanishing symbol induces the zero operator. The converse
is what an inverse problem needs, and it is not in the corpus: a symbol whose operator vanishes must
vanish almost everywhere.

It follows from testing the operator on the indicator of a ball — the very vector built for the
non-surjectivity of `⟨D⟩⁻¹`. Applying the operator to it multiplies the symbol by one on the ball, so
the symbol vanishes almost everywhere there; the balls of integer radius exhaust the space, and a
countable union of null sets is null.

The consequence is that the reconstruction theorems, which recover the *operator*, recover the
**potential**: two bounded real potentials whose clocks are observationally identical agree almost
everywhere.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Metric

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **A symbol whose multiplication operator vanishes vanishes almost everywhere.** -/
theorem ae_eq_zero_of_lpBoundedMulCLM_eq_zero {φ : E → ℂ} (hφ : Measurable φ) {C : ℝ}
    (hC0 : 0 ≤ C) (hC : ∀ x : E, ‖φ x‖ ≤ C)
    (hzero : lpBoundedMulCLM (p := 2) (μ := (volume : Measure E)) hφ hC0 hC = 0) :
    ∀ᵐ x ∂(volume : Measure E), φ x = 0 := by
  have hball : ∀ n : ℕ, ∀ᵐ x ∂(volume : Measure E),
      x ∈ ball (0 : E) ((n : ℝ) + 1) → φ x = 0 := by
    intro n
    have hr : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have h1 := lpBoundedMulCLM_coeFn (p := 2) (μ := (volume : Measure E)) hφ hC0 hC
      (kgBallFun 0 ((n : ℝ) + 1))
    have happ : lpBoundedMulCLM (p := 2) (μ := (volume : Measure E)) hφ hC0 hC
        (kgBallFun 0 ((n : ℝ) + 1)) = 0 := by
      rw [hzero]
      rfl
    have h2 : ((lpBoundedMulCLM (p := 2) (μ := (volume : Measure E)) hφ hC0 hC
        (kgBallFun 0 ((n : ℝ) + 1)) : Lp ℂ 2 (volume : Measure E)) : E → ℂ)
        =ᵐ[volume] fun _ => (0 : ℂ) := by
      rw [happ]
      exact Lp.coeFn_zero ℂ 2 volume
    have h3 := kgBallFun_coeFn (0 : E) ((n : ℝ) + 1)
    filter_upwards [h1, h2, h3] with x hx1 hx2 hx3 hmem
    have hone : (kgBallFun (0 : E) ((n : ℝ) + 1) : E → ℂ) x = 1 := by
      rw [hx3, Set.indicator_of_mem hmem]
    have hzx : (0 : ℂ) = φ x * (kgBallFun (0 : E) ((n : ℝ) + 1) : E → ℂ) x := by
      rw [← hx1, hx2]
    rw [hone, mul_one] at hzx
    exact hzx.symm
  have hall : ∀ᵐ x ∂(volume : Measure E), ∀ n : ℕ,
      x ∈ ball (0 : E) ((n : ℝ) + 1) → φ x = 0 := ae_all_iff.mpr hball
  filter_upwards [hall] with x hx
  obtain ⟨n, hn⟩ := exists_nat_gt ‖x‖
  refine hx n ?_
  rw [mem_ball, dist_zero_right]
  linarith

section Potential

variable {V₁ V₂ : E → ℝ} {b : ℝ}

/-- **A bounded real potential is determined by its multiplication operator.** -/
theorem kgMulOp_injective (hV₁ : Measurable V₁) (hV₂ : Measurable V₂) (hb0 : 0 ≤ b)
    (hb₁ : ∀ a : E, |V₁ a| ≤ b) (hb₂ : ∀ a : E, |V₂ a| ≤ b)
    (heq : kgMulOp hV₁ hb0 hb₁ = kgMulOp hV₂ hb0 hb₂) :
    V₁ =ᵐ[(volume : Measure E)] V₂ := by
  have hmeas : Measurable fun a : E => ((V₁ a - V₂ a : ℝ) : ℂ) :=
    Complex.continuous_ofReal.measurable.comp (hV₁.sub hV₂)
  have hbd : ∀ a : E, ‖((V₁ a - V₂ a : ℝ) : ℂ)‖ ≤ b + b := by
    intro a
    rw [Complex.norm_real, Real.norm_eq_abs]
    have h1 := hb₁ a
    have h2 := hb₂ a
    have h3 := abs_sub (V₁ a) (V₂ a)
    calc |V₁ a - V₂ a| ≤ |V₁ a| + |V₂ a| := abs_sub _ _
      _ ≤ b + b := by linarith
  have hb0' : (0 : ℝ) ≤ b + b := by linarith
  have hsub : lpBoundedMulCLM (p := 2) (μ := (volume : Measure E)) hmeas hb0' hbd
      = kgMulOp hV₁ hb0 hb₁ - kgMulOp hV₂ hb0 hb₂ := by
    rw [kgMulOp, kgMulOp]
    refine lpBoundedMulCLM_sub (measurable_ofReal_potential hV₁) (measurable_ofReal_potential hV₂)
      hmeas hb0 (norm_ofReal_potential_le hb₁) hb0 (norm_ofReal_potential_le hb₂) hb0' hbd ?_
    refine Filter.Eventually.of_forall fun a => ?_
    push_cast
    ring
  have hzero : lpBoundedMulCLM (p := 2) (μ := (volume : Measure E)) hmeas hb0' hbd = 0 := by
    rw [hsub, heq, sub_self]
  have hae := ae_eq_zero_of_lpBoundedMulCLM_eq_zero hmeas hb0' hbd hzero
  filter_upwards [hae] with a ha
  have hreal : V₁ a - V₂ a = 0 := by
    have := congrArg Complex.re ha
    simpa using this
  linarith

/-- **A static bounded real potential is determined almost everywhere by short-time clock
observations at every cut-off.** -/
theorem potential_ae_eq_of_exact_observation (hV₁ : Measurable V₁) (hV₂ : Measurable V₂)
    (hb0 : 0 ≤ b) (hb₁ : ∀ a : E, |V₁ a| ≤ b) (hb₂ : ∀ a : E, |V₂ a| ≤ b) {T : ℝ} (hT0 : 0 < T)
    (hobs : ∀ (R s : ℝ) (g k : Lp ℂ 2 (volume : Measure E)) (t : ℝ), |t| ≤ T →
      kgFieldMildT (fun r : ℝ => kgBandOpT (fun _ : ℝ => kgMulOp hV₁ hb0 hb₁) R (r + s)) g k t
        = kgFieldMildT (fun r : ℝ => kgBandOpT (fun _ : ℝ => kgMulOp hV₂ hb0 hb₂) R (r + s))
            g k t) :
    V₁ =ᵐ[(volume : Measure E)] V₂ := by
  have hWb₁ : ∀ r : ℝ, ‖(fun _ : ℝ => kgMulOp hV₁ hb0 hb₁) r‖ ≤ b := fun _ =>
    norm_kgMulOp_le hV₁ hb0 hb₁
  have hWb₂ : ∀ r : ℝ, ‖(fun _ : ℝ => kgMulOp hV₂ hb0 hb₂) r‖ ≤ b := fun _ =>
    norm_kgMulOp_le hV₂ hb0 hb₂
  have hWs₁ : ∀ y : Lp ℂ 2 (volume : Measure E),
      Continuous fun r : ℝ => (fun _ : ℝ => kgMulOp hV₁ hb0 hb₁) r y := fun _ => continuous_const
  have hWs₂ : ∀ y : Lp ℂ 2 (volume : Measure E),
      Continuous fun r : ℝ => (fun _ : ℝ => kgMulOp hV₂ hb0 hb₂) r y := fun _ => continuous_const
  have hLip : ∀ σ τ : ℝ,
      ‖((fun _ : ℝ => kgMulOp hV₁ hb0 hb₁) σ - (fun _ : ℝ => kgMulOp hV₂ hb0 hb₂) σ)
          - ((fun _ : ℝ => kgMulOp hV₁ hb0 hb₁) τ - (fun _ : ℝ => kgMulOp hV₂ hb0 hb₂) τ)‖
        ≤ 0 * |σ - τ| := by
    intro σ τ
    rw [sub_self, norm_zero, zero_mul]
  have hfun := eq_of_exact_observation_all_bands hb0 hWb₁ hWs₁ hWb₂ hWs₂ le_rfl hLip hT0 hobs
  exact kgMulOp_injective hV₁ hV₂ hb0 hb₁ hb₂ (congrFun hfun 0)

end Potential

end GaloisForLFunctions.HTGeometry
