/-
# Analytic continuation of the Böttcher coordinate along basin paths

The multivalued Böttcher coordinate `φ_c` on the basin is determined locally, up to a constant
factor, by `d log φ_c = ω`: its local branches are the holomorphic `g` with `g' = ω·g`, and `φ_c`
itself is one of them on the escape region.  A *continuation* along a `C¹` path `γ` in the basin is
a function `F` of the path parameter that near every parameter agrees with `g ∘ γ` for such a local
branch `g`.

* **Monodromy formula.**  `F(b) = exp(∫_a^b ω(γ)γ')·F(a)`: `F·exp(−∫ω(γ)γ')` has zero derivative.
* **Existence.**  From every initial value there is a continuation: `F = F₀·exp(∫_a^θ ω(γ)γ')`
  agrees locally with `F₀·exp(Φ)` for a primitive `Φ` of `ω` on a ball.

For a basin loop the continuation multiplier is therefore `exp ∮ω`, and for `c ∉ M` the scalar
monodromy image of the continuation of `φ_c` is exactly the Prüfer group `μ_{2^∞}`.
-/
import GaloisForLFunctions.Bottcher.BottcherLogPeriods

open Complex Set Filter Topology

namespace Bottcher

noncomputable section

/-- `F` continues a local branch of `φ_c` (a local solution of `g' = ω·g`) along the path `γ` over
the parameter interval `[a, b]`. -/
def IsBasinContinuation (c : ℂ) (γ : ℝ → ℂ) (a b : ℝ) (F : ℝ → ℂ) : Prop :=
  ∀ θ₀ ∈ Icc a b, ∃ U : Set ℂ, IsOpen U ∧ γ θ₀ ∈ U ∧ U ⊆ (filledJulia c)ᶜ ∧
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g U ∧ (∀ z ∈ U, deriv g z = greenLogDeriv c z * g z) ∧
      ∀ᶠ θ in 𝓝[Icc a b] θ₀, F θ = g (γ θ)

/-- **`φ_c` is a local branch on the escape region.** -/
theorem deriv_bottcherCoord_eq_greenLogDeriv_mul {c z : ℂ} (hz : z ∈ escapeOpen c) :
    deriv (bottcherCoord c) z = greenLogDeriv c z * bottcherCoord c z := by
  rw [greenLogDeriv_eq_logDeriv_bottcherCoord hz, logDeriv_apply,
    div_mul_cancel₀ _ (bottcherCoord_ne_zero c z)]

section Path

variable {c : ℂ} {γ : ℝ → ℂ}

/-- The integrand `ω(γ)·γ'` along a `C¹` basin path. -/
theorem continuous_greenLogDeriv_path (hγ : ContDiff ℝ 1 γ)
    (hmem : ∀ θ, γ θ ∉ filledJulia c) :
    Continuous fun θ => greenLogDeriv c (γ θ) * deriv γ θ :=
  ((differentiableOn_greenLogDeriv c).continuousOn.comp_continuous hγ.continuous hmem).mul
    (hγ.continuous_deriv le_rfl)

theorem hasDerivAt_greenLogDeriv_integral (hγ : ContDiff ℝ 1 γ)
    (hmem : ∀ θ, γ θ ∉ filledJulia c) (a θ : ℝ) :
    HasDerivAt (fun u => ∫ s in a..u, greenLogDeriv c (γ s) * deriv γ s)
      (greenLogDeriv c (γ θ) * deriv γ θ) θ :=
  ((continuous_greenLogDeriv_path hγ hmem).integral_hasStrictDerivAt a θ).hasDerivAt

/-- **Monodromy formula for continuations.** -/
theorem IsBasinContinuation.eq_exp_integral_mul {a b : ℝ} {F : ℝ → ℂ}
    (hγ : ContDiff ℝ 1 γ) (hmem : ∀ θ, γ θ ∉ filledJulia c) (hab : a ≤ b)
    (hF : IsBasinContinuation c γ a b F) :
    F b = Complex.exp (∫ s in a..b, greenLogDeriv c (γ s) * deriv γ s) * F a := by
  set E : ℝ → ℂ := fun u => ∫ s in a..u, greenLogDeriv c (γ s) * deriv γ s with hEdef
  set H : ℝ → ℂ := fun θ => F θ * Complex.exp (-E θ) with hHdef
  have hH : ∀ θ ∈ Icc a b, HasDerivWithinAt H 0 (Icc a b) θ := by
    intro θ hθ
    obtain ⟨U, hUo, hθU, -, g, hgd, hgω, hFg⟩ := hF θ hθ
    have hgda : DifferentiableAt ℂ g (γ θ) := hgd.differentiableAt (hUo.mem_nhds hθU)
    have hgγ : HasDerivAt (fun t => g (γ t))
        (greenLogDeriv c (γ θ) * g (γ θ) * deriv γ θ) θ := by
      have h := hgda.hasDerivAt.comp θ ((hγ.differentiable one_ne_zero θ).hasDerivAt)
      rwa [hgω (γ θ) hθU] at h
    have hFθ : F θ = g (γ θ) := hFg.self_of_nhdsWithin hθ
    have hFd : HasDerivWithinAt F (greenLogDeriv c (γ θ) * g (γ θ) * deriv γ θ) (Icc a b) θ :=
      hgγ.hasDerivWithinAt.congr_of_eventuallyEq hFg hFθ
    have hEd := hasDerivAt_greenLogDeriv_integral hγ hmem a θ
    have hexp := (hEd.neg.cexp).hasDerivWithinAt (s := Icc a b)
    have hprod : HasDerivWithinAt H
        (greenLogDeriv c (γ θ) * g (γ θ) * deriv γ θ * Complex.exp (-E θ) +
          F θ * (Complex.exp (-E θ) * -(greenLogDeriv c (γ θ) * deriv γ θ))) (Icc a b) θ :=
      hFd.mul hexp
    refine hprod.congr_deriv ?_
    rw [hFθ]
    ring
  rcases eq_or_lt_of_le hab with heq | hlt
  · subst heq
    simp
  have hconst := constant_of_derivWithin_zero (f := H)
    (fun θ hθ => (hH θ hθ).differentiableWithinAt)
    (fun θ hθ => (hH θ (Ico_subset_Icc_self hθ)).derivWithin
      (uniqueDiffOn_Icc hlt θ (Ico_subset_Icc_self hθ)))
    b ⟨hab, le_rfl⟩
  simp only [hHdef, hEdef, intervalIntegral.integral_same, neg_zero, Complex.exp_zero,
    mul_one] at hconst
  rw [← hconst, mul_comm (Complex.exp _), mul_assoc, ← Complex.exp_add, neg_add_cancel,
    Complex.exp_zero, mul_one]

/-- **Existence of continuations** from every initial value. -/
theorem exists_isBasinContinuation (hγ : ContDiff ℝ 1 γ) (hmem : ∀ θ, γ θ ∉ filledJulia c)
    (a b : ℝ) (F₀ : ℂ) :
    ∃ F : ℝ → ℂ, IsBasinContinuation c γ a b F ∧ F a = F₀ := by
  set E : ℝ → ℂ := fun u => ∫ s in a..u, greenLogDeriv c (γ s) * deriv γ s with hEdef
  refine ⟨fun θ => F₀ * Complex.exp (E θ), fun θ₀ _ => ?_, by simp [hEdef]⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp (isClosed_filledJulia c).isOpen_compl (γ θ₀)
    (hmem θ₀)
  set U := Metric.ball (γ θ₀) r
  obtain ⟨Φ, hΦ0, hΦ⟩ := ((differentiableOn_greenLogDeriv c).mono hball).isExactOn_ball
    |>.with_val_at (γ θ₀) (E θ₀)
  refine ⟨U, Metric.isOpen_ball, Metric.mem_ball_self hr, hball,
    fun z => F₀ * Complex.exp (Φ z), ?_, ?_, ?_⟩
  · exact fun z hz => ((hΦ z hz).differentiableAt.cexp.const_mul F₀).differentiableWithinAt
  · intro z hz
    rw [((hΦ z hz).cexp.const_mul F₀).deriv]
    beta_reduce
    ring
  · -- `E − Φ ∘ γ` is constant near `θ₀`
    have hpre : IsOpen (γ ⁻¹' U) := Metric.isOpen_ball.preimage hγ.continuous
    obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.mp hpre θ₀ (Metric.mem_ball_self hr)
    set D : ℝ → ℂ := fun θ => E θ - Φ (γ θ) with hDdef
    have hDd : ∀ θ ∈ Metric.ball θ₀ ε, HasDerivAt D 0 θ := by
      intro θ hθ
      have hγU : γ θ ∈ U := hεsub hθ
      have h1 := hasDerivAt_greenLogDeriv_integral hγ hmem a θ
      have h2 := (hΦ (γ θ) hγU).comp θ ((hγ.differentiable one_ne_zero θ).hasDerivAt)
      have h3 : HasDerivAt D (greenLogDeriv c (γ θ) * deriv γ θ -
          greenLogDeriv c (γ θ) * deriv γ θ) θ := h1.sub h2
      rwa [sub_self] at h3
    have hconst : ∀ x ∈ Metric.ball θ₀ ε, ∀ y ∈ Metric.ball θ₀ ε, D x = D y :=
      fun x hx y hy => (Metric.isOpen_ball).is_const_of_deriv_eq_zero
        (convex_ball θ₀ ε).isPreconnected
        (fun θ hθ => (hDd θ hθ).differentiableAt.differentiableWithinAt)
        (fun θ hθ => (hDd θ hθ).deriv) hx hy
    filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds θ₀ hε)] with θ hθ
    have hDθ := hconst θ hθ θ₀ (Metric.mem_ball_self hε)
    simp only [hDdef, hΦ0, sub_self] at hDθ
    rw [sub_eq_zero] at hDθ
    show F₀ * Complex.exp (E θ) = F₀ * Complex.exp (Φ (γ θ))
    rw [hDθ]

end Path

/-! ### Loops -/

/-- **The continuation multiplier around a basin loop is `exp ∮ω`.** -/
theorem BasinLoop.continuation_multiplier {c : ℂ} (ℓ : BasinLoop c) {F : ℝ → ℂ}
    (hF : IsBasinContinuation c ℓ.γ 0 (2 * Real.pi) F) :
    F (2 * Real.pi) = Complex.exp ℓ.period * F 0 :=
  hF.eq_exp_integral_mul ℓ.smooth ℓ.mem (by positivity)

/-- **Dyadic continuation loops.**  For `c ∉ M` and every `n` there is a basin loop along which a
branch of `φ_c` continues from every initial value, and every continuation is multiplied by the
primitive `2ⁿ`-th root of unity `exp(2πi/2ⁿ)`. -/
theorem exists_basinLoop_continuation_mul_dyadicRoot {c : ℂ} (hc : Disconnected c) (n : ℕ) :
    ∃ ℓ : BasinLoop c,
      (∀ F₀ : ℂ, ∃ F : ℝ → ℂ, IsBasinContinuation c ℓ.γ 0 (2 * Real.pi) F ∧ F 0 = F₀) ∧
      ∀ F : ℝ → ℂ, IsBasinContinuation c ℓ.γ 0 (2 * Real.pi) F →
        F (2 * Real.pi) = Complex.exp (2 * Real.pi * Complex.I / 2 ^ n) * F 0 := by
  obtain ⟨ℓ, hℓ⟩ := exists_basinLoop_exp_period_eq_dyadicRoot hc n
  exact ⟨ℓ, exists_isBasinContinuation ℓ.smooth ℓ.mem 0 (2 * Real.pi),
    fun F hF => by rw [ℓ.continuation_multiplier hF, hℓ]⟩

/-- **Exact Prüfer monodromy.**  For `c ∉ M`, the scalar monodromy image of analytic continuation of
the Böttcher coordinate around basin loops is exactly the group of dyadic roots of unity. -/
theorem basin_monodromy_image_eq_dyadicRootsOfUnity {c : ℂ} (hc : Disconnected c) :
    {μ : ℂ | ∃ (ℓ : BasinLoop c) (F : ℝ → ℂ), IsBasinContinuation c ℓ.γ 0 (2 * Real.pi) F ∧
      F 0 ≠ 0 ∧ F (2 * Real.pi) = μ * F 0} = dyadicRootsOfUnity := by
  ext μ
  constructor
  · rintro ⟨ℓ, F, hF, hF0, hμ⟩
    rw [ℓ.continuation_multiplier hF] at hμ
    have hμ' : μ = Complex.exp ℓ.period := (mul_right_cancel₀ hF0 hμ).symm
    rw [hμ']
    exact (exists_basinLoop_exp_period_iff hc _).mp ⟨ℓ, rfl⟩
  · intro hμ
    obtain ⟨ℓ, hℓ⟩ := (exists_basinLoop_exp_period_iff hc μ).mpr hμ
    obtain ⟨F, hF, hF0⟩ := exists_isBasinContinuation (c := c) ℓ.smooth ℓ.mem 0 (2 * Real.pi) 1
    refine ⟨ℓ, F, hF, by rw [hF0]; exact one_ne_zero, ?_⟩
    rw [ℓ.continuation_multiplier hF, hℓ]

end

end Bottcher
