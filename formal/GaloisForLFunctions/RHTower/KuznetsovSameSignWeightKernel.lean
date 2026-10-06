import GaloisForLFunctions.RHTower.KuznetsovSameSignGaussKernel

/-!
# The same-sign kernel integrated against a general weight

A *same-sign weight* is a pair `(h, G)`: an integrable continuous `h` on the spectral line and a
`C¹` function `G` with `∫ h(t) e^{2itw} dt = G'(w)` and `|G(w)| e^{|w|}` integrable.  For `σ > 1`
and `X > 0`,

`∫ h(t) Ξ_σ(t, X) dt = Ψ_σ^G(X) = ∫ (1+ξ²)^{−σ} ∫ G(w) X ζ(ξ) sinh w e^{−X ζ(ξ) cosh w} dw dξ`

(`integral_weight_mul_sameSignKernel`): Fubini over `(t, ξ, w)`, the defining identity of `G'`
and one integration by parts in `w`.  The right side is defined for every `σ ≥ 1`, satisfies
`|Ψ_σ^G(X)| ≤ π X ∫ |G sinh|` (`norm_weightKernel_le`), is continuous as `σ ↓ 1`
(`tendsto_weightKernel`), and at `σ = 1`

`Ψ_1^G(X) = 2 ∫ G(w) tanh w sin(X cosh w) dw`

(`weightKernel_one`).
-/

open MeasureTheory Set Filter Topology Complex

namespace GaloisForLFunctions.RHTower.DeckPointPair

noncomputable section

/-- A weight for the same-sign Kuznetsov identity: `∫ h(t) e^{2itw} dt = G'(w)`, `|G| e^{|w|}`
integrable. -/
structure SameSignWeight where
  /-- The weight on the spectral line. -/
  h : ℝ → ℂ
  /-- The primitive of the Fourier transform of `h`. -/
  G : ℝ → ℂ
  /-- The derivative of `G`. -/
  dG : ℝ → ℂ
  continuous_h : Continuous h
  integrable_h : Integrable h
  hasDerivAt_G : ∀ w, HasDerivAt G (dG w) w
  continuous_dG : Continuous dG
  integrable_dG : Integrable dG
  integrable_G_exp : Integrable fun w => ‖G w‖ * Real.exp |w|
  fourier_h : ∀ w : ℝ, ∫ t : ℝ, h t * cexp (2 * t * w * Complex.I) = dG w

namespace SameSignWeight

variable (W : SameSignWeight)

theorem continuous_G : Continuous W.G :=
  continuous_iff_continuousAt.2 fun w => (W.hasDerivAt_G w).continuousAt

theorem integrable_G : Integrable W.G := by
  refine W.integrable_G_exp.mono' W.continuous_G.aestronglyMeasurable
    (Eventually.of_forall fun w => ?_)
  exact le_mul_of_one_le_right (norm_nonneg _) (Real.one_le_exp (abs_nonneg w))

theorem integrable_G_mul_sinh : Integrable fun w => W.G w * Real.sinh w := by
  refine W.integrable_G_exp.mono' (W.continuous_G.mul (by fun_prop)).aestronglyMeasurable
    (Eventually.of_forall fun w => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (abs_sinh_le_exp_abs w) (norm_nonneg _)

end SameSignWeight

variable (W : SameSignWeight)

/-! ## The kernel `Ψ_σ^G` -/

/-- The inner integral `∫ G(w) X ζ(ξ) sinh w e^{−X ζ(ξ) cosh w} dw`. -/
def weightInner (X ξ : ℝ) : ℂ :=
  ∫ w : ℝ, W.G w * ((X : ℂ) * cayleyUnit ξ * Real.sinh w) * cexp (-(X * cayleyUnit ξ * Real.cosh w))

/-- `Ψ_σ^G(X) = ∫ (1+ξ²)^{−σ} ∫ G(w) X ζ(ξ) sinh w e^{−X ζ(ξ) cosh w} dw dξ`. -/
def weightKernel (σ X : ℝ) : ℂ :=
  ∫ ξ : ℝ, (((1 + ξ ^ 2) ^ (-σ) : ℝ) : ℂ) * weightInner W X ξ

/-- `C_G = ∫ |G(w) sinh w| dw`. -/
def weightSinhMass : ℝ := ∫ w : ℝ, ‖W.G w * Real.sinh w‖

theorem weightSinhMass_nonneg : 0 ≤ weightSinhMass W := integral_nonneg fun _ => norm_nonneg _

theorem norm_weightInner_integrand_le {X : ℝ} (hX : 0 ≤ X) (ξ w : ℝ) :
    ‖W.G w * ((X : ℂ) * cayleyUnit ξ * Real.sinh w) * cexp (-(X * cayleyUnit ξ * Real.cosh w))‖ ≤
      X * ‖W.G w * Real.sinh w‖ := by
  rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_cayleyUnit, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hX, norm_mul, Complex.norm_real,
    Real.norm_eq_abs]
  have := norm_cexp_neg_cayley_le hX ξ w
  calc ‖W.G w‖ * (X * 1 * |Real.sinh w|) * ‖cexp (-(X * cayleyUnit ξ * Real.cosh w))‖
      ≤ ‖W.G w‖ * (X * 1 * |Real.sinh w|) * 1 := mul_le_mul_of_nonneg_left this (by positivity)
    _ = X * (‖W.G w‖ * |Real.sinh w|) := by ring

theorem continuous_weightInner_integrand (X : ℝ) :
    Continuous fun p : ℝ × ℝ => W.G p.2 * ((X : ℂ) * cayleyUnit p.1 * Real.sinh p.2) *
      cexp (-(X * cayleyUnit p.1 * Real.cosh p.2)) := by
  have hS : Continuous fun p : ℝ × ℝ => (X : ℂ) * cayleyUnit p.1 * Real.sinh p.2 :=
    (continuous_const.mul (continuous_cayleyUnit.comp continuous_fst)).mul
      (Complex.continuous_ofReal.comp (Real.continuous_sinh.comp continuous_snd))
  exact ((W.continuous_G.comp continuous_snd).mul hS).mul (continuous_cexp_neg_cayley X)

theorem integrable_weightInner_integrand {X : ℝ} (hX : 0 ≤ X) (ξ : ℝ) :
    Integrable (fun w : ℝ => W.G w * ((X : ℂ) * cayleyUnit ξ * Real.sinh w) *
      cexp (-(X * cayleyUnit ξ * Real.cosh w))) := by
  refine (W.integrable_G_mul_sinh.norm.const_mul X).mono'
    ((continuous_weightInner_integrand W X).comp (continuous_const.prodMk continuous_id)
      |>.aestronglyMeasurable) (Eventually.of_forall fun w => ?_)
  exact norm_weightInner_integrand_le W hX ξ w

theorem norm_weightInner_le {X : ℝ} (hX : 0 ≤ X) (ξ : ℝ) :
    ‖weightInner W X ξ‖ ≤ X * weightSinhMass W := by
  rw [weightInner, weightSinhMass, ← integral_const_mul]
  exact (norm_integral_le_integral_norm _).trans (integral_mono_of_nonneg
    (Eventually.of_forall fun w => norm_nonneg _)
    (W.integrable_G_mul_sinh.norm.const_mul X)
    (Eventually.of_forall fun w => norm_weightInner_integrand_le W hX ξ w))

/-- **Integration by parts in `w`**: `∫ G'(w) e^{−Xζ cosh w} dw = ∫ G(w) Xζ sinh w e^{−Xζ cosh w} dw`. -/
theorem integral_dG_mul_cexp {X : ℝ} (hX : 0 ≤ X) (ξ : ℝ) :
    ∫ w : ℝ, W.dG w * cexp (-(X * cayleyUnit ξ * Real.cosh w)) = weightInner W X ξ := by
  have hv : ∀ w : ℝ, HasDerivAt (fun w : ℝ => cexp (-(X * cayleyUnit ξ * Real.cosh w)))
      (cexp (-(X * cayleyUnit ξ * Real.cosh w)) * (-((X : ℂ) * cayleyUnit ξ * Real.sinh w))) w :=
    fun w => (((Real.hasDerivAt_cosh w).ofReal_comp.const_mul ((X : ℂ) * cayleyUnit ξ)).neg).cexp
  have hE : Continuous fun w : ℝ => cexp (-(X * cayleyUnit ξ * Real.cosh w)) := by fun_prop
  have huv' : Integrable (fun w : ℝ => W.G w * (cexp (-(X * cayleyUnit ξ * Real.cosh w)) *
      (-((X : ℂ) * cayleyUnit ξ * Real.sinh w)))) := by
    refine (integrable_weightInner_integrand W hX ξ).neg.congr (Eventually.of_forall fun w => ?_)
    simp only [Pi.neg_apply]
    ring
  have hu'v : Integrable (fun w : ℝ => W.dG w * cexp (-(X * cayleyUnit ξ * Real.cosh w))) := by
    refine W.integrable_dG.norm.mono' (W.continuous_dG.mul hE).aestronglyMeasurable
      (Eventually.of_forall fun w => ?_)
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (norm_cexp_neg_cayley_le hX ξ w)
  have huv : Integrable (fun w : ℝ => W.G w * cexp (-(X * cayleyUnit ξ * Real.cosh w))) := by
    refine W.integrable_G.norm.mono' (W.continuous_G.mul hE).aestronglyMeasurable
      (Eventually.of_forall fun w => ?_)
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (norm_cexp_neg_cayley_le hX ξ w)
  have h := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := W.G) (u' := W.dG)
    (v := fun w : ℝ => cexp (-(X * cayleyUnit ξ * Real.cosh w)))
    (v' := fun w : ℝ => cexp (-(X * cayleyUnit ξ * Real.cosh w)) *
      (-((X : ℂ) * cayleyUnit ξ * Real.sinh w)))
    (fun w _ => W.hasDerivAt_G w) (fun w _ => hv w) huv' hu'v huv
  rw [weightInner]
  have h1 : ∫ w : ℝ, W.G w * (cexp (-(X * cayleyUnit ξ * Real.cosh w)) *
      (-((X : ℂ) * cayleyUnit ξ * Real.sinh w))) =
      -∫ w : ℝ, W.G w * ((X : ℂ) * cayleyUnit ξ * Real.sinh w) *
        cexp (-(X * cayleyUnit ξ * Real.cosh w)) := by
    rw [← integral_neg]; congr 1; funext w; ring
  rw [h1, neg_inj] at h
  exact h.symm

/-! ## Fubini over `(t, ξ, w)` -/

/-- **The kernel integrated against the weight**: `∫ h(t) Ξ_σ(t, X) dt = Ψ_σ^G(X)`. -/
theorem integral_weight_mul_sameSignKernel {σ X : ℝ} (hσ : 1 < σ) (hX : 0 < X) :
    ∫ t : ℝ, W.h t * sameSignKernel σ t X = weightKernel W σ X := by
  set c : ℝ → ℂ := fun ξ => (((1 + ξ ^ 2) ^ (-σ) : ℝ) : ℂ) with hc
  set E : ℝ × ℝ → ℂ := fun p => cexp (-(X * cayleyUnit p.1 * Real.cosh p.2)) with hE
  set Φ : ℝ → ℝ × ℝ → ℂ := fun t p => c p.1 * (cexp (2 * t * p.2 * Complex.I) * E p) with hΦdef
  set M : ℝ × ℝ → ℝ := fun p => (1 + p.1 ^ 2) ^ (-(σ - 1 / 2)) * (4 / X * (1 + p.2 ^ 2)⁻¹)
  have hMint : Integrable M (volume : Measure (ℝ × ℝ)) := by
    rw [Measure.volume_eq_prod]
    exact (Kuznetsov.integrable_one_add_sq_rpow (τ := σ - 1 / 2) (by linarith)).mul_prod
      (integrable_inv_one_add_sq.const_mul (4 / X))
  have hcont_c := continuous_one_add_sq_rpow σ
  have hcont_E := continuous_cexp_neg_cayley X
  have hnormΦ : ∀ t p, ‖Φ t p‖ ≤ M p := fun t p => by
    simp only [hΦdef, hc, hE, M]
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity),
      show (2 * (t : ℂ) * p.2 * Complex.I) = ((2 * t * p.2 : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, one_mul]
    exact rpow_mul_norm_cexp_neg_cayley_le hX p.1 p.2
  have hΦint : ∀ t, Integrable (Φ t) (volume : Measure (ℝ × ℝ)) := fun t =>
    hMint.mono' (by
      refine Continuous.aestronglyMeasurable ?_
      simp only [hΦdef]
      exact (hcont_c.comp continuous_fst).mul
        ((by fun_prop : Continuous fun p : ℝ × ℝ => cexp (2 * (t : ℂ) * p.2 * Complex.I)).mul
          hcont_E))
      (Eventually.of_forall (hnormΦ t))
  have hkern : ∀ t : ℝ, sameSignKernel σ t X = ∫ p, Φ t p := fun t => by
    have h := hΦint t
    rw [Measure.volume_eq_prod] at h ⊢
    rw [integral_prod _ h, sameSignKernel]
    congr 1; funext ξ
    rw [← integral_const_mul]
  simp_rw [hkern, ← integral_const_mul]
  have hint : Integrable (Function.uncurry fun (t : ℝ) (p : ℝ × ℝ) => W.h t * Φ t p)
      ((volume : Measure ℝ).prod (volume : Measure (ℝ × ℝ))) := by
    refine (W.integrable_h.norm.mul_prod hMint).mono' ?_ (Eventually.of_forall fun z => ?_)
    · refine Continuous.aestronglyMeasurable ?_
      simp only [hΦdef]
      exact (W.continuous_h.comp continuous_fst).mul
        ((hcont_c.comp (continuous_fst.comp continuous_snd)).mul
          ((by fun_prop : Continuous fun z : ℝ × (ℝ × ℝ) => cexp (2 * z.1 * z.2.2 * Complex.I)).mul
            (hcont_E.comp continuous_snd)))
    · simp only [Function.uncurry]
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hnormΦ z.1 z.2) (norm_nonneg _)
  rw [integral_integral_swap hint]
  have hinner : ∀ p : ℝ × ℝ, ∫ t : ℝ, W.h t * Φ t p = c p.1 * E p * W.dG p.2 := fun p => by
    have hpt : ∀ t : ℝ, W.h t * Φ t p =
        c p.1 * E p * (W.h t * cexp (2 * t * p.2 * Complex.I)) := fun t => by
      simp only [hΦdef]; ring
    simp_rw [hpt]
    rw [integral_const_mul, W.fourier_h]
  simp_rw [hinner]
  have hint2 : Integrable (fun p : ℝ × ℝ => c p.1 * E p * W.dG p.2)
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
    refine ((Kuznetsov.integrable_one_add_sq_rpow (τ := σ) (by linarith)).mul_prod
      W.integrable_dG.norm).mono' ?_ (Eventually.of_forall fun p => ?_)
    · exact (((hcont_c.comp continuous_fst).mul hcont_E).mul
        (W.continuous_dG.comp continuous_snd)).aestronglyMeasurable
    · simp only [hc, hE]
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      have := norm_cexp_neg_cayley_le hX.le p.1 p.2
      calc (1 + p.1 ^ 2) ^ (-σ) * ‖cexp (-(X * cayleyUnit p.1 * Real.cosh p.2))‖ * ‖W.dG p.2‖
          ≤ (1 + p.1 ^ 2) ^ (-σ) * 1 * ‖W.dG p.2‖ := by gcongr
        _ = _ := by ring
  rw [Measure.volume_eq_prod, integral_prod _ hint2, weightKernel]
  congr 1; funext ξ
  rw [← integral_dG_mul_cexp W hX.le ξ, ← integral_const_mul]
  congr 1; funext w
  simp only [hc, hE]
  ring

/-! ## Bounds and the limit `σ ↓ 1` -/

theorem aestronglyMeasurable_weightInner (X : ℝ) :
    AEStronglyMeasurable (weightInner W X) volume :=
  ((continuous_weightInner_integrand W X).stronglyMeasurable.integral_prod_right'
    (ν := (volume : Measure ℝ))).aestronglyMeasurable

theorem norm_weightKernel_integrand_le {σ X : ℝ} (hσ : 1 ≤ σ) (hX : 0 ≤ X) (ξ : ℝ) :
    ‖(((1 + ξ ^ 2) ^ (-σ) : ℝ) : ℂ) * weightInner W X ξ‖ ≤
      (1 + ξ ^ 2)⁻¹ * (X * weightSinhMass W) := by
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  exact mul_le_mul (one_add_sq_rpow_le_inv hσ ξ) (norm_weightInner_le W hX ξ) (norm_nonneg _)
    (by positivity)

/-- **`|Ψ_σ^G(X)| ≤ π X C_G`** for `σ ≥ 1`. -/
theorem norm_weightKernel_le {σ X : ℝ} (hσ : 1 ≤ σ) (hX : 0 ≤ X) :
    ‖weightKernel W σ X‖ ≤ Real.pi * X * weightSinhMass W := by
  rw [weightKernel]
  refine (norm_integral_le_of_norm_le (integrable_inv_one_add_sq.mul_const _)
    (Eventually.of_forall fun ξ => norm_weightKernel_integrand_le W hσ hX ξ)).trans (le_of_eq ?_)
  rw [integral_mul_const, integral_univ_inv_one_add_sq]
  ring

/-- **Continuity as `σ ↓ 1`.** -/
theorem tendsto_weightKernel {X : ℝ} (hX : 0 ≤ X) :
    Tendsto (fun σ => weightKernel W σ X) (𝓝[>] 1) (𝓝 (weightKernel W 1 X)) := by
  unfold weightKernel
  refine tendsto_integral_filter_of_dominated_convergence
    (fun ξ => (1 + ξ ^ 2)⁻¹ * (X * weightSinhMass W)) ?_ ?_
    (integrable_inv_one_add_sq.mul_const _) ?_
  · exact Eventually.of_forall fun σ =>
      ((continuous_one_add_sq_rpow σ).aestronglyMeasurable).mul (aestronglyMeasurable_weightInner W X)
  · filter_upwards [self_mem_nhdsWithin] with σ (hσ : 1 < σ)
    exact Eventually.of_forall fun ξ => norm_weightKernel_integrand_le W hσ.le hX ξ
  · refine Eventually.of_forall fun ξ => ?_
    have hξ : (0 : ℝ) < 1 + ξ ^ 2 := by positivity
    have h : Tendsto (fun σ : ℝ => (1 + ξ ^ 2) ^ (-σ)) (𝓝 1) (𝓝 ((1 + ξ ^ 2) ^ (-(1 : ℝ)))) :=
      ((Real.continuousAt_const_rpow hξ.ne').comp continuous_neg.continuousAt).tendsto
    exact ((Complex.continuous_ofReal.tendsto _).comp (h.mono_left nhdsWithin_le_nhds)).mul_const _

/-! ## The value at `σ = 1` -/

/-- **`Ψ_1^G(X) = 2 ∫ G(w) tanh w sin(X cosh w) dw`.** -/
theorem weightKernel_one {X : ℝ} (hX : 0 < X) :
    weightKernel W 1 X =
      2 * ∫ w : ℝ, W.G w * ((Real.tanh w * Real.sin (X * Real.cosh w) : ℝ) : ℂ) := by
  set f : ℝ → ℝ → ℂ := fun ξ w => (((1 + ξ ^ 2)⁻¹ : ℝ) : ℂ) *
    (W.G w * ((X : ℂ) * cayleyUnit ξ * Real.sinh w) *
      cexp (-(X * cayleyUnit ξ * Real.cosh w))) with hf
  have hint : Integrable (Function.uncurry f) ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
    refine (integrable_inv_one_add_sq.mul_prod
      (W.integrable_G_mul_sinh.norm.const_mul X)).mono' ?_
      (Eventually.of_forall fun p => ?_)
    · refine Continuous.aestronglyMeasurable ?_
      simp only [hf, Function.uncurry_def]
      exact (Complex.continuous_ofReal.comp ((by fun_prop : Continuous fun p : ℝ × ℝ =>
        1 + p.1 ^ 2).inv₀ fun p => by positivity)).mul (continuous_weightInner_integrand W X)
    · simp only [hf, Function.uncurry_def]
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left (norm_weightInner_integrand_le W hX.le p.1 p.2)
        (by positivity)
  have hkernel : weightKernel W 1 X = ∫ ξ : ℝ, ∫ w : ℝ, f ξ w := by
    rw [weightKernel]
    congr 1; funext ξ
    rw [weightInner, ← integral_const_mul, Real.rpow_neg_one]
  rw [hkernel, integral_integral_swap hint, ← integral_const_mul]
  congr 1; funext w
  have hc := Real.cosh_pos w
  have hpt : ∀ ξ : ℝ, f ξ w = (W.G w * X * Real.sinh w) *
      ((((1 + ξ ^ 2)⁻¹ : ℝ) : ℂ) * cayleyUnit ξ *
        cexp (-(((X * Real.cosh w : ℝ) : ℂ) * cayleyUnit ξ))) := fun ξ => by
    simp only [hf]; push_cast; ring_nf
  simp_rw [hpt]
  rw [integral_const_mul, integral_inv_one_add_sq_mul_cayley (by positivity),
    Real.tanh_eq_sinh_div_cosh]
  have hXc : (X : ℂ) ≠ 0 := by exact_mod_cast hX.ne'
  have hcc : (Real.cosh w : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  push_cast
  field_simp

end

end GaloisForLFunctions.RHTower.DeckPointPair
