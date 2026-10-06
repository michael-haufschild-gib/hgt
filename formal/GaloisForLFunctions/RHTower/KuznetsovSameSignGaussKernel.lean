import GaloisForLFunctions.RHTower.KuznetsovSameSignLine
import GaloisForLFunctions.RHTower.KuznetsovGaussianWeight

/-!
# The same-sign kernel integrated against the Gaussian weight

For `σ > 1`, `X > 0` and `K > 0`,

`∫ t² e^{−(t/K)²} Ξ_σ(t, X) dt = Ψ_σ(X) = ∫ (1+ξ²)^{−σ} ∫ 𝒢_K(w) X ζ(ξ) sinh w e^{−X ζ(ξ) cosh w} dw dξ`

(`integral_gaussWeight_mul_sameSignKernel`): Fubini over `(t, ξ, w)`, the Fourier transform
`∫ t² e^{−(t/K)²} e^{2itw} dt = 𝒢_K'(w)` and one integration by parts in `w`.  The right side is
defined for every `σ ≥ 1`, satisfies `|Ψ_σ(X)| ≤ π X ∫ |𝒢_K sinh|` (`norm_gaussKernel_le`), is
continuous as `σ ↓ 1` (`tendsto_gaussKernel`), and at `σ = 1`

`Ψ_1(X) = 2 ∫ 𝒢_K(w) tanh w sin(X cosh w) dw`

(`gaussKernel_one`), from `∫ (1+ξ²)⁻¹ ζ(ξ) e^{−b ζ(ξ)} dξ = 2 sin b / b`, `ζ(ξ) = e^{i arctan ξ}`.
-/

open MeasureTheory Set Filter Topology Complex

namespace GaloisForLFunctions.RHTower.DeckPointPair

open KuznetsovGauss

noncomputable section

/-! ## Integrability in `w` -/

theorem abs_sinh_le_exp_abs (w : ℝ) : |Real.sinh w| ≤ Real.exp |w| := by
  rw [Real.abs_sinh]
  have h1 := Real.sinh_lt_cosh |w|
  have h2 : Real.cosh |w| ≤ Real.exp |w| := by
    rw [Real.cosh_eq]
    have := Real.exp_le_exp.2 (show -|w| ≤ |w| by linarith [abs_nonneg w])
    linarith
  linarith

theorem cosh_le_exp_abs (w : ℝ) : Real.cosh w ≤ Real.exp |w| := by
  rw [← Real.cosh_abs, Real.cosh_eq]
  have := Real.exp_le_exp.2 (show -|w| ≤ |w| by linarith [abs_nonneg w])
  linarith

theorem integrable_gaussPrim {K : ℝ} (hK : 0 < K) : Integrable (gaussPrim K) := by
  have h := (integrable_mul_exp_neg_mul_sq (b := K ^ 2) (by positivity)).const_mul
    (Real.sqrt Real.pi * K ^ 3 / 2)
  refine h.congr (Eventually.of_forall fun w => ?_)
  simp only [gaussPrim]
  congr 3
  ring

theorem integrable_gaussDeriv {K : ℝ} (hK : 0 < K) : Integrable (gaussDeriv K) := by
  have h := ((integrable_exp_neg_mul_sq (b := K ^ 2) (by positivity)).sub
    ((integrable_pow_mul_exp_neg_sq (a := K ^ 2) (by positivity) 2).const_mul (2 * K ^ 2))).const_mul
    (Real.sqrt Real.pi * K ^ 3 / 2)
  refine h.congr (Eventually.of_forall fun w => ?_)
  simp only [gaussDeriv, Pi.sub_apply]
  have : -(K * w) ^ 2 = -K ^ 2 * w ^ 2 := by ring
  rw [this]
  ring

/-- `|𝒢_K(w)| e^{|w|}` is integrable. -/
theorem integrable_abs_gaussPrim_mul_exp_abs {K : ℝ} (hK : 0 < K) :
    Integrable (fun w => |gaussPrim K w| * Real.exp |w|) := by
  have h := ((integrable_mul_exp_neg_mul_sq (b := K ^ 2 / 2) (by positivity)).norm).const_mul
    (Real.sqrt Real.pi * K ^ 3 / 2 * Real.exp (1 / (2 * K ^ 2)))
  refine h.mono' (by unfold gaussPrim; fun_prop) (Eventually.of_forall fun w => ?_)
  have hK2 : (0 : ℝ) < K ^ 2 := by positivity
  have hq : |w| - K ^ 2 * w ^ 2 ≤ 1 / (2 * K ^ 2) - K ^ 2 / 2 * w ^ 2 := by
    have e : 1 / (2 * K ^ 2) - K ^ 2 / 2 * w ^ 2 - (|w| - K ^ 2 * w ^ 2) =
        (K ^ 2 * |w| - 1) ^ 2 / (2 * K ^ 2) := by
      rw [show w ^ 2 = |w| ^ 2 from (sq_abs w).symm]
      field_simp
      ring
    have : 0 ≤ (K ^ 2 * |w| - 1) ^ 2 / (2 * K ^ 2) := by positivity
    linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), gaussPrim, abs_mul,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ Real.sqrt Real.pi * K ^ 3 / 2), abs_mul,
    abs_of_pos (Real.exp_pos _), norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg (Real.exp_pos _).le]
  have he : Real.exp (-(K * w) ^ 2) * Real.exp |w| ≤
      Real.exp (1 / (2 * K ^ 2)) * Real.exp (-(K ^ 2 / 2) * w ^ 2) := by
    rw [← Real.exp_add, ← Real.exp_add]
    exact Real.exp_le_exp.2 (by nlinarith)
  calc Real.sqrt Real.pi * K ^ 3 / 2 * (|w| * Real.exp (-(K * w) ^ 2)) * Real.exp |w|
      = Real.sqrt Real.pi * K ^ 3 / 2 * |w| * (Real.exp (-(K * w) ^ 2) * Real.exp |w|) := by ring
    _ ≤ Real.sqrt Real.pi * K ^ 3 / 2 * |w| *
        (Real.exp (1 / (2 * K ^ 2)) * Real.exp (-(K ^ 2 / 2) * w ^ 2)) :=
        mul_le_mul_of_nonneg_left he (by positivity)
    _ = _ := by ring

theorem integrable_gaussPrim_mul_sinh {K : ℝ} (hK : 0 < K) :
    Integrable (fun w => gaussPrim K w * Real.sinh w) := by
  refine (integrable_abs_gaussPrim_mul_exp_abs hK).mono' (by unfold gaussPrim; fun_prop)
    (Eventually.of_forall fun w => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_left (abs_sinh_le_exp_abs w) (abs_nonneg _)

theorem integrable_gaussWeight {K : ℝ} (hK : 0 < K) : Integrable (gaussWeight K) := by
  refine (integrable_pow_mul_exp_neg_sq (a := (K ^ 2)⁻¹) (by positivity) 2).congr
    (Eventually.of_forall fun t => ?_)
  simp only [gaussWeight]
  congr 2
  field_simp

/-! ## The kernel `Ψ_σ` -/

theorem continuous_cayleyUnit : Continuous cayleyUnit := by
  unfold cayleyUnit
  have h : Continuous fun ξ : ℝ => (Real.sqrt (1 + ξ ^ 2))⁻¹ :=
    (Real.continuous_sqrt.comp (by fun_prop)).inv₀ fun ξ => (sqrt_one_add_sq_pos ξ).ne'
  fun_prop

theorem re_mul_cayleyUnit_mul (X ξ c : ℝ) :
    ((X : ℂ) * cayleyUnit ξ * (c : ℂ)).re = X * c * (Real.sqrt (1 + ξ ^ 2))⁻¹ := by
  rw [show (X : ℂ) * cayleyUnit ξ * (c : ℂ) = ((X * c : ℝ) : ℂ) * cayleyUnit ξ by push_cast; ring,
    Complex.re_ofReal_mul, re_cayleyUnit]

theorem norm_cexp_neg_cayley_le {X : ℝ} (hX : 0 ≤ X) (ξ w : ℝ) :
    ‖cexp (-(X * cayleyUnit ξ * Real.cosh w))‖ ≤ 1 := by
  rw [Complex.norm_exp, Complex.neg_re, re_mul_cayleyUnit_mul, Real.exp_le_one_iff, neg_nonpos]
  have := Real.cosh_pos w
  have := sqrt_one_add_sq_pos ξ
  positivity

/-- The inner integral `∫ 𝒢_K(w) X ζ(ξ) sinh w e^{−X ζ(ξ) cosh w} dw`. -/
def gaussInner (K X ξ : ℝ) : ℂ :=
  ∫ w : ℝ, (gaussPrim K w : ℂ) * ((X : ℂ) * cayleyUnit ξ * Real.sinh w) *
    cexp (-(X * cayleyUnit ξ * Real.cosh w))

/-- `Ψ_σ(X) = ∫ (1+ξ²)^{−σ} ∫ 𝒢_K(w) X ζ(ξ) sinh w e^{−X ζ(ξ) cosh w} dw dξ`. -/
def gaussKernel (σ K X : ℝ) : ℂ :=
  ∫ ξ : ℝ, (((1 + ξ ^ 2) ^ (-σ) : ℝ) : ℂ) * gaussInner K X ξ

/-- `C_K = ∫ |𝒢_K(w) sinh w| dw`. -/
def gaussSinhMass (K : ℝ) : ℝ := ∫ w : ℝ, |gaussPrim K w * Real.sinh w|

theorem norm_gaussInner_integrand_le {X : ℝ} (hX : 0 ≤ X) (K ξ w : ℝ) :
    ‖(gaussPrim K w : ℂ) * ((X : ℂ) * cayleyUnit ξ * Real.sinh w) *
      cexp (-(X * cayleyUnit ξ * Real.cosh w))‖ ≤ X * |gaussPrim K w * Real.sinh w| := by
  rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_cayleyUnit, Complex.norm_real, Complex.norm_real,
    Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hX,
    abs_mul]
  have := norm_cexp_neg_cayley_le hX ξ w
  calc |gaussPrim K w| * (X * 1 * |Real.sinh w|) * ‖cexp (-(X * cayleyUnit ξ * Real.cosh w))‖
      ≤ |gaussPrim K w| * (X * 1 * |Real.sinh w|) * 1 :=
        mul_le_mul_of_nonneg_left this (by positivity)
    _ = X * (|gaussPrim K w| * |Real.sinh w|) := by ring

theorem integrable_gaussInner_integrand {K X : ℝ} (hK : 0 < K) (hX : 0 ≤ X) (ξ : ℝ) :
    Integrable (fun w : ℝ => (gaussPrim K w : ℂ) * ((X : ℂ) * cayleyUnit ξ * Real.sinh w) *
      cexp (-(X * cayleyUnit ξ * Real.cosh w))) := by
  refine ((integrable_gaussPrim_mul_sinh hK).abs.const_mul X).mono'
    (by unfold gaussPrim; fun_prop) (Eventually.of_forall fun w => ?_)
  exact norm_gaussInner_integrand_le hX K ξ w

theorem norm_gaussInner_le {K X : ℝ} (hK : 0 < K) (hX : 0 ≤ X) (ξ : ℝ) :
    ‖gaussInner K X ξ‖ ≤ X * gaussSinhMass K := by
  rw [gaussInner, gaussSinhMass, ← integral_const_mul]
  refine (norm_integral_le_integral_norm _).trans (integral_mono_of_nonneg
    (Eventually.of_forall fun w => norm_nonneg _)
    ((integrable_gaussPrim_mul_sinh hK).abs.const_mul X)
    (Eventually.of_forall fun w => norm_gaussInner_integrand_le hX K ξ w))

/-- **Integration by parts in `w`**: `∫ G_K(w) e^{−Xζ cosh w} dw = ∫ 𝒢_K(w) Xζ sinh w e^{−Xζ cosh w} dw`. -/
theorem integral_gaussDeriv_mul_cexp {K X : ℝ} (hK : 0 < K) (hX : 0 ≤ X) (ξ : ℝ) :
    ∫ w : ℝ, (gaussDeriv K w : ℂ) * cexp (-(X * cayleyUnit ξ * Real.cosh w)) =
      gaussInner K X ξ := by
  have hv : ∀ w : ℝ, HasDerivAt (fun w : ℝ => cexp (-(X * cayleyUnit ξ * Real.cosh w)))
      (cexp (-(X * cayleyUnit ξ * Real.cosh w)) * (-((X : ℂ) * cayleyUnit ξ * Real.sinh w))) w :=
    fun w => (((Real.hasDerivAt_cosh w).ofReal_comp.const_mul ((X : ℂ) * cayleyUnit ξ)).neg).cexp
  have hG : Integrable (fun w : ℝ => ‖(gaussDeriv K w : ℂ)‖) := (integrable_gaussDeriv hK).ofReal.norm
  have hP : Integrable (fun w : ℝ => ‖(gaussPrim K w : ℂ)‖) := (integrable_gaussPrim hK).ofReal.norm
  have h := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := fun w : ℝ => (gaussPrim K w : ℂ)) (u' := fun w : ℝ => (gaussDeriv K w : ℂ))
    (v := fun w : ℝ => cexp (-(X * cayleyUnit ξ * Real.cosh w)))
    (v' := fun w : ℝ => cexp (-(X * cayleyUnit ξ * Real.cosh w)) *
      (-((X : ℂ) * cayleyUnit ξ * Real.sinh w)))
    (fun w _ => (hasDerivAt_gaussPrim K w).ofReal_comp) (fun w _ => hv w)
    (((integrable_gaussInner_integrand hK hX ξ).neg).congr
      (Eventually.of_forall fun w => by simp only [Pi.mul_apply, Pi.neg_apply]; ring))
    (hG.mono' (by unfold gaussDeriv; fun_prop)
      (Eventually.of_forall fun w => by
        rw [Pi.mul_apply, norm_mul]
        exact mul_le_of_le_one_right (norm_nonneg _) (norm_cexp_neg_cayley_le hX ξ w)))
    (hP.mono' (by unfold gaussPrim; fun_prop)
      (Eventually.of_forall fun w => by
        rw [Pi.mul_apply, norm_mul]
        exact mul_le_of_le_one_right (norm_nonneg _) (norm_cexp_neg_cayley_le hX ξ w)))
  rw [gaussInner]
  have h1 : ∫ w : ℝ, (gaussPrim K w : ℂ) * (cexp (-(X * cayleyUnit ξ * Real.cosh w)) *
      (-((X : ℂ) * cayleyUnit ξ * Real.sinh w))) =
      -∫ w : ℝ, (gaussPrim K w : ℂ) * ((X : ℂ) * cayleyUnit ξ * Real.sinh w) *
        cexp (-(X * cayleyUnit ξ * Real.cosh w)) := by
    rw [← integral_neg]; congr 1; funext w; ring
  rw [h1, neg_inj] at h
  exact h.symm

/-! ## Fubini over `(t, ξ, w)` -/

theorem exp_neg_le_inv {x : ℝ} (hx : 0 < x) : Real.exp (-x) ≤ x⁻¹ := by
  rw [Real.exp_neg, inv_le_inv₀ (Real.exp_pos x) hx]
  linarith [Real.add_one_le_exp x]

theorem one_add_sq_le_four_cosh (w : ℝ) : 1 + w ^ 2 ≤ 4 * Real.cosh w := by
  have h1 : Real.exp |w| ≤ 2 * Real.cosh w := by
    rw [← Real.cosh_abs, Real.cosh_eq]; linarith [Real.exp_pos (-|w|)]
  have h2 := Real.quadratic_le_exp_of_nonneg (abs_nonneg w)
  have h3 : |w| ^ 2 = w ^ 2 := sq_abs w
  nlinarith [abs_nonneg w]

theorem continuous_one_add_sq_rpow (σ : ℝ) :
    Continuous fun ξ : ℝ => (((1 + ξ ^ 2) ^ (-σ) : ℝ) : ℂ) :=
  Complex.continuous_ofReal.comp ((by fun_prop : Continuous fun ξ : ℝ => 1 + ξ ^ 2).rpow_const
    fun ξ => Or.inl (by positivity))

theorem continuous_cexp_neg_cayley (X : ℝ) :
    Continuous fun p : ℝ × ℝ => cexp (-(X * cayleyUnit p.1 * Real.cosh p.2)) :=
  ((continuous_const.mul (continuous_cayleyUnit.comp continuous_fst)).mul
    (Complex.continuous_ofReal.comp (Real.continuous_cosh.comp continuous_snd))).neg.cexp

/-- `(1+ξ²)^{−σ} e^{−X cosh w/√(1+ξ²)} ≤ (4/X)(1+ξ²)^{−(σ−½)}(1+w²)⁻¹`. -/
theorem rpow_mul_norm_cexp_neg_cayley_le {σ X : ℝ} (hX : 0 < X) (ξ w : ℝ) :
    (1 + ξ ^ 2) ^ (-σ) * ‖cexp (-(X * cayleyUnit ξ * Real.cosh w))‖ ≤
      (1 + ξ ^ 2) ^ (-(σ - 1 / 2)) * (4 / X * (1 + w ^ 2)⁻¹) := by
  have hs := sqrt_one_add_sq_pos ξ
  have hc := Real.cosh_pos w
  have hξ : (0 : ℝ) < 1 + ξ ^ 2 := by positivity
  rw [Complex.norm_exp, Complex.neg_re, re_mul_cayleyUnit_mul]
  have h1 := exp_neg_le_inv (show 0 < X * Real.cosh w * (Real.sqrt (1 + ξ ^ 2))⁻¹ by positivity)
  have h2 : (X * Real.cosh w * (Real.sqrt (1 + ξ ^ 2))⁻¹)⁻¹ ≤
      Real.sqrt (1 + ξ ^ 2) * (4 / X * (1 + w ^ 2)⁻¹) := by
    rw [mul_inv, mul_inv, inv_inv, mul_comm]
    have h4 := one_add_sq_le_four_cosh w
    have hw : (0 : ℝ) < 1 + w ^ 2 := by positivity
    refine mul_le_mul_of_nonneg_left ?_ hs.le
    rw [← mul_inv, show 4 / X * (1 + w ^ 2)⁻¹ = (X * (1 + w ^ 2) / 4)⁻¹ by field_simp]
    exact inv_anti₀ (by positivity) (by nlinarith)
  have hsq : (1 + ξ ^ 2) ^ (-σ) * Real.sqrt (1 + ξ ^ 2) = (1 + ξ ^ 2) ^ (-(σ - 1 / 2)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hξ]; congr 1; ring
  calc (1 + ξ ^ 2) ^ (-σ) * Real.exp (-(X * Real.cosh w * (Real.sqrt (1 + ξ ^ 2))⁻¹))
      ≤ (1 + ξ ^ 2) ^ (-σ) * (Real.sqrt (1 + ξ ^ 2) * (4 / X * (1 + w ^ 2)⁻¹)) :=
        mul_le_mul_of_nonneg_left (h1.trans h2) (by positivity)
    _ = _ := by rw [← mul_assoc, hsq]

/-- **The kernel integrated against the weight**: `∫ g_K(t) Ξ_σ(t, X) dt = Ψ_σ(X)`. -/
theorem integral_gaussWeight_mul_sameSignKernel {σ K X : ℝ} (hσ : 1 < σ) (hK : 0 < K)
    (hX : 0 < X) :
    ∫ t : ℝ, (gaussWeight K t : ℂ) * sameSignKernel σ t X = gaussKernel σ K X := by
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
  have hint : Integrable (Function.uncurry fun (t : ℝ) (p : ℝ × ℝ) => (gaussWeight K t : ℂ) * Φ t p)
      ((volume : Measure ℝ).prod (volume : Measure (ℝ × ℝ))) := by
    refine ((integrable_gaussWeight hK).mul_prod hMint).mono' ?_
      (Eventually.of_forall fun z => ?_)
    · refine Continuous.aestronglyMeasurable ?_
      simp only [hΦdef]
      have hg : Continuous fun z : ℝ × (ℝ × ℝ) => (gaussWeight K z.1 : ℂ) := by
        unfold gaussWeight; fun_prop
      exact hg.mul ((hcont_c.comp (continuous_fst.comp continuous_snd)).mul
        ((by fun_prop : Continuous fun z : ℝ × (ℝ × ℝ) => cexp (2 * z.1 * z.2.2 * Complex.I)).mul
          (hcont_E.comp continuous_snd)))
    · simp only [Function.uncurry]
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (gaussWeight_nonneg K z.1)]
      exact mul_le_mul_of_nonneg_left (hnormΦ z.1 z.2) (gaussWeight_nonneg K z.1)
  rw [integral_integral_swap hint]
  have hinner : ∀ p : ℝ × ℝ, ∫ t : ℝ, (gaussWeight K t : ℂ) * Φ t p =
      c p.1 * E p * gaussDeriv K p.2 := fun p => by
    have hpt : ∀ t : ℝ, (gaussWeight K t : ℂ) * Φ t p =
        c p.1 * E p * ((gaussWeight K t : ℂ) * cexp (2 * t * p.2 * Complex.I)) := fun t => by
      simp only [hΦdef]; ring
    simp_rw [hpt]
    rw [integral_const_mul, integral_gaussWeight_mul_cexp hK]
  simp_rw [hinner]
  have hint2 : Integrable (fun p : ℝ × ℝ => c p.1 * E p * (gaussDeriv K p.2 : ℂ))
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
    refine ((Kuznetsov.integrable_one_add_sq_rpow (τ := σ) (by linarith)).mul_prod
      (integrable_gaussDeriv hK).abs).mono' ?_ (Eventually.of_forall fun p => ?_)
    · refine Continuous.aestronglyMeasurable ?_
      have hG : Continuous fun p : ℝ × ℝ => (gaussDeriv K p.2 : ℂ) := by
        unfold gaussDeriv; fun_prop
      exact ((hcont_c.comp continuous_fst).mul hcont_E).mul hG
    · simp only [hc, hE]
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_of_nonneg (by positivity), Real.norm_eq_abs]
      have := norm_cexp_neg_cayley_le hX.le p.1 p.2
      calc (1 + p.1 ^ 2) ^ (-σ) * ‖cexp (-(X * cayleyUnit p.1 * Real.cosh p.2))‖ *
            |gaussDeriv K p.2|
          ≤ (1 + p.1 ^ 2) ^ (-σ) * 1 * |gaussDeriv K p.2| := by gcongr
        _ = _ := by ring
  rw [Measure.volume_eq_prod, integral_prod _ hint2, gaussKernel]
  congr 1; funext ξ
  rw [← integral_gaussDeriv_mul_cexp hK hX.le ξ, ← integral_const_mul]
  congr 1; funext w
  simp only [hc, hE]
  ring

/-! ## Bounds and the limit `σ ↓ 1` -/

theorem continuous_gaussInner_integrand (K X : ℝ) :
    Continuous fun p : ℝ × ℝ => (gaussPrim K p.2 : ℂ) * ((X : ℂ) * cayleyUnit p.1 * Real.sinh p.2) *
      cexp (-(X * cayleyUnit p.1 * Real.cosh p.2)) := by
  have hP : Continuous fun p : ℝ × ℝ => (gaussPrim K p.2 : ℂ) := by unfold gaussPrim; fun_prop
  have hS : Continuous fun p : ℝ × ℝ => (X : ℂ) * cayleyUnit p.1 * Real.sinh p.2 :=
    (continuous_const.mul (continuous_cayleyUnit.comp continuous_fst)).mul
      (Complex.continuous_ofReal.comp (Real.continuous_sinh.comp continuous_snd))
  exact (hP.mul hS).mul (continuous_cexp_neg_cayley X)

theorem aestronglyMeasurable_gaussInner (K X : ℝ) :
    AEStronglyMeasurable (gaussInner K X) volume :=
  ((continuous_gaussInner_integrand K X).stronglyMeasurable.integral_prod_right'
    (ν := (volume : Measure ℝ))).aestronglyMeasurable

theorem one_add_sq_rpow_le_inv {σ : ℝ} (hσ : 1 ≤ σ) (ξ : ℝ) :
    (1 + ξ ^ 2) ^ (-σ) ≤ (1 + ξ ^ 2)⁻¹ := by
  rw [← Real.rpow_neg_one]
  exact Real.rpow_le_rpow_of_exponent_le (by nlinarith [sq_nonneg ξ]) (by linarith)

theorem norm_gaussKernel_integrand_le {σ K X : ℝ} (hσ : 1 ≤ σ) (hK : 0 < K) (hX : 0 ≤ X) (ξ : ℝ) :
    ‖(((1 + ξ ^ 2) ^ (-σ) : ℝ) : ℂ) * gaussInner K X ξ‖ ≤
      (1 + ξ ^ 2)⁻¹ * (X * gaussSinhMass K) := by
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  exact mul_le_mul (one_add_sq_rpow_le_inv hσ ξ) (norm_gaussInner_le hK hX ξ) (norm_nonneg _)
    (by positivity)

/-- **`|Ψ_σ(X)| ≤ π X C_K`** for `σ ≥ 1`. -/
theorem norm_gaussKernel_le {σ K X : ℝ} (hσ : 1 ≤ σ) (hK : 0 < K) (hX : 0 ≤ X) :
    ‖gaussKernel σ K X‖ ≤ Real.pi * X * gaussSinhMass K := by
  rw [gaussKernel]
  refine (norm_integral_le_of_norm_le (integrable_inv_one_add_sq.mul_const _)
    (Eventually.of_forall fun ξ => norm_gaussKernel_integrand_le hσ hK hX ξ)).trans (le_of_eq ?_)
  rw [integral_mul_const, integral_univ_inv_one_add_sq]
  ring

/-- **Continuity as `σ ↓ 1`.** -/
theorem tendsto_gaussKernel {K X : ℝ} (hK : 0 < K) (hX : 0 ≤ X) :
    Tendsto (fun σ => gaussKernel σ K X) (𝓝[>] 1) (𝓝 (gaussKernel 1 K X)) := by
  unfold gaussKernel
  refine tendsto_integral_filter_of_dominated_convergence
    (fun ξ => (1 + ξ ^ 2)⁻¹ * (X * gaussSinhMass K)) ?_ ?_
    (integrable_inv_one_add_sq.mul_const _) ?_
  · exact Eventually.of_forall fun σ =>
      ((continuous_one_add_sq_rpow σ).aestronglyMeasurable).mul (aestronglyMeasurable_gaussInner K X)
  · filter_upwards [self_mem_nhdsWithin] with σ (hσ : 1 < σ)
    exact Eventually.of_forall fun ξ => norm_gaussKernel_integrand_le hσ.le hK hX ξ
  · refine Eventually.of_forall fun ξ => ?_
    have hξ : (0 : ℝ) < 1 + ξ ^ 2 := by positivity
    have h : Tendsto (fun σ : ℝ => (1 + ξ ^ 2) ^ (-σ)) (𝓝 1) (𝓝 ((1 + ξ ^ 2) ^ (-(1 : ℝ)))) :=
      ((Real.continuousAt_const_rpow hξ.ne').comp continuous_neg.continuousAt).tendsto
    exact ((Complex.continuous_ofReal.tendsto _).comp (h.mono_left nhdsWithin_le_nhds)).mul_const _

/-! ## The value at `σ = 1` -/

theorem cayleyUnit_eq_cexp (ξ : ℝ) : cayleyUnit ξ = cexp ((Real.arctan ξ : ℂ) * Complex.I) := by
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_arctan,
    Real.sin_arctan, cayleyUnit]
  push_cast
  ring

/-- **The `ξ`-integral at `σ = 1`**: `∫ (1+ξ²)⁻¹ ζ(ξ) e^{−b ζ(ξ)} dξ = 2 sin b / b`. -/
theorem integral_inv_one_add_sq_mul_cayley {b : ℝ} (hb : 0 < b) :
    ∫ ξ : ℝ, (((1 + ξ ^ 2)⁻¹ : ℝ) : ℂ) * cayleyUnit ξ * cexp (-(b * cayleyUnit ξ)) =
      2 * Real.sin b / b := by
  have hbc : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  set F : ℝ → ℂ := fun x => Complex.I / b * cexp (-(b * cexp ((x : ℂ) * Complex.I)))
  have hFc : Continuous F := by fun_prop
  have hderiv : ∀ ξ : ℝ, HasDerivAt (fun ξ => F (Real.arctan ξ))
      ((((1 + ξ ^ 2)⁻¹ : ℝ) : ℂ) * cayleyUnit ξ * cexp (-(b * cayleyUnit ξ))) ξ := fun ξ => by
    have h1 : HasDerivAt (fun ξ : ℝ => cexp ((Real.arctan ξ : ℂ) * Complex.I))
        (cexp ((Real.arctan ξ : ℂ) * Complex.I) * (((1 / (1 + ξ ^ 2) : ℝ) : ℂ) * Complex.I)) ξ :=
      ((Real.hasDerivAt_arctan ξ).ofReal_comp.mul_const Complex.I).cexp
    have h2 := ((h1.const_mul (b : ℂ)).neg.cexp).const_mul (Complex.I / b)
    refine h2.congr_deriv ?_
    simp only [Pi.neg_apply]
    rw [← cayleyUnit_eq_cexp]
    push_cast
    field_simp
    linear_combination (-(cayleyUnit ξ) / (1 + (ξ : ℂ) ^ 2)) * Complex.I_sq
  have hint : Integrable fun ξ : ℝ =>
      (((1 + ξ ^ 2)⁻¹ : ℝ) : ℂ) * cayleyUnit ξ * cexp (-(b * cayleyUnit ξ)) := by
    refine integrable_inv_one_add_sq.mono' (by
      have := continuous_cayleyUnit
      fun_prop) (Eventually.of_forall fun ξ => ?_)
    rw [norm_mul, norm_mul, norm_cayleyUnit, Complex.norm_real, Real.norm_of_nonneg (by positivity),
      mul_one]
    have := norm_cexp_neg_cayley_le hb.le ξ 0
    rw [Real.cosh_zero, Complex.ofReal_one, mul_one] at this
    exact mul_le_of_le_one_right (by positivity) this
  have htop : Tendsto (fun ξ => F (Real.arctan ξ)) atTop (𝓝 (F (Real.pi / 2))) :=
    (hFc.tendsto _).comp (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds)
  have hbot : Tendsto (fun ξ => F (Real.arctan ξ)) atBot (𝓝 (F (-(Real.pi / 2)))) :=
    (hFc.tendsto _).comp (Real.tendsto_arctan_atBot.mono_right nhdsWithin_le_nhds)
  rw [integral_of_hasDerivAt_of_tendsto hderiv hint hbot htop]
  simp only [F]
  have e1 : cexp (((Real.pi / 2 : ℝ) : ℂ) * Complex.I) = Complex.I := by
    push_cast; exact Complex.exp_pi_div_two_mul_I
  have e2 : cexp (((-(Real.pi / 2) : ℝ) : ℂ) * Complex.I) = -Complex.I := by
    push_cast
    rw [show -((Real.pi : ℂ) / 2) * Complex.I = -(Real.pi : ℂ) / 2 * Complex.I by ring,
      Complex.exp_neg_pi_div_two_mul_I]
  rw [e1, e2, Complex.ofReal_sin, Complex.sin]
  field_simp

/-- **DI (5.6)**: `Ψ_1(X) = 2 ∫ 𝒢_K(w) tanh w sin(X cosh w) dw`. -/
theorem gaussKernel_one {K X : ℝ} (hK : 0 < K) (hX : 0 < X) :
    gaussKernel 1 K X =
      ((2 * ∫ w : ℝ, gaussPrim K w * Real.tanh w * Real.sin (X * Real.cosh w) : ℝ) : ℂ) := by
  set f : ℝ → ℝ → ℂ := fun ξ w => (((1 + ξ ^ 2)⁻¹ : ℝ) : ℂ) *
    ((gaussPrim K w : ℂ) * ((X : ℂ) * cayleyUnit ξ * Real.sinh w) *
      cexp (-(X * cayleyUnit ξ * Real.cosh w))) with hf
  have hint : Integrable (Function.uncurry f) ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
    refine (integrable_inv_one_add_sq.mul_prod
      ((integrable_gaussPrim_mul_sinh hK).abs.const_mul X)).mono' ?_
      (Eventually.of_forall fun p => ?_)
    · refine Continuous.aestronglyMeasurable ?_
      simp only [hf, Function.uncurry_def]
      exact (Complex.continuous_ofReal.comp ((by fun_prop : Continuous fun p : ℝ × ℝ =>
        1 + p.1 ^ 2).inv₀ fun p => by positivity)).mul (continuous_gaussInner_integrand K X)
    · simp only [hf, Function.uncurry_def]
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left (norm_gaussInner_integrand_le hX.le K p.1 p.2)
        (by positivity)
  have hkernel : gaussKernel 1 K X = ∫ ξ : ℝ, ∫ w : ℝ, f ξ w := by
    rw [gaussKernel]
    congr 1; funext ξ
    rw [gaussInner, ← integral_const_mul, Real.rpow_neg_one]
  rw [hkernel, integral_integral_swap hint]
  have hinner : ∀ w : ℝ, ∫ ξ : ℝ, f ξ w =
      (((2 * (gaussPrim K w * Real.tanh w * Real.sin (X * Real.cosh w))) : ℝ) : ℂ) := fun w => by
    have hc := Real.cosh_pos w
    have hpt : ∀ ξ : ℝ, f ξ w = ((gaussPrim K w : ℂ) * X * Real.sinh w) *
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
  simp_rw [hinner]
  rw [integral_complex_ofReal, integral_const_mul]

end

end GaloisForLFunctions.RHTower.DeckPointPair
