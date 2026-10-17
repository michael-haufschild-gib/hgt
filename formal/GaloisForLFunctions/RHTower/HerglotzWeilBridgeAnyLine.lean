import GaloisForLFunctions.RHTower.HerglotzWeilPositiveBridge
import GaloisForLFunctions.RHTower.WeilLineIntegralAnyAbscissa

/-!
# Herglotz positivity on any line, and the bridge for any abscissa of absolute convergence

Let `lam` be real with `Σ |lam(n)| n^{−σ} < ∞` for every `σ > σ₂` (any `σ₂`), and let `Φ` be
holomorphic with `Re Φ ≥ 0` on `Re s > ½` and equal to the Weil function `Φ_lam` on `Re s > σ₂`.
Then `lam` is full-cone Weil-positive (`weilPositiveFull_of_herglotz_abscissa`).

This extends `AtomDomination.weilPositiveFull_of_herglotz`, which assumes absolute convergence for
every `σ > 1`.  The Weil functional is written as a line integral on a line `Re s = c > σ₂` of
absolute convergence (`WeilLineAnyAbscissa.weilFullFunctional_weilTest_eq_line`), where the Weil
function has linear growth (`norm_weilFunction_le_at`), and the Herglotz–Riesz argument is run on
that line (`re_lineIntegral_nonneg_of_herglotz_at`); the two auxiliary line identities move to
`Re s = 5/4` by a vertical contour shift.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real ENNReal ComplexConjugate

noncomputable section

namespace RHTower.HerglotzBridgeAnyLine

open GaloisForLFunctions.HTGeometry Zeta23 Zeta23.WeilEF RHTower.WeilLineIntegral RHTower.WeilAtomic
  RHTower.AtomDomination

/-- Vertical shift of `∫ (H_k(c + it) + H_k(1 − c − it)) q(c + it) dt` to `Re s = 5/4` for an
autocorrelation `k` and an entire `q` of linear growth on the strip. -/
theorem integral_line_weilTest_shift {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    {c : ℝ} (hc : 5 / 4 ≤ c) {q : ℂ → ℂ} (hq : Differentiable ℂ q) {B : ℝ} (hB : 0 ≤ B)
    (hqb : ∀ s : ℂ, 5 / 4 ≤ s.re → s.re ≤ c → ‖q s‖ ≤ B * (1 + |s.im|)) :
    (∫ t : ℝ, (Hfn (EF.weilTest f f) ((c : ℝ) + t * I) +
      Hfn (EF.weilTest f f) (1 - (c : ℝ) - t * I)) * q ((c : ℝ) + t * I)) =
    ∫ t : ℝ, (Hfn (EF.weilTest f f) ((5 / 4 : ℝ) + t * I) +
      Hfn (EF.weilTest f f) (1 - (5 / 4 : ℝ) - t * I)) * q ((5 / 4 : ℝ) + t * I) := by
  set k := EF.weilTest f f with hkdef
  have hk : ContDiff ℝ 2 k := EF.weilTest_contDiff hf hf.continuous hfc
  have hkc : HasCompactSupport k := EF.weilTest_hasCompactSupport hfc hfc
  obtain ⟨D, hD0, hD⟩ := WeilLineAnyAbscissa.norm_Hfn_weilTest_le_wide hf hfc c
  set Ψ : ℂ → ℂ := fun s => (Hfn k s + Hfn k (1 - s)) * q s with hΨ
  have hΨline : ∀ σ t : ℝ, Ψ ((σ : ℂ) + t * I) =
      (Hfn k ((σ : ℝ) + t * I) + Hfn k (1 - (σ : ℝ) - t * I)) * q ((σ : ℝ) + t * I) :=
    fun σ t => by simp only [hΨ]; congr 3; ring
  have hHd := differentiable_Hfn hk hkc
  have hd : ∀ s : ℂ, s.re ∈ uIcc (5 / 4) c → DifferentiableAt ℂ Ψ s := fun s _ =>
    ((hHd s).add ((hHd _).comp s ((differentiableAt_const _).sub differentiableAt_id))).mul (hq s)
  have hb : ∀ s : ℂ, s.re ∈ uIcc (5 / 4) c → ‖Ψ s‖ ≤ 4 * D * B / (1 + s.im ^ 2) := by
    intro s hs
    rw [uIcc_of_le hc] at hs
    have h1 : |s.re - 1 / 2| ≤ c := abs_le.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have h2 : |(1 - s.re) - 1 / 2| ≤ c := abs_le.mpr ⟨by linarith [hs.2], by linarith [hs.1]⟩
    have hb1 : ‖Hfn k s‖ ≤ D / (1 + s.im ^ 2) ^ 2 := by
      have := hD s.re s.im h1
      rwa [Complex.re_add_im] at this
    have hb2 : ‖Hfn k (1 - s)‖ ≤ D / (1 + s.im ^ 2) ^ 2 := by
      have := hD (1 - s.re) (-s.im) h2
      have e1 : ((1 - s.re : ℝ) : ℂ) + ((-s.im : ℝ) : ℂ) * I = 1 - s := by
        conv_rhs => rw [← Complex.re_add_im s]
        push_cast; ring
      rwa [e1, neg_sq] at this
    have hlin := hqb s hs.1 hs.2
    have hsq : (1 + |s.im|) ≤ 2 * (1 + s.im ^ 2) := by nlinarith [sq_abs s.im, abs_nonneg s.im]
    simp only [hΨ]
    rw [norm_mul]
    calc ‖Hfn k s + Hfn k (1 - s)‖ * ‖q s‖
        ≤ (D / (1 + s.im ^ 2) ^ 2 + D / (1 + s.im ^ 2) ^ 2) * (B * (1 + |s.im|)) :=
          mul_le_mul ((norm_add_le _ _).trans (add_le_add hb1 hb2)) hlin (norm_nonneg _)
            (by positivity)
      _ ≤ (D / (1 + s.im ^ 2) ^ 2 + D / (1 + s.im ^ 2) ^ 2) * (B * (2 * (1 + s.im ^ 2))) := by
          gcongr
      _ = 4 * D * B / (1 + s.im ^ 2) := by field_simp; ring
  have h := integral_vertical_line_shift_of_decay hd hb
  simp_rw [hΨline] at h
  exact h.symm

/-- `∫ (H(c + it) + H(1 − c − it)) dt` is real for an autocorrelation, for every `c ≥ 5/4`. -/
theorem im_integral_line_weilTest_at {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) {c : ℝ} (hc : 5 / 4 ≤ c) :
    (∫ t : ℝ, (Hfn (EF.weilTest f f) ((c : ℝ) + t * I) +
      Hfn (EF.weilTest f f) (1 - (c : ℝ) - t * I))).im = 0 := by
  have h := integral_line_weilTest_shift hf hfc hc (q := fun _ => 1) (differentiable_const 1)
    zero_le_one (fun s _ _ => by rw [norm_one]; linarith [abs_nonneg s.im])
  simp only [mul_one] at h
  rw [h]
  exact im_integral_line_weilTest hf hfc

/-- `∫ (H(c + it) + H(1 − c − it))(c − ½ + it) dt` is purely imaginary for an autocorrelation, for
every `c ≥ 5/4`. -/
theorem re_integral_line_weilTest_linear_at {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) {c : ℝ} (hc : 5 / 4 ≤ c) :
    (∫ t : ℝ, (Hfn (EF.weilTest f f) ((c : ℝ) + t * I) +
      Hfn (EF.weilTest f f) (1 - (c : ℝ) - t * I)) * (((c : ℝ) : ℂ) + t * I - 1 / 2)).re = 0 := by
  have h := integral_line_weilTest_shift hf hfc hc (q := fun s => s - 1 / 2)
    (differentiable_id.sub_const _) (B := c + 1) (by linarith) (fun s h1 h2 => by
      have hs : s - 1 / 2 = ((s.re - 1 / 2 : ℝ) : ℂ) + (s.im : ℂ) * I := by
        conv_lhs => rw [← Complex.re_add_im s]
        push_cast; ring
      rw [hs]
      refine (norm_add_le _ _).trans ?_
      rw [Complex.norm_real, norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
        Real.norm_eq_abs, Real.norm_eq_abs]
      have : |s.re - 1 / 2| ≤ c := abs_le.mpr ⟨by linarith, by linarith⟩
      nlinarith [abs_nonneg s.im])
  rw [h]
  exact re_integral_line_weilTest_linear hf hfc

theorem re_lineIntegral_nonneg_of_herglotz_at {G Φ : ℂ → ℂ} {σ₂ c₁ : ℝ} (hc : 5 / 4 ≤ c₁)
    (hσc : σ₂ < c₁)
    (hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re})
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hconj : ∀ s : ℂ, 1 / 2 < s.re → Φ (conj s) = conj (Φ s))
    (hΦG : ∀ s : ℂ, σ₂ < s.re → Φ s = G s) {A : ℝ} (hA0 : 0 ≤ A)
    (hA : ∀ t : ℝ, ‖G ((c₁ : ℂ) + t * I)‖ ≤ A * (1 + |t|))
    {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    0 ≤ ((1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ,
      (Hfn (EF.weilTest f f) ((c₁ : ℂ) + t * I) +
        Hfn (EF.weilTest f f) (1 - (c₁ : ℂ) - t * I)) *
        G ((c₁ : ℂ) + t * I)).re := by
  obtain ⟨ν, hfin, c, hrep⟩ := exists_herglotzRiesz_representation hΦd hΦre hconj
  set k : ℝ → ℂ := EF.weilTest f f with hk
  have hkd : ContDiff ℝ 2 k := EF.weilTest_contDiff hf hf.continuous hfc
  have hkc : HasCompactSupport k := EF.weilTest_hasCompactSupport hfc hfc
  obtain ⟨D, hD0, hD⟩ := WeilLineAnyAbscissa.norm_Hfn_weilTest_le_wide hf hfc c₁
  obtain ⟨Ck, hCk0, hCk⟩ := WeilLineAnyAbscissa.norm_Hfn_le_wide hkd hkc c₁
  set c₀ : ℝ := c₁ with hc₀
  have hcc : |c₀ - 1 / 2| ≤ c₁ := abs_le.mpr ⟨by linarith, by linarith⟩
  have hcc' : |(1 - c₀) - 1 / 2| ≤ c₁ := abs_le.mpr ⟨by linarith, by linarith⟩
  set F : ℝ → ℂ := fun t => Hfn k (c₀ + t * I) + Hfn k (1 - c₀ - t * I) with hF
  have hFb : ∀ t : ℝ, ‖F t‖ ≤ 2 * D / (1 + t ^ 2) ^ 2 := by
    intro t
    have e : (1 : ℂ) - c₀ - t * I = ((1 - c₀ : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I := by push_cast; ring
    refine (norm_add_le _ _).trans ?_
    rw [e]
    have h1 := hD c₀ t hcc
    have h2 := hD (1 - c₀) (-t) hcc'
    rw [neg_sq] at h2
    rw [two_mul, add_div]
    exact add_le_add h1 h2
  have hFc : Continuous F := by
    have hm : ∀ t : ℝ, Hfn k (1 - c₀ - t * I) = Hfn (fun u => k (-u)) (c₀ + t * I) :=
      fun t => Hfn_mirror k c₀ t
    simp only [hF, hm]
    exact (continuous_Hfn_line hkd hkc c₀).add
      (continuous_Hfn_line (hkd.comp contDiff_neg) (hkc.comp_homeomorph (Homeomorph.neg ℝ)) c₀)
  have hFi : Integrable F := by
    refine (integrable_inv_one_add_sq.const_mul (2 * D)).mono' hFc.aestronglyMeasurable
      (Eventually.of_forall fun t => ?_)
    calc ‖F t‖ ≤ 2 * D / (1 + t ^ 2) ^ 2 := hFb t
      _ ≤ 2 * D / (1 + t ^ 2) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) (by nlinarith [sq_nonneg t])
      _ = 2 * D * (1 + t ^ 2)⁻¹ := by ring
  have hre : ∀ t : ℝ, ((c₀ : ℂ) + t * I).re = c₀ := fun t => by simp
  have hs : ∀ t : ℝ, 1 / 2 < ((c₀ : ℂ) + t * I).re := fun t => by rw [hre]; linarith
  have hs1 : ∀ t : ℝ, σ₂ < ((c₀ : ℂ) + t * I).re := fun t => by rw [hre]; linarith
  set K : ℝ → ℝ → ℂ := fun t θ => symKernel (c₀ + t * I) (circleMap 0 1 θ) with hK
  have hKi : ∀ t, Integrable (K t) ν := fun t => integrable_diskSym (norm_discPt_lt_one (hs t))
  have hΦK : ∀ t : ℝ, G (c₀ + t * I) = (∫ θ, K t θ ∂ν) + c * I := fun t => by
    rw [← hΦG _ (hs1 t)]
    exact hrep _ (hs t)
  -- the majorant
  set w : ℝ → ℝ := fun t => ‖((c₀ : ℂ) + t * I) - 1 / 2‖ / (c₀ - 1 / 2) with hw
  have hw0 : ∀ t, 0 ≤ w t := fun t => div_nonneg (norm_nonneg _) (by linarith)
  have hwb : ∀ t : ℝ, w t ≤ 2 * (1 + |t|) := by
    intro t
    simp only [hw]
    rw [div_le_iff₀ (show (0 : ℝ) < c₀ - 1 / 2 by linarith)]
    have e : ((c₀ : ℂ) + t * I) - 1 / 2 = ((c₀ - 1 / 2 : ℝ) : ℂ) + t * I := by
      push_cast; ring
    rw [e]
    have hc0 : (3 / 4 : ℝ) ≤ c₀ - 1 / 2 := by linarith
    calc ‖((c₀ - 1 / 2 : ℝ) : ℂ) + t * I‖ ≤ ‖((c₀ - 1 / 2 : ℝ) : ℂ)‖ + ‖(t : ℂ) * I‖ :=
          norm_add_le _ _
      _ = (c₀ - 1 / 2) + |t| := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith), norm_mul,
            Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs]
      _ ≤ 2 * (1 + |t|) * (c₀ - 1 / 2) := by nlinarith [abs_nonneg t]
  have hKn : ∀ t : ℝ, ∫ θ, ‖K t θ‖ ∂ν ≤
      w t * ‖G (c₀ + t * I)‖ := by
    intro t
    have hpt : ∀ θ, ‖K t θ‖ ≤ w t * (K t θ).re := fun θ => by
      have := norm_symKernel_le (hs t) (norm_circleMap_one θ)
      rw [hre] at this
      exact this
    have hreI : ∫ θ, (K t θ).re ∂ν = (∫ θ, K t θ ∂ν).re := integral_re (hKi t)
    calc ∫ θ, ‖K t θ‖ ∂ν ≤ ∫ θ, w t * (K t θ).re ∂ν :=
          integral_mono (hKi t).norm ((hKi t).re.const_mul _) hpt
      _ = w t * (G (c₀ + t * I)).re := by
          rw [integral_const_mul, hreI, hΦK t, Complex.add_re]
          simp
      _ ≤ w t * ‖G (c₀ + t * I)‖ :=
          mul_le_mul_of_nonneg_left (Complex.re_le_norm _) (hw0 t)
  -- integrability on the product
  have hdc : Continuous fun t : ℝ => discPt ((c₀ : ℂ) + t * I) := by
    have heq : (fun t : ℝ => discPt ((c₀ : ℂ) + t * I)) =
        fun t : ℝ => (2 * ((c₀ : ℂ) + t * I) - 3) / (2 * ((c₀ : ℂ) + t * I) + 1) := rfl
    rw [heq]
    exact Continuous.div (by fun_prop) (by fun_prop) fun t =>
      two_mul_add_one_ne_zero (by rw [hre]; linarith)
  set g : ℝ × ℝ → ℂ := fun p => F p.1 * K p.1 p.2 with hg
  have hgc : Continuous g :=
    (hFc.comp continuous_fst).mul (continuous_diskSym_comp (hdc.comp continuous_fst)
      ((continuous_circleMap 0 1).comp continuous_snd) (fun p => norm_discPt_lt_one (hs p.1))
      fun p => norm_circleMap_one p.2)
  have hgi : Integrable g (volume.prod ν) := by
    rw [integrable_prod_iff hgc.aestronglyMeasurable]
    refine ⟨Eventually.of_forall fun t => (hKi t).const_mul (F t), ?_⟩
    refine (integrable_inv_one_add_sq.const_mul (8 * D * A)).mono'
      hgc.aestronglyMeasurable.norm.integral_prod_right' (Eventually.of_forall fun t => ?_)
    rw [Real.norm_of_nonneg (integral_nonneg fun θ => norm_nonneg _)]
    simp only [hg, norm_mul]
    rw [integral_const_mul]
    have hK1 : ∫ θ, ‖K t θ‖ ∂ν ≤ 2 * (1 + |t|) * (A * (1 + |t|)) :=
      (hKn t).trans (mul_le_mul (hwb t) (hA t) (norm_nonneg _) (by positivity))
    calc ‖F t‖ * ∫ θ, ‖K t θ‖ ∂ν
        ≤ (2 * D / (1 + t ^ 2) ^ 2) * (2 * (1 + |t|) * (A * (1 + |t|))) :=
          mul_le_mul (hFb t) hK1 (integral_nonneg fun θ => norm_nonneg _) (by positivity)
      _ = 4 * D * A * ((1 + |t|) ^ 2 / (1 + t ^ 2)) * (1 + t ^ 2)⁻¹ := by
          field_simp
          ring
      _ ≤ 4 * D * A * 2 * (1 + t ^ 2)⁻¹ := by
          gcongr
          rw [div_le_iff₀ (by positivity)]
          nlinarith [sq_abs t, sq_nonneg (|t| - 1)]
      _ = 8 * D * A * (1 + t ^ 2)⁻¹ := by ring
  -- the line integral as a `ν`-integral
  have hsplit : (∫ t : ℝ, F t * G (c₀ + t * I)) =
      (∫ θ, ∫ t, F t * K t θ ∂volume ∂ν) + (c * I) * ∫ t, F t := by
    have h1 : ∀ t, F t * G (c₀ + t * I) =
        (∫ θ, F t * K t θ ∂ν) + c * I * F t := by
      intro t
      rw [hΦK t, integral_const_mul]
      ring
    rw [integral_congr_ae (Eventually.of_forall h1),
      integral_add hgi.integral_prod_left (hFi.const_mul _), integral_const_mul]
    congr 1
    exact integral_integral_swap (f := fun t θ => F t * K t θ) hgi
  -- each angle contributes a nonnegative real part
  have hpi : (2 * Real.pi : ℂ) ≠ 0 := by
    have : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    exact mul_ne_zero two_ne_zero this
  have hJre : ∀ θ, 0 ≤ (∫ t, F t * K t θ).re := by
    intro θ
    set ζ := circleMap 0 1 θ with hζdef
    have hζ : ‖ζ‖ = 1 := norm_circleMap_one θ
    by_cases h1 : ζ = 1
    · have hKt : ∀ t, K t θ = (c₀ : ℂ) + t * I - 1 / 2 := fun t => by
        show symKernel _ ζ = _
        rw [h1]
        exact symKernel_one (two_mul_add_one_ne_zero (by rw [hre]; linarith))
      have e : (∫ t, F t * K t θ) = ∫ t, F t * ((c₀ : ℂ) + t * I - 1 / 2) :=
        integral_congr_ae (Eventually.of_forall fun t => congrArg (fun x => F t * x) (hKt t))
      rw [e]
      exact (re_integral_line_weilTest_linear_at hf hfc hc).symm.le
    · set γ : ℝ := circleOrd ζ with hγ
      have hKt : ∀ t, K t θ =
          (1 + (γ : ℂ) ^ 2) / 2 * gPair (1 / 2 + γ * I) (c₀ + t * I) := fun t =>
        symKernel_eq (hs t) hζ h1
      have h2 : (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, F t * gPair (1 / 2 + γ * I) (c₀ + t * I) =
          Hfn k (1 / 2 + γ * I) + Hfn k (1 - (1 / 2 + γ * I)) :=
        two_line_pair (differentiable_Hfn hkd hkc) (c := c₀) (C := Ck)
          (fun σ t h1 h2 => hCk σ t (abs_le.mpr ⟨by linarith, by linarith⟩)) (z₀ := 1 / 2 + γ * I)
          (by simp; linarith) (by simp; linarith)
      have hHz : Hfn k (1 / 2 + γ * I) + Hfn k (1 - (1 / 2 + γ * I)) =
          ((‖paperFT f γ‖ ^ 2 + ‖paperFT f (-γ)‖ ^ 2 : ℝ) : ℂ) := by
        have a := Hfn_weilTest_critical hf.continuous hfc γ
        have b := Hfn_weilTest_critical_neg hf.continuous hfc γ
        rw [show (1 / 2 : ℂ) + γ * I = ((1 / 2 : ℝ) : ℂ) + γ * I by push_cast; ring,
          show (1 : ℂ) - (((1 / 2 : ℝ) : ℂ) + γ * I) = ((1 / 2 : ℝ) : ℂ) - γ * I by
            push_cast; ring, a, b]
        push_cast
        ring
      have e : (∫ t, F t * K t θ) =
          (1 + (γ : ℂ) ^ 2) / 2 * ∫ t, F t * gPair (1 / 2 + γ * I) (c₀ + t * I) := by
        rw [← integral_const_mul]
        refine integral_congr_ae (Eventually.of_forall fun t => ?_)
        show F t * K t θ = (1 + (γ : ℂ) ^ 2) / 2 * (F t * gPair (1 / 2 + γ * I) (c₀ + t * I))
        rw [hKt t]
        ring
      have hX : (∫ t, F t * gPair (1 / 2 + γ * I) (c₀ + t * I)) =
          (2 * Real.pi : ℂ) * ((‖paperFT f γ‖ ^ 2 + ‖paperFT f (-γ)‖ ^ 2 : ℝ) : ℂ) := by
        rw [← hHz, ← h2, ← mul_assoc, mul_one_div_cancel hpi, one_mul]
      rw [e, hX]
      have hval : (1 + (γ : ℂ) ^ 2) / 2 * ((2 * Real.pi : ℂ) *
          ((‖paperFT f γ‖ ^ 2 + ‖paperFT f (-γ)‖ ^ 2 : ℝ) : ℂ)) =
          (((1 + γ ^ 2) / 2 * (2 * Real.pi) * (‖paperFT f γ‖ ^ 2 + ‖paperFT f (-γ)‖ ^ 2) : ℝ) :
            ℂ) := by
        push_cast
        ring
      rw [hval, Complex.ofReal_re]
      positivity
  -- assemble
  have hFim : (∫ t, F t).im = 0 := im_integral_line_weilTest_at hf hfc hc
  have hJi : Integrable (fun θ => ∫ t, F t * K t θ) ν := hgi.integral_prod_right
  have hJre' : ∫ θ, (∫ t, F t * K t θ).re ∂ν = (∫ θ, ∫ t, F t * K t θ ∂volume ∂ν).re :=
    integral_re hJi
  have hcI : ((c : ℂ) * I * ∫ t, F t).re = 0 := by
    simp [Complex.mul_re, hFim]
  rw [hsplit,
    show (1 / (2 * Real.pi) : ℂ) = ((1 / (2 * Real.pi) : ℝ) : ℂ) by push_cast; ring,
    Complex.re_ofReal_mul, Complex.add_re, hcI, add_zero, ← hJre']
  exact mul_nonneg (by positivity) (integral_nonneg hJre)

/-- Linear growth of the Weil function on a line `Re s = c ≥ 3/2` of absolute convergence. -/
theorem norm_weilFunction_le_at {lam : ℕ → ℝ} {c : ℝ} (hc : 3 / 2 ≤ c)
    (hsum : LSeriesSummable (WeilHerglotz.lamC lam) c) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ t : ℝ, ‖WeilHerglotz.weilFunction lam (c + t * I)‖ ≤ A * (1 + |t|) := by
  obtain ⟨B, hB0, hB⟩ := WeilLineAnyAbscissa.norm_logDeriv_Gammaℝ_le_lin c
  set S : ℝ := ∑' n, ‖LSeries.term (WeilHerglotz.lamC lam) c n‖ with hS
  have hS0 : 0 ≤ S := tsum_nonneg fun n => norm_nonneg _
  have hc1 : 1 < c := by linarith
  have hg0 : 0 ≤ 1 / c + 1 / (c - 1) := by
    have : 0 < c - 1 := by linarith
    positivity
  refine ⟨B + (1 / c + 1 / (c - 1)) + S, by positivity, fun t => ?_⟩
  have hre : ((c : ℂ) + t * I).re = c := by simp
  have him : ((c : ℂ) + t * I).im = t := by simp
  rw [weilFunction_eq lam (by rw [hre]; linarith)]
  have h1 : 1 ≤ 1 + |t| := by linarith [abs_nonneg t]
  have hl := hB ((c : ℂ) + t * I) (by rw [hre]; exact hc) (by rw [hre])
  rw [him] at hl
  calc ‖logDeriv Complex.Gammaℝ ((c : ℂ) + t * I) + gPair 0 ((c : ℂ) + t * I) -
        LSeries (WeilHerglotz.lamC lam) ((c : ℂ) + t * I)‖
      ≤ ‖logDeriv Complex.Gammaℝ ((c : ℂ) + t * I)‖ + ‖gPair 0 ((c : ℂ) + t * I)‖ +
          ‖LSeries (WeilHerglotz.lamC lam) ((c : ℂ) + t * I)‖ :=
        (norm_sub_le _ _).trans (by gcongr; exact norm_add_le _ _)
    _ ≤ B * (1 + |t|) + (1 / c + 1 / (c - 1)) + S := by
        gcongr
        · exact norm_gPair_zero_le hc1 t
        · exact WeilLineAnyAbscissa.norm_LSeries_line_le hsum t
    _ ≤ B * (1 + |t|) + (1 / c + 1 / (c - 1)) * (1 + |t|) + S * (1 + |t|) := by
        gcongr
        · exact le_mul_of_one_le_right hg0 h1
        · exact le_mul_of_one_le_right hS0 h1
    _ = (B + (1 / c + 1 / (c - 1)) + S) * (1 + |t|) := by ring

/-- A holomorphic `Φ` on `Re s > ½` agreeing with a Weil function on `Re s > σ₂` has real
coefficients. -/
theorem herglotz_conj_of_abscissa {lam : ℕ → ℝ} {Φ : ℂ → ℂ} {σ₂ : ℝ} (hσ₂ : 1 ≤ σ₂)
    (hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re})
    (hΦ : ∀ s : ℂ, σ₂ < s.re → Φ s = WeilHerglotz.weilFunction lam s) {s : ℂ}
    (hs : 1 / 2 < s.re) : Φ (conj s) = conj (Φ s) := by
  set U : Set ℂ := {z | 1 / 2 < z.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hUc : IsPreconnected U := (convex_halfSpace_re_gt (1 / 2)).isPreconnected
  set g : ℂ → ℂ := (starRingEnd ℂ) ∘ Φ ∘ (starRingEnd ℂ) with hg
  have hgd : DifferentiableOn ℂ g U := by
    intro z hz
    have hcz : conj z ∈ U := by simpa [hU] using hz
    have h := ((hΦd (conj z) hcz).differentiableAt (hUo.mem_nhds hcz)).conj_conj
    rw [Complex.conj_conj] at h
    exact h.differentiableWithinAt
  have h2 : ((σ₂ + 1 : ℝ) : ℂ) ∈ U := show (1 / 2 : ℝ) < ((σ₂ + 1 : ℝ) : ℂ).re by simp; linarith
  have heq : Φ =ᶠ[𝓝 ((σ₂ + 1 : ℝ) : ℂ)] g := by
    have hV : {z : ℂ | σ₂ < z.re} ∈ 𝓝 ((σ₂ + 1 : ℝ) : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by simp)
    filter_upwards [hV] with z hz
    have hz' : σ₂ < (conj z).re := by simpa using hz
    simp only [hg, Function.comp_apply]
    rw [hΦ z hz, hΦ _ hz', WeilSpectral.weilFunction_conj lam z, Complex.conj_conj]
  have hEq := (hΦd.analyticOnNhd hUo).eqOn_of_preconnected_of_eventuallyEq
    (hgd.analyticOnNhd hUo) hUc h2 heq
  have hcs : conj s ∈ U := by simpa [hU] using hs
  have := hEq hcs
  simp only [hg, Function.comp_apply, Complex.conj_conj] at this
  exact this

/-- **A Herglotz Weil function makes the weights full-cone Weil-positive, for any abscissa of
absolute convergence.**  If `Σ |lam(n)| n^{−σ} < ∞` for `σ > σ₂` and `Φ` is holomorphic with
`Re Φ ≥ 0` on `Re s > ½` and equal to the Weil function of `lam` on `Re s > σ₂`, then
`W_lam(f ⋆ f̃) ≥ 0` for every `C²` compactly supported `f`. -/
theorem weilPositiveFull_of_herglotz_abscissa {lam : ℕ → ℝ} {σ₂ : ℝ}
    (hsl : ∀ σ : ℝ, σ₂ < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ) {Φ : ℂ → ℂ}
    (hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re})
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hΦ : ∀ s : ℂ, σ₂ < s.re → Φ s = WeilHerglotz.weilFunction lam s) :
    WeilPositiveFull lam := by
  set σ₃ : ℝ := max σ₂ 1 with hσ₃
  have hσ₃1 : 1 ≤ σ₃ := le_max_right _ _
  have hΦ3 : ∀ s : ℂ, σ₃ < s.re → Φ s = WeilHerglotz.weilFunction lam s := fun s hs =>
    hΦ s ((le_max_left _ _).trans_lt hs)
  set c : ℝ := σ₃ + 1 with hcdef
  have hc : 3 / 2 ≤ c := by linarith
  have hsum : LSeriesSummable (WeilHerglotz.lamC lam) c := by
    refine Summable.of_norm_bounded (hsl c (by linarith [le_max_left σ₂ 1])) fun n => ?_
    rw [LSeries.norm_term_eq]
    split_ifs with h
    · positivity
    · simp only [WeilHerglotz.lamC]
      split_ifs with h2
      · have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
        rw [Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_re]
      · simp only [Complex.ofReal_zero, norm_zero, zero_div]
        positivity
  intro f hf hfc
  obtain ⟨A, hA0, hA⟩ := norm_weilFunction_le_at hc hsum
  rw [WeilLineAnyAbscissa.weilFullFunctional_weilTest_eq_line hc hsum hf hfc]
  exact re_lineIntegral_nonneg_of_herglotz_at (by linarith) (by linarith : σ₃ < c) hΦd hΦre
    (fun s hs => herglotz_conj_of_abscissa hσ₃1 hΦd hΦ3 hs) hΦ3 hA0 hA hf hfc

end RHTower.HerglotzBridgeAnyLine

end
