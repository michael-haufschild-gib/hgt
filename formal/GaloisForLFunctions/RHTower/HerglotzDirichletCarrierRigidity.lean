import GaloisForLFunctions.RHTower.HerglotzWeilPositiveBridge
import GaloisForLFunctions.RHTower.WeilConeCriticalZeroCarriedRigidity

/-!
# Herglotz Dirichlet series are not carried by the critical zeros of ζ

Let `Φ` be holomorphic on `Re s > ½` with `Re Φ ≥ 0`, and suppose that on `Re s ≥ 3/2` it is an
absolutely convergent Dirichlet series `Σ_{n≥1} a(n) n^{−s}` with real coefficients.

**Theorem** (`eq_zero_of_herglotz_dirichlet_criticalCarrier`).  If `Re Φ(s) → 0` as `s` tends to
every boundary point `½ + it` at which `ζ(½ + it) ≠ 0`, then `a = 0`.

So the boundary singularities of a nonzero Herglotz Dirichlet series cannot all sit at critical
zeros of `ζ`.

**Proof.**
* *Explicit formula for Herglotz functions* (`re_lineIntegral_eq_integral_spectralWeight`).  In the
  Herglotz–Riesz representation `Φ = ∫ K_sym dν + ic`, the real part of the line integral of
  `(H(s) + H(1 − s))Φ(s)` on `Re s = c₀`, for `k = f ⋆ f̃`, is
  `∫ ½(1 + γ²)(|f̂(γ)|² + |f̂(−γ)|²) dν`.  The point `ζ = 1` and the constant `ic` contribute purely
  imaginary amounts.
* On the Dirichlet side the same line integral is
  `2a(1)k(0) + Σ_{n≥2} a(n)n^{−½}(k(log n) + k(−log n))`.  So the symmetrised push-forward `μ` of
  `½(1 + γ²) dν` to the ordinates satisfies the spectral identity of the critical-zero uniqueness
  theorem `eq_zero_of_signedMeasure_criticalZeros_density`.
* *Support.*  Near a boundary point where `Re Φ → 0`, the Poisson lower bound
  `Re Φ(½ + ε + it) ≥ ν{|γ − t| ≤ ε}/(4ε)`, uniform smallness on compacta and a covering argument
  force `ν` to vanish on ordinates where `ζ ≠ 0`.  So `μ` is carried by the critical zeros, and the
  uniqueness theorem gives `a = 0`.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real ENNReal ComplexConjugate

noncomputable section

namespace RHTower.AtomDomination

open GaloisForLFunctions.HTGeometry Zeta23 Zeta23.WeilEF RHTower.WeilLineIntegral RHTower.WeilAtomic

/-! ## Line shifts on a general line -/

/-- `∫ (H(b + it) + H(1 − b − it)) dt` is real for an autocorrelation, `¾ < b ≤ 3/2`. -/
theorem im_integral_line_weilTest_of {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) {b : ℝ} (hb1 : 3 / 4 < b) (hb2 : b ≤ 3 / 2) :
    (∫ t : ℝ, (Hfn (EF.weilTest f f) (b + t * I) +
      Hfn (EF.weilTest f f) (1 - b - t * I))).im = 0 := by
  obtain ⟨D, -, hD⟩ := norm_Hfn_weilTest_le hf hfc
  have h := integral_line_shift_critical (EF.weilTest_contDiff hf hf.continuous hfc)
    (EF.weilTest_hasCompactSupport hfc hfc) hD (q := fun _ => 1) (differentiable_const 1)
    hb1 hb2 (fun σ t _ _ => by rw [norm_one]; linarith [abs_nonneg t])
  simp only [mul_one] at h
  have hpt : ∀ t : ℝ, Hfn (EF.weilTest f f) ((1 / 2 : ℝ) + t * I) +
      Hfn (EF.weilTest f f) ((1 / 2 : ℝ) - t * I) =
      ((‖paperFT f t‖ ^ 2 + ‖paperFT f (-t)‖ ^ 2 : ℝ) : ℂ) := by
    intro t
    rw [Hfn_weilTest_critical hf.continuous hfc, Hfn_weilTest_critical_neg hf.continuous hfc]
    push_cast
    ring
  rw [h, integral_congr_ae (Eventually.of_forall hpt)]
  rw [integral_complex_ofReal, Complex.ofReal_im]

/-- `∫ (H(b + it) + H(1 − b − it))(b − ½ + it) dt` is purely imaginary, `¾ < b ≤ 3/2`. -/
theorem re_integral_line_weilTest_linear_of {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) {b : ℝ} (hb1 : 3 / 4 < b) (hb2 : b ≤ 3 / 2) :
    (∫ t : ℝ, (Hfn (EF.weilTest f f) (b + t * I) +
      Hfn (EF.weilTest f f) (1 - b - t * I)) * ((b : ℂ) + t * I - 1 / 2)).re = 0 := by
  obtain ⟨D, -, hD⟩ := norm_Hfn_weilTest_le hf hfc
  have h := integral_line_shift_critical (EF.weilTest_contDiff hf hf.continuous hfc)
    (EF.weilTest_hasCompactSupport hfc hfc) hD (q := fun s => s - 1 / 2)
    (differentiable_id.sub_const _) hb1 hb2
    (fun σ t h1 h2 => by
      have e : (σ : ℂ) + t * I - 1 / 2 = ((σ - 1 / 2 : ℝ) : ℂ) + t * I := by push_cast; ring
      rw [e]
      refine (norm_add_le _ _).trans ?_
      rw [Complex.norm_real, norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
        Real.norm_eq_abs, Real.norm_eq_abs]
      have : |σ - 1 / 2| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
      linarith)
  rw [h]
  have hpt : ∀ t : ℝ, (Hfn (EF.weilTest f f) ((1 / 2 : ℝ) + t * I) +
      Hfn (EF.weilTest f f) ((1 / 2 : ℝ) - t * I)) * (((1 / 2 : ℝ) : ℂ) + t * I - 1 / 2) =
      I * ((t * (‖paperFT f t‖ ^ 2 + ‖paperFT f (-t)‖ ^ 2) : ℝ) : ℂ) := by
    intro t
    rw [Hfn_weilTest_critical hf.continuous hfc, Hfn_weilTest_critical_neg hf.continuous hfc]
    push_cast
    ring
  simp_rw [hpt]
  rw [integral_const_mul, integral_complex_ofReal, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

/-! ## The explicit formula for a Herglotz representation -/

/-- The spectral weight of a circle point `ζ = e^{iθ}`: `½(1 + γ²)(|f̂(γ)|² + |f̂(−γ)|²)` with
`iγ = (1 + ζ)/(1 − ζ)`, and `0` at `ζ = 1`. -/
def spectralWeight (f : ℝ → ℂ) (θ : ℝ) : ℝ :=
  if circleMap 0 1 θ = 1 then 0 else
    (1 + circleOrd (circleMap 0 1 θ) ^ 2) / 2 *
      (‖paperFT f (circleOrd (circleMap 0 1 θ))‖ ^ 2 +
        ‖paperFT f (-(circleOrd (circleMap 0 1 θ) : ℂ))‖ ^ 2)

/-- **The explicit formula for a Herglotz representation.**  If `Φ = ∫ K_sym dν + ic` on
`Re s > ½` and `|Φ(c₀ + it)| ≤ A(1 + |t|)` with `1 < c₀ ≤ 3/2`, then for every `C²` compactly
supported `f`, with `k = f ⋆ f̃`, the real part of `(1/2π) ∫ (H_k(c₀ + it) + H_k(1 − c₀ − it))
Φ(c₀ + it) dt` is `∫ spectralWeight f dν`. -/
theorem re_lineIntegral_eq_integral_spectralWeight {Φ : ℂ → ℂ} {ν : Measure ℝ}
    [IsFiniteMeasure ν] {c : ℝ}
    (hrep : ∀ s : ℂ, 1 / 2 < s.re → Φ s = (∫ θ, symKernel s (circleMap 0 1 θ) ∂ν) + c * I)
    {c₀ : ℝ} (hc1 : 1 < c₀) (hc2 : c₀ ≤ 3 / 2) {A : ℝ}
    (hA : ∀ t : ℝ, ‖Φ (c₀ + t * I)‖ ≤ A * (1 + |t|)) {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) :
    ((1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, (Hfn (EF.weilTest f f) (c₀ + t * I) +
      Hfn (EF.weilTest f f) (1 - c₀ - t * I)) * Φ (c₀ + t * I)).re =
      ∫ θ, spectralWeight f θ ∂ν := by
  set k : ℝ → ℂ := EF.weilTest f f with hk
  have hkd : ContDiff ℝ 2 k := EF.weilTest_contDiff hf hf.continuous hfc
  have hkc : HasCompactSupport k := EF.weilTest_hasCompactSupport hfc hfc
  obtain ⟨D, hD0, hD⟩ := norm_Hfn_weilTest_le hf hfc
  obtain ⟨Ck, hCk0, hCk⟩ := norm_Hfn_le hkd hkc
  have hA0 : 0 ≤ A := by
    have := (norm_nonneg _).trans (hA 0)
    simpa using this
  set F : ℝ → ℂ := fun t => Hfn k (c₀ + t * I) + Hfn k (1 - c₀ - t * I) with hF
  have hFb : ∀ t : ℝ, ‖F t‖ ≤ 2 * D / (1 + t ^ 2) ^ 2 := by
    intro t
    have e : (1 : ℂ) - c₀ - t * I = ((1 - c₀ : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I := by push_cast; ring
    refine (norm_add_le _ _).trans ?_
    rw [e]
    have h1 := hD c₀ t (by linarith) (by linarith)
    have h2 := hD (1 - c₀) (-t) (by linarith) (by linarith)
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
  set K : ℝ → ℝ → ℂ := fun t θ => symKernel (c₀ + t * I) (circleMap 0 1 θ) with hK
  have hKi : ∀ t, Integrable (K t) ν := fun t => integrable_diskSym (norm_discPt_lt_one (hs t))
  have hΦK : ∀ t : ℝ, Φ (c₀ + t * I) = (∫ θ, K t θ ∂ν) + c * I := fun t => hrep _ (hs t)
  set w : ℝ → ℝ := fun t => ‖((c₀ : ℂ) + t * I) - 1 / 2‖ / (c₀ - 1 / 2) with hw
  have hc12 : 0 < c₀ - 1 / 2 := by linarith
  have hw0 : ∀ t, 0 ≤ w t := fun t => div_nonneg (norm_nonneg _) hc12.le
  have hwb : ∀ t : ℝ, w t ≤ 2 * (1 + |t|) := by
    intro t
    simp only [hw]
    rw [div_le_iff₀ hc12]
    have e : ((c₀ : ℂ) + t * I) - 1 / 2 = ((c₀ - 1 / 2 : ℝ) : ℂ) + t * I := by push_cast; ring
    rw [e]
    calc ‖((c₀ - 1 / 2 : ℝ) : ℂ) + t * I‖ ≤ ‖((c₀ - 1 / 2 : ℝ) : ℂ)‖ + ‖(t : ℂ) * I‖ :=
          norm_add_le _ _
      _ = (c₀ - 1 / 2) + |t| := by
          rw [Complex.norm_real, norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
            Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hc12]
      _ ≤ 2 * (1 + |t|) * (c₀ - 1 / 2) := by nlinarith [abs_nonneg t]
  have hKn : ∀ t : ℝ, ∫ θ, ‖K t θ‖ ∂ν ≤ w t * ‖Φ (c₀ + t * I)‖ := by
    intro t
    have hpt : ∀ θ, ‖K t θ‖ ≤ w t * (K t θ).re := fun θ => by
      have := norm_symKernel_le (hs t) (norm_circleMap_one θ)
      rw [hre] at this
      exact this
    have hreI : ∫ θ, (K t θ).re ∂ν = (∫ θ, K t θ ∂ν).re := integral_re (hKi t)
    calc ∫ θ, ‖K t θ‖ ∂ν ≤ ∫ θ, w t * (K t θ).re ∂ν :=
          integral_mono (hKi t).norm ((hKi t).re.const_mul _) hpt
      _ = w t * (Φ (c₀ + t * I)).re := by
          rw [integral_const_mul, hreI, hΦK t, Complex.add_re]
          simp
      _ ≤ w t * ‖Φ (c₀ + t * I)‖ :=
          mul_le_mul_of_nonneg_left (Complex.re_le_norm _) (hw0 t)
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
  have hsplit : (∫ t : ℝ, F t * Φ (c₀ + t * I)) =
      (∫ θ, ∫ t, F t * K t θ ∂volume ∂ν) + (c * I) * ∫ t, F t := by
    have h1 : ∀ t, F t * Φ (c₀ + t * I) = (∫ θ, F t * K t θ ∂ν) + c * I * F t := by
      intro t
      rw [hΦK t, integral_const_mul]
      ring
    rw [integral_congr_ae (Eventually.of_forall h1),
      integral_add hgi.integral_prod_left (hFi.const_mul _), integral_const_mul]
    congr 1
    exact integral_integral_swap (f := fun t θ => F t * K t θ) hgi
  have hpi : (2 * Real.pi : ℂ) ≠ 0 := by
    have : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    exact mul_ne_zero two_ne_zero this
  have hJval : ∀ θ, (∫ t, F t * K t θ).re = 2 * Real.pi * spectralWeight f θ := by
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
      rw [e, re_integral_line_weilTest_linear_of hf hfc (by linarith) hc2, spectralWeight,
        if_pos h1, mul_zero]
    · set γ : ℝ := circleOrd ζ with hγ
      have hKt : ∀ t, K t θ =
          (1 + (γ : ℂ) ^ 2) / 2 * gPair (1 / 2 + γ * I) (c₀ + t * I) := fun t =>
        symKernel_eq (hs t) hζ h1
      have h2 : (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, F t * gPair (1 / 2 + γ * I) (c₀ + t * I) =
          Hfn k (1 / 2 + γ * I) + Hfn k (1 - (1 / 2 + γ * I)) :=
        two_line_pair (differentiable_Hfn hkd hkc) (c := c₀) (C := Ck)
          (fun σ t h1 h2 => hCk σ t (by linarith) (by linarith)) (z₀ := 1 / 2 + γ * I)
          (by simp; linarith) (by simp; linarith)
      have hHz : Hfn k (1 / 2 + γ * I) + Hfn k (1 - (1 / 2 + γ * I)) =
          ((‖paperFT f γ‖ ^ 2 + ‖paperFT f (-(γ : ℂ))‖ ^ 2 : ℝ) : ℂ) := by
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
          (2 * Real.pi : ℂ) * ((‖paperFT f γ‖ ^ 2 + ‖paperFT f (-(γ : ℂ))‖ ^ 2 : ℝ) : ℂ) := by
        rw [← hHz, ← h2, ← mul_assoc, mul_one_div_cancel hpi, one_mul]
      rw [e, hX]
      have hval : (1 + (γ : ℂ) ^ 2) / 2 * ((2 * Real.pi : ℂ) *
          ((‖paperFT f γ‖ ^ 2 + ‖paperFT f (-(γ : ℂ))‖ ^ 2 : ℝ) : ℂ)) =
          ((2 * Real.pi * ((1 + γ ^ 2) / 2 *
            (‖paperFT f γ‖ ^ 2 + ‖paperFT f (-(γ : ℂ))‖ ^ 2)) : ℝ) : ℂ) := by
        push_cast
        ring
      rw [hval, Complex.ofReal_re, spectralWeight, if_neg h1]
  have hFim : (∫ t, F t).im = 0 := im_integral_line_weilTest_of hf hfc (by linarith) hc2
  have hJi : Integrable (fun θ => ∫ t, F t * K t θ) ν := hgi.integral_prod_right
  have hJre' : ∫ θ, (∫ t, F t * K t θ).re ∂ν = (∫ θ, ∫ t, F t * K t θ ∂volume ∂ν).re :=
    integral_re hJi
  have hcI : ((c : ℂ) * I * ∫ t, F t).re = 0 := by
    simp [Complex.mul_re, hFim]
  rw [hsplit, show (1 / (2 * Real.pi) : ℂ) = ((1 / (2 * Real.pi) : ℝ) : ℂ) by push_cast; ring,
    Complex.re_ofReal_mul, Complex.add_re, hcI, add_zero, ← hJre']
  simp_rw [hJval]
  rw [integral_const_mul]
  field_simp

/-! ## The Dirichlet side -/

theorem norm_LSeries_line_le {a : ℕ → ℂ} {c : ℝ} (ha : LSeriesSummable a c) (t : ℝ) :
    ‖LSeries a (c + t * I)‖ ≤ ∑' n, ‖LSeries.term a c n‖ := by
  have hs : LSeriesSummable a ((c : ℂ) + t * I) :=
    (LSeriesSummable_iff_of_re_eq_re (by simp)).mpr ha
  unfold LSeries
  refine (norm_tsum_le_tsum_norm hs.norm).trans (le_of_eq (tsum_congr fun n => ?_))
  rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
  simp

theorem continuous_LSeries_line {a : ℕ → ℂ} {c : ℝ} (ha : LSeriesSummable a c) :
    Continuous fun t : ℝ => LSeries a (c + t * I) := by
  unfold LSeries
  refine continuous_tsum (u := fun n => ‖LSeries.term a c n‖) (fun n => ?_) ha.norm
    (fun n t => ?_)
  · rcases eq_or_ne n 0 with rfl | hn
    · simpa [LSeries.term_zero] using continuous_const
    · simp only [LSeries.term_of_ne_zero hn]
      refine continuous_const.div ?_ (fun t => ?_)
      · exact Continuous.const_cpow (by fun_prop) (Or.inl (by exact_mod_cast hn))
      · exact cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hn))
  · rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
    simp

/-- The prime sum of a real weight against the autocorrelation `g` of a real test, together with
its `n = 1` term: `Σ_{n≥1} a(n) n^{−½}(g(log n) + g(−log n)) = 2a(1)g(0) + Σ_{n≥2} …`. -/
theorem hasSum_densityPairing {a : ℕ → ℝ} {g : ℝ → ℝ} {x : ℝ}
    (h : HasSum (fun n : ℕ => a n / Real.sqrt n * (g (Real.log n) + g (-Real.log n))) x) :
    x = WeilSpectral.densityPairing (a 1) a g := by
  set u : ℕ → ℝ := fun n => a n / Real.sqrt n * (g (Real.log n) + g (-Real.log n)) with hu
  have hsplit : u = (fun n : ℕ => (if 2 ≤ n then a n / Real.sqrt n else 0) *
      (g (Real.log n) + g (-Real.log n))) + fun n : ℕ => if n = 1 then 2 * a 1 * g 0 else 0 := by
    funext n
    simp only [hu, Pi.add_apply]
    rcases (show n = 0 ∨ n = 1 ∨ 2 ≤ n by omega) with rfl | rfl | hn
    · simp
    · simp
      ring
    · rw [if_pos hn, if_neg (by omega), add_zero]
  have hs2 : Summable fun n : ℕ => if n = 1 then 2 * a 1 * g 0 else 0 :=
    (hasSum_ite_eq 1 (2 * a 1 * g 0)).summable
  have hs1 : Summable fun n : ℕ => (if 2 ≤ n then a n / Real.sqrt n else 0) *
      (g (Real.log n) + g (-Real.log n)) := by
    have := h.summable.sub hs2
    refine this.congr fun n => ?_
    rw [hsplit]
    simp
  rw [← h.tsum_eq, hsplit, Pi.add_def, hs1.tsum_add hs2, tsum_ite_eq,
    WeilSpectral.densityPairing, atomPairing]
  ring

/-- **The Dirichlet side.**  For a real weight `a` summable at `1 < c₀ ≤ 2` and a real `C²`
compactly supported `F`, `(1/2π) ∫ (H_k(c₀ + it) + H_k(1 − c₀ − it)) L_a(c₀ + it) dt` is the density
pairing `2a(1)k(0) + Σ_{n≥2} a(n)n^{−½}(k(log n) + k(−log n))`, `k = F ⋆ F̃`. -/
theorem lineIntegral_LSeries_weilTest_eq {a : ℕ → ℝ} {c₀ : ℝ} (hc1 : 1 < c₀) (hc2 : c₀ ≤ 2)
    (ha : LSeriesSummable (fun n => (a n : ℂ)) c₀) {F : ℝ → ℝ}
    (hF : ContDiff ℝ 2 fun u => (F u : ℂ)) (hFc : HasCompactSupport F) :
    (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ,
      (Hfn (EF.weilTest (fun u => (F u : ℂ)) (fun u => (F u : ℂ))) (c₀ + t * I) +
        Hfn (EF.weilTest (fun u => (F u : ℂ)) (fun u => (F u : ℂ))) (1 - c₀ - t * I)) *
          LSeries (fun n => (a n : ℂ)) (c₀ + t * I) =
      ((WeilSpectral.densityPairing (a 1) a (crossCorr F F) : ℝ) : ℂ) := by
  set f : ℝ → ℂ := fun u => (F u : ℂ) with hf
  have hfc : HasCompactSupport f := hFc.comp_left Complex.ofReal_zero
  set k := EF.weilTest f f with hk
  have hkd : ContDiff ℝ 2 k := EF.weilTest_contDiff hF hF.continuous hfc
  have hkc : HasCompactSupport k := EF.weilTest_hasCompactSupport hfc hfc
  set km : ℝ → ℂ := fun u => k (-u) with hkm
  have hkmd : ContDiff ℝ 2 km := hkd.comp contDiff_neg
  have hkmc : HasCompactSupport km := hkc.comp_homeomorph (Homeomorph.neg ℝ)
  have h1 := hasSum_prime_side_line hkd hkc ha
  have h2 := hasSum_prime_side_line hkmd hkmc ha
  set L : ℝ → ℂ := fun t => LSeries (fun n => (a n : ℂ)) (c₀ + t * I) with hL
  have hLc : Continuous L := continuous_LSeries_line ha
  set S := ∑' n, ‖LSeries.term (fun n => (a n : ℂ)) c₀ n‖ with hS
  have hLb : ∀ t, ‖L t‖ ≤ S := norm_LSeries_line_le ha
  have hS0 : 0 ≤ S := tsum_nonneg fun _ => norm_nonneg _
  have hint : ∀ {h : ℝ → ℂ}, ContDiff ℝ 2 h → HasCompactSupport h →
      Integrable (fun t : ℝ => Hfn h (c₀ + t * I) * L t) := by
    intro h hh hhc
    obtain ⟨C, hC0, hC⟩ := norm_Hfn_le hh hhc
    refine (integrable_inv_one_add_sq.const_mul (C * S)).mono'
      ((continuous_Hfn_line hh hhc c₀).mul hLc).aestronglyMeasurable
      (Eventually.of_forall fun t => ?_)
    rw [norm_mul]
    calc ‖Hfn h (c₀ + t * I)‖ * ‖L t‖ ≤ C / (1 + t ^ 2) * S :=
          mul_le_mul (hC c₀ t (by linarith) hc2) (hLb t) (norm_nonneg _) (by positivity)
      _ = C * S * (1 + t ^ 2)⁻¹ := by ring
  have hm : ∀ t : ℝ, Hfn k (1 - c₀ - t * I) = Hfn km (c₀ + t * I) := fun t => Hfn_mirror k c₀ t
  have hsum := h1.add h2
  have hval : (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ,
      (Hfn k (c₀ + t * I) + Hfn k (1 - c₀ - t * I)) * L t =
      (1 / (2 * Real.pi) : ℂ) * (∫ t : ℝ, Hfn k (c₀ + t * I) * L t) +
        (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, Hfn km (c₀ + t * I) * L t := by
    rw [← mul_add, ← integral_add (hint hkd hkc) (hint hkmd hkmc)]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only
    rw [hm t]
    ring
  have hreal : ∀ y : ℝ, k y = ((crossCorr F F y : ℝ) : ℂ) := fun y => weilTest_ofReal_eq F y
  have hsumR : HasSum (fun n : ℕ => a n / Real.sqrt n *
      (crossCorr F F (Real.log n) + crossCorr F F (-Real.log n)))
      ((1 / (2 * Real.pi) : ℂ) * (∫ t : ℝ, Hfn k (c₀ + t * I) * L t) +
        (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, Hfn km (c₀ + t * I) * L t).re := by
    have := Complex.hasSum_re hsum
    refine this.congr_fun fun n => ?_
    simp only [hkm, hreal]
    simp only [Complex.add_re, Complex.mul_re, Complex.div_ofReal_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.div_ofReal_im, mul_zero, sub_zero]
    ring
  have him : ((1 / (2 * Real.pi) : ℂ) * (∫ t : ℝ, Hfn k (c₀ + t * I) * L t) +
      (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, Hfn km (c₀ + t * I) * L t).im = 0 := by
    have := Complex.hasSum_im hsum
    rw [← this.tsum_eq]
    refine (tsum_congr fun n => ?_).trans tsum_zero
    simp only [hkm, hreal]
    simp
  rw [hval]
  apply Complex.ext
  · rw [Complex.ofReal_re]
    exact hasSum_densityPairing hsumR
  · rw [Complex.ofReal_im]
    exact him

/-! ## The ordinate measure -/

/-- The ordinate `γ` of the circle point `e^{iθ}`, `iγ = (1 + e^{iθ})/(1 − e^{iθ})`. -/
def angleOrd (θ : ℝ) : ℝ := circleOrd (circleMap 0 1 θ)

theorem measurable_angleOrd : Measurable angleOrd := by
  unfold angleOrd circleOrd
  exact Complex.measurable_im.comp ((measurable_const.add (continuous_circleMap 0 1).measurable).div
    (measurable_const.sub (continuous_circleMap 0 1).measurable))

theorem measurable_neg_angleOrd : Measurable fun θ => -angleOrd θ := measurable_angleOrd.neg

theorem measurableSet_circleMap_eq_one : MeasurableSet {θ : ℝ | circleMap 0 1 θ = 1} :=
  (isClosed_singleton.preimage (continuous_circleMap 0 1)).measurableSet

/-- The weight `½(1 + γ²)` away from `ζ = 1`. -/
def angleDensity (θ : ℝ) : ℝ≥0∞ :=
  if circleMap 0 1 θ = 1 then 0 else ENNReal.ofReal ((1 + angleOrd θ ^ 2) / 2)

theorem measurable_angleDensity : Measurable angleDensity := by
  unfold angleDensity
  exact Measurable.ite measurableSet_circleMap_eq_one measurable_const
    (ENNReal.measurable_ofReal.comp
      ((measurable_const.add (measurable_angleOrd.pow_const 2)).div_const 2))

/-- The symmetrised push-forward of `½(1 + γ²) dν` to the ordinates. -/
def ordinateMeasure (ν : Measure ℝ) : Measure ℝ :=
  (ν.withDensity angleDensity).map angleOrd +
    (ν.withDensity angleDensity).map (fun θ => -angleOrd θ)

theorem lintegral_ordinateMeasure (ν : Measure ℝ) {h : ℝ → ℝ≥0∞} (hh : Measurable h) :
    ∫⁻ r, h r ∂ordinateMeasure ν =
      ∫⁻ θ, angleDensity θ * (h (angleOrd θ) + h (-angleOrd θ)) ∂ν := by
  have hg1 : Measurable fun θ => h (angleOrd θ) := hh.comp measurable_angleOrd
  have hg2 : Measurable fun θ => h (-angleOrd θ) := hh.comp measurable_neg_angleOrd
  rw [ordinateMeasure, lintegral_add_measure, lintegral_map hh measurable_angleOrd,
    lintegral_map hh measurable_neg_angleOrd,
    lintegral_withDensity_eq_lintegral_mul _ measurable_angleDensity hg1,
    lintegral_withDensity_eq_lintegral_mul _ measurable_angleDensity hg2,
    ← lintegral_add_left (measurable_angleDensity.mul hg1)]
  congr 1
  funext θ
  simp only [Pi.mul_apply]
  ring

theorem integrable_inv_one_add_sq_ordinateMeasure (ν : Measure ℝ) [IsFiniteMeasure ν] :
    Integrable (fun r : ℝ => 1 / (1 + r ^ 2)) (ordinateMeasure ν) := by
  have hm : Measurable fun r : ℝ => 1 / (1 + r ^ 2) := by fun_prop
  refine ⟨hm.aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  have he : ∀ r : ℝ, ‖1 / (1 + r ^ 2)‖ₑ = ENNReal.ofReal (1 / (1 + r ^ 2)) := fun r => by
    rw [Real.enorm_eq_ofReal (by positivity)]
  simp_rw [he]
  have hmm : Measurable fun r : ℝ => ENNReal.ofReal (1 / (1 + r ^ 2)) :=
    ENNReal.measurable_ofReal.comp hm
  rw [lintegral_ordinateMeasure ν hmm]
  refine lt_of_le_of_lt (lintegral_mono (g := fun _ => 1) fun θ => ?_) ?_
  · unfold angleDensity
    split_ifs
    · simp
    · rw [neg_sq, ← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_one.mpr (le_of_eq ?_)
      field_simp
      ring
  · rw [lintegral_const, one_mul]
    exact measure_lt_top ν _

theorem measurable_spectralWeight {f : ℝ → ℂ} (hf : Continuous fun r : ℝ => paperFT f r) :
    Measurable (spectralWeight f) := by
  have hn : Continuous fun r : ℝ => paperFT f (-(r : ℂ)) := by
    refine (hf.comp continuous_neg).congr fun r => ?_
    simp [Function.comp, Complex.ofReal_neg]
  unfold spectralWeight
  refine Measurable.ite measurableSet_circleMap_eq_one measurable_const ?_
  have h1 : Measurable fun θ : ℝ => circleOrd (circleMap 0 1 θ) := measurable_angleOrd
  exact ((measurable_const.add (h1.pow_const 2)).div_const 2).mul
    (((hf.measurable.comp h1).norm.pow_const 2).add ((hn.measurable.comp h1).norm.pow_const 2))

theorem integral_norm_sq_ordinateMeasure (ν : Measure ℝ) {f : ℝ → ℂ}
    (hf : Continuous fun r : ℝ => paperFT f r) :
    ∫ r, ‖paperFT f r‖ ^ 2 ∂ordinateMeasure ν = ∫ θ, spectralWeight f θ ∂ν := by
  have hsw0 : ∀ θ, 0 ≤ spectralWeight f θ := fun θ => by
    unfold spectralWeight
    split_ifs
    · exact le_rfl
    · positivity
  have hm : Measurable fun r : ℝ => ‖paperFT f r‖ ^ 2 := (hf.norm.pow 2).measurable
  have hmm : Measurable fun r : ℝ => ENNReal.ofReal (‖paperFT f r‖ ^ 2) :=
    ENNReal.measurable_ofReal.comp hm
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun r => by positivity)
      hm.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hsw0)
      (measurable_spectralWeight hf).aestronglyMeasurable,
    lintegral_ordinateMeasure ν hmm]
  congr 1
  refine lintegral_congr fun θ => ?_
  unfold angleDensity spectralWeight angleOrd
  split_ifs
  · simp
  · rw [Complex.ofReal_neg, ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]

theorem ordinateMeasure_eq_zero {ν : Measure ℝ} {U : Set ℝ} (hUm : MeasurableSet U)
    (hU : ∀ r, -r ∈ U ↔ r ∈ U) (h0 : ν {θ | circleMap 0 1 θ ≠ 1 ∧ angleOrd θ ∈ U} = 0) :
    ordinateMeasure ν U = 0 := by
  have hsub : ∀ V : Set ℝ, (∀ θ ∈ V, angleOrd θ ∈ U) →
      (ν.withDensity angleDensity) V = 0 := by
    intro V hV
    rw [withDensity_apply_eq_zero' measurable_angleDensity.aemeasurable]
    refine measure_mono_null ?_ h0
    intro θ hθ
    refine ⟨?_, hV θ hθ.2⟩
    intro h1
    apply hθ.1
    simp [angleDensity, h1]
  rw [ordinateMeasure, Measure.add_apply, Measure.map_apply measurable_angleOrd hUm,
    Measure.map_apply measurable_neg_angleOrd hUm, hsub (angleOrd ⁻¹' U) (fun θ h => h),
    hsub ((fun θ => -angleOrd θ) ⁻¹' U) (fun θ h => (hU _).mp h), add_zero]

/-! ## Support of the ordinate measure -/

/-- A circle point other than `1` is the boundary point of its ordinate. -/
theorem eq_bdryPt_circleOrd {ζ : ℂ} (hζ : ‖ζ‖ = 1) (h1 : ζ ≠ 1) : ζ = bdryPt (circleOrd ζ) := by
  have hu := cayleyParam_eq hζ h1
  have hζ1 : (1 : ℂ) - ζ ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  have hden : 2 * (1 / 2 + (circleOrd ζ : ℂ) * I) + 1 ≠ 0 := bdry_two_mul_add_one_ne_zero _
  unfold bdryPt discPt
  rw [eq_div_iff hden, ← hu]
  field_simp
  ring

/-- **The Poisson lower bound.**  `ν{ζ ≠ 1, |γ − t| ≤ ε} ≤ 4ε Re Φ(½ + ε + it)`. -/
theorem measure_ordinate_ball_le {Φ : ℂ → ℂ} {ν : Measure ℝ} [IsFiniteMeasure ν] {c : ℝ}
    (hrep : ∀ s : ℂ, 1 / 2 < s.re → Φ s = (∫ θ, symKernel s (circleMap 0 1 θ) ∂ν) + c * I)
    (t : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ν {θ | circleMap 0 1 θ ≠ 1 ∧ |angleOrd θ - t| ≤ ε} ≤
      ENNReal.ofReal (4 * ε * (Φ ((1 / 2 : ℂ) + ε + t * I)).re) := by
  set s : ℂ := (1 / 2 : ℂ) + ε + t * I with hsdef
  have hsre : s.re = 1 / 2 + ε := by simp [hsdef]
  have hsim : s.im = t := by simp [hsdef]
  have hs : 1 / 2 < s.re := by rw [hsre]; linarith
  set A := {θ : ℝ | circleMap 0 1 θ ≠ 1 ∧ |angleOrd θ - t| ≤ ε} with hA
  have hAm : MeasurableSet A :=
    measurableSet_circleMap_eq_one.compl.inter
      (measurableSet_le (measurable_angleOrd.sub_const t).abs measurable_const)
  set g : ℝ → ℝ := fun θ => (symKernel s (circleMap 0 1 θ)).re with hg
  have hKi := integrable_diskSym (ν := ν) (norm_discPt_lt_one hs)
  have hgi : Integrable g ν := hKi.re
  have hg0 : ∀ θ, 0 ≤ g θ := fun θ => re_symKernel_nonneg hs (norm_circleMap_one θ)
  have hre : (Φ s).re = ∫ θ, g θ ∂ν := by
    have h : (∫ θ, symKernel s (circleMap 0 1 θ) ∂ν).re = ∫ θ, g θ ∂ν := (integral_re hKi).symm
    rw [hrep s hs, Complex.add_re]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero, Complex.ofReal_im,
      Complex.I_im, mul_one, sub_self, add_zero]
    exact h
  have hlow : ∀ θ ∈ A, 1 / (4 * ε) ≤ g θ := by
    intro θ hθ
    have hζ := norm_circleMap_one θ
    have hb := eq_bdryPt_circleOrd hζ hθ.1
    simp only [hg]
    rw [re_symKernel hζ]
    have hP2 : 0 ≤ poissonKernel 0 (discPt s) (conj (circleMap 0 1 θ)) := by
      rw [poissonKernel_conj_right]
      exact poissonKernel_circleMap_one_nonneg
        (by rw [Complex.norm_conj]; exact norm_discPt_lt_one hs) θ
    have hP1 : 1 / (2 * ε) ≤ poissonKernel 0 (discPt s) (circleMap 0 1 θ) := by
      rw [hb, poissonKernel_discPt_bdryPt hs, hsre, hsim]
      set γ := circleOrd (circleMap 0 1 θ)
      have hγ : |γ - t| ≤ ε := hθ.2
      have hsq : (t - γ) ^ 2 ≤ ε ^ 2 := by
        rw [← sq_abs, abs_sub_comm]
        exact pow_le_pow_left₀ (abs_nonneg _) hγ 2
      have e : (1 / 2 + ε - 1 / 2 : ℝ) = ε := by ring
      rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [sq_nonneg γ, mul_pos hε hε]
    have : 1 / (4 * ε) = (1 / (2 * ε)) / 2 := by field_simp; ring
    rw [this]
    linarith
  have h1 : ∫ θ in A, g θ ∂ν ≤ ∫ θ, g θ ∂ν :=
    setIntegral_le_integral hgi (Eventually.of_forall hg0)
  have h2 : ν.real A • (1 / (4 * ε)) ≤ ∫ θ in A, g θ ∂ν :=
    setIntegral_ge_of_const_le hAm (measure_ne_top ν A) hlow hgi.integrableOn
  rw [smul_eq_mul] at h2
  have h3 : ν.real A ≤ 4 * ε * (Φ s).re := by
    rw [hre]
    have := h2.trans h1
    rw [mul_one_div, div_le_iff₀ (by positivity)] at this
    linarith
  rw [← ENNReal.ofReal_toReal (measure_ne_top ν A)]
  exact ENNReal.ofReal_le_ofReal h3

/-- **Uniform smallness.**  If `Re Φ → 0` at every boundary point `½ + it`, `t ∈ U`, then on a
compact `[a, b] ⊆ U` it is uniformly small on `½ + ε + it`, `0 < ε ≤ ε₀`. -/
theorem exists_uniform_re_le {Φ : ℂ → ℂ} {U : Set ℝ} {a b : ℝ} (hab : Icc a b ⊆ U)
    (hlim : ∀ t ∈ U, Tendsto (fun s => (Φ s).re)
      (𝓝[{s : ℂ | 1 / 2 < s.re}] ((1 / 2 : ℂ) + t * I)) (𝓝 0))
    {η : ℝ} (hη : 0 < η) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ t ∈ Icc a b, ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      (Φ ((1 / 2 : ℂ) + (ε : ℂ) + t * I)).re ≤ η := by
  by_contra hcon
  push Not at hcon
  choose T hT E hE0 hE1 hE2 using fun n : ℕ => hcon (1 / ((n : ℝ) + 1)) (by positivity)
  obtain ⟨t₀, ht₀, φ, hφ, hlimT⟩ := isCompact_Icc.tendsto_subseq hT
  have hEφ : Tendsto (fun n => E (φ n)) atTop (𝓝 0) := by
    refine squeeze_zero (fun n => (hE0 _).le) (fun n => (hE1 (φ n)).trans ?_)
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hn : (n : ℝ) ≤ (φ n : ℝ) := by exact_mod_cast hφ.id_le n
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  have hseq : Tendsto (fun n => (1 / 2 : ℂ) + (E (φ n) : ℂ) + (T (φ n) : ℂ) * I) atTop
      (𝓝[{s : ℂ | 1 / 2 < s.re}] ((1 / 2 : ℂ) + t₀ * I)) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have h1 := (Complex.continuous_ofReal.tendsto 0).comp hEφ
      have h2 := (Complex.continuous_ofReal.tendsto t₀).comp hlimT
      have := (tendsto_const_nhds (x := (1 / 2 : ℂ))).add h1 |>.add (h2.mul_const I)
      simpa [Function.comp] using this
    · exact Eventually.of_forall fun n => by
        show (1 / 2 : ℝ) < ((1 / 2 : ℂ) + (E (φ n) : ℂ) + (T (φ n) : ℂ) * I).re
        simp
        exact hE0 (φ n)
  have hcomp := (hlim t₀ (hab ht₀)).comp hseq
  obtain ⟨n, hn⟩ := (hcomp.eventually (gt_mem_nhds hη)).exists
  exact absurd (hE2 (φ n)) (not_lt.mpr (le_of_lt hn))

/-- The ordinates of `ν` avoid every compact `[a, b] ⊆ U`. -/
theorem measure_ordinate_Icc_eq_zero {Φ : ℂ → ℂ} {ν : Measure ℝ} [IsFiniteMeasure ν] {c : ℝ}
    (hrep : ∀ s : ℂ, 1 / 2 < s.re → Φ s = (∫ θ, symKernel s (circleMap 0 1 θ) ∂ν) + c * I)
    {U : Set ℝ} (hlim : ∀ t ∈ U, Tendsto (fun s => (Φ s).re)
      (𝓝[{s : ℂ | 1 / 2 < s.re}] ((1 / 2 : ℂ) + t * I)) (𝓝 0))
    {a b : ℝ} (hab : Icc a b ⊆ U) :
    ν {θ | circleMap 0 1 θ ≠ 1 ∧ angleOrd θ ∈ Icc a b} = 0 := by
  set S := {θ | circleMap 0 1 θ ≠ 1 ∧ angleOrd θ ∈ Icc a b} with hSdef
  rcases lt_or_ge b a with hba | hab'
  · refine measure_mono_null (fun θ hθ => ?_) measure_empty
    exact absurd (hθ.2.1.trans hθ.2.2) (not_le.mpr hba)
  have hbound : ∀ η > 0, ν S ≤ ENNReal.ofReal ((2 * (b - a) + 8) * η) := by
    intro η hη
    obtain ⟨ε₀, hε₀, hunif⟩ := exists_uniform_re_le hab hlim hη
    set ε := min ε₀ 1 with hεdef
    have hε : 0 < ε := lt_min hε₀ one_pos
    have hε1 : ε ≤ 1 := min_le_right _ _
    set M : ℕ := ⌈(b - a) / (2 * ε)⌉₊ with hM
    set ctr : ℕ → ℝ := fun j => min (a + 2 * j * ε) b with hctr
    have hctr_mem : ∀ j, ctr j ∈ Icc a b := by
      intro j
      have h0 : (0 : ℝ) ≤ 2 * j * ε := by positivity
      exact ⟨le_min (by linarith) hab', min_le_right _ _⟩
    have hcover : S ⊆ ⋃ j ∈ Finset.range (M + 1),
        {θ | circleMap 0 1 θ ≠ 1 ∧ |angleOrd θ - ctr j| ≤ ε} := by
      intro θ hθ
      obtain ⟨h1, hγa, hγb⟩ := hθ
      set γ := angleOrd θ with hγ
      set x : ℝ := (γ - a) / (2 * ε) with hx
      have hx0 : 0 ≤ x := div_nonneg (by linarith) (by positivity)
      set j : ℕ := ⌊x + 1 / 2⌋₊ with hj
      have hj1 : (j : ℝ) ≤ x + 1 / 2 := Nat.floor_le (by linarith)
      have hj2 : x + 1 / 2 < (j : ℝ) + 1 := Nat.lt_floor_add_one _
      have hxM : x ≤ M := by
        refine le_trans ?_ (Nat.le_ceil _)
        exact div_le_div_of_nonneg_right (by linarith) (by positivity)
      have hjM : j < M + 1 := by
        have : (j : ℝ) < (M : ℝ) + 1 := by linarith
        exact_mod_cast this
      refine Set.mem_biUnion (Finset.mem_range.mpr hjM) ⟨h1, ?_⟩
      have hxe : x * (2 * ε) = γ - a := by rw [hx]; field_simp
      have hclose : |γ - (a + 2 * j * ε)| ≤ ε := by
        rw [abs_le]
        constructor <;> nlinarith
      show |γ - ctr j| ≤ ε
      by_cases hc : a + 2 * j * ε ≤ b
      · rw [hctr]
        simp only [min_eq_left hc]
        exact hclose
      · push Not at hc
        rw [hctr]
        simp only [min_eq_right hc.le]
        rw [abs_le] at hclose ⊢
        constructor <;> linarith [hclose.1]
    calc ν S ≤ ν (⋃ j ∈ Finset.range (M + 1),
          {θ | circleMap 0 1 θ ≠ 1 ∧ |angleOrd θ - ctr j| ≤ ε}) := measure_mono hcover
      _ ≤ ∑ j ∈ Finset.range (M + 1), ν {θ | circleMap 0 1 θ ≠ 1 ∧ |angleOrd θ - ctr j| ≤ ε} :=
          measure_biUnion_finset_le _ _
      _ ≤ ∑ j ∈ Finset.range (M + 1), ENNReal.ofReal (4 * ε * η) := by
          refine Finset.sum_le_sum fun j _ => (measure_ordinate_ball_le hrep (ctr j) hε).trans ?_
          exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
            (hunif (ctr j) (hctr_mem j) ε hε (min_le_left _ _)) (by positivity))
      _ = ENNReal.ofReal (((M : ℝ) + 1) * (4 * ε * η)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
            ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (M : ℝ) + 1)]
          congr 1
          rw [← ENNReal.ofReal_natCast, Nat.cast_add, Nat.cast_one]
      _ ≤ ENNReal.ofReal ((2 * (b - a) + 8) * η) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have hM1 : (M : ℝ) ≤ (b - a) / (2 * ε) + 1 := (Nat.ceil_lt_add_one (by
            exact div_nonneg (by linarith) (by positivity))).le
          have hMe : (M : ℝ) * (2 * ε) ≤ (b - a) + 2 * ε := by
            have := mul_le_mul_of_nonneg_right hM1 (by positivity : (0 : ℝ) ≤ 2 * ε)
            rw [add_mul, div_mul_cancel₀ _ (by positivity)] at this
            linarith
          nlinarith
  have hfin : ν S ≠ ⊤ := measure_ne_top ν S
  have hle : ∀ η > 0, (ν S).toReal ≤ (2 * (b - a) + 8) * η := fun η hη =>
    (ENNReal.toReal_le_of_le_ofReal (by nlinarith) (hbound η hη))
  have h0 : (ν S).toReal ≤ 0 := by
    refine le_of_forall_pos_le_add fun δ hδ => ?_
    have hC : 0 < 2 * (b - a) + 8 := by linarith
    have := hle (δ / (2 * (b - a) + 8)) (div_pos hδ hC)
    rw [mul_div_cancel₀ _ hC.ne'] at this
    linarith
  have := ENNReal.toReal_nonneg (a := ν S)
  rw [← ENNReal.ofReal_toReal hfin, show (ν S).toReal = 0 by linarith, ENNReal.ofReal_zero]

/-- The ordinates of `ν` avoid every open set on which `Re Φ` vanishes at the boundary. -/
theorem measure_ordinate_open_eq_zero {Φ : ℂ → ℂ} {ν : Measure ℝ} [IsFiniteMeasure ν] {c : ℝ}
    (hrep : ∀ s : ℂ, 1 / 2 < s.re → Φ s = (∫ θ, symKernel s (circleMap 0 1 θ) ∂ν) + c * I)
    {U : Set ℝ} (hU : IsOpen U) (hlim : ∀ t ∈ U, Tendsto (fun s => (Φ s).re)
      (𝓝[{s : ℂ | 1 / 2 < s.re}] ((1 / 2 : ℂ) + t * I)) (𝓝 0)) :
    ν {θ | circleMap 0 1 θ ≠ 1 ∧ angleOrd θ ∈ U} = 0 := by
  have hsub : {θ | circleMap 0 1 θ ≠ 1 ∧ angleOrd θ ∈ U} ⊆
      ⋃ p : ℚ × ℚ, {θ | circleMap 0 1 θ ≠ 1 ∧ angleOrd θ ∈ Icc (p.1 : ℝ) p.2 ∧
        Icc (p.1 : ℝ) p.2 ⊆ U} := by
    intro θ hθ
    obtain ⟨h1, hγ⟩ := hθ
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hU _ hγ
    obtain ⟨q1, hq1a, hq1b⟩ := exists_rat_btwn (show angleOrd θ - δ < angleOrd θ by linarith)
    obtain ⟨q2, hq2a, hq2b⟩ := exists_rat_btwn (show angleOrd θ < angleOrd θ + δ by linarith)
    refine Set.mem_iUnion.mpr ⟨(q1, q2), ?_⟩
    simp only [Set.mem_setOf_eq]
    refine ⟨h1, ⟨hq1b.le, hq2a.le⟩, fun r hr => hball ?_⟩
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hr.1, hr.2]
  refine measure_mono_null hsub (measure_iUnion_null fun p => ?_)
  by_cases hp : Icc (p.1 : ℝ) p.2 ⊆ U
  · refine measure_mono_null (fun θ hθ => ?_) (measure_ordinate_Icc_eq_zero hrep hlim hp)
    exact ⟨hθ.1, hθ.2.1⟩
  · refine measure_mono_null (fun θ hθ => ?_) measure_empty
    exact hp hθ.2.2

/-! ## The theorem -/

theorem LSeries_ofReal_conj (a : ℕ → ℝ) (s : ℂ) :
    LSeries (fun n => (a n : ℂ)) (conj s) = conj (LSeries (fun n => (a n : ℂ)) s) := by
  rw [LSeries, LSeries, Complex.conj_tsum]
  congr 1
  funext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term]
  · simp only [LSeries.term, hn, if_false, map_div₀, Complex.conj_ofReal,
      WeilSpectral.natCast_cpow_conj']

/-- A holomorphic `Φ` on `Re s > ½` equal to a real Dirichlet series on `Re s ≥ 3/2` has
`Φ(s̄) = conj Φ(s)`. -/
theorem conj_of_LSeries {Φ : ℂ → ℂ} {a : ℕ → ℝ}
    (hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re})
    (hΦ : ∀ s : ℂ, 3 / 2 ≤ s.re → Φ s = LSeries (fun n => (a n : ℂ)) s) {s : ℂ}
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
  have h2 : (2 : ℂ) ∈ U := show (1 / 2 : ℝ) < (2 : ℂ).re by norm_num
  have heq : Φ =ᶠ[𝓝 2] g := by
    have hV : {z : ℂ | 3 / 2 < z.re} ∈ 𝓝 (2 : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds
        (show (3 / 2 : ℝ) < (2 : ℂ).re by norm_num)
    filter_upwards [hV] with z hz
    have hz' : 3 / 2 < (conj z).re := by simpa using hz
    simp only [hg, Function.comp_apply]
    rw [hΦ z hz.le, hΦ _ hz'.le, LSeries_ofReal_conj, Complex.conj_conj]
  have hEq := (hΦd.analyticOnNhd hUo).eqOn_of_preconnected_of_eventuallyEq
    (hgd.analyticOnNhd hUo) hUc h2 heq
  have hcs : conj s ∈ U := by simpa [hU] using hs
  have := hEq hcs
  simp only [hg, Function.comp_apply, Complex.conj_conj] at this
  exact this

/-- **Herglotz Dirichlet series are not carried by the critical zeros of `ζ`.**  Let `Φ` be
holomorphic with `Re Φ ≥ 0` on `Re s > ½` and equal on `Re s ≥ 3/2` to `Σ_{n≥1} a(n) n^{−s}` with
real, absolutely summable (at `3/2`) coefficients.  If `Re Φ(s) → 0` as `s` tends to every
boundary point `½ + it` with `ζ(½ + it) ≠ 0`, then `a(n) = 0` for every `n ≥ 1`. -/
theorem eq_zero_of_herglotz_dirichlet_criticalCarrier {Φ : ℂ → ℂ} {a : ℕ → ℝ}
    (hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re})
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (ha : LSeriesSummable (fun n => (a n : ℂ)) (3 / 2))
    (hΦ : ∀ s : ℂ, 3 / 2 ≤ s.re → Φ s = LSeries (fun n => (a n : ℂ)) s)
    (hlim : ∀ t : ℝ, riemannZeta ((1 / 2 : ℂ) + t * I) ≠ 0 →
      Tendsto (fun s => (Φ s).re) (𝓝[{s : ℂ | 1 / 2 < s.re}] ((1 / 2 : ℂ) + t * I)) (𝓝 0)) :
    ∀ n, 1 ≤ n → a n = 0 := by
  obtain ⟨ν, hfin, c, hrep⟩ :=
    exists_herglotzRiesz_representation hΦd hΦre fun s hs => conj_of_LSeries hΦd hΦ hs
  have ha' : LSeriesSummable (fun n => (a n : ℂ)) ((3 / 2 : ℝ) : ℂ) := by
    simpa using ha
  set S := ∑' n, ‖LSeries.term (fun n => (a n : ℂ)) ((3 / 2 : ℝ) : ℂ) n‖ with hS
  have hS0 : 0 ≤ S := tsum_nonneg fun _ => norm_nonneg _
  have hA : ∀ t : ℝ, ‖Φ (((3 / 2 : ℝ) : ℂ) + t * I)‖ ≤ S * (1 + |t|) := fun t => by
    rw [hΦ _ (by simp)]
    exact (norm_LSeries_line_le ha' t).trans
      (le_mul_of_one_le_right hS0 (by linarith [abs_nonneg t]))
  have hrepF : ∀ F : ℝ → ℝ, ContDiff ℝ 2 (fun u => (F u : ℂ)) → HasCompactSupport F →
      WeilSpectral.densityPairing (a 1) a (crossCorr F F) =
        (∫ r, ‖paperFT (fun u => (F u : ℂ)) r‖ ^ 2 ∂ordinateMeasure ν) -
          ∫ r, ‖paperFT (fun u => (F u : ℂ)) r‖ ^ 2 ∂(0 : Measure ℝ) := by
    intro F hF hFc
    have hfc : HasCompactSupport (fun u => (F u : ℂ)) := hFc.comp_left Complex.ofReal_zero
    have hpc : Continuous fun r : ℝ => paperFT (fun u => (F u : ℂ)) r :=
      (differentiable_paperFT hF.continuous hfc).continuous.comp Complex.continuous_ofReal
    rw [integral_zero_measure, sub_zero, integral_norm_sq_ordinateMeasure ν hpc,
      ← re_lineIntegral_eq_integral_spectralWeight hrep (c₀ := 3 / 2) (by norm_num) le_rfl hA
        hF hfc]
    have hL := lineIntegral_LSeries_weilTest_eq (c₀ := 3 / 2) (by norm_num) (by norm_num) ha' hF
      hFc
    have hfun : (fun t : ℝ => (Hfn (EF.weilTest (fun u => (F u : ℂ)) (fun u => (F u : ℂ)))
        (((3 / 2 : ℝ) : ℂ) + t * I) + Hfn (EF.weilTest (fun u => (F u : ℂ))
          (fun u => (F u : ℂ))) (1 - ((3 / 2 : ℝ) : ℂ) - t * I)) *
          Φ (((3 / 2 : ℝ) : ℂ) + t * I)) = fun t : ℝ =>
        (Hfn (EF.weilTest (fun u => (F u : ℂ)) (fun u => (F u : ℂ)))
          (((3 / 2 : ℝ) : ℂ) + t * I) + Hfn (EF.weilTest (fun u => (F u : ℂ))
            (fun u => (F u : ℂ))) (1 - ((3 / 2 : ℝ) : ℂ) - t * I)) *
          LSeries (fun n => (a n : ℂ)) (((3 / 2 : ℝ) : ℂ) + t * I) := by
      funext t
      rw [hΦ _ (by simp)]
    rw [hfun, hL, Complex.ofReal_re]
  set U := {r : ℝ | riemannZeta ((1 / 2 : ℂ) + r * I) ≠ 0} with hUdef
  have hzc : Continuous fun r : ℝ => riemannZeta ((1 / 2 : ℂ) + r * I) := by
    refine continuous_iff_continuousAt.mpr fun r => ?_
    have hne : (1 / 2 : ℂ) + r * I ≠ 1 := by
      intro h
      have := congrArg Complex.re h
      norm_num at this
    exact (differentiableAt_riemannZeta hne).continuousAt.comp
      (f := fun r : ℝ => (1 / 2 : ℂ) + r * I) (by fun_prop)
  have hUo : IsOpen U := isOpen_ne_fun hzc continuous_const
  have hUsym : ∀ r : ℝ, -r ∈ U ↔ r ∈ U := by
    intro r
    have e : (1 / 2 : ℂ) + ((-r : ℝ) : ℂ) * I = conj ((1 / 2 : ℂ) + r * I) := by
      apply Complex.ext <;> simp
    simp only [hUdef, Set.mem_setOf_eq]
    rw [e, _root_.riemannZeta_conj, map_ne_zero]
  have hν0 := measure_ordinate_open_eq_zero hrep hUo fun t ht => hlim t ht
  have hcarried : ordinateMeasure ν U = 0 := ordinateMeasure_eq_zero hUo.measurableSet hUsym hν0
  have hw2 : Summable fun n : ℕ => |a n| / (n : ℝ) ^ 2 := by
    have hs := ha'.norm
    refine hs.of_nonneg_of_le (fun n => by positivity) fun n => ?_
    rw [LSeries.norm_term_eq]
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · rw [if_neg hn, Complex.norm_real, Real.norm_eq_abs]
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
      have : (n : ℝ) ^ (((3 / 2 : ℝ) : ℂ).re) ≤ (n : ℝ) ^ 2 := by
        rw [show (((3 / 2 : ℝ) : ℂ)).re = 3 / 2 by simp]
        calc (n : ℝ) ^ (3 / 2 : ℝ) ≤ (n : ℝ) ^ (2 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
          _ = (n : ℝ) ^ 2 := by norm_cast
      exact div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) this
  have hzero : (0 : Measure ℝ) {r : ℝ | riemannZeta ((1 / 2 : ℂ) + r * I) ≠ 0} = 0 := by simp
  obtain ⟨h1, h2⟩ := WeilSpectral.eq_zero_of_signedMeasure_criticalZeros_density hw2 hcarried
    hzero (integrable_inv_one_add_sq_ordinateMeasure ν) (integrable_zero_measure) hrepF
  intro n hn
  rcases eq_or_lt_of_le hn with rfl | hn2
  · exact h1
  · exact h2 n hn2

end RHTower.AtomDomination
