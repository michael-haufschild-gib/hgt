import GaloisForLFunctions.RHTower.SelbergTransformRealMonotone
import GaloisForLFunctions.RHTower.RepPointPairErgodic

/-!
# Holomorphic functions and the hyperbolic mean value

A holomorphic function `g` on `ℍ` is real-smooth and harmonic for the hyperbolic Laplacian:
`∂ₓ² g + ∂ᵧ² g = g'' + (i)² g'' = 0` (`positiveHyperbolicLaplacian_holomorphic`).  Selberg's theorem
at `s = 1` is then the **hyperbolic mean value property**
`∫_ℍ ψ(u(z, w)) g(w) dμ(w) = m_ψ g(z)` for every point-pair profile `ψ`
(`integral_kernel_mul_holomorphic`), and the Cauchy–Schwarz inequality turns it into the
sub-mean-value bound `m_ψ |g(z)|² ≤ ∫_ℍ ψ(u(z, w)) |g(w)|² dμ(w)` for `ψ ≥ 0`
(`mass_mul_normSq_le_holomorphic`).
-/

open UpperHalfPlane MeasureTheory Set Filter Topology
open scoped ContDiff

namespace GaloisForLFunctions.RHTower.RepPointPair

open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RHTower.DeckPointPair (selbergTransform integral_pairKernel_mul_eigen
  selbergTransform_one_eq_mass)

noncomputable section

/-- The open upper half-plane in `ℂ`. -/
theorem isOpen_im_pos : IsOpen {w : ℂ | 0 < w.im} := isOpen_lt continuous_const Complex.continuous_im

variable {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g {w : ℂ | 0 < w.im})

omit hg in
theorem chart_eventuallyEq_holomorphic {w : ℂ} (hw : 0 < w.im) :
    (fun z : ℍ => g z) ∘ ofComplex =ᶠ[𝓝 w] g := by
  filter_upwards [isOpen_im_pos.mem_nhds hw] with u hu
  simp [Function.comp_apply, ofComplex_apply_of_im_pos hu]

include hg in
/-- A holomorphic function on `ℍ` is real-`C²` in the chart. -/
theorem isRealSmooth_holomorphic : IsRealSmoothUpperHalfPlane (fun z : ℍ => g z) := by
  intro w hw
  have hc : ContDiffAt ℝ 2 g w :=
    ((hg.analyticAt (isOpen_im_pos.mem_nhds hw)).contDiffAt).restrict_scalars ℝ
  exact (hc.congr_of_eventuallyEq (chart_eventuallyEq_holomorphic hw)).contDiffWithinAt

include hg in
theorem fderiv_chart_holomorphic {w : ℂ} (hw : 0 < w.im) (v : ℂ) :
    fderiv ℝ ((fun z : ℍ => g z) ∘ ofComplex) w v = deriv g w * v := by
  rw [(chart_eventuallyEq_holomorphic hw).fderiv_eq]
  have hd : DifferentiableAt ℂ g w := hg.differentiableAt (isOpen_im_pos.mem_nhds hw)
  rw [hd.fderiv_restrictScalars ℝ]
  simp [mul_comm]

include hg in
/-- **Holomorphic functions are hyperbolic-harmonic.** -/
theorem positiveHyperbolicLaplacian_holomorphic (z : ℍ) :
    positiveHyperbolicLaplacian (fun z : ℍ => g z) z = 0 := by
  have hw : 0 < (z : ℂ).im := z.im_pos
  have hg' : DifferentiableOn ℂ (deriv g) {w : ℂ | 0 < w.im} := hg.deriv isOpen_im_pos
  have hd' : DifferentiableAt ℂ (deriv g) (z : ℂ) := hg'.differentiableAt (isOpen_im_pos.mem_nhds hw)
  have hfirst : ∀ v : ℂ, (fun u => fderiv ℝ ((fun z : ℍ => g z) ∘ ofComplex) u v) =ᶠ[𝓝 (z : ℂ)]
      fun u => deriv g u * v := by
    intro v
    filter_upwards [isOpen_im_pos.mem_nhds hw] with u hu
    exact fderiv_chart_holomorphic hg hu v
  have h2 : ∀ v : ℂ, fderiv ℝ (fun u => deriv g u * v) (z : ℂ) v = deriv (deriv g) z * v * v := by
    intro v
    have hdv : DifferentiableAt ℂ (fun u => deriv g u * v) (z : ℂ) := hd'.mul_const v
    rw [hdv.fderiv_restrictScalars ℝ]
    simp [deriv_mul_const_field]
    ring
  unfold positiveHyperbolicLaplacian
  rw [(hfirst 1).fderiv_eq, (hfirst Complex.I).fderiv_eq, h2, h2]
  simp only [mul_one, mul_assoc, Complex.I_mul_I]
  ring

include hg in
/-- **The hyperbolic mean value property** (Selberg's theorem at `s = 1`):
`∫_ℍ ψ(u(z, w)) g(w) dμ(w) = m_ψ g(z)`. -/
theorem integral_kernel_mul_holomorphic {ψ : ℝ → ℝ} {R : ℝ} (hψc : Continuous ψ)
    (hψR : KernelSupport ψ R) (z : ℍ) :
    ∫ w : ℍ, ((ψ (pairU z w) : ℝ) : ℂ) * g w = (kernelMassR ψ : ℂ) * g z := by
  have h := integral_pairKernel_mul_eigen hψc (kernelSupport_deck hψR)
    (isRealSmooth_holomorphic hg) (s := 1)
    (fun z => by rw [positiveHyperbolicLaplacian_holomorphic hg]; ring) z
  rw [h, selbergTransform_one_eq_mass hψc (kernelSupport_deck hψR), mul_comm]
  rfl


include hg in
theorem continuous_holomorphic : Continuous (fun w : ℍ => g w) :=
  hg.continuousOn.comp_continuous UpperHalfPlane.continuous_coe fun w => w.im_pos

include hg in
/-- **Sub-mean-value inequality**: for a nonnegative profile,
`m_ψ |g(z)|² ≤ ∫_ℍ ψ(u(z, w)) |g(w)|² dμ(w)`. -/
theorem mass_mul_normSq_le_holomorphic {ψ : ℝ → ℝ} {R : ℝ} (hψc : Continuous ψ)
    (hψ0 : ∀ u, 0 ≤ ψ u) (hψR : KernelSupport ψ R) (z : ℍ) :
    kernelMassR ψ * ‖g z‖ ^ 2 ≤ ∫ w : ℍ, ψ (pairU z w) * ‖g w‖ ^ 2 := by
  set a := ‖g z‖ with ha
  have ha0 : 0 ≤ a := norm_nonneg _
  have hm0 : 0 ≤ kernelMassR ψ := integral_nonneg fun w => hψ0 _
  have hgc := continuous_holomorphic hg
  have hi0 : Integrable (fun w : ℍ => ψ (pairU z w)) := by
    simpa using integrable_kernel_mul hψc hψR z (g := fun _ => (1 : ℝ)) continuous_const
  have hi1 : Integrable (fun w : ℍ => ψ (pairU z w) * ‖g w‖) := by
    simpa [smul_eq_mul] using integrable_kernel_mul hψc hψR z hgc.norm
  have hi2 : Integrable (fun w : ℍ => ψ (pairU z w) * ‖g w‖ ^ 2) := by
    simpa [smul_eq_mul] using integrable_kernel_mul hψc hψR z (hgc.norm.pow 2)
  have hmass : ∫ w : ℍ, ψ (pairU z w) = kernelMassR ψ := integral_pairU_eq (fun u => ψ u) z
  have h1 : kernelMassR ψ * a ≤ ∫ w : ℍ, ψ (pairU z w) * ‖g w‖ := by
    have h := norm_integral_le_integral_norm (μ := (volume : Measure ℍ))
      (fun w : ℍ => ((ψ (pairU z w) : ℝ) : ℂ) * g w)
    rw [integral_kernel_mul_holomorphic hg hψc hψR z, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hm0] at h
    refine h.trans (le_of_eq (integral_congr_ae (Eventually.of_forall fun w => ?_)))
    simp only
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hψ0 _)]
  have h2 : 0 ≤ ∫ w : ℍ, ψ (pairU z w) * (‖g w‖ - a) ^ 2 :=
    integral_nonneg fun w => mul_nonneg (hψ0 _) (sq_nonneg _)
  have e : ∀ w : ℍ, ψ (pairU z w) * (‖g w‖ - a) ^ 2 = ψ (pairU z w) * ‖g w‖ ^ 2 -
      2 * a * (ψ (pairU z w) * ‖g w‖) + a ^ 2 * ψ (pairU z w) := fun w => by ring
  simp_rw [e] at h2
  have hi21 : Integrable (fun w : ℍ => ψ (pairU z w) * ‖g w‖ ^ 2 -
      2 * a * (ψ (pairU z w) * ‖g w‖)) := hi2.sub (hi1.const_mul _)
  rw [integral_add hi21 (hi0.const_mul _), integral_sub hi2 (hi1.const_mul _),
    integral_const_mul, integral_const_mul, hmass] at h2
  nlinarith


/-! ## The local energy estimate -/

/-- The bump profile: `1` on `[0, a]`, `0` beyond `a + 1`, linear in between. -/
def bumpProfile (a : ℝ) (u : ℝ) : ℝ := min 1 (max 0 (a + 1 - u))

theorem continuous_bumpProfile (a : ℝ) : Continuous (bumpProfile a) := by
  unfold bumpProfile
  fun_prop

theorem bumpProfile_nonneg (a u : ℝ) : 0 ≤ bumpProfile a u := le_min zero_le_one (le_max_left _ _)

theorem bumpProfile_le_one (a u : ℝ) : bumpProfile a u ≤ 1 := min_le_left _ _

theorem bumpProfile_eq_one {a u : ℝ} (h : u ≤ a) : bumpProfile a u = 1 := by
  unfold bumpProfile
  rw [max_eq_right (by linarith), min_eq_left (by linarith)]

theorem kernelSupport_bumpProfile (a : ℝ) : KernelSupport (bumpProfile a) (a + 1) := by
  intro u hu
  unfold bumpProfile
  rw [max_eq_left (by linarith), min_eq_right zero_le_one]

theorem abs_bumpProfile_le (a u : ℝ) : |bumpProfile a u| ≤ 1 := by
  rw [abs_of_nonneg (bumpProfile_nonneg a u)]
  exact bumpProfile_le_one a u

/-- The bump at `0` has positive kernel mass. -/
theorem kernelMassR_bumpProfile_pos : 0 < kernelMassR (bumpProfile 0) := by
  have h := DeckPointPair.selbergRealTransform_pos (continuous_bumpProfile 0)
    (bumpProfile_nonneg 0) (kernelSupport_deck (kernelSupport_bumpProfile 0))
    ⟨0, le_refl 0, by rw [bumpProfile_eq_one (le_refl 0)]; norm_num⟩ 1
  rwa [DeckPointPair.selbergRealTransform_one_eq_mass (continuous_bumpProfile 0)
    (kernelSupport_deck (kernelSupport_bumpProfile 0))] at h

/-- Heights and distances along the Euclidean segment between near points. -/
theorem segment_bounds {R : ℝ} {z w : ℍ} (h : pairU z w ≤ R) {ζ : ℂ}
    (hζ : ζ ∈ segment ℝ (z : ℂ) (w : ℂ)) :
    z.im / (4 * R + 2) ≤ ζ.im ∧ dist (z : ℂ) ζ ^ 2 ≤ 4 * (4 * R + 2) * R * z.im ^ 2 := by
  have hR : 0 ≤ R := (pairU_nonneg _ _).trans h
  obtain ⟨hlow, -, -⟩ := pairU_le_bounds h
  have hy := z.im_pos
  have hy' := w.im_pos
  have hQ : 0 < 4 * R + 2 := by linarith
  have hzw : dist (z : ℂ) w ^ 2 ≤ 4 * (4 * R + 2) * R * z.im ^ 2 := by
    have hup := (pairU_le_bounds h).2.1
    have e : dist (z : ℂ) w ^ 2 = 4 * z.im * w.im * pairU z w := by
      unfold pairU
      field_simp
    rw [e]
    have : w.im * pairU z w ≤ (4 * R + 2) * z.im * R :=
      mul_le_mul hup h (pairU_nonneg _ _) (by positivity)
    nlinarith
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hζ
  have hzlow : z.im / (4 * R + 2) ≤ z.im := div_le_self hy.le (by linarith)
  refine ⟨?_, ?_⟩
  · simp only [Complex.add_im, Complex.real_smul, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero, UpperHalfPlane.coe_im]
    nlinarith
  · refine le_trans ?_ hzw
    rw [Complex.dist_eq, Complex.dist_eq]
    have e : (z : ℂ) - (a • (z : ℂ) + b • (w : ℂ)) = b • ((z : ℂ) - w) := by
      rw [show a = 1 - b by linarith]
      simp only [Complex.real_smul]
      push_cast
      ring
    rw [e, norm_smul, Real.norm_eq_abs, abs_of_nonneg hb, mul_pow]
    have hb1 : b ≤ 1 := by linarith
    have : b ^ 2 ≤ 1 := by nlinarith
    nlinarith [sq_nonneg ‖(z : ℂ) - w‖]

/-- `u(z, η) ≤ (cosh (d₁ + d₂) − 1)/2` from `d(z, ζ) ≤ d₁` and `u(ζ, η) ≤ R'`. -/
theorem pairU_le_of_dist_add {z ζ η : ℍ} {d₁ R' : ℝ} (h1 : dist z ζ ≤ d₁) (h2 : pairU ζ η ≤ R') :
    pairU z η ≤ (Real.cosh (d₁ + (1 + 2 * R')) - 1) / 2 := by
  have h2' : dist ζ η ≤ 1 + 2 * R' := DeckPointPair.dist_le_of_pairU_le h2
  have h3 : dist z η ≤ d₁ + (1 + 2 * R') := (dist_triangle _ _ _).trans (add_le_add h1 h2')
  rw [pairU_eq_cosh]
  have : Real.cosh (dist z η) ≤ Real.cosh (d₁ + (1 + 2 * R')) := by
    rw [Real.cosh_le_cosh, abs_of_nonneg dist_nonneg, abs_of_nonneg (dist_nonneg.trans h3)]
    exact h3
  linarith

/-- **The local energy estimate.**  For every `R ≥ 0` there are `C ≥ 0` and `R₂` such that, for every
holomorphic `g` on `ℍ` and every pair with `u(z, w) ≤ R`,
`|g(w) − g(z)|² ≤ C ∫_ℍ β_{R₂}(u(z, η)) (Im η)² |g'(η)|² dμ(η)` with the bump `β_{R₂}`. -/
theorem exists_normSq_sub_le_energy (R : ℝ) : ∃ C R₂ : ℝ, 0 ≤ C ∧
    ∀ g : ℂ → ℂ, DifferentiableOn ℂ g {w : ℂ | 0 < w.im} → ∀ z w : ℍ, pairU z w ≤ R →
      ‖g w - g z‖ ^ 2 ≤ C * ∫ η : ℍ, bumpProfile R₂ (pairU z η) *
        (η.im ^ 2 * ‖deriv g η‖ ^ 2) := by
  set m₁ := kernelMassR (bumpProfile 0)
  have hm₁ := kernelMassR_bumpProfile_pos
  set Q := 4 * R + 2
  set R₁ := Q * (4 * Q * R) / 4
  set R₂ := (Real.cosh ((1 + 2 * R₁) + (1 + 2 * 1)) - 1) / 2
  refine ⟨4 * |Q| * |R| * (6 * Q) ^ 2 / m₁, R₂, div_nonneg (by positivity) hm₁.le,
    fun g hg z w h => ?_⟩
  have hR : 0 ≤ R := (pairU_nonneg _ _).trans h
  have hQ : 0 < Q := by positivity
  have hy := z.im_pos
  set J := ∫ η : ℍ, bumpProfile R₂ (pairU z η) * (η.im ^ 2 * ‖deriv g η‖ ^ 2)
  have hg' : DifferentiableOn ℂ (deriv g) {w : ℂ | 0 < w.im} := hg.deriv isOpen_im_pos
  have hJ0 : 0 ≤ J := integral_nonneg fun η =>
    mul_nonneg (bumpProfile_nonneg _ _) (by positivity)
  -- a pointwise bound for `g'` on the segment
  have hpt : ∀ ζ ∈ segment ℝ (z : ℂ) (w : ℂ),
      ‖deriv g ζ‖ ≤ Real.sqrt ((6 * Q) ^ 2 / (m₁ * z.im ^ 2) * J) := by
    intro ζ hζ
    obtain ⟨hζlow, hζd⟩ := segment_bounds h hζ
    have hζpos : 0 < ζ.im := lt_of_lt_of_le (by positivity) hζlow
    set ζh : ℍ := ⟨ζ, hζpos⟩
    have hsub := mass_mul_normSq_le_holomorphic hg' (continuous_bumpProfile 0)
      (bumpProfile_nonneg 0) (kernelSupport_bumpProfile 0) ζh
    -- compare the bump at `ζ` with the bump of radius `R₂` at `z`
    have hdzζ : dist z ζh ≤ 1 + 2 * R₁ := by
      refine DeckPointPair.dist_le_of_pairU_le (R := R₁) ?_
      unfold pairU
      have hyζ : 0 < ζh.im := hζpos
      rw [div_le_iff₀ (by positivity)]
      have : z.im / Q ≤ ζh.im := hζlow
      calc dist (z : ℂ) (ζh : ℂ) ^ 2 ≤ 4 * Q * R * z.im ^ 2 := hζd
        _ ≤ R₁ * (4 * z.im * ζh.im) := by
          have hzq : z.im ≤ Q * ζh.im := by
            rw [div_le_iff₀ hQ] at this
            linarith
          simp only [R₁]
          nlinarith [mul_le_mul_of_nonneg_left hzq (by positivity : (0:ℝ) ≤ 4 * Q * R * z.im)]
    have hcmp : ∀ η : ℍ, bumpProfile 0 (pairU ζh η) * ‖deriv g η‖ ^ 2 ≤
        (6 * Q) ^ 2 / z.im ^ 2 *
          (bumpProfile R₂ (pairU z η) * (η.im ^ 2 * ‖deriv g η‖ ^ 2)) := by
      intro η
      by_cases hη : pairU ζh η ≤ 1
      · have hlowη := (pairU_le_bounds hη).1
        have hηim : z.im / (6 * Q) ≤ η.im := by
          have : z.im / Q / (4 * 1 + 2) ≤ ζh.im / (4 * 1 + 2) :=
            div_le_div_of_nonneg_right hζlow (by norm_num)
          calc z.im / (6 * Q) = z.im / Q / (4 * 1 + 2) := by field_simp; ring
            _ ≤ _ := this
            _ ≤ η.im := hlowη
        rw [bumpProfile_eq_one (pairU_le_of_dist_add hdzζ hη)]
        have hb := bumpProfile_le_one 0 (pairU ζh η)
        have hyη : 1 ≤ (6 * Q) ^ 2 / z.im ^ 2 * η.im ^ 2 := by
          rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity), one_mul]
          have h6 : z.im ≤ 6 * Q * η.im := by
            rw [div_le_iff₀ (by positivity)] at hηim
            linarith
          nlinarith [mul_le_mul h6 h6 hy.le (by positivity)]
        calc bumpProfile 0 (pairU ζh η) * ‖deriv g η‖ ^ 2 ≤ 1 * ‖deriv g η‖ ^ 2 :=
              mul_le_mul_of_nonneg_right hb (sq_nonneg _)
          _ ≤ ((6 * Q) ^ 2 / z.im ^ 2 * η.im ^ 2) * ‖deriv g η‖ ^ 2 :=
              mul_le_mul_of_nonneg_right hyη (sq_nonneg _)
          _ = _ := by ring
      · push Not at hη
        rw [kernelSupport_bumpProfile 0 _ (by linarith), zero_mul]
        exact mul_nonneg (by positivity)
          (mul_nonneg (bumpProfile_nonneg _ _) (by positivity))
    have hint1 : Integrable (fun η : ℍ => bumpProfile 0 (pairU ζh η) * ‖deriv g η‖ ^ 2) := by
      simpa [smul_eq_mul] using integrable_kernel_mul (continuous_bumpProfile 0)
        (kernelSupport_bumpProfile 0) ζh ((continuous_holomorphic hg').norm.pow 2)
    have hint2 : Integrable (fun η : ℍ => bumpProfile R₂ (pairU z η) *
        (η.im ^ 2 * ‖deriv g η‖ ^ 2)) := by
      simpa [smul_eq_mul] using integrable_kernel_mul (continuous_bumpProfile R₂)
        (kernelSupport_bumpProfile R₂) z
        ((UpperHalfPlane.continuous_im.pow 2).mul ((continuous_holomorphic hg').norm.pow 2))
    have hle : ∫ η : ℍ, bumpProfile 0 (pairU ζh η) * ‖deriv g η‖ ^ 2 ≤
        (6 * Q) ^ 2 / z.im ^ 2 * J := by
      rw [← integral_const_mul]
      exact integral_mono hint1 (hint2.const_mul _) hcmp
    have hsq : ‖deriv g ζ‖ ^ 2 ≤ (6 * Q) ^ 2 / (m₁ * z.im ^ 2) * J := by
      have : m₁ * ‖deriv g ζ‖ ^ 2 ≤ (6 * Q) ^ 2 / z.im ^ 2 * J := hsub.trans hle
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)] at this
      nlinarith
    exact Real.le_sqrt_of_sq_le hsq
  -- the mean value inequality along the segment
  have hmvi := (convex_segment (z : ℂ) (w : ℂ)).norm_image_sub_le_of_norm_deriv_le
    (f := g) (fun ζ hζ => hg.differentiableAt (isOpen_im_pos.mem_nhds
      (lt_of_lt_of_le (by positivity) (segment_bounds h hζ).1))) hpt
    (left_mem_segment ℝ _ _) (right_mem_segment ℝ _ _)
  have hzw := (segment_bounds h (right_mem_segment ℝ (z : ℂ) (w : ℂ))).2
  rw [Complex.dist_eq] at hzw
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hmvi 2
  rw [mul_pow, Real.sq_sqrt (by positivity), norm_sub_rev (w : ℂ)] at hsq
  refine hsq.trans ?_
  rw [abs_of_nonneg hR, abs_of_pos hQ]
  calc (6 * Q) ^ 2 / (m₁ * z.im ^ 2) * J * ‖(z : ℂ) - w‖ ^ 2
      ≤ (6 * Q) ^ 2 / (m₁ * z.im ^ 2) * J * (4 * (4 * R + 2) * R * z.im ^ 2) :=
        mul_le_mul_of_nonneg_left hzw (by positivity)
    _ = 4 * Q * R * (6 * Q) ^ 2 / m₁ * J := by
        simp only [Q]
        field_simp

end

end GaloisForLFunctions.RHTower.RepPointPair
