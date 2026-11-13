import GaloisForLFunctions.RHTower.HyperbolicOrbitalIntegral

/-!
# Horocyclic slices of nonnegative point-pair profiles

For a measurable profile `k : ℝ → [0, ∞]` the **Abel transform** is the integral along a horocycle,
`𝒜k(τ) = ∫ k(η²/4 + sinh²(τ/2)) dη` (`abelL`).  With `u(z, w) = |z − w|²/(4 Im z Im w)`:

* `∫ k(u(z, x + iy)) dx = √(Im z · y) 𝒜k(log y − log Im z)` (`lintegral_pairU_slice`);
* `∫_ℍ k(u(i, w)) (Im w)^σ dμ(w) = ∫ e^{(σ − ½)τ} 𝒜k(τ) dτ` (`lintegral_pairU_I_mul_rpow`);
* the horocycle integrals of `(k ⋆ k')(z, w) = ∫ k(u(z, ξ)) k'(u(ξ, w)) dμ(ξ)` are the
  convolutions of the Abel transforms (`lintegral_convK_slice`);
* `μ{w : u(i, w) ≤ U} ≤ 32 U` and `μ{w : u(i, w) ≤ δ} > 0` for `δ > 0`.

All statements are lower integrals, so no integrability hypotheses appear.
-/

open MeasureTheory Set Filter UpperHalfPlane
open scoped ENNReal

namespace GaloisForLFunctions.CompactHyperbolicSurfaces

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- The point `x + iy` of `ℍ`. -/
def hpt (x : ℝ) {y : ℝ} (hy : 0 < y) : ℍ := UpperHalfPlane.mk ⟨x, y⟩ hy

@[simp] theorem hpt_re (x : ℝ) {y : ℝ} (hy : 0 < y) : (hpt x hy).re = x := rfl
@[simp] theorem hpt_im (x : ℝ) {y : ℝ} (hy : 0 < y) : (hpt x hy).im = y := rfl

theorem continuous_hpt {y : ℝ} (hy : 0 < y) : Continuous fun x : ℝ => hpt x hy :=
  Continuous.subtype_mk (by fun_prop) _

theorem pairU_eq_coords (z w : ℍ) :
    pairU z w = ((z.re - w.re) ^ 2 + (z.im - w.im) ^ 2) / (4 * z.im * w.im) := by
  rw [pairU, Complex.dist_eq, Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  ring

theorem continuous_pairU : Continuous fun p : ℍ × ℍ => pairU p.1 p.2 := by
  have h : (fun p : ℍ × ℍ => pairU p.1 p.2) = fun p =>
      dist (p.1 : ℂ) (p.2 : ℂ) ^ 2 / (4 * p.1.im * p.2.im) := rfl
  rw [h]
  refine Continuous.div (by fun_prop) (by fun_prop) fun p => ?_
  have := p.1.im_pos; have := p.2.im_pos; positivity

theorem measurable_pairU : Measurable fun p : ℍ × ℍ => pairU p.1 p.2 :=
  continuous_pairU.measurable

/-- `(y − y')²/(4yy') = sinh²((log y − log y')/2)`. -/
theorem sq_sub_div_eq_sinh_sq' {y y' : ℝ} (hy : 0 < y) (hy' : 0 < y') :
    (y - y') ^ 2 / (4 * y * y') = Real.sinh ((Real.log y - Real.log y') / 2) ^ 2 := by
  have hs : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy
  have hs' : 0 < Real.sqrt y' := Real.sqrt_pos.mpr hy'
  have hlog : (Real.log y - Real.log y') / 2 = Real.log (Real.sqrt y) - Real.log (Real.sqrt y') := by
    rw [Real.log_sqrt hy.le, Real.log_sqrt hy'.le]; ring
  rw [hlog, Real.sinh_eq, Real.exp_sub, neg_sub, Real.exp_sub, Real.exp_log hs, Real.exp_log hs']
  have hy2 : Real.sqrt y ^ 2 = y := Real.sq_sqrt hy.le
  have hy2' : Real.sqrt y' ^ 2 = y' := Real.sq_sqrt hy'.le
  conv_lhs => rw [← hy2, ← hy2']
  field_simp
  ring

/-! ### The Abel transform -/

/-- The Abel transform of a nonnegative profile: `𝒜k(τ) = ∫ k(η²/4 + sinh²(τ/2)) dη`. -/
def abelL (k : ℝ → ℝ≥0∞) (τ : ℝ) : ℝ≥0∞ := ∫⁻ η : ℝ, k (η ^ 2 / 4 + Real.sinh (τ / 2) ^ 2)

theorem measurable_abelL {k : ℝ → ℝ≥0∞} (hk : Measurable k) : Measurable (abelL k) := by
  have : Measurable fun p : ℝ × ℝ => k (p.2 ^ 2 / 4 + Real.sinh (p.1 / 2) ^ 2) :=
    hk.comp (by fun_prop)
  exact this.lintegral_prod_right'

theorem abelL_neg (k : ℝ → ℝ≥0∞) (τ : ℝ) : abelL k (-τ) = abelL k τ := by
  simp only [abelL, neg_div, Real.sinh_neg, neg_sq]

/-- Scaling Lebesgue measure: `∫ f = c ∫ f(c ·)` for `c > 0`. -/
theorem lintegral_eq_ofReal_mul_lintegral_comp_mul (f : ℝ → ℝ≥0∞) {c : ℝ} (hc : 0 < c) :
    ∫⁻ x : ℝ, f x = ENNReal.ofReal c * ∫⁻ η : ℝ, f (c * η) := by
  have hmap := Real.map_volume_mul_left hc.ne'
  have h1 : ∫⁻ η : ℝ, f (c * η) = ∫⁻ x : ℝ, f x ∂(Measure.map (c * ·) volume) :=
    (lintegral_map_equiv f (Homeomorph.mulLeft₀ c hc.ne').toMeasurableEquiv).symm
  rw [h1, hmap, lintegral_smul_measure, smul_eq_mul, ← mul_assoc, ← ENNReal.ofReal_mul hc.le,
    abs_inv, abs_of_pos hc, mul_inv_cancel₀ hc.ne', ENNReal.ofReal_one, one_mul]

/-- **The horocyclic slice.**  `∫ k(u(z, x + iy)) dx = √(Im z · y) · 𝒜k(log y − log Im z)`. -/
theorem lintegral_pairU_slice (k : ℝ → ℝ≥0∞) (z : ℍ) {y : ℝ} (hy : 0 < y) :
    ∫⁻ x : ℝ, k (pairU z (hpt x hy)) =
      ENNReal.ofReal (Real.sqrt (z.im * y)) * abelL k (Real.log y - Real.log z.im) := by
  have hz := z.im_pos
  set c := Real.sqrt (z.im * y) with hcdef
  have hc : 0 < c := Real.sqrt_pos.mpr (mul_pos hz hy)
  have hc2 : c ^ 2 = z.im * y := Real.sq_sqrt (mul_pos hz hy).le
  have hfun : ∀ x : ℝ, k (pairU z (hpt x hy)) =
      (fun t : ℝ => k ((t ^ 2 + (z.im - y) ^ 2) / (4 * z.im * y))) (x + -z.re) := by
    intro x
    rw [pairU_eq_coords]
    simp only [hpt_re, hpt_im]
    congr 1; ring
  simp_rw [hfun]
  rw [lintegral_add_right_eq_self (fun t : ℝ => k ((t ^ 2 + (z.im - y) ^ 2) / (4 * z.im * y))),
    lintegral_eq_ofReal_mul_lintegral_comp_mul _ hc, abelL]
  congr 1
  refine lintegral_congr fun η => ?_
  congr 1
  rw [← sq_sub_div_eq_sinh_sq' hy hz]
  have h4 : 4 * z.im * y ≠ 0 := by positivity
  field_simp
  rw [show (c * η) ^ 2 = c ^ 2 * η ^ 2 by ring, hc2]
  ring

theorem lintegral_slice_pairU (k : ℝ → ℝ≥0∞) (z : ℍ) {y : ℝ} (hy : 0 < y) :
    ∫⁻ x : ℝ, k (pairU (hpt x hy) z) =
      ENNReal.ofReal (Real.sqrt (z.im * y)) * abelL k (Real.log y - Real.log z.im) := by
  simp_rw [pairU_comm _ z]
  exact lintegral_pairU_slice k z hy

/-- The exponential substitution `y = e^τ` on `(0, ∞)` for lower integrals. -/
theorem setLIntegral_Ioi_eq_lintegral_exp (g : ℝ → ℝ≥0∞) :
    ∫⁻ y in Ioi (0 : ℝ), g y = ∫⁻ τ : ℝ, ENNReal.ofReal (Real.exp τ) * g (Real.exp τ) := by
  have h := lintegral_image_eq_lintegral_abs_deriv_mul MeasurableSet.univ
    (fun τ _ => (Real.hasDerivAt_exp τ).hasDerivWithinAt) Real.exp_injective.injOn g
  rw [image_univ, Real.range_exp, Measure.restrict_univ] at h
  rw [h]
  exact lintegral_congr fun τ => by rw [abs_of_pos (Real.exp_pos τ)]

theorem sqrt_exp (τ : ℝ) : Real.sqrt (Real.exp τ) = Real.exp (τ / 2) := by
  rw [show τ = τ / 2 + τ / 2 by ring, Real.exp_add, Real.sqrt_mul_self (Real.exp_pos _).le]
  ring_nf

/-- `u(i, w)` in coordinates. -/
theorem pairU_I_eq (w : ℍ) : pairU I w = (w.re ^ 2 + (w.im - 1) ^ 2) / (4 * w.im) := by
  rw [pairU_eq_coords]
  simp only [UpperHalfPlane.I_re, UpperHalfPlane.I_im]
  ring

/-- The planar profile of `w ↦ u(i, w)`. -/
def pairUIc (w : ℂ) : ℝ := (w.re ^ 2 + (w.im - 1) ^ 2) / (4 * w.im)

theorem measurable_pairUIc : Measurable pairUIc := by
  unfold pairUIc; fun_prop

theorem pairUIc_coe (w : ℍ) : pairUIc (w : ℂ) = pairU I w := by
  rw [pairU_I_eq, pairUIc]; rfl

theorem pairUIc_mk (x : ℝ) {y : ℝ} (hy : 0 < y) : pairUIc ⟨x, y⟩ = pairU I (hpt x hy) := by
  rw [← pairUIc_coe]; rfl

/-- **Radial–height integrals.**  `∫_ℍ k(u(i, w)) H(Im w) dμ(w) = ∫ e^{−τ/2} H(e^τ) 𝒜k(τ) dτ`. -/
theorem lintegral_pairU_I_mul_im {k : ℝ → ℝ≥0∞} (hk : Measurable k) {H : ℝ → ℝ≥0∞}
    (hH : Measurable H) :
    ∫⁻ w : ℍ, k (pairU I w) * H w.im =
      ∫⁻ τ : ℝ, ENNReal.ofReal (Real.exp (-(τ / 2))) * H (Real.exp τ) * abelL k τ := by
  rw [RHTower.lintegral_upperHalfPlane_eq_iterated
    (Gc := fun w : ℂ => k (pairUIc w) * H w.im)
    ((hk.comp measurable_pairUIc).mul (hH.comp Complex.measurable_im))
    (fun z => by rw [pairUIc_coe]; rfl)]
  have hin : ∀ y ∈ Ioi (0 : ℝ), (∫⁻ x : ℝ, ENNReal.ofReal ((y ^ 2)⁻¹) *
      (k (pairUIc ⟨x, y⟩) * H ((⟨x, y⟩ : ℂ).im))) =
      ENNReal.ofReal ((y ^ 2)⁻¹ * Real.sqrt y) * H y * abelL k (Real.log y) := by
    intro y hy
    have hy : 0 < y := hy
    have e1 : ∀ x : ℝ, ENNReal.ofReal ((y ^ 2)⁻¹) *
        (k (pairUIc ⟨x, y⟩) * H ((⟨x, y⟩ : ℂ).im)) =
        (ENNReal.ofReal ((y ^ 2)⁻¹) * H y) * k (pairU I (hpt x hy)) := by
      intro x
      rw [pairUIc_mk x hy]
      ring
    simp_rw [e1]
    rw [lintegral_const_mul _ (hk.comp ((continuous_pairU.comp
      (continuous_const.prodMk (continuous_hpt hy))).measurable)), lintegral_pairU_slice k I hy]
    simp only [UpperHalfPlane.I_im, one_mul, Real.log_one, sub_zero]
    rw [ENNReal.ofReal_mul (by positivity)]
    ring
  rw [setLIntegral_congr_fun measurableSet_Ioi hin, setLIntegral_Ioi_eq_lintegral_exp]
  refine lintegral_congr fun τ => ?_
  rw [Real.log_exp, ← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos τ).le]
  congr 3
  rw [sqrt_exp, show ((Real.exp τ) ^ 2) = Real.exp (2 * τ) by rw [← Real.exp_nat_mul]; norm_num,
    ← Real.exp_neg, ← Real.exp_add, ← Real.exp_add]
  congr 1; ring

/-- **Weighted masses.**  `∫_ℍ k(u(i, w)) (Im w)^σ dμ(w) = ∫ e^{(σ − ½)τ} 𝒜k(τ) dτ`. -/
theorem lintegral_pairU_I_mul_rpow {k : ℝ → ℝ≥0∞} (hk : Measurable k) (σ : ℝ) :
    ∫⁻ w : ℍ, k (pairU I w) * ENNReal.ofReal (w.im ^ σ) =
      ∫⁻ τ : ℝ, ENNReal.ofReal (Real.exp ((σ - 1 / 2) * τ)) * abelL k τ := by
  rw [lintegral_pairU_I_mul_im hk (H := fun y => ENNReal.ofReal (y ^ σ)) (by fun_prop)]
  refine lintegral_congr fun τ => ?_
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, Real.rpow_def_of_pos (Real.exp_pos τ),
    Real.log_exp, ← Real.exp_add]
  congr 3; ring

/-- The mass of a profile: `∫_ℍ k(u(i, w)) dμ(w) = ∫ e^{−τ/2} 𝒜k(τ) dτ`. -/
theorem lintegral_pairU_I {k : ℝ → ℝ≥0∞} (hk : Measurable k) :
    ∫⁻ w : ℍ, k (pairU I w) = ∫⁻ τ : ℝ, ENNReal.ofReal (Real.exp (-(τ / 2))) * abelL k τ := by
  have h := lintegral_pairU_I_mul_im hk (H := fun _ => 1) measurable_const
  simp only [mul_one] at h
  exact h

/-! ### Convolution of point-pair profiles -/

/-- The convolution kernel `(k ⋆ k')(z, w) = ∫ k(u(z, ξ)) k'(u(ξ, w)) dμ(ξ)`. -/
def convK (k k' : ℝ → ℝ≥0∞) (z w : ℍ) : ℝ≥0∞ := ∫⁻ ξ : ℍ, k (pairU z ξ) * k' (pairU ξ w)

/-- **Horocycle integrals of a convolution.**
`∫ (k ⋆ k')(i, x + iy) dx = √y ∫ 𝒜k(σ) 𝒜k'(log y − σ) dσ`. -/
theorem lintegral_convK_slice {k k' : ℝ → ℝ≥0∞} (hk : Measurable k) (hk' : Measurable k')
    {y : ℝ} (hy : 0 < y) :
    ∫⁻ x : ℝ, convK k k' I (hpt x hy) =
      ENNReal.ofReal (Real.sqrt y) * ∫⁻ σ : ℝ, abelL k σ * abelL k' (Real.log y - σ) := by
  have hjoint : Measurable fun p : ℝ × ℍ => k (pairU I p.2) * k' (pairU p.2 (hpt p.1 hy)) := by
    refine (hk.comp ?_).mul (hk'.comp ?_)
    · exact (continuous_pairU.comp (continuous_const.prodMk continuous_snd)).measurable
    · exact (continuous_pairU.comp (continuous_snd.prodMk
        ((continuous_hpt hy).comp continuous_fst))).measurable
  unfold convK
  rw [lintegral_lintegral_swap hjoint.aemeasurable]
  have hin : ∀ ξ : ℍ, ∫⁻ x : ℝ, k (pairU I ξ) * k' (pairU ξ (hpt x hy)) =
      k (pairU I ξ) * (ENNReal.ofReal (Real.sqrt (ξ.im * y)) *
        abelL k' (Real.log y - Real.log ξ.im)) := by
    intro ξ
    rw [lintegral_const_mul _ (hk'.comp ((continuous_pairU.comp
      (continuous_const.prodMk (continuous_hpt hy))).measurable)), lintegral_pairU_slice k' ξ hy]
  simp_rw [hin]
  have hHm : Measurable fun η : ℝ => ENNReal.ofReal (Real.sqrt (η * y)) *
      abelL k' (Real.log y - Real.log η) :=
    (by fun_prop : Measurable fun η : ℝ => ENNReal.ofReal (Real.sqrt (η * y))).mul
      ((measurable_abelL hk').comp (by fun_prop))
  rw [lintegral_pairU_I_mul_im hk hHm, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun τ => ?_
  rw [Real.log_exp]
  have hr : Real.exp (-(τ / 2)) * Real.sqrt (Real.exp τ * y) = Real.sqrt y := by
    rw [Real.sqrt_mul (Real.exp_pos τ).le, sqrt_exp, ← mul_assoc, ← Real.exp_add]
    simp
  calc ENNReal.ofReal (Real.exp (-(τ / 2))) * (ENNReal.ofReal (Real.sqrt (Real.exp τ * y)) *
        abelL k' (Real.log y - τ)) * abelL k τ
      = ENNReal.ofReal (Real.exp (-(τ / 2)) * Real.sqrt (Real.exp τ * y)) *
          (abelL k τ * abelL k' (Real.log y - τ)) := by
        rw [ENNReal.ofReal_mul (Real.exp_pos _).le]; ring
    _ = _ := by rw [hr]

/-! ### Volumes of hyperbolic balls -/

theorem setOf_pairU_I_le_eq_preimage (U : ℝ) :
    {w : ℍ | pairU I w ≤ U} = (fun w => pairU I w) ⁻¹' Iic U := rfl

theorem measurableSet_pairU_le (z : ℍ) (U : ℝ) : MeasurableSet {w : ℍ | pairU z w ≤ U} :=
  measurableSet_le ((continuous_pairU.comp (continuous_const.prodMk continuous_id)).measurable)
    measurable_const

/-- `μ{w : u(i, w) ≤ U} ≤ 32 U`. -/
theorem volume_pairU_I_le {U : ℝ} (hU : 0 ≤ U) :
    volume {w : ℍ | pairU I w ≤ U} ≤ ENNReal.ofReal (32 * U) := by
  set k : ℝ → ℝ≥0∞ := (Iic U).indicator 1 with hkdef
  have hk : Measurable k := measurable_one.indicator measurableSet_Iic
  have hvol : volume {w : ℍ | pairU I w ≤ U} = ∫⁻ w : ℍ, k (pairU I w) := by
    rw [← lintegral_indicator_one (measurableSet_pairU_le I U)]
    rfl
  rw [hvol, lintegral_pairU_I hk]
  set f : ℝ → ℝ := fun τ => 2 * Real.sinh (τ / 2)
  set g : ℝ → ℝ≥0∞ := (Icc (-(2 * Real.sqrt U)) (2 * Real.sqrt U)).indicator 1
  have habel : ∀ τ, abelL k τ ≤ ENNReal.ofReal (4 * Real.sqrt U) * g (f τ) := by
    intro τ
    by_cases hτ : Real.sinh (τ / 2) ^ 2 ≤ U
    · have hg : g (f τ) = 1 := by
        refine indicator_of_mem ?_ _
        have h1 : |f τ| ≤ 2 * Real.sqrt U := by
          have := Real.abs_le_sqrt hτ
          simp only [f, abs_mul, abs_two]; linarith
        exact abs_le.mp h1
      rw [hg, mul_one]
      calc abelL k τ ≤ ∫⁻ η : ℝ, (Icc (-(2 * Real.sqrt U)) (2 * Real.sqrt U)).indicator 1 η := by
            refine lintegral_mono fun η => ?_
            by_cases hη : η ^ 2 / 4 + Real.sinh (τ / 2) ^ 2 ≤ U
            · have hmem : η ∈ Icc (-(2 * Real.sqrt U)) (2 * Real.sqrt U) := by
                have h2 : η ^ 2 ≤ 4 * U := by nlinarith [sq_nonneg (Real.sinh (τ / 2))]
                have h3 := Real.abs_le_sqrt h2
                rw [Real.sqrt_mul (by norm_num), show Real.sqrt 4 = 2 by
                  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] at h3
                exact abs_le.mp h3
              rw [indicator_of_mem hmem]
              simp only [k, indicator_apply, mem_Iic, hη, if_true, Pi.one_apply, le_refl]
            · simp only [k, indicator_apply, mem_Iic, hη, if_false, zero_le]
        _ = ENNReal.ofReal (4 * Real.sqrt U) := by
            rw [lintegral_indicator_one measurableSet_Icc, Real.volume_Icc]
            congr 1; ring
    · have h0 : abelL k τ = 0 := by
        refine lintegral_eq_zero_of_ae_eq_zero (Eventually.of_forall fun η => ?_)
        have : ¬ (η ^ 2 / 4 + Real.sinh (τ / 2) ^ 2 ≤ U) := by
          intro h; exact hτ (by nlinarith [sq_nonneg η])
        simp [k, indicator_apply, this]
      rw [h0]; exact zero_le _
  have hexp : ∀ τ : ℝ, ENNReal.ofReal (Real.exp (-(τ / 2))) ≤
      2 * ENNReal.ofReal |Real.cosh (τ / 2)| := by
    intro τ
    rw [abs_of_pos (Real.cosh_pos _), ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [Real.cosh_eq]
    have := Real.exp_pos (τ / 2)
    linarith
  have hcov : ∫⁻ τ : ℝ, ENNReal.ofReal |Real.cosh (τ / 2)| * g (f τ) = ∫⁻ v : ℝ, g v := by
    have hd : ∀ τ ∈ (univ : Set ℝ), HasDerivWithinAt f (Real.cosh (τ / 2)) univ τ := by
      intro τ _
      have := ((Real.hasDerivAt_sinh (τ / 2)).comp τ ((hasDerivAt_id τ).div_const 2)).const_mul 2
      refine (this.congr_deriv ?_).hasDerivWithinAt
      simp; ring
    have hinj : InjOn f univ := fun a _ b _ hab => by
      have : Real.sinh (a / 2) = Real.sinh (b / 2) := by simpa [f] using hab
      have := Real.sinh_injective this; linarith
    have hsurj : f '' univ = univ := by
      refine eq_univ_of_forall fun v => ⟨2 * Real.arsinh (v / 2), trivial, ?_⟩
      simp only [f]; rw [mul_div_cancel_left₀ _ two_ne_zero, Real.sinh_arsinh]; ring
    have h := lintegral_image_eq_lintegral_abs_deriv_mul MeasurableSet.univ hd hinj g
    rw [hsurj, Measure.restrict_univ, Measure.restrict_univ] at h
    exact h.symm
  calc ∫⁻ τ : ℝ, ENNReal.ofReal (Real.exp (-(τ / 2))) * abelL k τ
      ≤ ∫⁻ τ : ℝ, (2 * ENNReal.ofReal |Real.cosh (τ / 2)|) *
          (ENNReal.ofReal (4 * Real.sqrt U) * g (f τ)) :=
        lintegral_mono fun τ => mul_le_mul' (hexp τ) (habel τ)
    _ = (2 * ENNReal.ofReal (4 * Real.sqrt U)) *
          ∫⁻ τ : ℝ, ENNReal.ofReal |Real.cosh (τ / 2)| * g (f τ) := by
        rw [← lintegral_const_mul' _ _ (by simp [ENNReal.mul_eq_top])]
        refine lintegral_congr fun τ => ?_; ring
    _ = (2 * ENNReal.ofReal (4 * Real.sqrt U)) * ENNReal.ofReal (4 * Real.sqrt U) := by
        rw [hcov, lintegral_indicator_one measurableSet_Icc, Real.volume_Icc]
        congr 2; ring
    _ = ENNReal.ofReal (32 * U) := by
        rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        have := Real.mul_self_sqrt hU
        nlinarith

/-- Small hyperbolic balls have positive measure. -/
theorem volume_pairU_I_pos {δ : ℝ} (hδ : 0 < δ) : 0 < volume {w : ℍ | pairU I w ≤ δ} := by
  set r : ℝ := min (1 / 2) (Real.sqrt δ)
  have hr : 0 < r := lt_min (by norm_num) (Real.sqrt_pos.mpr hδ)
  have hsub : Metric.ball Complex.I r ⊆ (↑) '' {w : ℍ | pairU I w ≤ δ} := by
    intro z hz
    have hzI : ‖z - Complex.I‖ < r := by rwa [Metric.mem_ball, Complex.dist_eq] at hz
    have him : 1 / 2 < z.im := by
      have h1 : |z.im - 1| < r := by
        have := Complex.abs_im_le_norm (z - Complex.I)
        simp only [Complex.sub_im, Complex.I_im] at this; linarith
      have := min_le_left (1 / 2 : ℝ) (Real.sqrt δ)
      have := (abs_lt.mp h1).1; linarith
    refine ⟨⟨z, by linarith⟩, ?_, rfl⟩
    show pairU I ⟨z, _⟩ ≤ δ
    rw [pairU, Complex.dist_eq]
    simp only [UpperHalfPlane.I_im, UpperHalfPlane.coe_I, one_mul]
    have hn : ‖Complex.I - z‖ = ‖z - Complex.I‖ := norm_sub_rev _ _
    rw [hn]
    have hr2 : r ^ 2 ≤ δ := by
      have := min_le_right (1 / 2 : ℝ) (Real.sqrt δ)
      calc r ^ 2 ≤ Real.sqrt δ ^ 2 := pow_le_pow_left₀ hr.le this 2
        _ = δ := Real.sq_sqrt hδ.le
    have hz2 : ‖z - Complex.I‖ ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hzI.le 2
    have him' : (⟨z, by linarith⟩ : ℍ).im = z.im := rfl
    rw [him', div_le_iff₀ (by linarith)]
    nlinarith
  rw [volume_eq_lintegral]
  refine lt_of_lt_of_le ?_ (lintegral_mono_set hsub)
  rw [setLIntegral_pos_iff (by fun_prop)]
  have hsupp : Metric.ball Complex.I r ⊆ Function.support
      (fun z : ℂ => (((1 / ‖z.im‖₊) ^ 2 : NNReal) : ℝ≥0∞)) := by
    intro z hz
    have hzI : ‖z - Complex.I‖ < r := by rwa [Metric.mem_ball, Complex.dist_eq] at hz
    have him : 0 < z.im := by
      have h1 : |z.im - 1| < r := by
        have := Complex.abs_im_le_norm (z - Complex.I)
        simp only [Complex.sub_im, Complex.I_im] at this; linarith
      have := min_le_left (1 / 2 : ℝ) (Real.sqrt δ)
      have := (abs_lt.mp h1).1; linarith
    simp only [Function.mem_support, ne_eq, ENNReal.coe_eq_zero, pow_eq_zero_iff', one_div,
      inv_eq_zero, nnnorm_eq_zero, him.ne', not_false_eq_true, false_and, OfNat.ofNat_ne_zero]
  rw [inter_eq_right.mpr hsupp]
  exact Metric.measure_ball_pos _ _ hr

end

end GaloisForLFunctions.CompactHyperbolicSurfaces
