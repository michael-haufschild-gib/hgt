import GaloisForLFunctions.HTGeometry.DecreasingSineTransformPositivity
import GaloisForLFunctions.HTGeometry.StieltjesPrincipalValueBoundary

/-!
# The one-sided connection of a decreasing source as a Stieltjes transform

Let `k` be differentiable, strictly decreasing on `[0, ∞)`, integrable with its first moment on
`(0, ∞)`, and tending to zero.  Put `ω = -k' ≥ 0` on `(0, ∞)` and

`h(z) = ∫₀^∞ k(x) e^{izx} dx`,   `σ(t) = (1/(π√t)) ∫₀^∞ ω(x) (1 - cos(√t x)) dx`.

* Integration by parts gives `h(w) = (i/w) ∫₀^∞ ω(x) (1 - e^{iwx}) dx` for `Im w ≥ 0`, so
  `σ(u²) = Im h(u)/π = (1/π) ∫₀^∞ k(x) sin(ux) dx > 0`, with `σ(t) ≤ 2k(0)/(π√t)` and
  `σ(t) ≤ (√t/π) ∫₀^∞ x k(x) dx`; hence `∫₀^∞ σ(t)/(1+t) dt < ∞`.
* **Stieltjes representation.** For `Im w > 0`, `h(w) = ∫₀^∞ σ(t)/(t - w²) dt`.  The proof
  substitutes `t = u²`, exchanges the order by Tonelli, and evaluates the inner integral by the
  Lorentzian formula `∫₀^∞ (1 - cos(ux))/(u² - w²) du = (πi/(2w)) (1 - e^{iwx})`.
* With `m(ζ) = h(w)`, `w = i(-ζ)^{1/2}`, this reads `m(ζ) = ∫₀^∞ σ(t)/(t - ζ) dt` on
  `ℂ \ [0, ∞)`; `Im m > 0` in the upper half-plane and `m(-r²) = ∫₀^∞ k(x)e^{-rx} dx > 0`.
* **Boundary sheets.** `m(u² ± iη) → h(±u)` with `h(-u) = conj h(u)`, and the truncated principal
  value `∫_{t>0, |t-u²|>ε} σ(t)/(t - u²) dt` tends to `Re h(u)`; the Lipschitz bound
  `|σ(t) - σ(τ)| ≤ (∫ x k)/(π√τ) |t - τ|` feeds the Poisson-versus-truncation estimate.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open MeasureTheory Complex Set Filter Topology ComplexConjugate

/-- A one-port source: a differentiable function, strictly decreasing on `[0, ∞)`, integrable
with its first moment on `(0, ∞)`, and tending to zero at infinity. -/
structure OnePortSource (k : ℝ → ℝ) : Prop where
  differentiable : Differentiable ℝ k
  strictAntiOn : StrictAntiOn k (Ici 0)
  integrableOn : IntegrableOn k (Ioi 0)
  integrableOn_mul : IntegrableOn (fun x => x * k x) (Ioi 0)
  tendsto_atTop : Tendsto k atTop (𝓝 0)

/-- The one-sided connection `h(z) = ∫₀^∞ k(x) e^{izx} dx`. -/
def onePortConnection (k : ℝ → ℝ) (z : ℂ) : ℂ :=
  ∫ x in Ioi (0 : ℝ), (k x : ℂ) * cexp (I * z * x)

/-- The one-port spectral density
`σ(t) = (1/(π√t)) ∫₀^∞ ω(x) (1 - cos(√t x)) dx`, `ω = -k'`. -/
def onePortDensity (k : ℝ → ℝ) (t : ℝ) : ℝ :=
  1 / (Real.pi * √t) * ∫ x in Ioi (0 : ℝ), -deriv k x * (1 - Real.cos (√t * x))

variable {k : ℝ → ℝ}

namespace OnePortSource

theorem continuous (hk : OnePortSource k) : Continuous k := hk.differentiable.continuous

theorem pos (hk : OnePortSource k) {x : ℝ} (hx : 0 ≤ x) : 0 < k x := by
  have hx1 : x + 1 ∈ Ici (0 : ℝ) := mem_Ici.mpr (by linarith)
  have h1 : 0 ≤ k (x + 1) := by
    refine le_of_tendsto hk.tendsto_atTop (eventually_atTop.mpr ⟨x + 1, fun y hy => ?_⟩)
    exact hk.strictAntiOn.antitoneOn hx1 (mem_Ici.mpr (by linarith)) hy
  exact lt_of_le_of_lt h1 (hk.strictAntiOn (mem_Ici.mpr hx) hx1 (by linarith))

theorem deriv_nonpos (hk : OnePortSource k) {x : ℝ} (hx : 0 < x) : deriv k x ≤ 0 := by
  have h := (hk.strictAntiOn.antitoneOn.mono (Ioi_subset_Ici_self (a := (0 : ℝ)))).derivWithin_nonpos
    (x := x)
  rwa [derivWithin_of_isOpen isOpen_Ioi hx] at h

theorem integrableOn_deriv (hk : OnePortSource k) : IntegrableOn (deriv k) (Ioi 0) :=
  integrableOn_Ioi_deriv_of_nonpos hk.continuous.continuousWithinAt
    (fun x _ => (hk.differentiable x).hasDerivAt) (fun _ hx => hk.deriv_nonpos hx)
    hk.tendsto_atTop

/-- The total mass of `ω = -k'` is `k(0)`. -/
theorem integral_neg_deriv (hk : OnePortSource k) :
    ∫ x in Ioi (0 : ℝ), -deriv k x = k 0 := by
  rw [integral_neg, integral_Ioi_of_hasDerivAt_of_nonpos hk.continuous.continuousWithinAt
    (fun x _ => (hk.differentiable x).hasDerivAt) (fun _ hx => hk.deriv_nonpos hx)
    hk.tendsto_atTop]
  ring

theorem norm_cexp_I_mul_le (z : ℂ) (hz : 0 ≤ z.im) {x : ℝ} (hx : 0 ≤ x) :
    ‖cexp (I * z * x)‖ ≤ 1 := by
  rw [Complex.norm_exp]
  refine Real.exp_le_one_iff.mpr ?_
  simp only [mul_re, I_re, zero_mul, I_im, one_mul, zero_sub, ofReal_re, mul_im, ofReal_im,
    mul_zero, sub_zero]
  nlinarith

theorem integrableOn_mul_cexp (hk : OnePortSource k) {z : ℂ} (hz : 0 ≤ z.im) :
    IntegrableOn (fun x : ℝ => (k x : ℂ) * cexp (I * z * x)) (Ioi 0) := by
  refine hk.integrableOn.norm.mono' ?_ ?_
  · have hc := hk.continuous
    exact (by fun_prop : Continuous fun x : ℝ => (k x : ℂ) * cexp (I * z * x)).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun x hx => ?_)
    rw [norm_mul, Complex.norm_real]
    exact mul_le_of_le_one_right (norm_nonneg _) (norm_cexp_I_mul_le z hz (le_of_lt hx))

theorem integrableOn_neg_deriv_mul (hk : OnePortSource k) {g : ℝ → ℂ} (hg : Measurable g)
    {C : ℝ} (hC : ∀ x, 0 < x → ‖g x‖ ≤ C) :
    IntegrableOn (fun x : ℝ => ((-deriv k x : ℝ) : ℂ) * g x) (Ioi 0) := by
  refine (hk.integrableOn_deriv.norm.const_mul C).mono' ?_ ?_
  · exact (by fun_prop : Measurable fun x : ℝ => ((-deriv k x : ℝ) : ℂ) * g x).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun x hx => ?_)
    rw [norm_mul, Complex.norm_real, norm_neg, mul_comm]
    exact mul_le_mul_of_nonneg_right (hC x hx) (norm_nonneg _)

/-- **Integration by parts.** For `Im w ≥ 0`, `w ≠ 0`:
`h(w) = (i/w) ∫₀^∞ ω(x) (1 - e^{iwx}) dx`. -/
theorem onePortConnection_eq (hk : OnePortSource k) {w : ℂ} (hw : 0 ≤ w.im) (hw0 : w ≠ 0) :
    onePortConnection k w =
      I / w * ∫ x in Ioi (0 : ℝ), ((-deriv k x : ℝ) : ℂ) * (1 - cexp (I * w * x)) := by
  have hIw : I * w ≠ 0 := mul_ne_zero I_ne_zero hw0
  set u : ℝ → ℂ := fun x => (k x : ℂ)
  set u' : ℝ → ℂ := fun x => ((deriv k x : ℝ) : ℂ)
  set v : ℝ → ℂ := fun x => (cexp (I * w * x) - 1) / (I * w)
  set v' : ℝ → ℂ := fun x => cexp (I * w * x)
  have hu : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt u (u' x) x := fun x _ =>
    (hk.differentiable x).hasDerivAt.ofReal_comp
  have hv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt v (v' x) x := by
    intro x _
    have h := ((((hasDerivAt_id (x : ℂ)).const_mul (I * w)).cexp).comp_ofReal.sub_const
      1).div_const (I * w)
    refine h.congr_deriv ?_
    simp only [id, mul_one, v']
    field_simp
  have hnv : ∀ x : ℝ, 0 ≤ x → ‖v x‖ ≤ 2 / ‖w‖ := by
    intro x hx
    simp only [v, norm_div, norm_mul, Complex.norm_I, one_mul]
    gcongr
    calc ‖cexp (I * w * x) - 1‖ ≤ ‖cexp (I * w * x)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := by gcongr; exact norm_cexp_I_mul_le w hw hx; simp
      _ = 2 := by norm_num
  have huv' : IntegrableOn (u * v') (Ioi 0) := hk.integrableOn_mul_cexp hw
  have hu'v : IntegrableOn (u' * v) (Ioi 0) := by
    have h := hk.integrableOn_neg_deriv_mul (g := fun x => -v x) (by fun_prop)
      (C := 2 / ‖w‖) (fun x hx => by rw [norm_neg]; exact hnv x hx.le)
    refine h.congr_fun (fun x _ => ?_) measurableSet_Ioi
    simp only [Pi.mul_apply, u', ofReal_neg]
    ring
  have hcont : Continuous (u * v) := by
    have := hk.continuous
    simp only [u, v]
    fun_prop
  have h0 : Tendsto (u * v) (𝓝[>] 0) (𝓝 0) := by
    have h := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    simpa [u, v] using h
  have htop : Tendsto (u * v) atTop (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun x => 2 / ‖w‖ * |k x|) ?_ ?_
    · refine eventually_atTop.mpr ⟨0, fun x hx => ?_⟩
      rw [Pi.mul_apply, norm_mul, mul_comm]
      simp only [u, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hnv x hx) (abs_nonneg _)
    · simpa using (hk.tendsto_atTop.abs.const_mul (2 / ‖w‖))
  have h := integral_Ioi_mul_deriv_eq_deriv_mul hu hv huv' hu'v h0 htop
  rw [onePortConnection]
  change ∫ x in Ioi (0 : ℝ), u x * v' x = _
  rw [h, ← integral_const_mul, sub_zero, zero_sub, ← integral_neg]
  refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
  simp only [u', v, ofReal_neg]
  field_simp
  ring_nf
  rw [I_sq]
  ring

theorem integrableOn_neg_deriv_mul_one_sub_cos (hk : OnePortSource k) (y : ℝ) :
    IntegrableOn (fun x => -deriv k x * (1 - Real.cos (y * x))) (Ioi 0) := by
  refine (hk.integrableOn_deriv.norm.const_mul 2).mono' (by fun_prop) ?_
  refine Eventually.of_forall fun x => ?_
  rw [norm_mul, norm_neg, mul_comm]
  gcongr
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith [Real.cos_le_one (y * x), Real.neg_one_le_cos (y * x)]

theorem integral_neg_deriv_mul_one_sub_cos_nonneg (hk : OnePortSource k) (y : ℝ) :
    0 ≤ ∫ x in Ioi (0 : ℝ), -deriv k x * (1 - Real.cos (y * x)) :=
  setIntegral_nonneg measurableSet_Ioi fun x hx =>
    mul_nonneg (neg_nonneg.mpr (hk.deriv_nonpos hx)) (by linarith [Real.cos_le_one (y * x)])

theorem integral_neg_deriv_mul_one_sub_cos_le (hk : OnePortSource k) (y : ℝ) :
    ∫ x in Ioi (0 : ℝ), -deriv k x * (1 - Real.cos (y * x)) ≤ 2 * k 0 := by
  rw [← hk.integral_neg_deriv, ← integral_const_mul]
  refine setIntegral_mono_on (hk.integrableOn_neg_deriv_mul_one_sub_cos y)
    (hk.integrableOn_deriv.neg.const_mul 2) measurableSet_Ioi fun x hx => ?_
  have := neg_nonneg.mpr (hk.deriv_nonpos hx)
  nlinarith [Real.neg_one_le_cos (y * x)]

/-- The imaginary part of the connection on the real axis is the sine transform of `k`. -/
theorem im_onePortConnection_ofReal (hk : OnePortSource k) (u : ℝ) :
    (onePortConnection k u).im = ∫ x in Ioi (0 : ℝ), k x * Real.sin (u * x) := by
  have h := integral_im (hk.integrableOn_mul_cexp (z := u) (by simp))
  simp only [RCLike.im_to_complex] at h
  rw [onePortConnection, ← h]
  refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
  rw [show I * (u : ℂ) * x = ((u * x : ℝ) : ℂ) * I by push_cast; ring, im_ofReal_mul,
    Complex.exp_ofReal_mul_I_im]

theorem re_onePortConnection_ofReal (hk : OnePortSource k) (u : ℝ) :
    (onePortConnection k u).re = ∫ x in Ioi (0 : ℝ), k x * Real.cos (u * x) := by
  have h := integral_re (hk.integrableOn_mul_cexp (z := u) (by simp))
  simp only [RCLike.re_to_complex] at h
  rw [onePortConnection, ← h]
  refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
  rw [show I * (u : ℂ) * x = ((u * x : ℝ) : ℂ) * I by push_cast; ring, re_ofReal_mul,
    Complex.exp_ofReal_mul_I_re]

/-- **(5).** For `u > 0`, `Im h(u) = (1/u) ∫₀^∞ ω(x) (1 - cos(ux)) dx`. -/
theorem im_onePortConnection_eq (hk : OnePortSource k) {u : ℝ} (hu : 0 < u) :
    (onePortConnection k u).im =
      1 / u * ∫ x in Ioi (0 : ℝ), -deriv k x * (1 - Real.cos (u * x)) := by
  have hu0 : (u : ℂ) ≠ 0 := by exact_mod_cast hu.ne'
  have hint := hk.integrableOn_neg_deriv_mul (g := fun x : ℝ => 1 - cexp (I * u * x))
    (by fun_prop) (C := 2) fun x hx => by
      calc ‖1 - cexp (I * u * x)‖ ≤ ‖(1 : ℂ)‖ + ‖cexp (I * u * x)‖ := norm_sub_le _ _
        _ ≤ 1 + 1 := by gcongr; simp; exact norm_cexp_I_mul_le u (by simp) hx.le
        _ = 2 := by norm_num
  rw [hk.onePortConnection_eq (by simp) hu0]
  have hre := integral_re hint
  simp only [RCLike.re_to_complex] at hre
  rw [show I / (u : ℂ) = ((1 / u : ℝ) : ℂ) * I by push_cast; ring, mul_assoc, im_ofReal_mul,
    mul_comm I, Complex.mul_I_im, ← hre]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
  rw [show I * (u : ℂ) * x = ((u * x : ℝ) : ℂ) * I by push_cast; ring]
  simp only [mul_re, ofReal_re, ofReal_im, sub_re, one_re,
    Complex.exp_ofReal_mul_I_re, zero_mul, sub_zero]

/-- **(1)/(3).** For `u > 0`, `σ(u²) = Im h(u) / π`. -/
theorem onePortDensity_sq (hk : OnePortSource k) {u : ℝ} (hu : 0 < u) :
    onePortDensity k (u ^ 2) = (onePortConnection k u).im / Real.pi := by
  rw [onePortDensity, Real.sqrt_sq hu.le, hk.im_onePortConnection_eq hu]
  field_simp

theorem onePortDensity_eq_sine (hk : OnePortSource k) {t : ℝ} (ht : 0 < t) :
    onePortDensity k t = (∫ x in Ioi (0 : ℝ), k x * Real.sin (√t * x)) / Real.pi := by
  have h := hk.onePortDensity_sq (Real.sqrt_pos.mpr ht)
  rw [Real.sq_sqrt ht.le] at h
  rw [h, hk.im_onePortConnection_ofReal]

/-- **(1).** The spectral density is strictly positive on `(0, ∞)`. -/
theorem onePortDensity_pos (hk : OnePortSource k) {t : ℝ} (ht : 0 < t) :
    0 < onePortDensity k t := by
  rw [hk.onePortDensity_eq_sine ht]
  exact div_pos (integral_mul_sin_pos_of_strictAntiOn hk.continuous hk.strictAntiOn
    hk.integrableOn (Real.sqrt_pos.mpr ht)) Real.pi_pos

theorem onePortDensity_nonneg (hk : OnePortSource k) (t : ℝ) : 0 ≤ onePortDensity k t := by
  rw [onePortDensity]
  rcases le_or_gt t 0 with ht | ht
  · rw [Real.sqrt_eq_zero'.mpr ht]; simp
  · exact mul_nonneg (by positivity) (hk.integral_neg_deriv_mul_one_sub_cos_nonneg _)

/-- **Decay at infinity.** `σ(t) ≤ 2k(0) / (π√t)`. -/
theorem onePortDensity_le_inv_sqrt (hk : OnePortSource k) {t : ℝ} (ht : 0 < t) :
    onePortDensity k t ≤ 2 * k 0 / (Real.pi * √t) := by
  rw [onePortDensity, one_div_mul_eq_div]
  exact div_le_div_of_nonneg_right (hk.integral_neg_deriv_mul_one_sub_cos_le _) (by positivity)

/-- **Vanishing at the origin.** `σ(t) ≤ (√t/π) ∫₀^∞ x k(x) dx`. -/
theorem onePortDensity_le_sqrt (hk : OnePortSource k) {t : ℝ} (ht : 0 < t) :
    onePortDensity k t ≤ √t / Real.pi * ∫ x in Ioi (0 : ℝ), x * k x := by
  rw [hk.onePortDensity_eq_sine ht, div_mul_eq_mul_div, ← integral_const_mul]
  refine div_le_div_of_nonneg_right ?_ Real.pi_pos.le
  refine setIntegral_mono_on ?_ (hk.integrableOn_mul.const_mul _) measurableSet_Ioi fun x hx => ?_
  · refine (hk.integrableOn.norm).mono' (by have := hk.continuous; fun_prop) ?_
    refine Eventually.of_forall fun x => ?_
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (by
      rw [Real.norm_eq_abs]; exact Real.abs_sin_le_one _)
  · have hkx := (hk.pos (le_of_lt hx)).le
    have hs : Real.sin (√t * x) ≤ √t * x :=
      Real.sin_le (mul_nonneg (Real.sqrt_nonneg t) (le_of_lt hx))
    nlinarith

/-- **(2).** The one-sided connection is the Stieltjes transform of `σ`:
`h(w) = ∫₀^∞ σ(t) / (t - w²) dt` for `Im w > 0`. -/
theorem onePortConnection_eq_stieltjes (hk : OnePortSource k) {w : ℂ} (hw : 0 < w.im) :
    onePortConnection k w =
      ∫ t in Ioi (0 : ℝ), (onePortDensity k t : ℂ) / ((t : ℂ) - w ^ 2) := by
  have hw0 : w ≠ 0 := fun h => by simp [h] at hw
  obtain ⟨c, hc, hcle⟩ := exists_mul_one_add_sq_le_norm_sq_sub hw
  have hsub := integral_comp_rpow_Ioi
    (fun t : ℝ => (onePortDensity k t : ℂ) / ((t : ℂ) - w ^ 2)) (p := 2) two_ne_zero
  set F : ℝ × ℝ → ℂ := fun p =>
    ((-deriv k p.2 * (1 - Real.cos (p.1 * p.2)) : ℝ) : ℂ) / ((p.1 : ℂ) ^ 2 - w ^ 2) with hF
  have hpt : ∀ u ∈ Ioi (0 : ℝ), (|(2 : ℝ)| * u ^ ((2 : ℝ) - 1)) •
      ((onePortDensity k (u ^ (2 : ℝ)) : ℂ) / (((u ^ (2 : ℝ) : ℝ) : ℂ) - w ^ 2)) =
      (2 / Real.pi : ℂ) * ∫ x in Ioi (0 : ℝ), F (u, x) := by
    intro u hu
    have hu : 0 < u := hu
    have h0 := sq_sub_sq_ne_zero hw u
    rw [Real.rpow_two, show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, abs_two,
      onePortDensity, Real.sqrt_sq hu.le]
    simp only [hF]
    rw [integral_div, integral_complex_ofReal]
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have hu0 : (u : ℂ) ≠ 0 := by exact_mod_cast hu.ne'
    rw [real_smul]
    push_cast
    field_simp
  rw [← hsub, setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul]
  have hmeas : AEStronglyMeasurable F
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) :=
    (by simp only [hF]; fun_prop : Measurable F).aestronglyMeasurable
  have hfib : ∀ u : ℝ, IntegrableOn (fun x => F (u, x)) (Ioi 0) := by
    intro u
    have h0 := sq_sub_sq_ne_zero hw u
    have h := hk.integrableOn_neg_deriv_mul
      (g := fun x : ℝ => ((1 - Real.cos (u * x) : ℝ) : ℂ) / ((u : ℂ) ^ 2 - w ^ 2)) (by fun_prop)
      (C := 2 / ‖(u : ℂ) ^ 2 - w ^ 2‖) fun x _ => by
        rw [norm_div, Complex.norm_real, Real.norm_eq_abs]
        gcongr
        rw [abs_le]
        constructor <;> linarith [Real.cos_le_one (u * x), Real.neg_one_le_cos (u * x)]
    refine h.congr_fun (fun x _ => ?_) measurableSet_Ioi
    simp only [hF]
    push_cast
    ring
  have hnormint : Integrable (fun u => ∫ x in Ioi (0 : ℝ), ‖F (u, x)‖)
      (volume.restrict (Ioi (0 : ℝ))) := by
    set M := ∫ x in Ioi (0 : ℝ), ‖deriv k x‖
    refine (((integrable_inv_one_add_sq.const_mul (2 * M / c))).integrableOn (s := Ioi 0)).mono'
      (hmeas.norm.integral_prod_right') ?_
    refine Eventually.of_forall fun u => ?_
    have hpos : 0 < c * (1 + u ^ 2) := by positivity
    rw [Real.norm_of_nonneg (integral_nonneg fun x => norm_nonneg _)]
    calc ∫ x in Ioi (0 : ℝ), ‖F (u, x)‖
        ≤ ∫ x in Ioi (0 : ℝ), 2 / (c * (1 + u ^ 2)) * ‖deriv k x‖ := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun x => norm_nonneg _)
            (hk.integrableOn_deriv.norm.const_mul _) (Eventually.of_forall fun x => ?_)
          simp only [hF, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_neg]
          rw [div_le_iff₀ (lt_of_lt_of_le hpos (hcle u))]
          have h1 : |1 - Real.cos (u * x)| ≤ 2 := by
            rw [abs_le]
            constructor <;> linarith [Real.cos_le_one (u * x), Real.neg_one_le_cos (u * x)]
          have h2 : 2 / (c * (1 + u ^ 2)) * ‖deriv k x‖ * (c * (1 + u ^ 2)) = 2 * |deriv k x| := by
            rw [Real.norm_eq_abs]; field_simp
          calc |deriv k x| * |1 - Real.cos (u * x)| ≤ 2 * |deriv k x| := by
                nlinarith [abs_nonneg (deriv k x)]
            _ = 2 / (c * (1 + u ^ 2)) * ‖deriv k x‖ * (c * (1 + u ^ 2)) := h2.symm
            _ ≤ 2 / (c * (1 + u ^ 2)) * ‖deriv k x‖ * ‖(u : ℂ) ^ 2 - w ^ 2‖ := by
                gcongr; exact hcle u
      _ = 2 * M / c * (1 + u ^ 2)⁻¹ := by
          rw [integral_const_mul, show (∫ x in Ioi (0 : ℝ), ‖deriv k x‖) = M from rfl]
          field_simp
  have hint : Integrable F
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) :=
    (integrable_prod_iff hmeas).mpr ⟨Eventually.of_forall hfib, hnormint⟩
  rw [integral_integral_swap (f := fun u x => F (u, x)) hint]
  have hinner : ∀ x ∈ Ioi (0 : ℝ), ∫ u in Ioi (0 : ℝ), F (u, x) =
      (Real.pi * I / (2 * w)) * (((-deriv k x : ℝ) : ℂ) * (1 - cexp (I * w * x))) := by
    intro x hx
    have h := integral_Ioi_one_sub_cos_div_sq_sub_sq hw x
    rw [abs_of_pos (mem_Ioi.mp hx)] at h
    rw [show (Real.pi * I / (2 * w)) * (((-deriv k x : ℝ) : ℂ) * (1 - cexp (I * w * x))) =
      ((-deriv k x : ℝ) : ℂ) * (Real.pi * I / (2 * w) * (1 - cexp (I * w * x))) by ring,
      ← h, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    simp only [hF]
    push_cast
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hinner, integral_const_mul,
    hk.onePortConnection_eq hw.le hw0]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp

/-- The connection is continuous on the closed upper half-plane. -/
theorem continuousOn_onePortConnection (hk : OnePortSource k) :
    ContinuousOn (onePortConnection k) {z : ℂ | 0 ≤ z.im} := by
  have hc := hk.continuous
  refine continuousOn_of_dominated (bound := fun x => ‖k x‖)
    (fun z _ => (by fun_prop : Continuous fun x : ℝ =>
      (k x : ℂ) * cexp (I * z * x)).aestronglyMeasurable) (fun z hz => ?_)
    hk.integrableOn.norm (Eventually.of_forall fun _ => by fun_prop)
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun x hx => ?_)
  rw [norm_mul, Complex.norm_real]
  exact mul_le_of_le_one_right (norm_nonneg _) (norm_cexp_I_mul_le z hz (le_of_lt hx))

theorem onePortDensity_eq_im (hk : OnePortSource k) (t : ℝ) :
    onePortDensity k t = (onePortConnection k (√t : ℝ)).im / Real.pi := by
  rcases le_or_gt t 0 with ht | ht
  · rw [onePortDensity, hk.im_onePortConnection_ofReal, Real.sqrt_eq_zero'.mpr ht]
    simp
  · have h := hk.onePortDensity_sq (Real.sqrt_pos.mpr ht)
    rwa [Real.sq_sqrt ht.le] at h

theorem continuous_onePortDensity (hk : OnePortSource k) : Continuous (onePortDensity k) := by
  have h : Continuous fun t : ℝ => onePortConnection k (√t : ℝ) :=
    hk.continuousOn_onePortConnection.comp_continuous (by fun_prop) fun t => by simp
  rw [show onePortDensity k = fun t => (onePortConnection k (√t : ℝ)).im / Real.pi from
    funext hk.onePortDensity_eq_im]
  fun_prop

theorem integral_mul_nonneg (hk : OnePortSource k) : 0 ≤ ∫ x in Ioi (0 : ℝ), x * k x :=
  setIntegral_nonneg measurableSet_Ioi fun _ hx =>
    mul_nonneg (le_of_lt hx) (hk.pos (le_of_lt hx)).le

theorem aestronglyMeasurable_onePortDensity_div (hk : OnePortSource k) {s : Set ℝ}
    (hs : s ⊆ Ioi 0) (hms : MeasurableSet s) :
    AEStronglyMeasurable (fun t => onePortDensity k t / (1 + t)) (volume.restrict s) :=
  (hk.continuous_onePortDensity.continuousOn.div (by fun_prop) fun t ht => by
    have : 0 < t := hs ht
    positivity).aestronglyMeasurable hms

theorem rpow_neg_three_halves {t : ℝ} (ht : 0 < t) : t ^ (-(3 / 2) : ℝ) = (t * √t)⁻¹ := by
  rw [Real.rpow_neg ht.le, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add ht,
    Real.rpow_one, ← Real.sqrt_eq_rpow]

/-- **(1).** `∫₀^∞ σ(t) / (1 + t) dt < ∞`. -/
theorem integrableOn_onePortDensity_div (hk : OnePortSource k) :
    IntegrableOn (fun t => onePortDensity k t / (1 + t)) (Ioi 0) := by
  set M := ∫ x in Ioi (0 : ℝ), x * k x
  have hM : 0 ≤ M := hk.integral_mul_nonneg
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
  refine IntegrableOn.union ?_ ?_
  · refine (integrableOn_const (C := M / Real.pi) (by simp)).mono'
      (hk.aestronglyMeasurable_onePortDensity_div Ioc_subset_Ioi_self measurableSet_Ioc) ?_
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun t ht => ?_)
    have ht0 : 0 < t := ht.1
    have hσ := hk.onePortDensity_nonneg t
    have hle := hk.onePortDensity_le_sqrt ht0
    have hs1 : √t ≤ 1 := Real.sqrt_le_one.mpr ht.2
    rw [Real.norm_of_nonneg (by positivity), div_le_iff₀ (by positivity)]
    have h1 : √t / Real.pi * M ≤ M / Real.pi := by
      rw [div_mul_eq_mul_div]
      exact div_le_div_of_nonneg_right (by nlinarith) Real.pi_pos.le
    have h2 : M / Real.pi ≤ M / Real.pi * (1 + t) := by
      have : 0 ≤ M / Real.pi := by positivity
      nlinarith
    linarith
  · refine ((integrableOn_Ioi_rpow_of_lt (a := -(3 / 2)) (by norm_num) one_pos).const_mul
      (2 * k 0 / Real.pi)).mono'
      (hk.aestronglyMeasurable_onePortDensity_div (Ioi_subset_Ioi zero_le_one)
        measurableSet_Ioi) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    have ht1 : 1 < t := ht
    have ht0 : 0 < t := by linarith
    have hσ := hk.onePortDensity_nonneg t
    have hle := hk.onePortDensity_le_inv_sqrt ht0
    have hk0 := (hk.pos le_rfl).le
    have hsq : 0 < √t := Real.sqrt_pos.mpr ht0
    rw [Real.norm_of_nonneg (by positivity), rpow_neg_three_halves ht0]
    calc onePortDensity k t / (1 + t) ≤ 2 * k 0 / (Real.pi * √t) / t := by
          gcongr; linarith
      _ = 2 * k 0 / Real.pi * (t * √t)⁻¹ := by field_simp

/-- Away from the closed positive half-line the Stieltjes integrand is integrable. -/
theorem integrableOn_onePortDensity_div_sub (hk : OnePortSource k) {ζ : ℂ}
    (hζ : -ζ ∈ slitPlane) :
    IntegrableOn (fun t : ℝ => (onePortDensity k t : ℂ) / ((t : ℂ) - ζ)) (Ioi 0) := by
  obtain ⟨c, hc, hcle⟩ := exists_mul_one_add_le_norm_sub hζ
  have hne : ∀ t : ℝ, 0 ≤ t → (t : ℂ) - ζ ≠ 0 := fun t ht h0 => by
    have := hcle t ht
    rw [h0, norm_zero] at this
    nlinarith
  refine (hk.integrableOn_onePortDensity_div.const_mul c⁻¹).mono' ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    have := hk.continuous_onePortDensity
    exact (by fun_prop : Continuous fun t : ℝ => (onePortDensity k t : ℂ)).continuousOn.div
      (by fun_prop) fun t ht => hne t (le_of_lt ht)
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    have ht0 : 0 ≤ t := le_of_lt ht
    have hσ := hk.onePortDensity_nonneg t
    have hpos : 0 < c * (1 + t) := by positivity
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hσ,
      div_le_iff₀ (lt_of_lt_of_le hpos (hcle t ht0))]
    calc onePortDensity k t = c⁻¹ * (onePortDensity k t / (1 + t)) * (c * (1 + t)) := by
          field_simp
      _ ≤ c⁻¹ * (onePortDensity k t / (1 + t)) * ‖(t : ℂ) - ζ‖ := by
          gcongr; exact hcle t ht0

/-- **(2).** In the upper half-plane the Stieltjes transform has positive imaginary part. -/
theorem im_integral_onePortDensity_div_sub_pos (hk : OnePortSource k) {ζ : ℂ} (hζ : 0 < ζ.im) :
    0 < (∫ t in Ioi (0 : ℝ), (onePortDensity k t : ℂ) / ((t : ℂ) - ζ)).im := by
  have hsl : -ζ ∈ slitPlane := Or.inr (by simp; exact hζ.ne')
  have hint := hk.integrableOn_onePortDensity_div_sub hsl
  have h := integral_im hint
  simp only [RCLike.im_to_complex] at h
  rw [← h]
  have hpt : ∀ t ∈ Ioi (0 : ℝ), 0 < ((onePortDensity k t : ℂ) / ((t : ℂ) - ζ)).im := by
    intro t ht
    have hσ := hk.onePortDensity_pos (mem_Ioi.mp ht)
    have hn : 0 < normSq ((t : ℂ) - ζ) := by
      rw [normSq_pos]
      intro h0
      have := congrArg Complex.im h0
      simp at this
      exact hζ.ne' this
    rw [Complex.div_im]
    simp only [ofReal_im, zero_mul, zero_div, ofReal_re, sub_im, zero_sub, mul_neg, neg_div,
      sub_neg_eq_add, zero_add]
    positivity
  rw [setIntegral_pos_iff_support_of_nonneg_ae
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => (hpt t ht).le))
    hint.im]
  rw [show Function.support (fun t : ℝ => ((onePortDensity k t : ℂ) / ((t : ℂ) - ζ)).im) ∩
      Ioi 0 = Ioi 0 from inter_eq_right.mpr fun t ht => (hpt t ht).ne']
  simp

end OnePortSource

/-- On the positive imaginary axis the connection is the real Laplace transform of `k`. -/
theorem onePortConnection_I_mul (k : ℝ → ℝ) (r : ℝ) :
    onePortConnection k (I * r) = ((∫ x in Ioi (0 : ℝ), k x * Real.exp (-(r * x)) : ℝ) : ℂ) := by
  rw [onePortConnection, ← integral_complex_ofReal]
  refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
  push_cast
  congr 2
  linear_combination (r * x : ℂ) * I_sq

namespace OnePortSource

theorem integral_mul_exp_neg_pos (hk : OnePortSource k) {r : ℝ} (hr : 0 ≤ r) :
    0 < ∫ x in Ioi (0 : ℝ), k x * Real.exp (-(r * x)) := by
  have hint : IntegrableOn (fun x => k x * Real.exp (-(r * x))) (Ioi 0) := by
    refine hk.integrableOn.norm.mono' (by have := hk.continuous; fun_prop) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun x hx => ?_)
    rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le]
    refine mul_le_of_le_one_right (norm_nonneg _) (Real.exp_le_one_iff.mpr ?_)
    nlinarith [mem_Ioi.mp hx]
  have hpt : ∀ x ∈ Ioi (0 : ℝ), 0 < k x * Real.exp (-(r * x)) := fun x hx =>
    mul_pos (hk.pos (le_of_lt hx)) (Real.exp_pos _)
  rw [setIntegral_pos_iff_support_of_nonneg_ae
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun x hx => (hpt x hx).le))
    hint, show Function.support (fun x => k x * Real.exp (-(r * x))) ∩ Ioi 0 = Ioi 0 from
      inter_eq_right.mpr fun x hx => (hpt x hx).ne']
  simp

end OnePortSource

/-! ## The slit-plane parametrisation -/

/-- The square root of `ζ` in the upper half-plane, `w = i (-ζ)^{1/2}`. -/
def upperRoot (ζ : ℂ) : ℂ := I * (-ζ) ^ (2⁻¹ : ℂ)

theorem upperRoot_sq (ζ : ℂ) : upperRoot ζ ^ 2 = ζ := by
  rw [upperRoot, mul_pow, cpow_ofNat_inv_pow, I_sq]
  ring

theorem re_cpow_inv_two_pos {x : ℂ} (hx : x ∈ slitPlane) : 0 < (x ^ (2⁻¹ : ℂ)).re := by
  have hx0 : x ≠ 0 := slitPlane_ne_zero hx
  rw [cpow_def_of_ne_zero hx0, Complex.exp_re]
  refine mul_pos (Real.exp_pos _) (Real.cos_pos_of_mem_Ioo ?_)
  have him : (log x * 2⁻¹).im = x.arg / 2 := by
    rw [show (2⁻¹ : ℂ) = ((2⁻¹ : ℝ) : ℂ) by push_cast; ring, im_mul_ofReal, log_im]
    ring
  rw [him]
  have h1 := neg_pi_lt_arg x
  have h2 : x.arg < Real.pi :=
    lt_of_le_of_ne (arg_le_pi x) (mem_slitPlane_iff_arg.mp hx).1
  constructor <;> linarith

theorem upperRoot_im_pos {ζ : ℂ} (hζ : -ζ ∈ slitPlane) : 0 < (upperRoot ζ).im := by
  rw [upperRoot, mul_im, I_re, I_im, zero_mul, one_mul, zero_add]
  exact re_cpow_inv_two_pos hζ

/-- The Stieltjes function of the port, `m(ζ) = h(w)` with `w² = ζ`, `Im w > 0`. -/
def onePortStieltjes (k : ℝ → ℝ) (ζ : ℂ) : ℂ := onePortConnection k (upperRoot ζ)

namespace OnePortSource

/-- **(2).** `m(ζ) = ∫₀^∞ σ(t) / (t - ζ) dt` on `ℂ \ [0, ∞)`. -/
theorem onePortStieltjes_eq (hk : OnePortSource k) {ζ : ℂ} (hζ : -ζ ∈ slitPlane) :
    onePortStieltjes k ζ = ∫ t in Ioi (0 : ℝ), (onePortDensity k t : ℂ) / ((t : ℂ) - ζ) := by
  rw [onePortStieltjes, hk.onePortConnection_eq_stieltjes (upperRoot_im_pos hζ), upperRoot_sq]

/-- **(2).** `Im m(ζ) > 0` for `Im ζ > 0`. -/
theorem im_onePortStieltjes_pos (hk : OnePortSource k) {ζ : ℂ} (hζ : 0 < ζ.im) :
    0 < (onePortStieltjes k ζ).im := by
  rw [hk.onePortStieltjes_eq (Or.inr (by simp; exact hζ.ne'))]
  exact hk.im_integral_onePortDensity_div_sub_pos hζ

end OnePortSource

theorem upperRoot_neg_sq {r : ℝ} (hr : 0 < r) : upperRoot (-(r ^ 2 : ℝ)) = I * r := by
  rw [upperRoot, neg_neg, show (2⁻¹ : ℂ) = ((2⁻¹ : ℝ) : ℂ) by push_cast; ring,
    ← ofReal_cpow (sq_nonneg r), show (2⁻¹ : ℝ) = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow,
    Real.sqrt_sq hr.le]

namespace OnePortSource

/-- **(2).** `m(-r²) = h(ir) = ∫₀^∞ k(x) e^{-rx} dx > 0` for `r > 0`. -/
theorem onePortStieltjes_neg_sq (hk : OnePortSource k) {r : ℝ} (hr : 0 < r) :
    onePortStieltjes k (-(r ^ 2 : ℝ)) = onePortConnection k (I * r) ∧
      onePortStieltjes k (-(r ^ 2 : ℝ)) =
        ((∫ x in Ioi (0 : ℝ), k x * Real.exp (-(r * x)) : ℝ) : ℂ) ∧
      0 < ∫ x in Ioi (0 : ℝ), k x * Real.exp (-(r * x)) := by
  rw [onePortStieltjes, upperRoot_neg_sq hr]
  exact ⟨rfl, onePortConnection_I_mul k r, hk.integral_mul_exp_neg_pos hr.le⟩

/-! ## Local Lipschitz bound for the density -/

end OnePortSource

theorem abs_sqrt_sub_sqrt_le {t τ : ℝ} (hτ : 0 < τ) : |√t - √τ| ≤ |t - τ| / √τ := by
  have hs := Real.sqrt_pos.mpr hτ
  rw [le_div_iff₀ hs]
  rcases le_or_gt t 0 with ht | ht
  · rw [Real.sqrt_eq_zero'.mpr ht, zero_sub, abs_neg, abs_of_pos hs,
      abs_of_neg (by linarith), ← sq, Real.sq_sqrt hτ.le]
    linarith
  · have hst := Real.sqrt_pos.mpr ht
    have key : (√t - √τ) * (√t + √τ) = t - τ := by
      rw [show (√t - √τ) * (√t + √τ) = √t ^ 2 - √τ ^ 2 by ring, Real.sq_sqrt ht.le,
        Real.sq_sqrt hτ.le]
    rw [← key, abs_mul, abs_of_pos (by positivity : 0 < √t + √τ)]
    nlinarith [abs_nonneg (√t - √τ)]

namespace OnePortSource

/-- **Local regularity of `σ`.** For `τ > 0` and every `t`,
`|σ(t) - σ(τ)| ≤ (∫₀^∞ x k(x) dx) / (π √τ) · |t - τ|`. -/
theorem abs_onePortDensity_sub_le (hk : OnePortSource k) (t : ℝ) {τ : ℝ} (hτ : 0 < τ) :
    |onePortDensity k t - onePortDensity k τ| ≤
      (∫ x in Ioi (0 : ℝ), x * k x) / (Real.pi * √τ) * |t - τ| := by
  set M := ∫ x in Ioi (0 : ℝ), x * k x
  have hM : 0 ≤ M := hk.integral_mul_nonneg
  have hsin : ∀ y : ℝ, IntegrableOn (fun x => k x * Real.sin (y * x)) (Ioi 0) := fun y =>
    hk.integrableOn.norm.mono' (by have := hk.continuous; fun_prop) (Eventually.of_forall fun x => by
      rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (by
        rw [Real.norm_eq_abs]; exact Real.abs_sin_le_one _))
  rw [hk.onePortDensity_eq_im, hk.onePortDensity_eq_im, hk.im_onePortConnection_ofReal,
    hk.im_onePortConnection_ofReal, ← sub_div, ← integral_sub (hsin _) (hsin _), abs_div,
    abs_of_pos Real.pi_pos]
  have hbound : |∫ x in Ioi (0 : ℝ), (k x * Real.sin (√t * x) - k x * Real.sin (√τ * x))| ≤
      |√t - √τ| * M := by
    rw [← integral_const_mul]
    refine (abs_integral_le_integral_abs).trans (setIntegral_mono_on ((hsin _).sub (hsin _)).abs
      (hk.integrableOn_mul.const_mul _) measurableSet_Ioi fun x hx => ?_)
    have hx : 0 < x := hx
    have hkx := (hk.pos hx.le).le
    rw [← mul_sub, abs_mul, abs_of_nonneg hkx]
    have h1 := Real.abs_sin_sub_sin_le (√t * x) (√τ * x)
    rw [← sub_mul, abs_mul, abs_of_pos hx] at h1
    nlinarith [abs_nonneg (√t - √τ)]
  have hsq := abs_sqrt_sub_sqrt_le (t := t) hτ
  have hs := Real.sqrt_pos.mpr hτ
  rw [div_le_iff₀ Real.pi_pos]
  calc _ ≤ |√t - √τ| * M := hbound
    _ ≤ |t - τ| / √τ * M := by gcongr
    _ = M / (Real.pi * √τ) * |t - τ| * Real.pi := by field_simp

end OnePortSource

/-! ## The two boundary sheets and the principal value -/

/-- On the real axis the two sheets are conjugate: `h(-u) = conj h(u)`. -/
theorem onePortConnection_neg_ofReal (k : ℝ → ℝ) (u : ℝ) :
    onePortConnection k (-u : ℝ) = conj (onePortConnection k u) := by
  rw [onePortConnection, onePortConnection, ← integral_conj]
  refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
  rw [map_mul, conj_ofReal, ← Complex.exp_conj]
  congr 2
  simp [conj_ofReal]

theorem integral_div_sub_conj (g : ℝ → ℝ) (ζ : ℂ) :
    ∫ t in Ioi (0 : ℝ), (g t : ℂ) / ((t : ℂ) - conj ζ) =
      conj (∫ t in Ioi (0 : ℝ), (g t : ℂ) / ((t : ℂ) - ζ)) := by
  rw [← integral_conj]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  simp [map_div₀, map_sub, conj_ofReal]

/-- The upper square root of `τ + iη` for `η ≥ 0`, written in real coordinates. -/
def upperRootPath (τ η : ℝ) : ℂ :=
  (√((√(τ ^ 2 + η ^ 2) + τ) / 2) : ℝ) + (√((√(τ ^ 2 + η ^ 2) - τ) / 2) : ℝ) * I

theorem continuous_upperRootPath (τ : ℝ) : Continuous (upperRootPath τ) := by
  unfold upperRootPath; fun_prop

theorem upperRootPath_sq {τ η : ℝ} (hη : 0 ≤ η) : upperRootPath τ η ^ 2 = τ + η * I := by
  set R := √(τ ^ 2 + η ^ 2)
  have hR : τ ≤ R := by
    calc τ ≤ |τ| := le_abs_self τ
      _ = √(τ ^ 2) := (Real.sqrt_sq_eq_abs τ).symm
      _ ≤ R := Real.sqrt_le_sqrt (by nlinarith)
  have hR' : -τ ≤ R := by
    calc -τ ≤ |τ| := neg_le_abs τ
      _ = √(τ ^ 2) := (Real.sqrt_sq_eq_abs τ).symm
      _ ≤ R := Real.sqrt_le_sqrt (by nlinarith)
  have hR2 : R ^ 2 = τ ^ 2 + η ^ 2 := Real.sq_sqrt (by positivity)
  have ha : √((R + τ) / 2) ^ 2 = (R + τ) / 2 := Real.sq_sqrt (by linarith)
  have hb : √((R - τ) / 2) ^ 2 = (R - τ) / 2 := Real.sq_sqrt (by linarith)
  have hab : √((R + τ) / 2) * √((R - τ) / 2) = η / 2 := by
    rw [← Real.sqrt_mul (by linarith), show (R + τ) / 2 * ((R - τ) / 2) = (η / 2) ^ 2 by
      nlinarith, Real.sqrt_sq (by linarith)]
  unfold upperRootPath
  rw [show ((√((R + τ) / 2) : ℝ) + (√((R - τ) / 2) : ℝ) * I : ℂ) ^ 2 =
      ((√((R + τ) / 2) ^ 2 - √((R - τ) / 2) ^ 2 : ℝ) : ℂ) +
        ((2 * (√((R + τ) / 2) * √((R - τ) / 2)) : ℝ) : ℂ) * I by
    push_cast; ring_nf; rw [I_sq]; ring, ha, hb, hab]
  push_cast
  ring

theorem upperRootPath_im {τ η : ℝ} : (upperRootPath τ η).im = √((√(τ ^ 2 + η ^ 2) - τ) / 2) := by
  simp [upperRootPath]

theorem upperRootPath_im_pos {τ η : ℝ} (hη : 0 < η) : 0 < (upperRootPath τ η).im := by
  rw [upperRootPath_im]
  refine Real.sqrt_pos.mpr ?_
  have : τ < √(τ ^ 2 + η ^ 2) := by
    calc τ ≤ |τ| := le_abs_self τ
      _ = √(τ ^ 2) := (Real.sqrt_sq_eq_abs τ).symm
      _ < √(τ ^ 2 + η ^ 2) := Real.sqrt_lt_sqrt (sq_nonneg _) (by nlinarith)
  linarith

theorem upperRootPath_zero {τ : ℝ} (hτ : 0 < τ) : upperRootPath τ 0 = (√τ : ℝ) := by
  simp only [upperRootPath, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero,
    Real.sqrt_sq hτ.le, sub_self, zero_div, Real.sqrt_zero, ofReal_zero, zero_mul]
  congr 2
  ring

namespace OnePortSource

/-- **(3), upper sheet.** `m(u² + iη) → h(u)` as `η → 0⁺`. -/
theorem tendsto_stieltjes_upper (hk : OnePortSource k) {u : ℝ} (hu : 0 < u) :
    Tendsto (fun η : ℝ => ∫ t in Ioi (0 : ℝ), (onePortDensity k t : ℂ) /
      ((t : ℂ) - ((u ^ 2 : ℝ) + η * I))) (𝓝[>] 0) (𝓝 (onePortConnection k u)) := by
  have hτ : 0 < u ^ 2 := by positivity
  have heq : ∀ η ∈ Ioi (0 : ℝ), onePortConnection k (upperRootPath (u ^ 2) η) =
      ∫ t in Ioi (0 : ℝ), (onePortDensity k t : ℂ) / ((t : ℂ) - ((u ^ 2 : ℝ) + η * I)) := by
    intro η hη
    rw [hk.onePortConnection_eq_stieltjes (upperRootPath_im_pos hη),
      upperRootPath_sq (le_of_lt hη)]
  refine Tendsto.congr' (eventually_nhdsWithin_of_forall heq) ?_
  have h0 : upperRootPath (u ^ 2) 0 = (u : ℂ) := by
    rw [upperRootPath_zero hτ, Real.sqrt_sq hu.le]
  have hw : Tendsto (upperRootPath (u ^ 2)) (𝓝[>] 0) (𝓝[{z : ℂ | 0 ≤ z.im}] (u : ℂ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, eventually_nhdsWithin_of_forall fun η hη =>
      (upperRootPath_im_pos hη).le⟩
    rw [← h0]
    exact ((continuous_upperRootPath _).tendsto 0).mono_left nhdsWithin_le_nhds
  exact (hk.continuousOn_onePortConnection (u : ℂ) (by simp)).tendsto.comp hw

/-- **(3), lower sheet.** `m(u² - iη) → h(-u) = conj h(u)` as `η → 0⁺`. -/
theorem tendsto_stieltjes_lower (hk : OnePortSource k) {u : ℝ} (hu : 0 < u) :
    Tendsto (fun η : ℝ => ∫ t in Ioi (0 : ℝ), (onePortDensity k t : ℂ) /
      ((t : ℂ) - ((u ^ 2 : ℝ) - η * I))) (𝓝[>] 0) (𝓝 (onePortConnection k (-u : ℝ))) := by
  rw [onePortConnection_neg_ofReal]
  have h := (continuous_conj.tendsto _).comp (hk.tendsto_stieltjes_upper hu)
  refine h.congr fun η => ?_
  simp only [Function.comp_apply]
  rw [← integral_div_sub_conj]
  congr 1
  funext t
  simp [map_add, map_mul, conj_ofReal, sub_eq_add_neg]

/-- **(3).** For `u > 0` the truncated principal value converges to `Re h(u)`:
`PV ∫₀^∞ σ(t)/(t - u²) dt = Re h(u)`. -/
theorem tendsto_onePortPrincipalValue (hk : OnePortSource k) {u : ℝ} (hu : 0 < u) :
    Tendsto (fun ε => ∫ t in Ioi (0 : ℝ) \ Icc (u ^ 2 - ε) (u ^ 2 + ε),
      onePortDensity k t / (t - u ^ 2)) (𝓝[>] 0) (𝓝 (onePortConnection k u).re) := by
  have hτ : 0 < u ^ 2 := by positivity
  have hA := (Complex.continuous_re.tendsto _).comp (hk.tendsto_stieltjes_upper hu)
  have hB := tendsto_re_stieltjes_sub_truncated hk.continuous_onePortDensity
    hk.integrableOn_onePortDensity_div hτ
    (L := (∫ x in Ioi (0 : ℝ), x * k x) / (Real.pi * √(u ^ 2)))
    (fun t _ => hk.abs_onePortDensity_sub_le t hτ)
  have h := hA.sub hB
  rw [sub_zero] at h
  refine h.congr fun ε => ?_
  simp only [Function.comp_apply]
  push_cast
  ring

end OnePortSource

end

end GaloisForLFunctions.HTGeometry
