import GaloisForLFunctions.RHTower.CHMDStage11SechSquareToeplitzSpectralDecomposition

/-!
# The d'Alembert kernel of the CHMD sech² wave

The massless (d'Alembert) counterpart of the CHMD prime kernel is the cosine transform of the
weight `sech²(r/2)`:

`(1/2π) ∫ sech²(r/2) cos(v r) dr = D(v),   D(v) = 2v / sinh(πv),   D(0) = 2/π`

(`integral_sechSqHalf_mul_cos_eq`).  This module builds `D` as a function of a complex variable,
`D(w) = 2 / S(w)` with the entire slope `S(w) = sinh(πw)/w` (`sinhSlope`, value `π` at `0`), so that
`D` is analytic wherever `S(w) ≠ 0`, i.e. off the punctured imaginary lattice `{k i : k ∈ ℤ, k ≠ 0}`
(`sinhSlope_eq_zero_iff`).  On the real line `D` is even, strictly positive and decays like
`8(1+|v|) e^{−π|v|}` (`dAlembertReal_pos`, `dAlembertReal_le`), and the product of two cosines
splits it into two translates (`integral_cos_mul_sechSqHalf_mul_cos`):

`(1/π) ∫ cos(a r) sech²(r/2) cos(r u) dr = D(u + a) + D(u − a)`.

Near the first poles `w = ± i` the kernel has the simple polar parts
`(w − i) D(w) → −2i/π` and `(w + i) D(w) → 2i/π` (`tendsto_sub_I_mul_dAlembertKernel`).
-/

open Complex MeasureTheory Set Filter Topology
open scoped ComplexConjugate Real
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower.CHMDLightCone

/-! ## The entire slope `sinh(πw)/w` -/

/-- The entire function `S(w) = sinh(πw)/w`, `S(0) = π`. -/
def sinhSlope (w : ℂ) : ℂ := dslope (fun w : ℂ => Complex.sinh (π * w)) 0 w

theorem differentiable_sinhSlope : Differentiable ℂ sinhSlope := by
  have h := (Complex.differentiableOn_dslope (f := fun w : ℂ => Complex.sinh (π * w)) (c := 0)
    (s := Set.univ) Filter.univ_mem).mpr
    (by fun_prop : Differentiable ℂ fun w : ℂ => Complex.sinh (π * w)).differentiableOn
  exact fun w => (h w (mem_univ _)).differentiableAt Filter.univ_mem

theorem sinhSlope_of_ne {w : ℂ} (hw : w ≠ 0) : sinhSlope w = Complex.sinh (π * w) / w := by
  rw [sinhSlope, dslope_of_ne _ hw, slope_def_field]
  simp

theorem sinhSlope_zero : sinhSlope 0 = π := by
  have h : HasDerivAt (fun w : ℂ => Complex.sinh (π * w)) (Complex.cosh (π * 0) * (π * 1)) 0 :=
    (Complex.hasDerivAt_sinh _).comp 0 ((hasDerivAt_id (0 : ℂ)).const_mul (π : ℂ))
  rw [sinhSlope, dslope_same, h.deriv]
  simp

theorem sinh_pi_mul_eq_zero_iff (w : ℂ) : Complex.sinh (π * w) = 0 ↔ ∃ k : ℤ, w = k * I := by
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  constructor
  · intro h
    have hs : Complex.sin (π * w * I) = 0 := by rw [Complex.sin_mul_I, h, zero_mul]
    obtain ⟨k, hk⟩ := Complex.sin_eq_zero_iff.mp hs
    have h1 : w * I = k := by
      apply mul_left_cancel₀ hpi
      linear_combination hk
    refine ⟨-k, ?_⟩
    push_cast
    linear_combination (-I) * h1 + w * I_sq
  · rintro ⟨k, rfl⟩
    rw [show (π : ℂ) * (k * I) = (k * π) * I by ring, Complex.sinh_mul_I, Complex.sin_int_mul_pi,
      zero_mul]

/-- The zeros of the slope are the nonzero integer multiples of `i`. -/
theorem sinhSlope_eq_zero_iff (w : ℂ) : sinhSlope w = 0 ↔ ∃ k : ℤ, k ≠ 0 ∧ w = k * I := by
  by_cases hw : w = 0
  · subst hw
    rw [sinhSlope_zero]
    simp only [ofReal_eq_zero, Real.pi_ne_zero, false_iff, not_exists, not_and]
    intro k hk h
    have : (k : ℂ) = 0 := by simpa using h.symm
    exact hk (by exact_mod_cast this)
  · rw [sinhSlope_of_ne hw, div_eq_zero_iff, or_iff_left hw, sinh_pi_mul_eq_zero_iff]
    refine ⟨fun ⟨k, hk⟩ => ⟨k, fun h0 => hw (by rw [hk, h0]; simp), hk⟩, fun ⟨k, _, hk⟩ => ⟨k, hk⟩⟩

theorem sinhSlope_ne_zero_of_abs_im_lt {w : ℂ} (hw : |w.im| < 1) : sinhSlope w ≠ 0 := by
  rw [Ne, sinhSlope_eq_zero_iff]
  rintro ⟨k, hk, rfl⟩
  simp only [mul_im, intCast_re, I_im, mul_one, intCast_im, I_re, mul_zero, add_zero] at hw
  have : (1 : ℝ) ≤ |(k : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hk
  linarith

theorem sinhSlope_ne_zero_of_re_ne {w : ℂ} (hw : w.re ≠ 0) : sinhSlope w ≠ 0 := by
  rw [Ne, sinhSlope_eq_zero_iff]
  rintro ⟨k, -, rfl⟩
  simp at hw

theorem sinhSlope_neg (w : ℂ) : sinhSlope (-w) = sinhSlope w := by
  by_cases hw : w = 0
  · subst hw; simp
  · rw [sinhSlope_of_ne (neg_ne_zero.mpr hw), sinhSlope_of_ne hw, mul_neg, Complex.sinh_neg,
      neg_div_neg_eq]

theorem sinhSlope_conj (w : ℂ) : sinhSlope (conj w) = conj (sinhSlope w) := by
  by_cases hw : w = 0
  · subst hw; simp [sinhSlope_zero]
  · rw [sinhSlope_of_ne ((map_ne_zero _).mpr hw), sinhSlope_of_ne hw, map_div₀,
      ← Complex.sinh_conj, map_mul, Complex.conj_ofReal]

/-! ## The d'Alembert kernel -/

/-- The d'Alembert kernel `D(w) = 2/S(w) = 2w/sinh(πw)`, `D(0) = 2/π`. -/
def dAlembertKernel (w : ℂ) : ℂ := 2 / sinhSlope w

theorem dAlembertKernel_of_ne {w : ℂ} (hw : w ≠ 0) :
    dAlembertKernel w = 2 * w / Complex.sinh (π * w) := by
  rw [dAlembertKernel, sinhSlope_of_ne hw, div_div_eq_mul_div]

theorem dAlembertKernel_zero : dAlembertKernel 0 = 2 / π := by
  rw [dAlembertKernel, sinhSlope_zero]

theorem dAlembertKernel_neg (w : ℂ) : dAlembertKernel (-w) = dAlembertKernel w := by
  rw [dAlembertKernel, dAlembertKernel, sinhSlope_neg]

theorem dAlembertKernel_conj (w : ℂ) : dAlembertKernel (conj w) = conj (dAlembertKernel w) := by
  rw [dAlembertKernel, dAlembertKernel, sinhSlope_conj, map_div₀, map_ofNat]

theorem differentiableAt_dAlembertKernel {w : ℂ} (hw : sinhSlope w ≠ 0) :
    DifferentiableAt ℂ dAlembertKernel w :=
  (differentiableAt_const _).div (differentiable_sinhSlope w) hw

theorem differentiableOn_dAlembertKernel : DifferentiableOn ℂ dAlembertKernel {w | sinhSlope w ≠ 0} :=
  fun _ hw => (differentiableAt_dAlembertKernel hw).differentiableWithinAt

theorem isOpen_sinhSlope_ne_zero : IsOpen {w : ℂ | sinhSlope w ≠ 0} :=
  isOpen_ne_fun differentiable_sinhSlope.continuous continuous_const

/-! ## The real kernel -/

/-- The d'Alembert kernel on the real line. -/
def dAlembertReal (v : ℝ) : ℝ := (dAlembertKernel v).re

theorem dAlembertReal_of_ne {v : ℝ} (hv : v ≠ 0) : dAlembertReal v = 2 * v / Real.sinh (π * v) := by
  rw [dAlembertReal, dAlembertKernel_of_ne (by exact_mod_cast hv),
    show (2 : ℂ) * v / Complex.sinh (π * v) = ((2 * v / Real.sinh (π * v) : ℝ) : ℂ) by
      push_cast; rfl, ofReal_re]

theorem dAlembertReal_zero : dAlembertReal 0 = 2 / π := by
  rw [dAlembertReal, ofReal_zero, dAlembertKernel_zero,
    show (2 : ℂ) / π = ((2 / π : ℝ) : ℂ) by push_cast; rfl, ofReal_re]

theorem dAlembertKernel_ofReal (v : ℝ) : dAlembertKernel v = (dAlembertReal v : ℂ) := by
  by_cases hv : v = 0
  · subst hv
    rw [dAlembertReal_zero, ofReal_zero, dAlembertKernel_zero]
    push_cast; rfl
  · rw [dAlembertReal_of_ne hv, dAlembertKernel_of_ne (by exact_mod_cast hv)]
    push_cast; rfl

theorem dAlembertReal_neg (v : ℝ) : dAlembertReal (-v) = dAlembertReal v := by
  rw [dAlembertReal, dAlembertReal, ofReal_neg, dAlembertKernel_neg]

theorem dAlembertReal_pos (v : ℝ) : 0 < dAlembertReal v := by
  rcases lt_trichotomy v 0 with hv | hv | hv
  · rw [← dAlembertReal_neg, dAlembertReal_of_ne (by linarith)]
    have : 0 < Real.sinh (π * -v) := Real.sinh_pos_iff.mpr (by nlinarith [Real.pi_pos])
    exact div_pos (by linarith) this
  · rw [hv, dAlembertReal_zero]; exact div_pos two_pos Real.pi_pos
  · rw [dAlembertReal_of_ne hv.ne']
    exact div_pos (by linarith) (Real.sinh_pos_iff.mpr (by positivity))

theorem continuous_dAlembertReal : Continuous dAlembertReal := by
  have h : Continuous fun v : ℝ => dAlembertKernel v :=
    continuous_iff_continuousAt.mpr fun v =>
      ((differentiableAt_dAlembertKernel (sinhSlope_ne_zero_of_abs_im_lt (by simp))).continuousAt).comp
        continuous_ofReal.continuousAt
  exact continuous_re.comp h

theorem exp_div_four_le_sinh {x : ℝ} (hx : 1 ≤ x) : Real.exp x / 4 ≤ Real.sinh x := by
  rw [Real.sinh_eq]
  have h1 : Real.exp (-x) ≤ Real.exp x / 2 := by
    have h2 : 2 ≤ Real.exp (2 * x) := by linarith [Real.add_one_le_exp (2 * x)]
    have h3 : Real.exp (2 * x) = Real.exp x * Real.exp x := by rw [← Real.exp_add]; ring_nf
    have h4 : Real.exp (-x) * Real.exp x = 1 := by rw [← Real.exp_add]; simp
    have hpos := Real.exp_pos x
    nlinarith
  linarith

/-- **Exponential decay of the d'Alembert kernel**: `D(v) ≤ 8 (1 + |v|) e^{−π|v|}`. -/
theorem dAlembertReal_le (v : ℝ) : dAlembertReal v ≤ 8 * (1 + |v|) * Real.exp (-(π * |v|)) := by
  wlog hv : 0 ≤ v generalizing v
  · have := this (-v) (by linarith)
    rwa [dAlembertReal_neg, abs_neg] at this
  rw [abs_of_nonneg hv]
  rcases hv.eq_or_lt with h0 | hpos
  · subst h0
    rw [dAlembertReal_zero]
    simp only [mul_zero, neg_zero, Real.exp_zero, mul_one, add_zero]
    have := Real.pi_gt_three
    rw [div_le_iff₀ Real.pi_pos]
    nlinarith
  rw [dAlembertReal_of_ne hpos.ne']
  have hsinh : 0 < Real.sinh (π * v) := Real.sinh_pos_iff.mpr (by positivity)
  rw [div_le_iff₀ hsinh]
  by_cases hbig : 1 ≤ π * v
  · have h := exp_div_four_le_sinh hbig
    have hE : Real.exp (-(π * v)) * Real.exp (π * v) = 1 := by rw [← Real.exp_add]; simp
    have hE0 := Real.exp_pos (-(π * v))
    have hA : 8 * (1 + v) * Real.exp (-(π * v)) * (Real.exp (π * v) / 4) ≤
        8 * (1 + v) * Real.exp (-(π * v)) * Real.sinh (π * v) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    have hB : 8 * (1 + v) * Real.exp (-(π * v)) * (Real.exp (π * v) / 4) = 2 * (1 + v) := by
      linear_combination (2 * (1 + v)) * hE
    linarith
  · have hsmall : π * v < 1 := not_le.mp hbig
    have h1 : π * v ≤ Real.sinh (π * v) := Real.self_le_sinh_iff.mpr (by positivity)
    have h2 : Real.exp (-1) ≤ Real.exp (-(π * v)) := Real.exp_le_exp.mpr (by linarith)
    have h3 : 1 / 4 ≤ Real.exp (-1) := by
      rw [Real.exp_neg, inv_eq_one_div]
      exact one_div_le_one_div_of_le (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
    have hA : 1 / 4 * (π * v) ≤ Real.exp (-(π * v)) * Real.sinh (π * v) :=
      mul_le_mul (h3.trans h2) h1 (by positivity) (Real.exp_pos _).le
    have hpi := Real.pi_gt_three
    have hB : 8 * (1 + v) * (1 / 4 * (π * v)) ≤
        8 * (1 + v) * (Real.exp (-(π * v)) * Real.sinh (π * v)) :=
      mul_le_mul_of_nonneg_left hA (by positivity)
    have hC0 : 0 ≤ v * ((1 + v) * π - 1) := mul_nonneg hv (by nlinarith)
    have hC : 2 * v ≤ 8 * (1 + v) * (1 / 4 * (π * v)) := by nlinarith [hC0]
    have hD : 8 * (1 + v) * Real.exp (-(π * v)) * Real.sinh (π * v) =
        8 * (1 + v) * (Real.exp (-(π * v)) * Real.sinh (π * v)) := by ring
    linarith

/-! ## The cosine transform of `sech²(r/2)` -/

theorem integrable_sechSqHalf_mul {g : ℝ → ℝ} (hg : Continuous g) (hb : ∀ r, |g r| ≤ 1) :
    Integrable fun r => sechSqHalf r * g r :=
  integrable_sechSqHalf.mono' (continuous_sechSqHalf.mul hg).aestronglyMeasurable
    (Eventually.of_forall fun r => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (sechSqHalf_pos r)]
      exact mul_le_of_le_one_right (sechSqHalf_pos r).le (hb r))

/-- **`(1/2π) ∫ sech²(r/2) cos(r v) dr = D(v)`.** -/
theorem integral_sechSqHalf_mul_cos_eq (v : ℝ) :
    ∫ r : ℝ, sechSqHalf r * Real.cos (r * v) = 2 * π * dAlembertReal v := by
  have key : ∀ x : ℝ, 0 < x → ∫ r : ℝ, sechSqHalf r * Real.cos (r * x) = 2 * π * dAlembertReal x := by
    intro x hx
    have h := CHMDStage11.integral_sechSqHalf_mul_cos_of_pos hx
    rw [dAlembertReal_of_ne hx.ne']
    have hpi := Real.pi_pos
    have hs : 0 < Real.sinh (π * x) := Real.sinh_pos_iff.mpr (by positivity)
    rw [show 2 * π * (2 * x / Real.sinh (π * x)) = π * (4 * x / Real.sinh (π * x)) by ring, ← h,
      ← mul_assoc, mul_one_div_cancel hpi.ne', one_mul]
  rcases lt_trichotomy v 0 with hv | hv | hv
  · have h := key (-v) (by linarith)
    rw [dAlembertReal_neg] at h
    rw [← h]
    congr 1; funext r
    rw [mul_neg, Real.cos_neg]
  · subst hv
    simp only [mul_zero, Real.cos_zero, mul_one, integral_sechSqHalf, dAlembertReal_zero]
    field_simp
    norm_num
  · exact key v hv

/-- **Product of cosines**: `(1/π) ∫ cos(a r) sech²(r/2) cos(r u) dr = D(u + a) + D(u − a)`. -/
theorem integral_cos_mul_sechSqHalf_mul_cos (a u : ℝ) :
    1 / π * ∫ r : ℝ, Real.cos (a * r) * sechSqHalf r * Real.cos (r * u) =
      dAlembertReal (u + a) + dAlembertReal (u - a) := by
  have h : ∀ r : ℝ, Real.cos (a * r) * sechSqHalf r * Real.cos (r * u) =
      (1 / 2) * (sechSqHalf r * Real.cos (r * (u + a))) +
        (1 / 2) * (sechSqHalf r * Real.cos (r * (u - a))) := by
    intro r
    rw [show r * (u + a) = r * u + a * r by ring, show r * (u - a) = r * u - a * r by ring,
      Real.cos_add, Real.cos_sub]
    ring
  simp_rw [h]
  rw [integral_add ((integrable_sechSqHalf_mul (by fun_prop) fun r => Real.abs_cos_le_one _).const_mul _)
      ((integrable_sechSqHalf_mul (by fun_prop) fun r => Real.abs_cos_le_one _).const_mul _),
    integral_const_mul, integral_const_mul, integral_sechSqHalf_mul_cos_eq,
    integral_sechSqHalf_mul_cos_eq]
  have hpi := Real.pi_pos
  field_simp

/-! ## The polar part at `w = i` -/

/-- **The first pole**: `(w − i) D(w) → −2i/π` as `w → i`. -/
theorem tendsto_sub_I_mul_dAlembertKernel :
    Tendsto (fun w => (w - I) * dAlembertKernel w) (𝓝[≠] I) (𝓝 (-2 * I / π)) := by
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hd : HasDerivAt (fun w : ℂ => Complex.sinh (π * w)) (Complex.cosh (π * I) * (π * 1)) I :=
    (Complex.hasDerivAt_sinh _).comp I ((hasDerivAt_id I).const_mul (π : ℂ))
  have hcosh : Complex.cosh (π * I) * (π * 1) = -π := by
    rw [Complex.cosh_mul_I, ← ofReal_cos, Real.cos_pi]; push_cast; ring
  rw [hcosh] at hd
  have hsl := hasDerivAt_iff_tendsto_slope.mp hd
  have hsinhI : Complex.sinh (π * I) = 0 := by
    rw [Complex.sinh_mul_I, ← ofReal_sin, Real.sin_pi, ofReal_zero, zero_mul]
  have hinv := hsl.inv₀ (neg_ne_zero.mpr hpi)
  have hw : Tendsto (fun w : ℂ => 2 * w) (𝓝[≠] I) (𝓝 (2 * I)) :=
    ((continuous_const.mul continuous_id).tendsto I).mono_left nhdsWithin_le_nhds
  have hlim : 2 * I * (-(π : ℂ))⁻¹ = -2 * I / π := by field_simp
  rw [← hlim]
  refine (hw.mul hinv).congr' ?_
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (isOpen_ne.mem_nhds (by simp : I ≠ 0))] with w hwI hw0
  rw [slope_def_module, hsinhI, sub_zero, smul_eq_mul, mul_inv, inv_inv,
    dAlembertKernel_of_ne hw0]
  have : w - I ≠ 0 := sub_ne_zero.mpr hwI
  field_simp

end RHTower.CHMDLightCone
