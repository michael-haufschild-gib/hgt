import GaloisForLFunctions.RHTower.ThetaHalfPortStieltjesSpectral
import GaloisForLFunctions.RHTower.ThetaZeroDivisionSource
import GaloisForLFunctions.HTGeometry.WaveTraceSpectrum
import GaloisForLFunctions.HTGeometry.WaveTracePoleTransform

/-!
# Theta Xi as an equality of reflected Lévy jump exponents

For the literal even theta source `k` put `ω = -k' > 0` on `(0, ∞)` (total mass `k(0)`),
`h(z) = ∫₀^∞ k(x) e^{izx} dx` and `K(z) = ∫₀^∞ ω(x)(1 - e^{izx}) dx`.

* Integration by parts gives the entire identities `K(z) = -iz h(z)` and
  `K(z) - K(-z) = -iz Ξ(z)`: every nonzero Xi zero is an equality `K(z) = K(-z)`.
* On the real axis `K(u) = B(u) - i uΞ(u)/2`, `u h(u) = uΞ(u)/2 + iB(u)` with
  `B(u) = ∫₀^∞ ω(1 - cos ux) = πuσ(u²) > 0`.
* The finite positive measure `dν = ω(x)/x dx` (bounded density since `k'(0) = 0`) has entire even
  exponent `G(z) = ∫₀^∞ (1 - cos zx) dν` with `G'(z) = ∫₀^∞ ω sin(zx) = zΞ(z)/2`,
  `K(z) - K(-z) = -2iG'(z)`, `G(u) > 0` for real `u ≠ 0` and `∫₀^u vΞ(v) dv = 2G(u)`.
* `d/dz e^{-tG} = -(tzΞ/2) e^{-tG}`: the nonzero Xi divisor is the critical-point set of the
  nowhere-zero entire semigroup `e^{-tG}`.
* `M = Ξ(0) = 2∫₀^∞ x ω`, the size-biased radius law `2xω(x)/M dx` is a probability law and
  `Ξ(z)/M = E[sin(zR)/(zR)]` for every complex `z`.
-/
open Complex Filter Topology Set MeasureTheory
open scoped ComplexConjugate

namespace RHTower

noncomputable section

/-! ## The jump density `ω = -k'` -/

/-- The jump density `ω = -k'` of the literal theta source. -/
def thetaJumpDensity (x : ℝ) : ℝ := -deriv thetaCuspFullSource x

theorem thetaJumpDensity_pos {x : ℝ} (hx : 0 < x) : 0 < thetaJumpDensity x := by
  rw [thetaJumpDensity]; linarith [deriv_thetaCuspFullSource_neg_of_pos hx]

theorem continuous_thetaJumpDensity : Continuous thetaJumpDensity :=
  continuous_deriv_thetaCuspFullSource.neg

theorem exists_abs_thetaJumpDensity_le (A : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |thetaJumpDensity x| ≤ C * Real.exp (-(A * |x|)) := by
  obtain ⟨C, hC, h⟩ := exists_abs_deriv_thetaCuspFullSource_le A
  exact ⟨C, hC, fun x => by rw [thetaJumpDensity, abs_neg]; exact h x⟩

/-- `ω` against any complex exponential is integrable on the whole line. -/
theorem integrable_thetaJumpDensity_mul_cexp (w : ℂ) :
    Integrable fun x : ℝ => (thetaJumpDensity x : ℂ) * cexp (w * x) := by
  obtain ⟨C, hC, h⟩ := exists_abs_thetaJumpDensity_le (‖w‖ + 1)
  have hc := continuous_thetaJumpDensity
  refine ((integrable_exp_neg_abs_line).const_mul C).mono' (by fun_prop)
    (Eventually.of_forall fun x => ?_)
  rw [norm_mul, Complex.norm_real, Complex.norm_exp, Real.norm_eq_abs]
  have h2 : (w * x).re ≤ ‖w‖ * |x| :=
    (Complex.re_le_norm _).trans (by rw [norm_mul, Complex.norm_real, Real.norm_eq_abs])
  calc |thetaJumpDensity x| * Real.exp (w * x).re
      ≤ C * Real.exp (-((‖w‖ + 1) * |x|)) * Real.exp (‖w‖ * |x|) :=
        mul_le_mul (h x) (Real.exp_le_exp.mpr h2) (Real.exp_pos _).le (by positivity)
    _ = C * Real.exp (-|x|) := by rw [mul_assoc, ← Real.exp_add]; ring_nf

theorem integrable_thetaJumpDensity : Integrable thetaJumpDensity := by
  have h := (integrable_thetaJumpDensity_mul_cexp 0).re
  simpa using h

/-- The jump measure `ω dx` has total mass `k(0)`. -/
theorem integral_thetaJumpDensity : ∫ x in Ioi (0 : ℝ), thetaJumpDensity x = thetaCuspFullSource 0 := by
  simp only [thetaJumpDensity]
  rw [integral_neg, integral_Ioi_deriv_thetaCuspFullSource, neg_neg]

/-! ## The reflected jump exponents -/

/-- The jump exponent `K(z) = ∫₀^∞ ω(x) (1 - e^{izx}) dx`. -/
def thetaJumpExponent (z : ℂ) : ℂ :=
  ∫ x in Ioi (0 : ℝ), (thetaJumpDensity x : ℂ) * (1 - cexp (I * z * x))

theorem integrableOn_thetaJumpExponent (z : ℂ) :
    IntegrableOn (fun x : ℝ => (thetaJumpDensity x : ℂ) * (1 - cexp (I * z * x))) (Ioi 0) := by
  have h0 := integrable_thetaJumpDensity_mul_cexp 0
  have h1 := integrable_thetaJumpDensity_mul_cexp (I * z)
  refine (h0.sub h1).integrableOn.congr_fun (fun x _ => ?_) measurableSet_Ioi
  simp only [Pi.sub_apply, zero_mul, Complex.exp_zero]
  ring

/-- **(2).** `K(z) = -iz h(z)` for every complex `z`. -/
theorem thetaJumpExponent_eq (z : ℂ) :
    thetaJumpExponent z = -(I * z) * thetaOneSidedConnection z := by
  have hu : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt (fun t : ℝ => (thetaCuspFullSource t : ℂ))
      ((deriv thetaCuspFullSource x : ℝ) : ℂ) x :=
    fun x _ => (differentiable_thetaCuspFullSource x).hasDerivAt.ofReal_comp
  have hv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt (fun t : ℝ => 1 - cexp (I * z * t))
      (-(I * z * cexp (I * z * x))) x := fun x _ => by
    have h := ((hasDerivAt_id (x : ℂ)).const_mul (I * z)).cexp.comp_ofReal
    exact (h.const_sub 1).congr_deriv (by simp only [id]; ring)
  have hk := integrableOn_cexp_mul_thetaCuspFullSource (I * z) (Ioi 0)
  have huv' : IntegrableOn ((fun t : ℝ => (thetaCuspFullSource t : ℂ)) *
      fun x : ℝ => -(I * z * cexp (I * z * (x : ℂ)))) (Ioi 0) :=
    IntegrableOn.congr_fun (Integrable.const_mul hk (-(I * z)))
      (fun x _ => by simp only [Pi.mul_apply]; ring) measurableSet_Ioi
  have hu'v : IntegrableOn ((fun x => ((deriv thetaCuspFullSource x : ℝ) : ℂ)) *
      fun t : ℝ => 1 - cexp (I * z * t)) (Ioi 0) :=
    (integrableOn_thetaJumpExponent z).neg.congr_fun (fun x _ => by
      simp only [Pi.mul_apply, Pi.neg_apply, thetaJumpDensity]; push_cast; ring) measurableSet_Ioi
  have hcont : Continuous fun t : ℝ => (thetaCuspFullSource t : ℂ) * (1 - cexp (I * z * t)) := by
    have := continuous_thetaCuspFullSource; fun_prop
  have hlim0 : Tendsto ((fun t : ℝ => (thetaCuspFullSource t : ℂ)) *
      fun t : ℝ => 1 - cexp (I * z * t)) (𝓝[>] 0) (𝓝 0) := by
    have := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, sub_self] at this
    exact this
  have hlimtop : Tendsto ((fun t : ℝ => (thetaCuspFullSource t : ℂ)) *
      fun t : ℝ => 1 - cexp (I * z * t)) atTop (𝓝 0) := by
    obtain ⟨C, hC, hb⟩ := exists_abs_thetaCuspFullSource_le (‖z‖ + 1)
    refine squeeze_zero_norm' ?_ ((Real.tendsto_exp_neg_atTop_nhds_zero).const_mul (2 * C) |>.congr'
      (Eventually.of_forall fun t => rfl) |> fun h => by simpa using h)
    filter_upwards [eventually_ge_atTop 0] with t ht
    simp only [Pi.mul_apply]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hbt := hb t
    rw [abs_of_nonneg ht] at hbt
    have he : ‖1 - cexp (I * z * t)‖ ≤ 2 * Real.exp (‖z‖ * t) := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_one, Complex.norm_exp]
      have hre : (I * z * (t : ℂ)).re ≤ ‖z‖ * t :=
        (Complex.re_le_norm _).trans (by
          rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg ht])
      have h1 : (1 : ℝ) ≤ Real.exp (‖z‖ * t) := Real.one_le_exp (by positivity)
      linarith [Real.exp_le_exp.mpr hre]
    calc |thetaCuspFullSource t| * ‖1 - cexp (I * z * t)‖
        ≤ C * Real.exp (-((‖z‖ + 1) * t)) * (2 * Real.exp (‖z‖ * t)) :=
          mul_le_mul hbt he (norm_nonneg _) (by positivity)
      _ = 2 * C * Real.exp (-t) := by
          rw [show C * Real.exp (-((‖z‖ + 1) * t)) * (2 * Real.exp (‖z‖ * t)) =
            2 * C * (Real.exp (-((‖z‖ + 1) * t)) * Real.exp (‖z‖ * t)) by ring, ← Real.exp_add]
          ring_nf
  have hibp := integral_Ioi_mul_deriv_eq_deriv_mul hu hv huv' hu'v hlim0 hlimtop
  rw [sub_self, zero_sub] at hibp
  rw [thetaJumpExponent, thetaOneSidedConnection]
  have hK : ∫ x in Ioi (0 : ℝ), (thetaJumpDensity x : ℂ) * (1 - cexp (I * z * x)) =
      -∫ x in Ioi (0 : ℝ), ((deriv thetaCuspFullSource x : ℝ) : ℂ) * (1 - cexp (I * z * x)) := by
    rw [← integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    simp only [thetaJumpDensity]; push_cast; ring
  rw [hK, ← hibp, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
  ring

/-- **(2).** `K(z) - K(-z) = -iz Ξ(z)`. -/
theorem thetaJumpExponent_sub_neg (z : ℂ) :
    thetaJumpExponent z - thetaJumpExponent (-z) = -(I * z) * XiC z := by
  rw [thetaJumpExponent_eq, thetaJumpExponent_eq, XiC_eq_thetaOneSidedConnection_add]
  ring

/-- Every nonzero Xi zero is an equality of the reflected exponents. -/
theorem XiC_eq_zero_iff_thetaJumpExponent_eq {z : ℂ} (hz : z ≠ 0) :
    XiC z = 0 ↔ thetaJumpExponent z = thetaJumpExponent (-z) := by
  have h := thetaJumpExponent_sub_neg z
  have hIz : -(I * z) ≠ 0 := neg_ne_zero.mpr (mul_ne_zero I_ne_zero hz)
  constructor
  · intro hX; rw [hX, mul_zero] at h; exact sub_eq_zero.mp h
  · intro hK; rw [hK, sub_self] at h
    exact (mul_eq_zero.mp h.symm).resolve_left hIz

/-! ## The real axis -/

/-- `B(u) = ∫₀^∞ ω(x) (1 - cos ux) dx`. -/
def thetaJumpCosineMass (u : ℝ) : ℝ :=
  ∫ x in Ioi (0 : ℝ), thetaJumpDensity x * (1 - Real.cos (u * x))

/-- A positive integrable weight against `1 - cos(ux)`, `u ≠ 0`, has positive integral. -/
theorem integral_mul_one_sub_cos_pos {f : ℝ → ℝ} (hf : ContinuousOn f (Ioi 0))
    (hpos : ∀ x, 0 < x → 0 < f x) (hint : IntegrableOn f (Ioi 0)) {u : ℝ} (hu : u ≠ 0) :
    0 < ∫ x in Ioi (0 : ℝ), f x * (1 - Real.cos (u * x)) := by
  have hu' : 0 < |u| := abs_pos.mpr hu
  set P := 2 * Real.pi / |u|
  have hP : 0 < P := by positivity
  have hg0 : ∀ x ∈ Ioi (0 : ℝ), 0 ≤ f x * (1 - Real.cos (u * x)) := fun x hx =>
    mul_nonneg (hpos x hx).le (by linarith [Real.cos_le_one (u * x)])
  have hgint : IntegrableOn (fun x => f x * (1 - Real.cos (u * x))) (Ioi 0) := by
    refine (hint.norm.mul_const 2).mono' ?_ ((ae_restrict_iff' measurableSet_Ioi).mpr
      (ae_of_all _ fun x _ => ?_))
    · exact (hf.mul (by fun_prop)).aestronglyMeasurable measurableSet_Ioi
    · rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      rw [abs_le]; constructor <;> linarith [Real.neg_one_le_cos (u * x), Real.cos_le_one (u * x)]
  have hsub : Ioo 0 P ⊆ Ioi (0 : ℝ) := fun x hx => hx.1
  have hpos' : 0 < ∫ x in Ioo 0 P, f x * (1 - Real.cos (u * x)) := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hP.le]
    refine intervalIntegral.intervalIntegral_pos_of_pos_on ?_ (fun x hx => mul_pos (hpos x hx.1) ?_) hP
    · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hP.le).mpr
        (hgint.mono_set Ioc_subset_Ioi_self)
    · have hcos : Real.cos (u * x) = Real.cos (|u| * x) := by
        rcases abs_cases u with ⟨h, _⟩ | ⟨h, _⟩
        · rw [h]
        · rw [h, neg_mul, Real.cos_neg]
      rw [hcos, sub_pos]
      have h1 : 0 < |u| * x := mul_pos hu' hx.1
      have h2 : |u| * x < 2 * Real.pi := by
        have := mul_lt_mul_of_pos_left hx.2 hu'
        rwa [show |u| * P = 2 * Real.pi by simp only [P]; field_simp] at this
      refine lt_of_le_of_ne (Real.cos_le_one _) fun h => ?_
      have := (Real.cos_eq_one_iff_of_lt_of_lt (by linarith [Real.pi_pos]) h2).mp h
      linarith
  calc 0 < ∫ x in Ioo 0 P, f x * (1 - Real.cos (u * x)) := hpos'
    _ ≤ ∫ x in Ioi (0 : ℝ), f x * (1 - Real.cos (u * x)) :=
        setIntegral_mono_set hgint ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ hg0))
          (Eventually.of_forall hsub)

theorem thetaJumpCosineMass_pos {u : ℝ} (hu : u ≠ 0) : 0 < thetaJumpCosineMass u :=
  integral_mul_one_sub_cos_pos continuous_thetaJumpDensity.continuousOn
    (fun _ hx => thetaJumpDensity_pos hx) integrable_thetaJumpDensity.integrableOn hu

/-- **(3).** `K(u) = B(u) - i uΞ(u)/2` on the real axis. -/
theorem thetaJumpExponent_ofReal (u : ℝ) :
    thetaJumpExponent u = (thetaJumpCosineMass u : ℂ) - I * (u * Xi u / 2 : ℝ) := by
  have hint := integrableOn_thetaJumpExponent (u : ℂ)
  have hre : (thetaJumpExponent u).re = thetaJumpCosineMass u := by
    have h := integral_re hint
    simp only [RCLike.re_to_complex] at h
    rw [thetaJumpExponent, ← h, thetaJumpCosineMass]
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    rw [Complex.re_ofReal_mul, Complex.sub_re, Complex.one_re,
      show I * (u : ℂ) * x = ((u * x : ℝ) : ℂ) * I by push_cast; ring, Complex.exp_ofReal_mul_I_re]
  have hconj : thetaJumpExponent (-(u : ℂ)) = conj (thetaJumpExponent u) := by
    rw [thetaJumpExponent, thetaJumpExponent, ← integral_conj]
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    rw [map_mul, Complex.conj_ofReal, map_sub, map_one, ← Complex.exp_conj]
    congr 3
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring
  have hsub := thetaJumpExponent_sub_neg u
  rw [hconj, XiC_ofReal] at hsub
  have him : (thetaJumpExponent u).im = -(u * Xi u / 2) := by
    have := congrArg Complex.im hsub
    simp only [Complex.sub_im, Complex.conj_im, Complex.mul_im, Complex.neg_re, Complex.neg_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re] at this
    linarith
  apply Complex.ext
  · simp [hre]
  · simp [him]

/-- **(3).** `u h(u) = uΞ(u)/2 + i B(u)`. -/
theorem mul_thetaOneSidedConnection_ofReal (u : ℝ) :
    (u : ℂ) * thetaOneSidedConnection u = (u * Xi u / 2 : ℝ) + I * (thetaJumpCosineMass u : ℂ) := by
  have h := thetaJumpExponent_eq (u : ℂ)
  rw [thetaJumpExponent_ofReal] at h
  have : (u : ℂ) * thetaOneSidedConnection u = I * (-(I * u) * thetaOneSidedConnection u) := by
    linear_combination (u * thetaOneSidedConnection u) * I_sq
  rw [this, ← h]
  linear_combination (-(u * Xi u / 2 : ℝ) : ℂ) * I_sq

/-- **(3).** `B(u) = π u σ(u²)` for `u > 0`. -/
theorem thetaJumpCosineMass_eq_pi_mul_thetaPortDensity {u : ℝ} (hu : 0 < u) :
    thetaJumpCosineMass u = Real.pi * u * thetaPortDensity (u ^ 2) := by
  rw [thetaPortDensity_sq hu]
  have h := congrArg Complex.im (mul_thetaOneSidedConnection_ofReal u)
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
    Complex.add_im, Complex.I_re, Complex.I_im, one_mul, zero_add] at h
  field_simp
  linarith

/-- At a positive real Xi zero the exponent `K(u) = B(u)` is strictly positive real. -/
theorem thetaJumpExponent_of_Xi_eq_zero {u : ℝ} (hu : 0 < u) (hX : Xi u = 0) :
    thetaJumpExponent u = (thetaJumpCosineMass u : ℂ) ∧ 0 < thetaJumpCosineMass u := by
  refine ⟨?_, thetaJumpCosineMass_pos hu.ne'⟩
  rw [thetaJumpExponent_ofReal, hX]; simp

/-! ## The dispersion exponent `G` -/

theorem deriv_thetaCuspFullSource_zero : deriv thetaCuspFullSource 0 = 0 := by
  have h := deriv_comp_neg thetaCuspFullSource 0
  rw [show (fun x => thetaCuspFullSource (-x)) = thetaCuspFullSource from
    funext thetaCuspFullSource_neg, neg_zero] at h
  linarith

/-- `|k'(x)| ≤ C |x|`: the jump density vanishes linearly at the seam. -/
theorem exists_abs_deriv_thetaCuspFullSource_le_mul :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |deriv thetaCuspFullSource x| ≤ C * |x| := by
  obtain ⟨C, hC, h⟩ := exists_abs_iteratedDeriv_thetaCuspFullSource_le 0 2
  refine ⟨C, hC, fun x => ?_⟩
  have hd : ∀ y ∈ (univ : Set ℝ), DifferentiableAt ℝ (deriv thetaCuspFullSource) y := fun y _ =>
    ((contDiff_thetaCuspFullSource.differentiable_iteratedDeriv 1 (by simp)) y).congr_of_eventuallyEq
      (Eventually.of_forall fun z => by rw [iteratedDeriv_one])
  have hb : ∀ y ∈ (univ : Set ℝ), ‖deriv (deriv thetaCuspFullSource) y‖ ≤ C := fun y _ => by
    have := h y
    rw [show iteratedDeriv 2 thetaCuspFullSource = deriv (deriv thetaCuspFullSource) by
      rw [iteratedDeriv_succ, iteratedDeriv_one]] at this
    simpa using this
  have := convex_univ.norm_image_sub_le_of_norm_deriv_le hd hb (mem_univ 0) (mem_univ x)
  simpa [deriv_thetaCuspFullSource_zero] using this

/-- The Lévy density `ω(x)/x` of the dispersion measure `ν`. -/
def thetaLevyDensity (x : ℝ) : ℝ := thetaJumpDensity x / x

theorem thetaLevyDensity_pos {x : ℝ} (hx : 0 < x) : 0 < thetaLevyDensity x :=
  div_pos (thetaJumpDensity_pos hx) hx

theorem continuousOn_thetaLevyDensity : ContinuousOn thetaLevyDensity (Ioi 0) :=
  continuous_thetaJumpDensity.continuousOn.div continuousOn_id fun _ hx => ne_of_gt hx

theorem mul_thetaLevyDensity {x : ℝ} (hx : x ≠ 0) : x * thetaLevyDensity x = thetaJumpDensity x := by
  rw [thetaLevyDensity]; field_simp

/-- `ν` decays faster than every exponential on the positive ray. -/
theorem exists_abs_thetaLevyDensity_le {A : ℝ} (hA : 0 ≤ A) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x, 0 < x → |thetaLevyDensity x| ≤ K * Real.exp (-(A * x)) := by
  obtain ⟨C₂, hC₂, h₂⟩ := exists_abs_deriv_thetaCuspFullSource_le_mul
  obtain ⟨CA, hCA, hA'⟩ := exists_abs_thetaJumpDensity_le A
  refine ⟨C₂ * Real.exp A + CA, by positivity, fun x hx => ?_⟩
  rw [thetaLevyDensity, abs_div, abs_of_pos hx, div_le_iff₀ hx]
  have he := Real.exp_pos (-(A * x))
  rcases le_or_gt x 1 with h1 | h1
  · have hω : |thetaJumpDensity x| ≤ C₂ * x := by
      have := h₂ x; rwa [abs_of_pos hx, ← abs_neg] at this
    have hex : 1 ≤ Real.exp A * Real.exp (-(A * x)) := by
      rw [← Real.exp_add]; exact Real.one_le_exp (by nlinarith)
    calc |thetaJumpDensity x| ≤ C₂ * x := hω
      _ ≤ C₂ * (Real.exp A * Real.exp (-(A * x))) * x := by
          have := mul_le_mul_of_nonneg_left hex hC₂; nlinarith
      _ ≤ (C₂ * Real.exp A + CA) * Real.exp (-(A * x)) * x := by nlinarith [mul_nonneg hCA he.le]
  · have hω := hA' x
    rw [abs_of_pos hx] at hω
    calc |thetaJumpDensity x| ≤ CA * Real.exp (-(A * x)) := hω
      _ ≤ (C₂ * Real.exp A + CA) * Real.exp (-(A * x)) * 1 := by
          have : 0 ≤ C₂ * Real.exp A * Real.exp (-(A * x)) := by positivity
          nlinarith
      _ ≤ (C₂ * Real.exp A + CA) * Real.exp (-(A * x)) * x := by
          have : 0 ≤ (C₂ * Real.exp A + CA) * Real.exp (-(A * x)) := by positivity
          nlinarith

theorem integrableOn_thetaLevyDensity_mul_exp (A : ℝ) :
    IntegrableOn (fun x => |thetaLevyDensity x| * Real.exp (A * x)) (Ioi 0) := by
  obtain ⟨K, hK, h⟩ := exists_abs_thetaLevyDensity_le (A := |A| + 1) (by positivity)
  have hmeas : AEStronglyMeasurable (fun x => |thetaLevyDensity x| * Real.exp (A * x))
      (volume.restrict (Ioi 0)) :=
    ((continuousOn_thetaLevyDensity.abs).mul (by fun_prop : Continuous fun x : ℝ =>
      Real.exp (A * x)).continuousOn).aestronglyMeasurable measurableSet_Ioi
  refine ((integrableOn_exp_mul_Ioi (a := -1) (by norm_num) 0).const_mul K).mono' hmeas
    ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun x hx => ?_))
  rw [Real.norm_eq_abs, abs_mul, abs_abs, abs_of_pos (Real.exp_pos _)]
  have hx : (0 : ℝ) < x := hx
  calc |thetaLevyDensity x| * Real.exp (A * x) ≤ K * Real.exp (-((|A| + 1) * x)) * Real.exp (A * x) :=
        mul_le_mul_of_nonneg_right (h x hx) (Real.exp_pos _).le
    _ = K * Real.exp (-((|A| + 1) * x) + A * x) := by rw [mul_assoc, ← Real.exp_add]
    _ ≤ K * Real.exp (-1 * x) := by
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hK
        nlinarith [le_abs_self A]

theorem integrableOn_thetaLevyDensity : IntegrableOn thetaLevyDensity (Ioi 0) := by
  have h := (integrableOn_thetaLevyDensity_mul_exp 0).norm
  refine h.mono' (continuousOn_thetaLevyDensity.aestronglyMeasurable measurableSet_Ioi)
    (Eventually.of_forall fun x => ?_)
  simp

/-- The integrand of the dispersion exponent is integrable at every complex frequency. -/
theorem integrableOn_thetaDispersion (z : ℂ) :
    IntegrableOn (fun x : ℝ => (thetaLevyDensity x : ℂ) * (1 - Complex.cos (z * x))) (Ioi 0) := by
  have h := (integrableOn_thetaLevyDensity_mul_exp ‖z‖).const_mul 2
  refine h.mono' ?_ ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun x hx => ?_))
  · refine ((Complex.continuous_ofReal.comp_continuousOn continuousOn_thetaLevyDensity).mul
      (by fun_prop : Continuous fun x : ℝ => 1 - Complex.cos (z * x)).continuousOn)
      |>.aestronglyMeasurable measurableSet_Ioi
  · have hx : (0 : ℝ) < x := hx
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hc := GaloisForLFunctions.HTGeometry.norm_ccos_le_exp_abs_im (z * x)
    have him : |(z * (x : ℂ)).im| ≤ ‖z‖ * x := by
      rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add, abs_mul,
        abs_of_pos hx]
      exact mul_le_mul_of_nonneg_right (Complex.abs_im_le_norm z) hx.le
    have h1 : ‖1 - Complex.cos (z * x)‖ ≤ 2 * Real.exp (‖z‖ * x) := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_one]
      have := Real.one_le_exp (show 0 ≤ ‖z‖ * x by positivity)
      linarith [Real.exp_le_exp.mpr him]
    calc |thetaLevyDensity x| * ‖1 - Complex.cos (z * x)‖
        ≤ |thetaLevyDensity x| * (2 * Real.exp (‖z‖ * x)) :=
          mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      _ = 2 * (|thetaLevyDensity x| * Real.exp (‖z‖ * x)) := by ring

/-- The dispersion exponent `G(z) = ∫₀^∞ (1 - cos zx) dν(x)`, `dν = ω(x)/x dx`. -/
def thetaDispersionExponent (z : ℂ) : ℂ :=
  ∫ x in Ioi (0 : ℝ), (thetaLevyDensity x : ℂ) * (1 - Complex.cos (z * x))

theorem thetaDispersionExponent_neg (z : ℂ) :
    thetaDispersionExponent (-z) = thetaDispersionExponent z := by
  simp only [thetaDispersionExponent, neg_mul, Complex.cos_neg]

/-- **(5).** `∫₀^∞ ω(x) sin(zx) dx = zΞ(z)/2`. -/
theorem integral_thetaJumpDensity_mul_sin (z : ℂ) :
    ∫ x in Ioi (0 : ℝ), (thetaJumpDensity x : ℂ) * Complex.sin (z * x) = z * XiC z / 2 := by
  have h := thetaJumpExponent_sub_neg z
  rw [thetaJumpExponent, thetaJumpExponent,
    ← integral_sub (integrableOn_thetaJumpExponent z) (integrableOn_thetaJumpExponent (-z))] at h
  have hpt : ∀ x : ℝ, (thetaJumpDensity x : ℂ) * (1 - cexp (I * z * x)) -
      (thetaJumpDensity x : ℂ) * (1 - cexp (I * -z * x)) =
      (-2 * I) * ((thetaJumpDensity x : ℂ) * Complex.sin (z * x)) := by
    intro x
    rw [Complex.sin]
    have e1 : I * z * (x : ℂ) = z * x * I := by ring
    have e2 : I * -z * (x : ℂ) = -(z * x) * I := by ring
    rw [e1, e2]
    linear_combination (thetaJumpDensity x : ℂ) *
      (cexp (-(z * ↑x) * I) - cexp (z * ↑x * I)) * I_sq
  simp_rw [hpt] at h
  rw [integral_const_mul] at h
  have hI : (-2 * I : ℂ) ≠ 0 := by simp [I_ne_zero]
  apply mul_left_cancel₀ hI
  rw [h]
  ring

/-- **(5).** `G'(z) = ∫₀^∞ ω(x) sin(zx) dx = zΞ(z)/2`: `G` is entire. -/
theorem hasDerivAt_thetaDispersionExponent (z₀ : ℂ) :
    HasDerivAt thetaDispersionExponent (z₀ * XiC z₀ / 2) z₀ := by
  set F : ℂ → ℝ → ℂ := fun z x => (thetaLevyDensity x : ℂ) * (1 - Complex.cos (z * x))
  set F' : ℂ → ℝ → ℂ := fun z x => (thetaLevyDensity x : ℂ) * (x * Complex.sin (z * x))
  set bound : ℝ → ℝ := fun x => |thetaJumpDensity x| * Real.exp ((‖z₀‖ + 1) * x)
  have hmeasF : ∀ z, AEStronglyMeasurable (F z) (volume.restrict (Ioi 0)) := fun z =>
    ((Complex.continuous_ofReal.comp_continuousOn continuousOn_thetaLevyDensity).mul
      (by fun_prop : Continuous fun x : ℝ => 1 - Complex.cos (z * x)).continuousOn)
      |>.aestronglyMeasurable measurableSet_Ioi
  have hmeasF' : AEStronglyMeasurable (F' z₀) (volume.restrict (Ioi 0)) :=
    ((Complex.continuous_ofReal.comp_continuousOn continuousOn_thetaLevyDensity).mul
      (by fun_prop : Continuous fun x : ℝ => (x : ℂ) * Complex.sin (z₀ * x)).continuousOn)
      |>.aestronglyMeasurable measurableSet_Ioi
  have hbound_int : Integrable bound (volume.restrict (Ioi 0)) := by
    obtain ⟨C, hC, h⟩ := exists_abs_thetaJumpDensity_le (‖z₀‖ + 2)
    refine ((integrableOn_exp_mul_Ioi (a := -1) (by norm_num) 0).const_mul C).mono'
      (by have := continuous_thetaJumpDensity; fun_prop)
      ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun x hx => ?_))
    have hx : (0 : ℝ) < x := hx
    simp only [bound, Real.norm_eq_abs, abs_mul, abs_abs, abs_of_pos (Real.exp_pos _)]
    have := h x
    rw [abs_of_pos hx] at this
    calc |thetaJumpDensity x| * Real.exp ((‖z₀‖ + 1) * x)
        ≤ C * Real.exp (-((‖z₀‖ + 2) * x)) * Real.exp ((‖z₀‖ + 1) * x) :=
          mul_le_mul_of_nonneg_right this (Real.exp_pos _).le
      _ = C * Real.exp (-1 * x) := by rw [mul_assoc, ← Real.exp_add]; ring_nf
  have hbound : ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))), ∀ z ∈ Metric.ball z₀ 1,
      ‖F' z x‖ ≤ bound x := by
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun x hx z hz => ?_)
    have hx : (0 : ℝ) < x := hx
    simp only [F', bound]
    rw [← mul_assoc, show (thetaLevyDensity x : ℂ) * x = (thetaJumpDensity x : ℂ) by
      rw [← mul_thetaLevyDensity hx.ne']; push_cast; ring, norm_mul, Complex.norm_real,
      Real.norm_eq_abs]
    refine mul_le_mul_of_nonneg_left ((GaloisForLFunctions.HTGeometry.norm_csin_le_exp_abs_im _).trans
      (Real.exp_le_exp.mpr ?_)) (abs_nonneg _)
    rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add, abs_mul,
      abs_of_pos hx]
    have hz' : ‖z‖ ≤ ‖z₀‖ + 1 := by
      have := norm_sub_norm_le z z₀
      rw [Metric.mem_ball, dist_eq_norm] at hz
      linarith
    exact mul_le_mul_of_nonneg_right ((Complex.abs_im_le_norm z).trans hz') hx.le
  have hdiff : ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))), ∀ z ∈ Metric.ball z₀ 1,
      HasDerivAt (fun z => F z x) (F' z x) z := by
    refine ae_of_all _ fun x z _ => ?_
    have h := ((hasDerivAt_id z).mul_const (x : ℂ)).ccos
    have h2 := (h.const_sub 1).const_mul (thetaLevyDensity x : ℂ)
    refine h2.congr_deriv ?_
    simp only [id, F']
    ring
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds z₀ one_pos)
    (Eventually.of_forall hmeasF) (integrableOn_thetaDispersion z₀) hmeasF' hbound hbound_int hdiff
  have hval : ∫ x in Ioi (0 : ℝ), F' z₀ x = z₀ * XiC z₀ / 2 := by
    rw [← integral_thetaJumpDensity_mul_sin]
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    have hx : (0 : ℝ) < x := hx
    simp only [F']
    rw [← mul_assoc, show (thetaLevyDensity x : ℂ) * x = (thetaJumpDensity x : ℂ) by
      rw [← mul_thetaLevyDensity hx.ne']; push_cast; ring]
  rw [← hval]
  exact key.2

theorem differentiable_thetaDispersionExponent : Differentiable ℂ thetaDispersionExponent :=
  fun z => (hasDerivAt_thetaDispersionExponent z).differentiableAt

/-- **(5).** `K(z) - K(-z) = -2i G'(z)`. -/
theorem thetaJumpExponent_sub_neg_eq_deriv (z : ℂ) :
    thetaJumpExponent z - thetaJumpExponent (-z) = -2 * I * deriv thetaDispersionExponent z := by
  rw [thetaJumpExponent_sub_neg, (hasDerivAt_thetaDispersionExponent z).deriv]
  ring

/-- The real dispersion exponent `G(u) = ∫₀^∞ (1 - cos ux) dν(x)`. -/
def thetaDispersionExponentReal (u : ℝ) : ℝ :=
  ∫ x in Ioi (0 : ℝ), thetaLevyDensity x * (1 - Real.cos (u * x))

theorem thetaDispersionExponent_ofReal (u : ℝ) :
    thetaDispersionExponent u = (thetaDispersionExponentReal u : ℂ) := by
  rw [thetaDispersionExponent, thetaDispersionExponentReal, ← integral_complex_ofReal]
  refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
  push_cast; rfl

/-- `G(u) > 0` for real `u ≠ 0`. -/
theorem thetaDispersionExponentReal_pos {u : ℝ} (hu : u ≠ 0) : 0 < thetaDispersionExponentReal u :=
  integral_mul_one_sub_cos_pos continuousOn_thetaLevyDensity (fun _ hx => thetaLevyDensity_pos hx)
    integrableOn_thetaLevyDensity hu

theorem thetaDispersionExponentReal_zero : thetaDispersionExponentReal 0 = 0 := by
  simp [thetaDispersionExponentReal]

theorem hasDerivAt_thetaDispersionExponentReal (u : ℝ) :
    HasDerivAt thetaDispersionExponentReal (u * Xi u / 2) u := by
  have h := (hasDerivAt_thetaDispersionExponent (u : ℂ)).real_of_complex
  rw [XiC_ofReal] at h
  refine (h.congr_of_eventuallyEq (Eventually.of_forall fun v => ?_)).congr_deriv ?_
  · simp [thetaDispersionExponent_ofReal]
  · simp only [← Complex.ofReal_mul, ← Complex.ofReal_ofNat, ← Complex.ofReal_div, Complex.ofReal_re]

/-- **(7).** The weighted-area law `∫₀^u vΞ(v) dv = 2G(u) > 0` for `u > 0`. -/
theorem integral_mul_Xi_eq (u : ℝ) : ∫ v in (0 : ℝ)..u, v * Xi v = 2 * thetaDispersionExponentReal u := by
  have hcont : Continuous fun v : ℝ => v * Xi v / 2 := by
    have : Continuous Xi := by
      have h := XiC_differentiable.continuous.comp Complex.continuous_ofReal
      have e : (fun v : ℝ => (XiC (v : ℂ)).re) = Xi := funext fun v => by simp [XiC_ofReal]
      rw [← e]; exact Complex.continuous_re.comp h
    fun_prop
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun v _ => hasDerivAt_thetaDispersionExponentReal v) (hcont.intervalIntegrable 0 u)
  rw [thetaDispersionExponentReal_zero, sub_zero] at h
  rw [← h, ← intervalIntegral.integral_const_mul]
  congr 1; ext v; ring

theorem integral_mul_Xi_pos {u : ℝ} (hu : 0 < u) : 0 < ∫ v in (0 : ℝ)..u, v * Xi v := by
  rw [integral_mul_Xi_eq]; linarith [thetaDispersionExponentReal_pos hu.ne']

/-! ## The characteristic-function semigroup -/

/-- **(6).** `d/dz e^{-tG(z)} = -(t zΞ(z)/2) e^{-tG(z)}`. -/
theorem hasDerivAt_cexp_neg_mul_thetaDispersionExponent (t z : ℂ) :
    HasDerivAt (fun z => cexp (-t * thetaDispersionExponent z))
      (-(t * z * XiC z / 2) * cexp (-t * thetaDispersionExponent z)) z := by
  have h := ((hasDerivAt_thetaDispersionExponent z).const_mul (-t)).cexp
  exact h.congr_deriv (by ring)

/-- The semigroup `e^{-tG}` is entire and nowhere zero, and for `t ≠ 0` its critical points
away from the origin are exactly the zeros of Ξ. -/
theorem deriv_cexp_neg_mul_thetaDispersionExponent_eq_zero_iff {t z : ℂ} (ht : t ≠ 0)
    (hz : z ≠ 0) :
    deriv (fun z => cexp (-t * thetaDispersionExponent z)) z = 0 ↔ XiC z = 0 := by
  rw [(hasDerivAt_cexp_neg_mul_thetaDispersionExponent t z).deriv]
  constructor
  · intro h
    have h1 := (mul_eq_zero.mp h).resolve_right (Complex.exp_ne_zero _)
    have h2 : t * z * XiC z = 0 := by linear_combination -2 * h1
    exact ((mul_eq_zero.mp h2).resolve_left (mul_ne_zero ht hz))
  · intro h; rw [h]; simp

/-! ## The mass `M = Ξ(0)` and the size-biased radius law -/

/-- `∫₀^∞ x ω(x) dx = ∫₀^∞ k(x) dx`. -/
theorem integral_mul_thetaJumpDensity :
    ∫ x in Ioi (0 : ℝ), x * thetaJumpDensity x = ∫ x in Ioi (0 : ℝ), thetaCuspFullSource x := by
  obtain ⟨C, hC, h⟩ := exists_abs_deriv_thetaCuspFullSource_le 2
  obtain ⟨C', hC', h'⟩ := exists_abs_thetaCuspFullSource_le 2
  have hu : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt (fun t : ℝ => t) 1 x := fun x _ => hasDerivAt_id x
  have hv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt thetaCuspFullSource (deriv thetaCuspFullSource x) x :=
    fun x _ => (differentiable_thetaCuspFullSource x).hasDerivAt
  have hbd : ∀ x : ℝ, |x| ≤ Real.exp |x| := fun x => by linarith [Real.add_one_le_exp |x|]
  have huv' : IntegrableOn ((fun t : ℝ => t) * deriv thetaCuspFullSource) (Ioi 0) := by
    have hc : Continuous ((fun t : ℝ => t) * deriv thetaCuspFullSource) :=
      continuous_id.mul continuous_deriv_thetaCuspFullSource
    refine ((integrable_exp_neg_abs_line).const_mul C).integrableOn.mono'
      hc.aestronglyMeasurable (ae_of_all _ fun x => ?_)
    rw [Pi.mul_apply, Real.norm_eq_abs, abs_mul]
    calc |x| * |deriv thetaCuspFullSource x| ≤ Real.exp |x| * (C * Real.exp (-(2 * |x|))) :=
          mul_le_mul (hbd x) (h x) (abs_nonneg _) (Real.exp_pos _).le
      _ = C * Real.exp (-|x|) := by rw [mul_left_comm, ← Real.exp_add]; ring_nf
  have hu'v : IntegrableOn ((fun _ : ℝ => (1 : ℝ)) * thetaCuspFullSource) (Ioi 0) :=
    integrable_thetaCuspFullSource'.integrableOn.congr_fun (fun x _ => by simp) measurableSet_Ioi
  have hlim0 : Tendsto ((fun t : ℝ => t) * thetaCuspFullSource) (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous ((fun t : ℝ => t) * thetaCuspFullSource) :=
      continuous_id.mul continuous_thetaCuspFullSource
    have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    rwa [Pi.mul_apply, zero_mul] at this
  have hlimtop : Tendsto ((fun t : ℝ => t) * thetaCuspFullSource) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ ((Real.tendsto_exp_neg_atTop_nhds_zero).const_mul C' |>.congr'
      (Eventually.of_forall fun t => rfl) |> fun h => by simpa using h)
    filter_upwards [eventually_ge_atTop 0] with t ht
    rw [Pi.mul_apply, Real.norm_eq_abs, abs_mul]
    calc |t| * |thetaCuspFullSource t| ≤ Real.exp |t| * (C' * Real.exp (-(2 * |t|))) :=
          mul_le_mul (hbd t) (h' t) (abs_nonneg _) (Real.exp_pos _).le
      _ = C' * Real.exp (-t) := by rw [abs_of_nonneg ht, mul_left_comm, ← Real.exp_add]; ring_nf
  have hibp := integral_Ioi_mul_deriv_eq_deriv_mul hu hv huv' hu'v hlim0 hlimtop
  simp only [sub_self, zero_sub, one_mul] at hibp
  simp only [thetaJumpDensity, mul_neg, integral_neg, hibp, neg_neg]

/-- `M = 2 ∫₀^∞ x ω(x) dx`. -/
theorem Xi_zero_eq_integral_mul_thetaJumpDensity :
    Xi 0 = 2 * ∫ x in Ioi (0 : ℝ), x * thetaJumpDensity x := by
  rw [integral_mul_thetaJumpDensity, Xi_zero_eq_two_mul_integral_thetaCuspFullSource]

/-- The size-biased radius density `2x ω(x)/M` on `(0, ∞)`. -/
def thetaRadiusDensity (x : ℝ) : ℝ := 2 * x * thetaJumpDensity x / Xi 0

theorem thetaRadiusDensity_pos {x : ℝ} (hx : 0 < x) : 0 < thetaRadiusDensity x :=
  div_pos (mul_pos (mul_pos two_pos hx) (thetaJumpDensity_pos hx)) Xi_zero_pos

/-- The radius law is a probability law. -/
theorem integral_thetaRadiusDensity : ∫ x in Ioi (0 : ℝ), thetaRadiusDensity x = 1 := by
  simp only [thetaRadiusDensity]
  rw [integral_div, show (fun x : ℝ => 2 * x * thetaJumpDensity x) =
    fun x => 2 * (x * thetaJumpDensity x) by funext x; ring, integral_const_mul,
    ← Xi_zero_eq_integral_mul_thetaJumpDensity, div_self Xi_zero_pos.ne']

/-- The entire function `sin w / w` (value `1` at `0`). -/
def complexSinc (w : ℂ) : ℂ := if w = 0 then 1 else Complex.sin w / w

/-- **Spherical characteristic function.** `Ξ(z)/M = E[sin(zR)/(zR)]` for every complex `z`. -/
theorem integral_thetaRadiusDensity_mul_complexSinc (z : ℂ) :
    ∫ x in Ioi (0 : ℝ), (thetaRadiusDensity x : ℂ) * complexSinc (z * x) = XiC z / Xi 0 := by
  have hM : (Xi 0 : ℂ) ≠ 0 := by exact_mod_cast Xi_zero_pos.ne'
  rcases eq_or_ne z 0 with rfl | hz
  · simp only [zero_mul, complexSinc, if_true, mul_one]
    rw [integral_complex_ofReal, integral_thetaRadiusDensity, show (0 : ℂ) = ((0 : ℝ) : ℂ) by simp,
      XiC_ofReal, div_self hM, Complex.ofReal_one]
  · have hpt : ∀ x ∈ Ioi (0 : ℝ), (thetaRadiusDensity x : ℂ) * complexSinc (z * x) =
        (2 / (Xi 0 * z)) * ((thetaJumpDensity x : ℂ) * Complex.sin (z * x)) := by
      intro x hx
      have hx : (x : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (show (0 : ℝ) < x from hx))
      have hzx : z * x ≠ 0 := mul_ne_zero hz hx
      simp only [complexSinc, hzx, if_false, thetaRadiusDensity]
      push_cast
      field_simp
    rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul,
      integral_thetaJumpDensity_mul_sin]
    field_simp

end

end RHTower
