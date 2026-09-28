import GaloisForLFunctions.RHTower.ThetaRenewalPhaseSlope
import GaloisForLFunctions.RHTower.ThetaCuspSchwartzFourierXi
import GaloisForLFunctions.RHTower.ConnesDirichletSineIntegral

/-!
# The single probability-phase level of `Ξ`

With `η + S = iΦ` on the strip and `cosh η(s) · ((a + s)(a - s))^{1/2} = a` (both square roots are
principal, the arguments of `a ± s` lie in `(-π/2, π/2)`), the hyperbolic-cosine factorization
becomes the amplitude–phase law
`Ξ(2z) = 2c (a² + z²)^{1/2} exp(-∫₀^∞ Q(t) cos(zt) dt) cos Φ(z)` on `|Im z| < a`, whose prefactor
never vanishes; its zeros are `Φ(z) = π/2` for `Re z > 0` and `Φ(z) = -π/2` for `Re z < 0`.

On real frequencies `Φ(u) = arctan(u/a) + ∫₀^∞ Q sin(ut)` is real, and the complementary phase
`π/2 - Φ(u)` lies in `(-1/5, π/2 + 1/5)` for `u > 0`.  It equals `∫ (π/2 - Si(us)) μ(ds)` and the
conditionally convergent sine transform `lim_T ∫₀^T ρ(t) sin(ut) dt` (Dirichlet's integral and the
Frullani identity `∫₀^∞ e^{-at} sin(ut)/t dt = arctan(u/a)`); it vanishes exactly at the zeros of
`Ξ(2u)`.  Since `|x| ≤ 3|sin x|` on that range, `|cos Φ(u)| ≤ (5/2)|Ξ(2u)|`, and `Ξ` is the Fourier
transform of the Schwartz source, `π/2 - Φ(u) = O_N(u^{-N})` for every `N`.
-/

open Complex Filter Topology Set MeasureTheory HurwitzZeta
open GaloisForLFunctions.HTGeometry
open scoped FourierTransform

noncomputable section

namespace RHTower

local notation "Θ" => evenKernel (0 : UnitAddCircle)

/-! ## The amplitude–phase law on the strip (15) -/

/-- `cosh η(s) · ((a + s)(a - s))^{1/2} = a` on `|Re s| < a`. -/
theorem cosh_thetaRenewalPhase_mul_cpow {s : ℂ} (hs : |s.re| < 1 / 4) :
    Complex.cosh (thetaRenewalPhase s) * (((1 / 4 : ℂ) + s) * ((1 / 4 : ℂ) - s)) ^ (1 / 2 : ℂ) =
      1 / 4 := by
  have hp0 := add_ne_zero_of_abs_re_lt hs
  have hm0 := sub_ne_zero_of_abs_re_lt hs
  have hp : 0 < ((1 / 4 : ℂ) + s).re := by simp; linarith [abs_lt.mp hs]
  have hm : 0 < ((1 / 4 : ℂ) - s).re := by simp; linarith [abs_lt.mp hs]
  have h1 := arg_lt_of_re_pos hp
  have h2 := arg_lt_of_re_pos hm
  set A := Complex.log ((1 / 4 : ℂ) + s)
  set B := Complex.log ((1 / 4 : ℂ) - s)
  have hlog : Complex.log (((1 / 4 : ℂ) + s) * ((1 / 4 : ℂ) - s)) = A + B :=
    Complex.log_mul hp0 hm0 ⟨by linarith [abs_lt.mp h1, abs_lt.mp h2],
      by linarith [abs_lt.mp h1, abs_lt.mp h2]⟩
  rw [Complex.cpow_def_of_ne_zero (mul_ne_zero hp0 hm0), hlog, thetaRenewalPhase, Complex.cosh]
  have e1 : Complex.exp ((A - B) / 2) * Complex.exp ((A + B) * (1 / 2)) = 1 / 4 + s := by
    rw [← Complex.exp_add, show (A - B) / 2 + (A + B) * (1 / 2) = A by ring, Complex.exp_log hp0]
  have e2 : Complex.exp (-((A - B) / 2)) * Complex.exp ((A + B) * (1 / 2)) = 1 / 4 - s := by
    rw [← Complex.exp_add, show -((A - B) / 2) + (A + B) * (1 / 2) = B by ring,
      Complex.exp_log hm0]
  calc (Complex.exp ((A - B) / 2) + Complex.exp (-((A - B) / 2))) / 2 *
        Complex.exp ((A + B) * (1 / 2))
      = (Complex.exp ((A - B) / 2) * Complex.exp ((A + B) * (1 / 2)) +
          Complex.exp (-((A - B) / 2)) * Complex.exp ((A + B) * (1 / 2))) / 2 := by ring
    _ = 1 / 4 := by rw [e1, e2]; ring

theorem one_sixteenth_add_sq_eq (z : ℂ) :
    (1 / 16 : ℂ) + z ^ 2 = ((1 / 4 : ℂ) + I * z) * ((1 / 4 : ℂ) - I * z) := by
  ring_nf; rw [Complex.I_sq]; ring

/-- The branch `(a² + z²)^{1/2}` is holomorphic on the strip, with value `a` at the origin. -/
theorem one_sixteenth_add_sq_mem_slitPlane {z : ℂ} (hz : |z.im| < 1 / 4) :
    (1 / 16 : ℂ) + z ^ 2 ∈ Complex.slitPlane := by
  refine Complex.mem_slitPlane_iff.mpr (Or.inl ?_)
  have h := abs_lt.mp hz
  have h1 := mul_pos (sub_pos.mpr h.2) (by linarith : (0 : ℝ) < z.im + 1 / 4)
  simp [sq]
  nlinarith [sq_nonneg z.re]

theorem differentiableOn_one_sixteenth_add_sq_cpow :
    DifferentiableOn ℂ (fun z : ℂ => ((1 / 16 : ℂ) + z ^ 2) ^ (1 / 2 : ℂ)) thetaPhaseStrip :=
  fun z hz => (DifferentiableAt.cpow (f := fun z : ℂ => (1 / 16 : ℂ) + z ^ 2)
    (g := fun _ => (1 / 2 : ℂ)) (by fun_prop) (differentiableAt_const _)
    (one_sixteenth_add_sq_mem_slitPlane hz)).differentiableWithinAt

theorem one_sixteenth_add_sq_cpow_zero : ((1 / 16 : ℂ) + 0 ^ 2) ^ (1 / 2 : ℂ) = 1 / 4 := by
  have h : ((1 / 4 : ℝ) ^ (2 : ℝ)) ^ (2⁻¹ : ℝ) = 1 / 4 :=
    Real.rpow_rpow_inv (by norm_num) (by norm_num)
  have h2 : ((1 / 4 : ℝ) ^ (2 : ℝ)) = 1 / 16 := by rw [Real.rpow_two]; norm_num
  rw [h2] at h
  have h3 := Complex.ofReal_cpow (x := 1 / 16) (by norm_num) (2⁻¹)
  rw [h] at h3
  push_cast at h3
  rw [show (1 / 2 : ℂ) = 2⁻¹ by norm_num, zero_pow two_ne_zero, add_zero, ← h3]

/-- **The amplitude–phase law (15).** On `|Im z| < a`,
`Ξ(2z) = 2c (a² + z²)^{1/2} exp(-∫₀^∞ Q(t) cos(zt) dt) cos Φ(z)`. -/
theorem XiC_two_mul_eq_cos_thetaWaitingPhase {z : ℂ} (hz : |z.im| < 1 / 4) :
    XiC (2 * z) = 2 * (Θ 1 : ℂ) * ((1 / 16 : ℂ) + z ^ 2) ^ (1 / 2 : ℂ) *
      Complex.exp (-∫ t in Ioi (0 : ℝ), (thetaRenewalLogKernel t : ℂ) * Complex.cos (z * t)) *
        Complex.cos (thetaWaitingPhase z) := by
  have hs : |(-(I * z)).re| < 1 / 4 := by simpa using hz
  have hIz : |(I * z).re| < 1 / 4 := by simpa using hz
  have h4 := XiC_two_I_mul_eq_cosh hs
  rw [show 2 * I * -(I * z) = 2 * z by ring_nf; rw [Complex.I_sq]; ring] at h4
  have hC : thetaRenewalCosTransform (-(I * z)) =
      ∫ t in Ioi (0 : ℝ), (thetaRenewalLogKernel t : ℂ) * Complex.cos (z * t) := by
    rw [thetaRenewalCosTransform_neg, thetaRenewalCosTransform]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    rw [show I * z * t = (z * t) * I by ring, Complex.cosh_mul_I]
  have hΦ : thetaRenewalPhase (-(I * z)) + thetaRenewalSinTransform (-(I * z)) =
      thetaWaitingPhase z * -I := by
    rw [thetaRenewalPhase_neg, thetaRenewalSinTransform_neg, thetaWaitingPhase_eq_neg_I_mul hz]
    ring_nf; rw [Complex.I_sq]; ring
  have hcosh := cosh_thetaRenewalPhase_mul_cpow hIz
  rw [hC, hΦ] at h4
  rw [thetaRenewalPhase_neg, Complex.cosh_neg] at h4
  rw [h4, one_sixteenth_add_sq_eq, show thetaWaitingPhase z * -I = -(thetaWaitingPhase z * I) by ring,
    Complex.cosh_neg, Complex.cosh_mul_I]
  have hne : Complex.cosh (thetaRenewalPhase (I * z)) ≠ 0 := by
    intro h; rw [h, zero_mul] at hcosh; norm_num at hcosh
  rw [div_eq_iff hne]
  linear_combination (-(2 * (Θ 1 : ℂ) * Complex.exp (-∫ t in Ioi (0 : ℝ),
    (thetaRenewalLogKernel t : ℂ) * Complex.cos (z * t)) * Complex.cos (thetaWaitingPhase z))) *
      hcosh

/-- The prefactor of (15) never vanishes on the strip. -/
theorem thetaWaitingPhase_prefactor_ne_zero {z : ℂ} (hz : |z.im| < 1 / 4) :
    2 * (Θ 1 : ℂ) * ((1 / 16 : ℂ) + z ^ 2) ^ (1 / 2 : ℂ) *
      Complex.exp (-∫ t in Ioi (0 : ℝ), (thetaRenewalLogKernel t : ℂ) * Complex.cos (z * t)) ≠ 0 := by
  have hc : (Θ 1 : ℂ) ≠ 0 := by exact_mod_cast thetaSeam_pos.ne'
  have hb : (1 / 16 : ℂ) + z ^ 2 ≠ 0 := Complex.slitPlane_ne_zero (one_sixteenth_add_sq_mem_slitPlane hz)
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hc) ?_) (Complex.exp_ne_zero _)
  rw [Complex.cpow_def_of_ne_zero hb]
  exact Complex.exp_ne_zero _

theorem neg_I_mul_eq_thetaRenewal_level {z : ℂ} (hz : |z.im| < 1 / 4) :
    thetaRenewalPhase (-(I * z)) + thetaRenewalSinTransform (-(I * z)) =
      -(thetaWaitingPhase z * I) := by
  rw [thetaRenewalPhase_neg, thetaRenewalSinTransform_neg, thetaWaitingPhase_eq_neg_I_mul hz]
  ring_nf; rw [Complex.I_sq]; ring

/-- **Zero condition, right half.** For `Re z > 0`: `Ξ(2z) = 0 ⟺ Φ(z) = π/2`. -/
theorem XiC_two_mul_eq_zero_iff_of_re_pos {z : ℂ} (hz : |z.im| < 1 / 4) (hre : 0 < z.re) :
    XiC (2 * z) = 0 ↔ thetaWaitingPhase z = Real.pi / 2 := by
  have hs : |(-(I * z)).re| < 1 / 4 := by simpa using hz
  have him : (-(I * z)).im < 0 := by simp; linarith
  have h := XiC_two_I_mul_eq_zero_iff_of_im_neg hs him
  rw [show 2 * I * -(I * z) = 2 * z by ring_nf; rw [Complex.I_sq]; ring,
    neg_I_mul_eq_thetaRenewal_level hz] at h
  rw [h]
  constructor
  · intro h'
    exact mul_right_cancel₀ Complex.I_ne_zero (by linear_combination -h')
  · intro h'; rw [h']

/-- **Zero condition, left half.** For `Re z < 0`: `Ξ(2z) = 0 ⟺ Φ(z) = -π/2`. -/
theorem XiC_two_mul_eq_zero_iff_of_re_neg {z : ℂ} (hz : |z.im| < 1 / 4) (hre : z.re < 0) :
    XiC (2 * z) = 0 ↔ thetaWaitingPhase z = -(Real.pi / 2) := by
  have hs : |(-(I * z)).re| < 1 / 4 := by simpa using hz
  have him : 0 < (-(I * z)).im := by simp; linarith
  have h := XiC_two_I_mul_eq_zero_iff hs him
  rw [show 2 * I * -(I * z) = 2 * z by ring_nf; rw [Complex.I_sq]; ring,
    neg_I_mul_eq_thetaRenewal_level hz] at h
  rw [h]
  constructor
  · intro h'
    exact mul_right_cancel₀ Complex.I_ne_zero (by linear_combination -h')
  · intro h'; rw [h']; ring

/-! ## The complementary phase on real frequencies (16) -/

theorem integrableOn_thetaRenewalLogKernel : IntegrableOn thetaRenewalLogKernel (Ioi 0) := by
  refine integrableOn_exp_mul_thetaRenewalLogKernel.mono' continuous_thetaRenewalLogKernel.aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (thetaRenewalLogKernel_pos ht)]
  exact le_mul_of_one_le_left (thetaRenewalLogKernel_pos ht).le
    (Real.one_le_exp (by linarith [show (0 : ℝ) < t from ht]))

theorem integral_thetaRenewalLogKernel_lt : ∫ t in Ioi (0 : ℝ), thetaRenewalLogKernel t < 1 / 5 := by
  refine lt_of_le_of_lt ?_ (integral_exp_mul_thetaRenewalLogKernel ▸
    neg_log_one_sub_thetaRenewalMass_lt)
  refine setIntegral_mono_on integrableOn_thetaRenewalLogKernel
    integrableOn_exp_mul_thetaRenewalLogKernel measurableSet_Ioi fun t ht => ?_
  exact le_mul_of_one_le_left (thetaRenewalLogKernel_pos ht).le
    (Real.one_le_exp (by linarith [show (0 : ℝ) < t from ht]))

theorem integrableOn_thetaRenewalLogKernel_mul_sin (u : ℝ) :
    IntegrableOn (fun t => thetaRenewalLogKernel t * Real.sin (u * t)) (Ioi 0) := by
  refine integrableOn_thetaRenewalLogKernel.mono' ((continuous_thetaRenewalLogKernel.mul
    (by fun_prop : Continuous fun t : ℝ => Real.sin (u * t))).aestronglyMeasurable) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (thetaRenewalLogKernel_pos ht)]
  exact mul_le_of_le_one_right (thetaRenewalLogKernel_pos ht).le (Real.abs_sin_le_one _)

theorem abs_integral_thetaRenewalLogKernel_mul_sin_lt (u : ℝ) :
    |∫ t in Ioi (0 : ℝ), thetaRenewalLogKernel t * Real.sin (u * t)| < 1 / 5 := by
  refine lt_of_le_of_lt ?_ integral_thetaRenewalLogKernel_lt
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_integral_norm _).trans (setIntegral_mono_on
    (integrableOn_thetaRenewalLogKernel_mul_sin u).norm integrableOn_thetaRenewalLogKernel
    measurableSet_Ioi fun t ht => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (thetaRenewalLogKernel_pos ht)]
  exact mul_le_of_le_one_right (thetaRenewalLogKernel_pos ht).le (Real.abs_sin_le_one _)

/-- The real phase `Φ(u) = arctan(u/a) + ∫₀^∞ Q(t) sin(ut) dt`. -/
def thetaWaitingPhaseReal (u : ℝ) : ℝ :=
  Real.arctan (4 * u) + ∫ t in Ioi (0 : ℝ), thetaRenewalLogKernel t * Real.sin (u * t)

/-- The complementary phase `π/2 - Φ(u)`. -/
def thetaWaitingPhaseGap (u : ℝ) : ℝ := Real.pi / 2 - thetaWaitingPhaseReal u

theorem thetaWaitingPhase_ofReal (u : ℝ) :
    thetaWaitingPhase u = (thetaWaitingPhaseReal u : ℂ) := by
  rw [thetaWaitingPhase_eq_arctan_add (by simp), thetaWaitingPhaseReal, Complex.ofReal_add,
    Complex.ofReal_arctan, ← integral_complex_ofReal]
  push_cast
  rfl

/-- **Range of the complementary phase.** For `u > 0`, `π/2 - Φ(u) ∈ (-1/5, π/2 + 1/5)`. -/
theorem thetaWaitingPhaseGap_mem {u : ℝ} (hu : 0 < u) :
    -(1 / 5) < thetaWaitingPhaseGap u ∧ thetaWaitingPhaseGap u < Real.pi / 2 + 1 / 5 := by
  have h1 : 0 < Real.arctan (4 * u) := Real.arctan_pos.mpr (by linarith)
  have h2 := Real.arctan_lt_pi_div_two (4 * u)
  have h3 := abs_lt.mp (abs_integral_thetaRenewalLogKernel_mul_sin_lt u)
  simp only [thetaWaitingPhaseGap, thetaWaitingPhaseReal]
  constructor <;> linarith [h3.1, h3.2]

/-- `|x| ≤ 3 |sin x|` on `(-1/5, π/2 + 1/5)`. -/
theorem abs_le_three_mul_abs_sin {x : ℝ} (h1 : -(1 / 5) < x) (h2 : x < Real.pi / 2 + 1 / 5) :
    |x| ≤ 3 * |Real.sin x| := by
  have hpi := Real.pi_gt_three
  have hpi' := Real.pi_lt_d2
  rcases lt_or_ge x 0 with hx | hx
  · have hs := Real.mul_le_sin (x := -x) (by linarith) (by linarith)
    rw [Real.sin_neg] at hs
    have hpos : 0 < 2 / Real.pi * -x := mul_pos (by positivity) (by linarith)
    rw [abs_of_neg hx, abs_of_neg (by linarith : Real.sin x < 0)]
    have : 2 / Real.pi * -x ≥ -x / 3 := by
      rw [ge_iff_le, div_mul_eq_mul_div, le_div_iff₀ Real.pi_pos]; nlinarith
    linarith
  · rcases le_or_gt x (Real.pi / 2) with hx2 | hx2
    · have hs := Real.mul_le_sin hx hx2
      rw [abs_of_nonneg hx, abs_of_nonneg (le_trans (by positivity) hs)]
      have : 2 / Real.pi * x ≥ x / 3 := by
        rw [ge_iff_le, div_mul_eq_mul_div, le_div_iff₀ Real.pi_pos]; nlinarith
      linarith
    · have hc := Real.one_sub_sq_div_two_le_cos (x := x - Real.pi / 2)
      rw [Real.cos_sub_pi_div_two] at hc
      have hsq : (x - Real.pi / 2) ^ 2 ≤ 1 / 25 := by nlinarith
      rw [abs_of_nonneg hx, abs_of_nonneg (by nlinarith)]
      nlinarith

/-- **Schwartz decay of `Ξ`.** For every `N`, `|t|^N ‖Ξ(t)‖` is bounded. -/
theorem exists_pow_mul_norm_XiC_le (N : ℕ) : ∃ K, 0 ≤ K ∧ ∀ t : ℝ, |t| ^ N * ‖XiC t‖ ≤ K := by
  obtain ⟨C, hC, h⟩ := (𝓕 thetaCuspSchwartz).decay N 0
  refine ⟨C * (2 * Real.pi) ^ N, by positivity, fun t => ?_⟩
  have ht := h (t / (2 * Real.pi))
  rw [norm_iteratedFDeriv_zero, fourier_thetaCuspSchwartz_scaled, Real.norm_eq_abs, abs_div,
    abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi), div_pow] at ht
  have hp : (0 : ℝ) < (2 * Real.pi) ^ N := by positivity
  rw [div_mul_eq_mul_div, div_le_iff₀ hp] at ht
  exact ht

/-- `|cos Φ(u)| ≤ (5/2) ‖Ξ(2u)‖` on real frequencies. -/
theorem abs_cos_thetaWaitingPhaseReal_le (u : ℝ) :
    |Real.cos (thetaWaitingPhaseReal u)| ≤ 5 / 2 * ‖XiC (2 * u)‖ := by
  have h6 := XiC_two_mul_ofReal_eq u
  rw [h6, Complex.norm_real, Real.norm_eq_abs]
  have hc : 1 < Θ 1 := one_lt_evenKernel_zero one_pos
  have hsq : 1 / 4 ≤ Real.sqrt (1 / 16 + u ^ 2) := by
    rw [show (1 / 4 : ℝ) = Real.sqrt (1 / 16) by
      rw [show (1 / 16 : ℝ) = (1 / 4) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hC : |∫ t in Ioi (0 : ℝ), thetaRenewalLogKernel t * Real.cos (u * t)| < 1 / 5 := by
    refine lt_of_le_of_lt ?_ integral_thetaRenewalLogKernel_lt
    rw [← Real.norm_eq_abs]
    have hint : IntegrableOn (fun t => thetaRenewalLogKernel t * Real.cos (u * t)) (Ioi 0) := by
      refine integrableOn_thetaRenewalLogKernel.mono' ((continuous_thetaRenewalLogKernel.mul
        (by fun_prop : Continuous fun t : ℝ => Real.cos (u * t))).aestronglyMeasurable) ?_
      refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (thetaRenewalLogKernel_pos ht)]
      exact mul_le_of_le_one_right (thetaRenewalLogKernel_pos ht).le (Real.abs_cos_le_one _)
    refine (norm_integral_le_integral_norm _).trans (setIntegral_mono_on hint.norm
      integrableOn_thetaRenewalLogKernel measurableSet_Ioi fun t ht => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (thetaRenewalLogKernel_pos ht)]
    exact mul_le_of_le_one_right (thetaRenewalLogKernel_pos ht).le (Real.abs_cos_le_one _)
  have hexp : 4 / 5 ≤ Real.exp (-∫ t in Ioi (0 : ℝ), thetaRenewalLogKernel t * Real.cos (u * t)) := by
    have := Real.add_one_le_exp (-∫ t in Ioi (0 : ℝ), thetaRenewalLogKernel t * Real.cos (u * t))
    linarith [(abs_lt.mp hC).2]
  have hprod : 2 / 5 ≤ 2 * Θ 1 * Real.sqrt (1 / 16 + u ^ 2) *
      Real.exp (-∫ t in Ioi (0 : ℝ), thetaRenewalLogKernel t * Real.cos (u * t)) := by
    have h1 : 1 / 2 ≤ 2 * Θ 1 * Real.sqrt (1 / 16 + u ^ 2) := by nlinarith
    nlinarith
  rw [thetaWaitingPhaseReal]
  set P := 2 * Θ 1 * Real.sqrt (1 / 16 + u ^ 2) *
      Real.exp (-∫ t in Ioi (0 : ℝ), thetaRenewalLogKernel t * Real.cos (u * t))
  set X := Real.cos (Real.arctan (4 * u) +
    ∫ t in Ioi (0 : ℝ), thetaRenewalLogKernel t * Real.sin (u * t))
  rw [abs_mul, abs_of_pos (show 0 < P by linarith)]
  nlinarith [abs_nonneg X]

/-- **Beyond all orders (16).** `π/2 - Φ(u) = O_N(u^{-N})` as `u → ∞`, for every `N`. -/
theorem exists_abs_thetaWaitingPhaseGap_le (N : ℕ) :
    ∃ C, ∀ u : ℝ, 1 ≤ u → |thetaWaitingPhaseGap u| ≤ C / u ^ N := by
  obtain ⟨K, hK, hXi⟩ := exists_pow_mul_norm_XiC_le N
  refine ⟨15 / 2 * K, fun u hu => ?_⟩
  have hu0 : 0 < u := by linarith
  obtain ⟨hg1, hg2⟩ := thetaWaitingPhaseGap_mem hu0
  have hsin : Real.sin (thetaWaitingPhaseGap u) = Real.cos (thetaWaitingPhaseReal u) := by
    rw [thetaWaitingPhaseGap, Real.sin_pi_div_two_sub]
  have h1 := abs_le_three_mul_abs_sin hg1 hg2
  rw [hsin] at h1
  have h2 := abs_cos_thetaWaitingPhaseReal_le u
  have h3 := hXi (2 * u)
  rw [abs_of_pos (by linarith : (0 : ℝ) < 2 * u)] at h3
  push_cast at h3
  have hpow : u ^ N ≤ (2 * u) ^ N := pow_le_pow_left₀ hu0.le (by linarith) N
  have hupos : 0 < u ^ N := pow_pos hu0 N
  have h4 : ‖XiC (2 * u)‖ ≤ K / u ^ N := by
    rw [le_div_iff₀ hupos]
    calc ‖XiC (2 * u)‖ * u ^ N ≤ ‖XiC (2 * u)‖ * (2 * u) ^ N :=
          mul_le_mul_of_nonneg_left hpow (norm_nonneg _)
      _ = (2 * u) ^ N * ‖XiC (2 * u)‖ := by ring
      _ ≤ K := h3
  calc |thetaWaitingPhaseGap u| ≤ 3 * (5 / 2 * ‖XiC (2 * u)‖) := by linarith
    _ ≤ 3 * (5 / 2 * (K / u ^ N)) := by gcongr
    _ = 15 / 2 * K / u ^ N := by ring

/-- **Zero criterion (16).** For `u > 0`, `Ξ(2u) = 0` exactly when the complementary phase
vanishes. -/
theorem XiC_two_mul_ofReal_eq_zero_iff {u : ℝ} (hu : 0 < u) :
    XiC (2 * u) = 0 ↔ thetaWaitingPhaseGap u = 0 := by
  obtain ⟨hg1, hg2⟩ := thetaWaitingPhaseGap_mem hu
  have hpi := Real.pi_gt_three
  have hsin : Real.sin (thetaWaitingPhaseGap u) = Real.cos (thetaWaitingPhaseReal u) := by
    rw [thetaWaitingPhaseGap, Real.sin_pi_div_two_sub]
  rw [← Real.sin_eq_zero_iff_of_lt_of_lt (by linarith) (by linarith), hsin, XiC_two_mul_ofReal_eq,
    Complex.ofReal_eq_zero]
  have hc := thetaSeam_pos
  have hpos : 0 < 2 * Θ 1 * Real.sqrt (1 / 16 + u ^ 2) *
      Real.exp (-∫ t in Ioi (0 : ℝ), thetaRenewalLogKernel t * Real.cos (u * t)) := by
    have := Real.sqrt_pos.mpr (show (0 : ℝ) < 1 / 16 + u ^ 2 by positivity)
    positivity
  rw [thetaWaitingPhaseReal] at *
  constructor
  · intro h; exact (mul_eq_zero.mp h).resolve_left hpos.ne'
  · intro h; rw [h, mul_zero]

/-- **Expectation form (16).** `π/2 - Φ(u) = ∫ (π/2 - Si(us)) μ(ds)`. -/
theorem thetaWaitingPhaseGap_eq_expectation (u : ℝ) :
    (thetaWaitingPhaseGap u : ℂ) =
      ∫ t, ((Real.pi / 2 : ℝ) - thetaSineIntegral (u * t) : ℂ) ∂thetaWaitingTimeLaw := by
  have hM := integrableOn_deriv_thetaWaitingCDF (le_refl (0 : ℝ))
  have hA : IntegrableOn (fun t : ℝ => ((Real.pi / 2 : ℝ) : ℂ) *
      ((deriv thetaWaitingCDF t : ℝ) : ℂ)) (Ioi 0) :=
    (hM.ofReal (𝕜 := ℂ)).const_mul _
  have hB := integrableOn_thetaSineIntegral_mul_deriv (z := (u : ℂ)) (by simp)
  have hmass : ∫ t in Ioi (0 : ℝ), ((deriv thetaWaitingCDF t : ℝ) : ℂ) = 1 := by
    rw [integral_complex_ofReal, integral_Ioi_deriv_thetaWaitingCDF le_rfl,
      thetaRenewalReflectionProfile_zero, Complex.ofReal_one]
  rw [integral_thetaWaitingTimeLaw]
  have e : ∀ t : ℝ, (((Real.pi / 2 : ℝ) : ℂ) - thetaSineIntegral (u * t)) *
      ((deriv thetaWaitingCDF t : ℝ) : ℂ) = ((Real.pi / 2 : ℝ) : ℂ) *
        ((deriv thetaWaitingCDF t : ℝ) : ℂ) -
          thetaSineIntegral (u * t) * ((deriv thetaWaitingCDF t : ℝ) : ℂ) := fun t => by ring
  simp_rw [e]
  rw [integral_sub hA hB, integral_const_mul, hmass, ← thetaWaitingPhase_eq_integral,
    thetaWaitingPhase_ofReal, thetaWaitingPhaseGap]
  push_cast
  ring

theorem abs_sin_mul_div_le {u : ℝ} (hu : 0 ≤ u) {t : ℝ} (ht : 0 < t) :
    |Real.sin (u * t) / t| ≤ u := by
  rw [abs_div, abs_of_pos ht, div_le_iff₀ ht]
  calc |Real.sin (u * t)| ≤ |u * t| := Real.abs_sin_le_abs
    _ = u * t := abs_of_nonneg (mul_nonneg hu ht.le)

theorem intervalIntegrable_of_abs_le {f : ℝ → ℝ} (hf : Measurable f) {C T : ℝ} (hT : 0 ≤ T)
    (hb : ∀ t, 0 < t → |f t| ≤ C) : IntervalIntegrable f volume 0 T := by
  refine (intervalIntegrable_const (c := C)).mono_fun' hf.aestronglyMeasurable ?_
  rw [uIoc_of_le hT]
  exact (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun t ht => by
    show ‖f t‖ ≤ C
    rw [Real.norm_eq_abs]; exact hb t ht.1)

/-- `∫₀^∞ e^{-at} sin(ut)/t dt = arctan(u/a)`. -/
theorem integral_exp_mul_sin_div_eq_arctan (u : ℝ) :
    IntegrableOn (fun t => Real.exp (-(t / 4)) * Real.sin (u * t) / t) (Ioi 0) ∧
      ∫ t in Ioi (0 : ℝ), Real.exp (-(t / 4)) * Real.sin (u * t) / t = Real.arctan (4 * u) := by
  have hs : |(I * (u : ℂ)).re| < 1 / 4 := by simp
  have hg := integrableOn_thetaRenewalFrullani_integrand (s := I * u) (b := 0) (by norm_num)
    (by simp)
  have e : ∀ t : ℝ, (Real.exp (-(t / 4)) : ℂ) * Complex.sinh (I * u * t) / t =
      ((Real.exp (-(t / 4)) * Real.sin (u * t) / t : ℝ) : ℂ) * I := by
    intro t
    rw [show I * (u : ℂ) * t = ((u * t : ℝ) : ℂ) * I by push_cast; ring, Complex.sinh_mul_I,
      ← Complex.ofReal_sin]
    push_cast; ring
  have hC : IntegrableOn (fun t : ℝ => ((Real.exp (-(t / 4)) * Real.sin (u * t) / t : ℝ) : ℂ))
      (Ioi 0) := by
    refine IntegrableOn.congr_fun (hg.mul_const (-I)) (fun t _ => ?_) measurableSet_Ioi
    rw [e, mul_assoc, show I * -I = 1 by rw [mul_neg, Complex.I_mul_I, neg_neg], mul_one]
  have hR : IntegrableOn (fun t => Real.exp (-(t / 4)) * Real.sin (u * t) / t) (Ioi 0) := by
    refine hC.re.congr (Eventually.of_forall fun t => ?_)
    exact Complex.ofReal_re _
  refine ⟨hR, ?_⟩
  have hF := thetaRenewalFrullani_eq hs
  rw [thetaRenewalPhase_I_mul, thetaRenewalFrullani] at hF
  simp_rw [e] at hF
  rw [integral_mul_const, integral_complex_ofReal] at hF
  exact_mod_cast mul_right_cancel₀ Complex.I_ne_zero hF

/-- **The complementary phase as a conditionally convergent sine transform (16).**
For `u > 0`, `∫₀^T ρ(t) sin(ut) dt → π/2 - Φ(u)` as `T → ∞`. -/
theorem tendsto_integral_thetaWaitingRate_mul_sin {u : ℝ} (hu : 0 < u) :
    Tendsto (fun T => ∫ t in (0 : ℝ)..T, thetaWaitingRate t * Real.sin (u * t)) atTop
      (𝓝 (thetaWaitingPhaseGap u)) := by
  obtain ⟨hint2, hval2⟩ := integral_exp_mul_sin_div_eq_arctan u
  set f1 : ℝ → ℝ := fun t => Real.sin (u * t) / t
  set f2 : ℝ → ℝ := fun t => Real.exp (-(t / 4)) * Real.sin (u * t) / t
  set f3 : ℝ → ℝ := fun t => thetaRenewalLogKernel t * Real.sin (u * t)
  have hm1 : Measurable f1 := (by fun_prop : Continuous fun t : ℝ => Real.sin (u * t)).measurable.div
    measurable_id
  have hm2 : Measurable f2 := (by fun_prop : Continuous fun t : ℝ =>
    Real.exp (-(t / 4)) * Real.sin (u * t)).measurable.div measurable_id
  have hi1 : ∀ T, 0 ≤ T → IntervalIntegrable f1 volume 0 T := fun T hT =>
    intervalIntegrable_of_abs_le hm1 hT fun t ht => abs_sin_mul_div_le hu.le ht
  have hi2 : ∀ T, 0 ≤ T → IntervalIntegrable f2 volume 0 T := fun T hT =>
    intervalIntegrable_of_abs_le hm2 hT fun t ht => by
      simp only [f2, mul_div_assoc, abs_mul, abs_of_pos (Real.exp_pos _)]
      exact (mul_le_of_le_one_left (abs_nonneg _) (Real.exp_le_one_iff.mpr (by linarith))).trans
        (abs_sin_mul_div_le hu.le ht)
  have hi3 : ∀ T, IntervalIntegrable f3 volume 0 T := fun T =>
    ((continuous_thetaRenewalLogKernel.mul (by fun_prop : Continuous fun t : ℝ =>
      Real.sin (u * t)))).intervalIntegrable _ _
  have hsplit : ∀ T, 0 ≤ T → ∫ t in (0 : ℝ)..T, thetaWaitingRate t * Real.sin (u * t) =
      (∫ t in (0 : ℝ)..T, f1 t) - (∫ t in (0 : ℝ)..T, f2 t) - ∫ t in (0 : ℝ)..T, f3 t := by
    intro T hT
    rw [← intervalIntegral.integral_sub (hi1 T hT) (hi2 T hT),
      ← intervalIntegral.integral_sub ((hi1 T hT).sub (hi2 T hT)) (hi3 T)]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [f1, f2, f3, thetaWaitingRate, thetaWaitingPole]
    ring
  have hf1 : ∀ T, ∫ t in (0 : ℝ)..T, f1 t = ∫ r in (0 : ℝ)..u * T, Real.sin r / r := by
    intro T
    have h := intervalIntegral.integral_comp_mul_left (a := 0) (b := T)
      (fun r => Real.sin r / r) hu.ne'
    rw [mul_zero] at h
    rw [show (fun t => f1 t) = fun t => u * (Real.sin (u * t) / (u * t)) by
      funext t
      rcases eq_or_ne t 0 with rfl | ht
      · simp [f1]
      · simp only [f1]; field_simp,
      intervalIntegral.integral_const_mul, h, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hu.ne',
      one_mul]
  have hL1 : Tendsto (fun T => ∫ t in (0 : ℝ)..T, f1 t) atTop (𝓝 (Real.pi / 2)) := by
    simp_rw [hf1]
    exact GaloisForLFunctions.RHTower.connes_dirichlet_integral.comp
      (tendsto_id.const_mul_atTop hu)
  have hL2 := intervalIntegral_tendsto_integral_Ioi 0 hint2 tendsto_id
  have hL3 := intervalIntegral_tendsto_integral_Ioi 0
    (integrableOn_thetaRenewalLogKernel_mul_sin u) tendsto_id
  have hlim := (hL1.sub hL2).sub hL3
  rw [hval2] at hlim
  refine (hlim.congr' ((eventually_ge_atTop 0).mono fun T hT => (hsplit T hT).symm)).trans ?_
  rw [thetaWaitingPhaseGap, thetaWaitingPhaseReal]
  simp only [sub_sub]
  exact le_rfl

end RHTower
