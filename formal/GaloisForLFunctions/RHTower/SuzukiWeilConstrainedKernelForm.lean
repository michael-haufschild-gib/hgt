import GaloisForLFunctions.RHTower.SuzukiCCMExactSourceIdentification

/-!
# The constrained kernel form of Suzuki's restricted Weil form

Suzuki's source-locked restricted Weil form at aperture `a` (difference interval `[-S, S]`,
`S = 2a`) is, by `suzukiRestrictedWeilForm_eq_polarPrime_sub_globalWeil`, the polar–prime
autocorrelation carrier minus the real part of the explicit global archimedean Weil distribution.
This file rewrites the archimedean part in the *positive kernel form*

```
  Q_∞(u) = A(S) · g(0) + ∫_0^S K₊(h) (g(0) − g(h)) dh,
  K₊(h)  = e^{h/2} / sinh h = 2 e^{-h/2} / (1 − e^{-2h}) > 0,
  A(S)   = −γ − log π − log (1 − e^{-2S}) − ∫_0^S (e^{h/2} − e^{-h}) / sinh h dh,
```

where `g = suzukiCoreAutocorrelation u` is the autocorrelation of the test, so that
`g(0) = ‖u‖²` and `g(0) − g(h) = ½ ‖u − T_h u‖² ≥ 0`.  The pole term is the product of the two
polar moments `∫ e^{±x/2} u`, hence vanishes on the polar-constrained subspace, and the prime term is
Suzuki's prime block.  Everything is an exact identity; the only inputs are the corpus's explicit
distribution formula and two elementary hyperbolic integrals.

This is the analytic backbone of the constrained-positivity certificate across the prime-2 entry:
on the polar-constrained subspace the whole form is the Fourier multiplier
`A(S) + ∫_0^S K₊(h)(1 − cos hξ) dh − Σ_p (prime terms) cos(ξ log p)`, and the certificate bounds
that multiplier from below band by band.
-/

open Filter MeasureTheory Set Topology

namespace RHTower

open GaloisForLFunctions.RHTower

/-- The positive archimedean weight `K₊ h = e^{h/2} / sinh h`. -/
noncomputable def weilPositiveKernel (h : ℝ) : ℝ := Real.exp (h / 2) / Real.sinh h

/-- `K₊ h = 2 e^{-h/2} / (1 − e^{-2h})`, the form used by the numerical certificate. -/
theorem weilPositiveKernel_eq {h : ℝ} (hh : 0 < h) :
    weilPositiveKernel h = 2 * Real.exp (-(h / 2)) / (1 - Real.exp (-(2 * h))) := by
  unfold weilPositiveKernel
  have hx : Real.exp h = Real.exp (h / 2) ^ 2 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hx2 : Real.exp (2 * h) = Real.exp (h / 2) ^ 4 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hpos : 0 < Real.exp (h / 2) := Real.exp_pos _
  have hsinh : Real.sinh h ≠ 0 := (Real.sinh_ne_zero).2 hh.ne'
  have hden : 1 - Real.exp (-(2 * h)) ≠ 0 := by
    have : Real.exp (-(2 * h)) < Real.exp 0 := Real.exp_lt_exp.2 (by linarith)
    rw [Real.exp_zero] at this
    linarith
  rw [div_eq_div_iff hsinh hden, Real.sinh_eq, Real.exp_neg, Real.exp_neg, Real.exp_neg, hx, hx2]
  field_simp
  try ring

theorem weilPositiveKernel_pos {h : ℝ} (hh : 0 < h) : 0 < weilPositiveKernel h :=
  div_pos (Real.exp_pos _) (Real.sinh_pos_iff.2 hh)

/-- The constrained aperture constant
`A(S) = −γ − log π − log (1 − e^{-2S}) − ∫_0^S (e^{h/2} − e^{-h}) / sinh h dh`. -/
noncomputable def weilConstrainedConstant (S : ℝ) : ℝ :=
  -Real.eulerMascheroniConstant - Real.log Real.pi - Real.log (1 - Real.exp (-(2 * S))) -
    ∫ h in Ioc (0 : ℝ) S, (Real.exp (h / 2) - Real.exp (-h)) / Real.sinh h

theorem continuous_two_exp_neg_div :
    Continuous fun h : ℝ => 2 * Real.exp (-h) / (1 + Real.exp (-h)) :=
  (continuous_const.mul (Real.continuous_exp.comp continuous_neg)).div
    (continuous_const.add (Real.continuous_exp.comp continuous_neg)) (fun x => by positivity)

/-- `∫_0^S (1 − e^{-h}) / sinh h dh = 2 log 2 − 2 log (1 + e^{-S})`. -/
theorem integral_Ioc_one_sub_exp_neg_div_sinh {S : ℝ} (hS : 0 < S) :
    (∫ h in Ioc (0 : ℝ) S, (1 - Real.exp (-h)) / Real.sinh h) =
      2 * Real.log 2 - 2 * Real.log (1 + Real.exp (-S)) := by
  have hpt : ∀ h ∈ Ioc (0 : ℝ) S,
      (1 - Real.exp (-h)) / Real.sinh h = 2 * Real.exp (-h) / (1 + Real.exp (-h)) := by
    intro h hh
    have hsinh : Real.sinh h ≠ 0 := (Real.sinh_ne_zero).2 hh.1.ne'
    have hden : 1 + Real.exp (-h) ≠ 0 := by positivity
    rw [div_eq_div_iff hsinh hden, Real.sinh_eq]
    have hx : Real.exp h = (Real.exp (-h))⁻¹ := by rw [Real.exp_neg, inv_inv]
    rw [hx]
    have hne : Real.exp (-h) ≠ 0 := (Real.exp_pos _).ne'
    field_simp
    ring
  rw [setIntegral_congr_fun measurableSet_Ioc hpt, ← intervalIntegral.integral_of_le hS.le]
  have hderiv : ∀ h : ℝ, HasDerivAt (fun h : ℝ => -2 * Real.log (1 + Real.exp (-h)))
      (2 * Real.exp (-h) / (1 + Real.exp (-h))) h := by
    intro h
    have h1 : HasDerivAt (fun h : ℝ => Real.exp (-h)) (Real.exp (-h) * -1) h :=
      (Real.hasDerivAt_exp (-h)).comp h (hasDerivAt_neg h)
    have h2 : HasDerivAt (fun h : ℝ => 1 + Real.exp (-h)) (Real.exp (-h) * -1) h := h1.const_add 1
    have hne : 1 + Real.exp (-h) ≠ 0 := by positivity
    have h3 := (h2.log hne).const_mul (-2)
    refine h3.congr_deriv ?_
    field_simp
    try ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun h _ => hderiv h)]
  · have h11 : (1 : ℝ) + Real.exp (-0) = 2 := by norm_num
    simp only [h11]
    try ring
  · exact (continuous_two_exp_neg_div).intervalIntegrable _ _

/-- `∫_S^∞ dh / sinh h = log (1 + e^{-S}) − log (1 − e^{-S})`. -/
theorem integral_Ioi_inv_sinh_eq_log {S : ℝ} (hS : 0 < S) :
    (∫ h in Ioi S, 1 / Real.sinh h) =
      Real.log (1 + Real.exp (-S)) - Real.log (1 - Real.exp (-S)) := by
  rw [integral_Ioi_inv_sinh hS]
  unfold suzukiHyperbolicPrimitive
  have hhalf : 0 < S / 2 := by linarith
  have he : 0 < Real.exp (-S) := Real.exp_pos _
  have he1 : Real.exp (-S) < 1 := by
    have : Real.exp (-S) < Real.exp 0 := Real.exp_lt_exp.2 (by linarith)
    rwa [Real.exp_zero] at this
  have hcosh : Real.cosh (S / 2) = Real.exp (S / 2) * (1 + Real.exp (-S)) / 2 := by
    rw [Real.cosh_eq]
    have : Real.exp (-(S / 2)) = Real.exp (S / 2) * Real.exp (-S) := by
      rw [← Real.exp_add]; ring_nf
    rw [this]; ring
  have hsinh : Real.sinh (S / 2) = Real.exp (S / 2) * (1 - Real.exp (-S)) / 2 := by
    rw [Real.sinh_eq]
    have : Real.exp (-(S / 2)) = Real.exp (S / 2) * Real.exp (-S) := by
      rw [← Real.exp_add]; ring_nf
    rw [this]; ring
  rw [hcosh, hsinh]
  have hp : 0 < Real.exp (S / 2) := Real.exp_pos _
  rw [Real.log_div (by positivity) (by norm_num), Real.log_div (by positivity) (by norm_num),
    Real.log_mul hp.ne' (by positivity), Real.log_mul hp.ne' (by linarith)]
  try ring

/-- The elementary bound `(e^{h/2} − 1) / sinh h ≤ e^{S/2} / 2` on `(0, S]`. -/
theorem exp_half_sub_one_div_sinh_le {h S : ℝ} (hh : 0 < h) (hhS : h ≤ S) :
    (Real.exp (h / 2) - 1) / Real.sinh h ≤ Real.exp (S / 2) / 2 := by
  have hsinh : h ≤ Real.sinh h := (Real.self_le_sinh_iff).2 hh.le
  have hsinhpos : 0 < Real.sinh h := Real.sinh_pos_iff.2 hh
  have hA : Real.exp (h / 2) - 1 ≤ h / 2 * Real.exp (S / 2) := by
    have h1 : 1 - h / 2 ≤ Real.exp (-(h / 2)) := by
      have := Real.add_one_le_exp (-(h / 2)); linarith
    have h2 : Real.exp (h / 2) * (1 - h / 2) ≤ 1 := by
      calc Real.exp (h / 2) * (1 - h / 2) ≤ Real.exp (h / 2) * Real.exp (-(h / 2)) :=
            mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
        _ = 1 := by rw [← Real.exp_add]; simp
    have h3 : Real.exp (h / 2) ≤ Real.exp (S / 2) := Real.exp_le_exp.2 (by linarith)
    nlinarith [Real.exp_pos (h / 2)]
  rw [div_le_iff₀ hsinhpos]
  calc Real.exp (h / 2) - 1 ≤ h / 2 * Real.exp (S / 2) := hA
    _ ≤ Real.sinh h / 2 * Real.exp (S / 2) := by gcongr
    _ = Real.exp (S / 2) / 2 * Real.sinh h := by ring

theorem exp_half_sub_one_div_sinh_nonneg {h : ℝ} (hh : 0 < h) :
    0 ≤ (Real.exp (h / 2) - 1) / Real.sinh h := by
  apply div_nonneg _ (Real.sinh_pos_iff.2 hh).le
  have := Real.add_one_le_exp (h / 2); linarith

theorem integrableOn_exp_half_sub_one_div_sinh {S : ℝ} (_hS : 0 < S) :
    IntegrableOn (fun h : ℝ => (Real.exp (h / 2) - 1) / Real.sinh h) (Ioc 0 S) := by
  refine Measure.integrableOn_of_bounded (M := Real.exp (S / 2) / 2) (by simp) ?_ ?_
  · exact (by fun_prop : Measurable fun h : ℝ => (Real.exp (h / 2) - 1) / Real.sinh h).aestronglyMeasurable
  · rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards with h hh
    rw [Real.norm_eq_abs, abs_of_nonneg (exp_half_sub_one_div_sinh_nonneg hh.1)]
    exact exp_half_sub_one_div_sinh_le hh.1 hh.2

theorem integrableOn_one_sub_exp_neg_div_sinh {S : ℝ} (_hS : 0 < S) :
    IntegrableOn (fun h : ℝ => (1 - Real.exp (-h)) / Real.sinh h) (Ioc 0 S) := by
  have hpt : ∀ h ∈ Ioc (0 : ℝ) S,
      2 * Real.exp (-h) / (1 + Real.exp (-h)) = (1 - Real.exp (-h)) / Real.sinh h := by
    intro h hh
    have hsinh : Real.sinh h ≠ 0 := (Real.sinh_ne_zero).2 hh.1.ne'
    have hden : 1 + Real.exp (-h) ≠ 0 := by positivity
    rw [div_eq_div_iff hden hsinh, Real.sinh_eq]
    have hx : Real.exp h = (Real.exp (-h))⁻¹ := by rw [Real.exp_neg, inv_inv]
    rw [hx]
    have hne : Real.exp (-h) ≠ 0 := (Real.exp_pos _).ne'
    field_simp
    ring
  have hc : IntegrableOn (fun h : ℝ => 2 * Real.exp (-h) / (1 + Real.exp (-h))) (Ioc 0 S) :=
    (continuous_two_exp_neg_div.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  exact hc.congr_fun hpt measurableSet_Ioc

/-- Integrability of the deficit integrand `(e^{h/2} − e^{-h}) / sinh h` on `(0, S]`. -/
theorem integrableOn_exp_half_sub_exp_neg_div_sinh {S : ℝ} (hS : 0 < S) :
    IntegrableOn (fun h : ℝ => (Real.exp (h / 2) - Real.exp (-h)) / Real.sinh h) (Ioc 0 S) := by
  have := (integrableOn_exp_half_sub_one_div_sinh hS).add (integrableOn_one_sub_exp_neg_div_sinh hS)
  refine this.congr_fun (fun h hh => ?_) measurableSet_Ioc
  simp only [Pi.add_apply]
  rw [← add_div]; ring_nf

/-- `∫_0^S (e^{h/2} − 1) / sinh h = ∫_0^S (e^{h/2} − e^{-h}) / sinh h − 2 log 2 + 2 log (1 + e^{-S})`. -/
theorem integral_Ioc_exp_half_sub_one_div_sinh {S : ℝ} (hS : 0 < S) :
    (∫ h in Ioc (0 : ℝ) S, (Real.exp (h / 2) - 1) / Real.sinh h) =
      (∫ h in Ioc (0 : ℝ) S, (Real.exp (h / 2) - Real.exp (-h)) / Real.sinh h) -
        2 * Real.log 2 + 2 * Real.log (1 + Real.exp (-S)) := by
  have hsplit : (∫ h in Ioc (0 : ℝ) S, (Real.exp (h / 2) - 1) / Real.sinh h) =
      (∫ h in Ioc (0 : ℝ) S, (Real.exp (h / 2) - Real.exp (-h)) / Real.sinh h) -
        ∫ h in Ioc (0 : ℝ) S, (1 - Real.exp (-h)) / Real.sinh h := by
    rw [← integral_sub (integrableOn_exp_half_sub_exp_neg_div_sinh hS)
      (integrableOn_one_sub_exp_neg_div_sinh hS)]
    refine setIntegral_congr_fun measurableSet_Ioc (fun h _ => ?_)
    rw [← sub_div]; ring_nf
  rw [hsplit, integral_Ioc_one_sub_exp_neg_div_sinh hS]
  ring

/-- Pointwise decomposition of the sharp real-place density. -/
theorem sharp_density_decomposition {h g0 gh : ℝ} (hh : 0 < h) :
    (Real.exp (h / 2) * gh - g0) / Real.sinh h =
      weilPositiveKernel h * (gh - g0) + g0 * ((Real.exp (h / 2) - 1) / Real.sinh h) := by
  unfold weilPositiveKernel
  have hsinh : Real.sinh h ≠ 0 := (Real.sinh_ne_zero).2 hh.ne'
  field_simp
  ring

/-- The sharp real-place density is integrable on the aperture interval. -/
theorem integrableOn_sharp_density (A : SuzukiPositiveAperture) (u : SuzukiRestrictedWeilCore A.1) :
    IntegrableOn (fun h : ℝ => (Real.exp (h / 2) * suzukiCoreAutocorrelation u h -
      suzukiCoreAutocorrelation u 0) / Real.sinh h) (Ioc 0 (2 * A.1)) := by
  have hint : IntegrableOn (ccmArchimedeanWeilSharpIntegrand
      (ccmCompactSchwartzLogEvenization (suzukiRestrictedWeilCoreAutocorrelationTest u)))
      (Ioc 0 (2 * A.1)) :=
    (ccmArchimedeanWeilSharpIntegrand_integrableOn_Ioi _).mono_set Ioc_subset_Ioi_self
  have hre : IntegrableOn (fun h => (ccmArchimedeanWeilSharpIntegrand
      (ccmCompactSchwartzLogEvenization (suzukiRestrictedWeilCoreAutocorrelationTest u)) h).re)
      (Ioc 0 (2 * A.1)) := hint.re
  refine hre.congr_fun (fun h hh => ?_) measurableSet_Ioc
  exact ccmArchimedeanWeilSharpIntegrand_evenized_suzukiCore_re u hh.1.ne'

/-- Integrability of the positive-kernel energy density `K₊(h)(g h − g 0)`. -/
theorem integrableOn_weilPositiveKernel_mul_defect (A : SuzukiPositiveAperture)
    (u : SuzukiRestrictedWeilCore A.1) :
    IntegrableOn (fun h : ℝ => weilPositiveKernel h *
      (suzukiCoreAutocorrelation u h - suzukiCoreAutocorrelation u 0)) (Ioc 0 (2 * A.1)) := by
  have hS : 0 < 2 * A.1 := by have := A.property; linarith
  have h1 := integrableOn_sharp_density A u
  have h2 := (integrableOn_exp_half_sub_one_div_sinh hS).const_mul (suzukiCoreAutocorrelation u 0)
  refine (h1.sub h2).congr_fun (fun h hh => ?_) measurableSet_Ioc
  simp only [Pi.sub_apply]
  rw [sharp_density_decomposition hh.1]
  ring

/-- **Suzuki's restricted Weil form in constrained kernel form.**  With `S = 2a` and
`g = suzukiCoreAutocorrelation u`,
`Q(u) = A(S) g(0) + ∫_0^S K₊(h)(g(0) − g(h)) dh + 2 (∫ e^{x/2} u)(∫ e^{-x/2} u) + prime block`. -/
theorem suzukiRestrictedWeilForm_eq_constrainedKernelForm (A : SuzukiPositiveAperture)
    (u : SuzukiRestrictedWeilCore A.1) :
    suzukiRestrictedWeilForm A.1 u u =
      weilConstrainedConstant (2 * A.1) * suzukiCoreAutocorrelation u 0 +
        (∫ h in Ioc (0 : ℝ) (2 * A.1), weilPositiveKernel h *
          (suzukiCoreAutocorrelation u 0 - suzukiCoreAutocorrelation u h)) +
        2 * ((∫ x : ℝ, Real.exp (x / 2) * u x) * ∫ x : ℝ, Real.exp (-(x / 2)) * u x) +
        weilPrimeBlock (suzukiRestrictedWeilIndices A.1) u u := by
  have hS : 0 < 2 * A.1 := by have := A.property; linarith
  rw [suzukiRestrictedWeilForm_eq_polarPrime_sub_globalWeil,
    polarPrimeAutocorrelationQuadratic_eq_polar_add_weilPrimeBlock,
    ccmArchimedeanWeilDistribution_suzukiCore_re_eq_restricted_add_tail]
  -- the pole term
  have hpole : 4 * (∫ h in Ioc (0 : ℝ) (2 * A.1), Real.cosh (h / 2) * suzukiCoreAutocorrelation u h) =
      2 * ((∫ x : ℝ, Real.exp (x / 2) * u x) * ∫ x : ℝ, Real.exp (-(x / 2)) * u x) := by
    rw [← integral_exp_half_mul_suzukiCoreAutocorrelation u,
      integral_exp_half_mul_suzukiCoreAutocorrelation_eq_Ioc_cosh A u, ← integral_const_mul,
      ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioc (fun h _ => ?_)
    ring
  -- the sharp density integral
  have hdens : (∫ h in Ioc (0 : ℝ) (2 * A.1), (Real.exp (h / 2) * suzukiCoreAutocorrelation u h -
        suzukiCoreAutocorrelation u 0) / Real.sinh h) =
      (∫ h in Ioc (0 : ℝ) (2 * A.1), weilPositiveKernel h *
          (suzukiCoreAutocorrelation u h - suzukiCoreAutocorrelation u 0)) +
        suzukiCoreAutocorrelation u 0 *
          ∫ h in Ioc (0 : ℝ) (2 * A.1), (Real.exp (h / 2) - 1) / Real.sinh h := by
    rw [← integral_const_mul, ← integral_add (integrableOn_weilPositiveKernel_mul_defect A u)
      ((integrableOn_exp_half_sub_one_div_sinh hS).const_mul (suzukiCoreAutocorrelation u 0))]
    refine setIntegral_congr_fun measurableSet_Ioc (fun h hh => ?_)
    exact sharp_density_decomposition hh.1
  have hneg : (∫ h in Ioc (0 : ℝ) (2 * A.1), weilPositiveKernel h *
        (suzukiCoreAutocorrelation u h - suzukiCoreAutocorrelation u 0)) =
      -∫ h in Ioc (0 : ℝ) (2 * A.1), weilPositiveKernel h *
        (suzukiCoreAutocorrelation u 0 - suzukiCoreAutocorrelation u h) := by
    rw [← integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioc (fun h _ => ?_)
    ring
  have htail := integral_Ioi_inv_sinh_eq_log hS
  have hJ := integral_Ioc_exp_half_sub_one_div_sinh hS
  have hlog4 : Real.log (4 * Real.pi) = 2 * Real.log 2 + Real.log Real.pi := by
    rw [Real.log_mul (by norm_num) Real.pi_ne_zero, show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.log_pow]
    push_cast; ring
  have hlog2S : Real.log (1 - Real.exp (-(2 * (2 * A.1)))) =
      Real.log (1 + Real.exp (-(2 * A.1))) + Real.log (1 - Real.exp (-(2 * A.1))) := by
    have he1 : Real.exp (-(2 * A.1)) < 1 := by
      have : Real.exp (-(2 * A.1)) < Real.exp 0 := Real.exp_lt_exp.2 (by linarith)
      rwa [Real.exp_zero] at this
    rw [← Real.log_mul (by positivity) (by linarith)]
    congr 1
    have : Real.exp (-(2 * (2 * A.1))) = Real.exp (-(2 * A.1)) ^ 2 := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [this]; ring
  unfold weilConstrainedConstant
  rw [hpole, hdens, hneg, htail, hJ, hlog4, hlog2S]
  ring

/-- On the polar-constrained subspace (either exponential moment vanishing) the pole term is gone:
`Q(u) = A(S) g(0) + ∫_0^S K₊ (g(0) − g(h)) dh + prime block`. -/
theorem suzukiRestrictedWeilForm_eq_constrainedKernelForm_of_moment_eq_zero
    (A : SuzukiPositiveAperture) (u : SuzukiRestrictedWeilCore A.1)
    (hmom : (∫ x : ℝ, Real.exp (x / 2) * u x) = 0 ∨ (∫ x : ℝ, Real.exp (-(x / 2)) * u x) = 0) :
    suzukiRestrictedWeilForm A.1 u u =
      weilConstrainedConstant (2 * A.1) * suzukiCoreAutocorrelation u 0 +
        (∫ h in Ioc (0 : ℝ) (2 * A.1), weilPositiveKernel h *
          (suzukiCoreAutocorrelation u 0 - suzukiCoreAutocorrelation u h)) +
        weilPrimeBlock (suzukiRestrictedWeilIndices A.1) u u := by
  rw [suzukiRestrictedWeilForm_eq_constrainedKernelForm]
  rcases hmom with h | h <;> rw [h] <;> ring

/-- The positive-kernel energy is nonnegative: `g(0) − g(h) = ½‖u − T_h u‖² ≥ 0` and `K₊ > 0`. -/
theorem integral_weilPositiveKernel_mul_defect_nonneg (A : SuzukiPositiveAperture)
    (u : SuzukiRestrictedWeilCore A.1) :
    0 ≤ ∫ h in Ioc (0 : ℝ) (2 * A.1), weilPositiveKernel h *
      (suzukiCoreAutocorrelation u 0 - suzukiCoreAutocorrelation u h) := by
  refine setIntegral_nonneg measurableSet_Ioc (fun h hh => ?_)
  refine mul_nonneg (weilPositiveKernel_pos hh.1).le ?_
  have := suzukiRealTranslationDifferenceEnergy_eq_autocorrelation u h
  have hnn : 0 ≤ suzukiRealTranslationDifferenceEnergy u h := by
    unfold suzukiRealTranslationDifferenceEnergy
    exact integral_nonneg fun x => sq_nonneg _
  linarith

end RHTower
