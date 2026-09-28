import GaloisForLFunctions.RHTower.ThetaSurgeryEnvelope
import GaloisForLFunctions.RHTower.ProfileRenewalLogKernel

/-!
# Exact variation of the theta renewal profile under an even seam-flat perturbation

For the literal profile `P(t) = e^{t/4} Θ(e^t)` and an even real-analytic perturbation `g`
(built from the envelope `ψ(t) = t^{2N+2} exp(-(e^{2t} + e^{-2t}))`), put `P_g = P + g`,
`ν_g = P_g/4 - P_g'`, `D_g(s) = Θ(1) - ∫₀^∞ e^{-st} ν_g` and
`X_g(z) = (1/4 - iz) D_g(-iz) + (1/4 + iz) D_g(iz)`.

* one-sided integration by parts: `D_g(s) = D(s) - (1/4 - s) ĝ(s)`;
* the exact variation `X_g(z) = Ξ(2z) - (z² + 1/16) ∫_ℝ e^{-izt} g(t) dt`;
* the exact mass `∫₀^∞ e^{t/4} ν_g = ∫₀^∞ e^{t/4} ν + (1/2) ∫₀^∞ e^{t/4} g`;
* the perturbed full-source density `k_g(x) = k(x) + 2[g''(2x) - g(2x)/16]`, whose
  Fourier–Laplace transform is `X_g(w/2)`.
-/
open Complex Filter Topology Set MeasureTheory HurwitzZeta
open GaloisForLFunctions.HTGeometry
open scoped ContDiff

namespace RHTower

noncomputable section

local notation "Θ" => evenKernel (0 : UnitAddCircle)

/-! ## Decay of the perturbation and its derivatives -/

/-- Every derivative of the perturbation decays faster than every exponential. -/
theorem exists_abs_iteratedDeriv_surgeryPerturbation_le_exp (N k : ℕ) {T : ℝ} (hT : 0 ≤ T)
    (ε : Fin 3 → ℝ) (B : ℝ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ t,
      |iteratedDeriv k (surgeryPerturbation N T ε) t| ≤ C * Real.exp (-(B * |t|)) := by
  set L := k.factorial * 8 ^ k * ((|ε 0| + |ε 1| + |ε 2|) * Real.exp (T / 8))
  refine ⟨L * ((2 * N + 3).factorial * Real.exp (1 + (|B| + 1) ^ 2 * Real.exp (1 / 4) / 2)),
    by positivity, fun t => ?_⟩
  have h1 := abs_iteratedDeriv_surgeryPerturbation_le N k hT ε t
  have h2 := exp_mul_pow_mul_surgeryDecay_le B (2 * N + 3) t
  have hE := Real.exp_pos (B * |t|)
  rw [show Real.exp (-(B * |t|)) = (Real.exp (B * |t|))⁻¹ by rw [Real.exp_neg]]
  rw [← div_eq_mul_inv, le_div_iff₀ hE]
  calc |iteratedDeriv k (surgeryPerturbation N T ε) t| * Real.exp (B * |t|)
      ≤ (L * ((|t| + 1) ^ (2 * N + 3) * surgeryDecay t)) * Real.exp (B * |t|) := by
        refine mul_le_mul_of_nonneg_right (h1.trans (le_of_eq ?_)) hE.le
        simp only [L]; ring
    _ = L * (Real.exp (B * |t|) * ((|t| + 1) ^ (2 * N + 3) * surgeryDecay t)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h2 (by positivity)

theorem integrable_exp_mul_iteratedDeriv_surgeryPerturbation (N k : ℕ) {T : ℝ} (hT : 0 ≤ T)
    (ε : Fin 3 → ℝ) (σ : ℝ) :
    Integrable fun t => Real.exp (σ * |t|) * |iteratedDeriv k (surgeryPerturbation N T ε) t| := by
  obtain ⟨C, hC, h⟩ := exists_abs_iteratedDeriv_surgeryPerturbation_le_exp N k hT ε (|σ| + 1)
  have hc : Continuous (iteratedDeriv k (surgeryPerturbation N T ε)) :=
    (contDiff_surgeryPerturbation N T ε).continuous_iteratedDeriv k (mod_cast le_top)
  refine ((integrable_exp_neg_abs_line).const_mul C).mono' (by fun_prop)
    (Eventually.of_forall fun t => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_abs, abs_of_pos (Real.exp_pos _)]
  calc Real.exp (σ * |t|) * |iteratedDeriv k (surgeryPerturbation N T ε) t|
      ≤ Real.exp (σ * |t|) * (C * Real.exp (-((|σ| + 1) * |t|))) :=
        mul_le_mul_of_nonneg_left (h t) (Real.exp_pos _).le
    _ = C * Real.exp (σ * |t| - (|σ| + 1) * |t|) := by
        rw [sub_eq_add_neg, Real.exp_add]; ring
    _ ≤ C * Real.exp (-|t|) := by
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC
        nlinarith [le_abs_self σ, abs_nonneg t, mul_le_mul_of_nonneg_right (le_abs_self σ) (abs_nonneg t)]

/-! ## Laplace transforms of the perturbation -/

theorem hasDerivAt_surgeryPerturbation (N : ℕ) (T : ℝ) (ε : Fin 3 → ℝ) (t : ℝ) :
    HasDerivAt (surgeryPerturbation N T ε) (deriv (surgeryPerturbation N T ε) t) t :=
  ((contDiff_surgeryPerturbation N T ε).differentiable (by simp) t).hasDerivAt

theorem continuous_deriv_surgeryPerturbation (N : ℕ) (T : ℝ) (ε : Fin 3 → ℝ) :
    Continuous (deriv (surgeryPerturbation N T ε)) :=
  (contDiff_surgeryPerturbation N T ε).continuous_deriv (by simp)

theorem integrableOn_cexp_mul_iteratedDeriv (N k : ℕ) {T : ℝ} (hT : 0 ≤ T) (ε : Fin 3 → ℝ) (s : ℂ) :
    Integrable fun t : ℝ => cexp (-(s * t)) * ((iteratedDeriv k (surgeryPerturbation N T ε) t : ℝ) : ℂ) := by
  have hc : Continuous (iteratedDeriv k (surgeryPerturbation N T ε)) :=
    (contDiff_surgeryPerturbation N T ε).continuous_iteratedDeriv k (mod_cast le_top)
  refine (integrable_exp_mul_iteratedDeriv_surgeryPerturbation N k hT ε ‖s‖).mono' (by fun_prop)
    (Eventually.of_forall fun t => ?_)
  rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs]
  refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (abs_nonneg _)
  calc (-(s * (t : ℂ))).re ≤ ‖-(s * (t : ℂ))‖ := Complex.re_le_norm _
    _ = ‖s‖ * |t| := by rw [norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs]

/-- **Half-line integration by parts.** `∫₀^∞ e^{-st} g' = s ∫₀^∞ e^{-st} g`, since `g(0) = 0`. -/
theorem renewalLaplace_deriv_surgeryPerturbation (N : ℕ) {T : ℝ} (hT : 0 ≤ T) (ε : Fin 3 → ℝ)
    (s : ℂ) : renewalLaplace (deriv (surgeryPerturbation N T ε)) s =
      s * renewalLaplace (surgeryPerturbation N T ε) s := by
  set g := surgeryPerturbation N T ε
  have hu : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt (fun t : ℝ => cexp (-(s * t))) (-s * cexp (-(s * x))) x :=
    fun x _ => by
      have := ((hasDerivAt_id (x : ℂ)).const_mul (-s)).cexp.comp_ofReal
      simpa [mul_comm] using this
  have hv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt (fun t : ℝ => (g t : ℂ)) ((deriv g x : ℝ) : ℂ) x :=
    fun x _ => (hasDerivAt_surgeryPerturbation N T ε x).ofReal_comp
  have h1 := (integrableOn_cexp_mul_iteratedDeriv N 1 hT ε s).integrableOn (s := Ioi 0)
  have h0 := (integrableOn_cexp_mul_iteratedDeriv N 0 hT ε s).integrableOn (s := Ioi 0)
  simp only [iteratedDeriv_one, iteratedDeriv_zero] at h1 h0
  have hcont : Continuous fun t : ℝ => cexp (-(s * t)) * (g t : ℂ) := by
    have := (contDiff_surgeryPerturbation N T ε).continuous; fun_prop
  have hlim0 : Tendsto ((fun t : ℝ => cexp (-(s * t))) * fun t => (g t : ℂ)) (𝓝[>] 0) (𝓝 0) := by
    have := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    simp only [g, surgeryPerturbation_zero_arg, Complex.ofReal_zero, mul_zero] at this
    exact this
  have hlimtop : Tendsto ((fun t : ℝ => cexp (-(s * t))) * fun t => (g t : ℂ)) atTop (𝓝 0) := by
    obtain ⟨C, hC, hb⟩ := exists_abs_iteratedDeriv_surgeryPerturbation_le_exp N 0 hT ε (‖s‖ + 1)
    refine squeeze_zero_norm' ?_ ((Real.tendsto_exp_neg_atTop_nhds_zero).const_mul C |>.congr'
      (Eventually.of_forall fun t => rfl) |> fun h => by simpa using h)
    filter_upwards [eventually_ge_atTop 0] with t ht
    simp only [Pi.mul_apply]
    rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs]
    have hbt := hb t
    simp only [iteratedDeriv_zero] at hbt
    rw [abs_of_nonneg ht] at hbt
    have hre : (-(s * (t : ℂ))).re ≤ ‖s‖ * t := by
      calc (-(s * (t : ℂ))).re ≤ ‖-(s * (t : ℂ))‖ := Complex.re_le_norm _
        _ = ‖s‖ * t := by rw [norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht]
    calc Real.exp (-(s * (t : ℂ))).re * |g t| ≤ Real.exp (‖s‖ * t) * (C * Real.exp (-((‖s‖ + 1) * t))) :=
          mul_le_mul (Real.exp_le_exp.mpr hre) hbt (abs_nonneg _) (Real.exp_pos _).le
      _ = C * Real.exp (-t) := by rw [mul_left_comm, ← Real.exp_add]; ring_nf
  have hibp := integral_Ioi_mul_deriv_eq_deriv_mul hu hv
    (IntegrableOn.congr_fun h1 (fun t _ => rfl) measurableSet_Ioi)
    (IntegrableOn.congr_fun (h0.const_mul (-s)) (fun t _ => by simp only [Pi.mul_apply]; ring)
      measurableSet_Ioi)
    hlim0 hlimtop
  rw [renewalLaplace, renewalLaplace, hibp, sub_self, zero_sub, ← integral_neg,
    ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  ring

/-! ## The surgered profile, increment, denominator and two-ended function -/

/-- The surgered profile `P_g = P + g`. -/
def surgeryProfile (N : ℕ) (T : ℝ) (ε : Fin 3 → ℝ) (t : ℝ) : ℝ :=
  thetaLogProfile t + surgeryPerturbation N T ε t

/-- The surgered increment `ν_g = aP_g - P_g'`. -/
def surgeryIncrement (N : ℕ) (T : ℝ) (ε : Fin 3 → ℝ) (t : ℝ) : ℝ :=
  1 / 4 * surgeryProfile N T ε t - deriv (surgeryProfile N T ε) t

theorem surgeryIncrement_eq (N : ℕ) (T : ℝ) (ε : Fin 3 → ℝ) (t : ℝ) :
    surgeryIncrement N T ε t = thetaRenewalIncrement t +
      (1 / 4 * surgeryPerturbation N T ε t - deriv (surgeryPerturbation N T ε) t) := by
  have hP := hasDerivAt_thetaLogProfile t
  have hg := hasDerivAt_surgeryPerturbation N T ε t
  have hd : deriv (surgeryProfile N T ε) t =
      (thetaLogProfile t / 4 - thetaRenewalIncrement t) + deriv (surgeryPerturbation N T ε) t :=
    (hP.add hg).deriv
  rw [surgeryIncrement, hd, surgeryProfile]; ring

theorem hasDerivAt_surgeryProfile (N : ℕ) (T : ℝ) (ε : Fin 3 → ℝ) (t : ℝ) :
    HasDerivAt (surgeryProfile N T ε) (1 / 4 * surgeryProfile N T ε t - surgeryIncrement N T ε t) t := by
  have h := (hasDerivAt_thetaLogProfile t).add (hasDerivAt_surgeryPerturbation N T ε t)
  refine h.congr_deriv ?_
  rw [surgeryIncrement_eq, surgeryProfile]; ring

theorem continuous_surgeryIncrement (N : ℕ) (T : ℝ) (ε : Fin 3 → ℝ) :
    Continuous (surgeryIncrement N T ε) := by
  have h : surgeryIncrement N T ε = fun t => thetaRenewalIncrement t +
      (1 / 4 * surgeryPerturbation N T ε t - deriv (surgeryPerturbation N T ε) t) :=
    funext (surgeryIncrement_eq N T ε)
  rw [h]
  have := continuous_thetaRenewalIncrement
  have := (contDiff_surgeryPerturbation N T ε).continuous
  have := continuous_deriv_surgeryPerturbation N T ε
  fun_prop

theorem surgeryProfile_neg (N : ℕ) (T : ℝ) (ε : Fin 3 → ℝ) (t : ℝ) :
    surgeryProfile N T ε (-t) = surgeryProfile N T ε t := by
  rw [surgeryProfile, surgeryProfile, thetaLogProfile_neg, surgeryPerturbation_neg]

theorem surgeryProfile_zero (N : ℕ) (T : ℝ) (ε : Fin 3 → ℝ) : surgeryProfile N T ε 0 = Θ 1 := by
  rw [surgeryProfile, surgeryPerturbation_zero_arg, add_zero, thetaLogProfile_zero]

/-- The surgered denominator `D_g(s) = c - ∫₀^∞ e^{-st} ν_g`. -/
def surgeryDenominator (N : ℕ) (T : ℝ) (ε : Fin 3 → ℝ) (s : ℂ) : ℂ :=
  (Θ 1 : ℂ) - renewalLaplace (surgeryIncrement N T ε) s

/-- The surgered two-ended function `X_g(z) = (a - iz) D_g(-iz) + (a + iz) D_g(iz)`. -/
def surgeryXi (N : ℕ) (T : ℝ) (ε : Fin 3 → ℝ) (z : ℂ) : ℂ :=
  (1 / 4 - I * z) * surgeryDenominator N T ε (-(I * z)) +
    (1 / 4 + I * z) * surgeryDenominator N T ε (I * z)

/-- `D_g(s) = D(s) - (a - s) ĝ(s)`. -/
theorem surgeryDenominator_eq (N : ℕ) {T : ℝ} (hT : 0 ≤ T) (ε : Fin 3 → ℝ) (s : ℂ) :
    surgeryDenominator N T ε s = thetaRenewalDenominator s -
      (1 / 4 - s) * renewalLaplace (surgeryPerturbation N T ε) s := by
  have hν := integrableOn_cexp_mul_of_superexp continuous_thetaRenewalIncrement
    thetaRenewalIncrement_superexp s
  have h0 := (integrableOn_cexp_mul_iteratedDeriv N 0 hT ε s).integrableOn (s := Ioi 0)
  have h1 := (integrableOn_cexp_mul_iteratedDeriv N 1 hT ε s).integrableOn (s := Ioi 0)
  simp only [iteratedDeriv_one, iteratedDeriv_zero] at h1 h0
  have hA : IntegrableOn (fun t : ℝ => 1 / 4 * (cexp (-(s * t)) * (surgeryPerturbation N T ε t : ℂ)) -
      cexp (-(s * t)) * ((deriv (surgeryPerturbation N T ε) t : ℝ) : ℂ)) (Ioi 0) :=
    (h0.const_mul _).sub h1
  have hsplit : renewalLaplace (surgeryIncrement N T ε) s = thetaRenewalLaplace s +
      (1 / 4 * renewalLaplace (surgeryPerturbation N T ε) s -
        renewalLaplace (deriv (surgeryPerturbation N T ε)) s) := by
    calc renewalLaplace (surgeryIncrement N T ε) s = ∫ t in Ioi (0 : ℝ),
          (cexp (-(s * t)) * (thetaRenewalIncrement t : ℂ) +
            (1 / 4 * (cexp (-(s * t)) * (surgeryPerturbation N T ε t : ℂ)) -
              cexp (-(s * t)) * ((deriv (surgeryPerturbation N T ε) t : ℝ) : ℂ))) := by
          refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
          simp only [surgeryIncrement_eq]; push_cast; ring
      _ = _ := by
          rw [integral_add hν hA, integral_sub (h0.const_mul _) h1, integral_const_mul]
          rfl
  rw [surgeryDenominator, hsplit, renewalLaplace_deriv_surgeryPerturbation N hT ε,
    thetaRenewalDenominator]
  ring


/-- `∫₀^∞ e^{-st} ν_g = N(s) + (a - s) ĝ(s)`. -/
theorem renewalLaplace_surgeryIncrement (N : ℕ) {T : ℝ} (hT : 0 ≤ T) (ε : Fin 3 → ℝ) (s : ℂ) :
    renewalLaplace (surgeryIncrement N T ε) s = thetaRenewalLaplace s +
      (1 / 4 - s) * renewalLaplace (surgeryPerturbation N T ε) s := by
  have h := surgeryDenominator_eq N hT ε s
  rw [surgeryDenominator, thetaRenewalDenominator] at h
  linear_combination -h

/-- The two-sided transform `F_g(z) = ∫ e^{-izt} g(t) dt`. -/
def surgeryTransform (N : ℕ) (T : ℝ) (ε : Fin 3 → ℝ) (z : ℂ) : ℂ :=
  ∫ t : ℝ, cexp (-(I * z * t)) * (surgeryPerturbation N T ε t : ℂ)

/-- For even `g`, `ĝ(-iz) + ĝ(iz) = F_g(z)`. -/
theorem renewalLaplace_add_eq_surgeryTransform (N : ℕ) {T : ℝ} (hT : 0 ≤ T) (ε : Fin 3 → ℝ) (z : ℂ) :
    renewalLaplace (surgeryPerturbation N T ε) (-(I * z)) +
      renewalLaplace (surgeryPerturbation N T ε) (I * z) = surgeryTransform N T ε z := by
  set g := surgeryPerturbation N T ε
  have hint := integrableOn_cexp_mul_iteratedDeriv N 0 hT ε (I * z)
  simp only [iteratedDeriv_zero] at hint
  have hsplit := intervalIntegral.integral_Iic_add_Ioi (b := 0) hint.integrableOn hint.integrableOn
  have hneg := integral_comp_neg_Iic 0 (fun t : ℝ => cexp (-(I * z * t)) * (g t : ℂ))
  have hneg' : ∫ t in Iic (0 : ℝ), cexp (-(I * z * t)) * (g t : ℂ) =
      ∫ t in Ioi (0 : ℝ), cexp (-(-(I * z) * t)) * (g t : ℂ) := by
    have h2 := integral_comp_neg_Iic 0 (fun t : ℝ => cexp (-(-(I * z) * t)) * (g t : ℂ))
    rw [neg_zero] at h2
    rw [← h2]
    refine setIntegral_congr_fun measurableSet_Iic fun t _ => ?_
    simp only [g, surgeryPerturbation_neg, Complex.ofReal_neg]
    congr 2; ring
  rw [surgeryTransform, ← hsplit, hneg', renewalLaplace, renewalLaplace]

/-- **The exact variation (5).** `X_g(z) - Ξ(2z) = -(z² + a²) F_g(z)`. -/
theorem surgeryXi_eq (N : ℕ) {T : ℝ} (hT : 0 ≤ T) (ε : Fin 3 → ℝ) (z : ℂ) :
    surgeryXi N T ε z = XiC (2 * z) - (z ^ 2 + 1 / 16) * surgeryTransform N T ε z := by
  rw [surgeryXi, surgeryDenominator_eq N hT ε, surgeryDenominator_eq N hT ε,
    ← renewalLaplace_add_eq_surgeryTransform N hT ε z, ← thetaRenewal_two_ended z]
  have hI : I ^ 2 = -1 := Complex.I_sq
  linear_combination (renewalLaplace (surgeryPerturbation N T ε) (-(I * z)) +
    renewalLaplace (surgeryPerturbation N T ε) (I * z)) * z ^ 2 * hI

/-- The two-sided transform on the line `Im z = b` is the strip evaluation. -/
theorem surgeryTransform_eq_stripEval (N : ℕ) (T : ℝ) (ε : Fin 3 → ℝ) (u b : ℝ) :
    surgeryTransform N T ε ((u : ℂ) + b * I) = stripEval b u (surgeryPerturbation N T ε) := by
  rw [surgeryTransform, stripEval]
  congr 1; ext t; congr 2; ring

/-- **The exact mass (3).** `∫₀^∞ e^{at} ν_g = ∫₀^∞ e^{at} ν + 2a ∫₀^∞ e^{at} g`. -/
theorem integral_exp_mul_surgeryIncrement (N : ℕ) {T : ℝ} (hT : 0 ≤ T) (ε : Fin 3 → ℝ) :
    ∫ t in Ioi (0 : ℝ), Real.exp (1 / 4 * t) * surgeryIncrement N T ε t =
      (∫ t in Ioi (0 : ℝ), Real.exp (1 / 4 * t) * thetaRenewalIncrement t) +
        1 / 2 * ∫ t in Ioi (0 : ℝ), Real.exp (1 / 4 * t) * surgeryPerturbation N T ε t := by
  have h := renewalLaplace_surgeryIncrement N hT ε (-(1 / 4))
  have hre : ∀ f : ℝ → ℝ, renewalLaplace f (-(1 / 4)) =
      ((∫ t in Ioi (0 : ℝ), Real.exp (1 / 4 * t) * f t : ℝ) : ℂ) := by
    intro f
    rw [renewalLaplace, ← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    push_cast
    congr 2; ring
  rw [hre, show thetaRenewalLaplace (-(1 / 4)) = renewalLaplace thetaRenewalIncrement (-(1 / 4)) from rfl,
    hre, hre] at h
  have h' : ((∫ t in Ioi (0 : ℝ), Real.exp (1 / 4 * t) * surgeryIncrement N T ε t : ℝ) : ℂ) =
      (((∫ t in Ioi (0 : ℝ), Real.exp (1 / 4 * t) * thetaRenewalIncrement t) +
        1 / 2 * ∫ t in Ioi (0 : ℝ), Real.exp (1 / 4 * t) * surgeryPerturbation N T ε t : ℝ) : ℂ) := by
    rw [h]; push_cast; ring
  exact_mod_cast h'

/-! ## The perturbed Fourier density -/

/-- Whole-line Fourier differentiation at complex frequency:
`∫ e^{-izt} g^{(k+1)} = iz ∫ e^{-izt} g^{(k)}`. -/
theorem integral_cexp_mul_iteratedDeriv_succ (N k : ℕ) {T : ℝ} (hT : 0 ≤ T) (ε : Fin 3 → ℝ)
    (z : ℂ) :
    ∫ t : ℝ, cexp (-(I * z * t)) * ((iteratedDeriv (k + 1) (surgeryPerturbation N T ε) t : ℝ) : ℂ) =
      I * z * ∫ t : ℝ, cexp (-(I * z * t)) *
        ((iteratedDeriv k (surgeryPerturbation N T ε) t : ℝ) : ℂ) := by
  set g := surgeryPerturbation N T ε
  have hdiff : Differentiable ℝ (iteratedDeriv k g) :=
    (contDiff_surgeryPerturbation N T ε).differentiable_iteratedDeriv k
      (WithTop.coe_lt_coe.mpr (ENat.coe_lt_top k))
  have hu : ∀ t : ℝ, HasDerivAt (fun t : ℝ => cexp (-(I * z * t)))
      (-(I * z) * cexp (-(I * z * t))) t := by
    intro t
    have h := ((hasDerivAt_id (t : ℂ)).const_mul (-(I * z))).cexp.comp_ofReal
    simpa [mul_comm, mul_left_comm, mul_assoc, neg_mul] using h
  have hv : ∀ t : ℝ, HasDerivAt (fun t : ℝ => ((iteratedDeriv k g t : ℝ) : ℂ))
      ((iteratedDeriv (k + 1) g t : ℝ) : ℂ) t := by
    intro t
    rw [iteratedDeriv_succ]
    exact (hdiff t).hasDerivAt.ofReal_comp
  have h1 := integrableOn_cexp_mul_iteratedDeriv N (k + 1) hT ε (I * z)
  have h0 := integrableOn_cexp_mul_iteratedDeriv N k hT ε (I * z)
  have hibp := integral_mul_deriv_eq_deriv_mul_of_integrable (fun t _ => hu t) (fun t _ => hv t)
    h1 ((h0.const_mul (-(I * z))).congr (Eventually.of_forall fun t => by
      simp only [Pi.mul_apply]; ring)) h0
  rw [hibp, ← integral_const_mul, ← integral_neg]
  congr 1; ext t; ring

/-- `∫ e^{-izt} g'' = -z² ∫ e^{-izt} g`. -/
theorem integral_cexp_mul_iteratedDeriv_two (N : ℕ) {T : ℝ} (hT : 0 ≤ T) (ε : Fin 3 → ℝ)
    (z : ℂ) :
    ∫ t : ℝ, cexp (-(I * z * t)) * ((iteratedDeriv 2 (surgeryPerturbation N T ε) t : ℝ) : ℂ) =
      -z ^ 2 * surgeryTransform N T ε z := by
  rw [integral_cexp_mul_iteratedDeriv_succ N 1 hT ε, integral_cexp_mul_iteratedDeriv_succ N 0 hT ε,
    surgeryTransform]
  simp only [iteratedDeriv_zero]
  have hI : I ^ 2 = -1 := Complex.I_sq
  linear_combination (z ^ 2 * ∫ t : ℝ, cexp (-(I * z * t)) * (surgeryPerturbation N T ε t : ℂ)) * hI

/-- The perturbed full-source density `k_g(x) = k(x) + 2[g''(2x) - a² g(2x)]`. -/
def surgeryDensity (N : ℕ) (T : ℝ) (ε : Fin 3 → ℝ) (x : ℝ) : ℝ :=
  thetaCuspFullSource x + 2 * (iteratedDeriv 2 (surgeryPerturbation N T ε) (2 * x) -
    surgeryPerturbation N T ε (2 * x) / 16)

theorem integrable_cexp_mul_comp_two (N k : ℕ) {T : ℝ} (hT : 0 ≤ T) (ε : Fin 3 → ℝ) (w : ℂ) :
    Integrable fun x : ℝ => cexp (-I * w * x) *
      ((iteratedDeriv k (surgeryPerturbation N T ε) (2 * x) : ℝ) : ℂ) := by
  have h := (integrableOn_cexp_mul_iteratedDeriv N k hT ε (I * (w / 2))).comp_mul_left'
    (two_ne_zero : (2 : ℝ) ≠ 0)
  refine h.congr (Eventually.of_forall fun x => ?_)
  push_cast
  congr 1; congr 1; ring

theorem integral_cexp_mul_comp_two (N k : ℕ) (T : ℝ) (ε : Fin 3 → ℝ) (w : ℂ) :
    ∫ x : ℝ, cexp (-I * w * x) * ((iteratedDeriv k (surgeryPerturbation N T ε) (2 * x) : ℝ) : ℂ) =
      1 / 2 * ∫ t : ℝ, cexp (-(I * (w / 2) * t)) *
        ((iteratedDeriv k (surgeryPerturbation N T ε) t : ℝ) : ℂ) := by
  have h := Measure.integral_comp_mul_left (fun t : ℝ => cexp (-(I * (w / 2) * t)) *
    ((iteratedDeriv k (surgeryPerturbation N T ε) t : ℝ) : ℂ)) 2
  rw [show |(2 : ℝ)⁻¹| = 1 / 2 by norm_num] at h
  rw [Complex.real_smul] at h
  push_cast at h
  rw [← h]
  congr 1; ext x; congr 2; ring

/-- **The perturbed density (7).** `∫ e^{-iwx} k_g(x) dx = X_g(w/2)`. -/
theorem integral_cexp_mul_surgeryDensity (N : ℕ) {T : ℝ} (hT : 0 ≤ T) (ε : Fin 3 → ℝ) (w : ℂ) :
    ∫ x : ℝ, cexp (-I * w * x) * (surgeryDensity N T ε x : ℂ) = surgeryXi N T ε (w / 2) := by
  have hk := HedenmalmThetaSource.integrable_thetaCuspFourierLaplaceIntegrand_all w
  have h2 := integrable_cexp_mul_comp_two N 2 hT ε w
  have h0 := integrable_cexp_mul_comp_two N 0 hT ε w
  simp only [iteratedDeriv_zero] at h0
  have hsplit : (fun x : ℝ => cexp (-I * w * x) * (surgeryDensity N T ε x : ℂ)) =
      fun x => thetaCuspFourierLaplaceIntegrand w x +
        (2 * (cexp (-I * w * x) * ((iteratedDeriv 2 (surgeryPerturbation N T ε) (2 * x) : ℝ) : ℂ)) -
          1 / 8 * (cexp (-I * w * x) * ((surgeryPerturbation N T ε (2 * x) : ℝ) : ℂ))) := by
    ext x
    rw [surgeryDensity, thetaCuspFourierLaplaceIntegrand]
    push_cast; ring
  have hrest : Integrable fun x : ℝ =>
      2 * (cexp (-I * w * x) * ((iteratedDeriv 2 (surgeryPerturbation N T ε) (2 * x) : ℝ) : ℂ)) -
        1 / 8 * (cexp (-I * w * x) * ((surgeryPerturbation N T ε (2 * x) : ℝ) : ℂ)) :=
    (h2.const_mul 2).sub (h0.const_mul (1 / 8))
  rw [hsplit, integral_add hk hrest,
    integral_sub (h2.const_mul 2) (h0.const_mul (1 / 8)), integral_const_mul, integral_const_mul,
    integral_cexp_mul_comp_two N 2 T ε w,
    show (fun x : ℝ => cexp (-I * w * x) * ((surgeryPerturbation N T ε (2 * x) : ℝ) : ℂ)) =
      fun x : ℝ => cexp (-I * w * x) * ((iteratedDeriv 0 (surgeryPerturbation N T ε) (2 * x) : ℝ) : ℂ)
      by simp only [iteratedDeriv_zero],
    integral_cexp_mul_comp_two N 0 T ε w, integral_cexp_mul_iteratedDeriv_two N hT ε,
    surgeryXi_eq N hT ε, show 2 * (w / 2) = w by ring, ← thetaCuspFourierLaplace,
    HedenmalmThetaSource.thetaCuspFourierLaplace_eq_XiC_all]
  simp only [iteratedDeriv_zero]
  rw [← surgeryTransform]
  ring

end

end RHTower
