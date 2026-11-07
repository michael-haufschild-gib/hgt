import GaloisForLFunctions.CompletedArithmeticForms.BesselHalfOrderSquare
import GaloisForLFunctions.CompletedArithmeticForms.BesselWeightedTail
import GaloisForLFunctions.CompletedArithmeticForms.BesselGammaMomentScale
import GaloisForLFunctions.RHTower.UnwindowedHankelSignCone
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMCauchyPowerFourierBessel
import GaloisForLFunctions.HTGeometry.GammaCosineCriticalModulus
/-!
# A Gamma spectral reserve for the integrated first atom

The half-order Bessel square has an exact Gamma limit at zero. Its
exponential monotonicity propagates that limit to every positive argument.
Radial integration gives a positive hyperbolic-secant reserve uniform
over all frequencies and all polynomial degrees.
-/

open MeasureTheory Complex Filter Set Topology

noncomputable section
namespace GaloisForLFunctions.CompletedArithmeticForms

private def gammaKernel (s : ℂ) (t : ℝ) : ℂ :=
  (Real.exp (-t) : ℂ) * (t : ℂ) ^ (s - 1)

private def regularizedGamma (s : ℂ) (x : ℝ) : ℂ :=
  ∫ t in Ioi (0 : ℝ), gammaKernel s t * (Real.exp (-(x ^ 2 / (4 * t))) : ℂ)

private theorem regularizedGamma_tendsto {s : ℂ} (hs : 0 < s.re) :
    Tendsto (regularizedGamma s) (𝓝 0) (𝓝 (Complex.Gamma s)) := by
  have hg : IntegrableOn (gammaKernel s) (Ioi 0) := Complex.GammaIntegral_convergent hs
  have hbound (x : ℝ) : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)),
      ‖gammaKernel s t * (Real.exp (-(x ^ 2 / (4 * t))) : ℂ)‖ ≤ ‖gammaKernel s t‖ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := ht
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have he : Real.exp (-(x ^ 2 / (4 * t))) ≤ 1 :=
      Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))
    simpa only [mul_one] using mul_le_mul_of_nonneg_left he (norm_nonneg _)
  have hlim : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)),
      Tendsto (fun x : ℝ => gammaKernel s t * (Real.exp (-(x ^ 2 / (4 * t))) : ℂ))
        (𝓝 0) (𝓝 (gammaKernel s t)) := by
    filter_upwards with t
    have hc : Continuous (fun x : ℝ =>
        gammaKernel s t * (Real.exp (-(x ^ 2 / (4 * t))) : ℂ)) := by fun_prop
    simpa using (hc.continuousAt (x := (0 : ℝ))).tendsto
  have hh := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict (Ioi (0 : ℝ))) (l := 𝓝 (0 : ℝ))
    (F := fun x t => gammaKernel s t * (Real.exp (-(x ^ 2 / (4 * t))) : ℂ))
    (f := gammaKernel s) (fun t => ‖gammaKernel s t‖)
    (Eventually.of_forall fun x => hg.aestronglyMeasurable.mul
      ((by fun_prop : Measurable fun t : ℝ =>
        (Real.exp (-(x ^ 2 / (4 * t))) : ℂ)).aestronglyMeasurable))
    (Eventually.of_forall hbound) hg.norm hlim
  rw [Complex.Gamma_eq_integral hs]
  exact hh

open GaloisForLFunctions.HTGeometry

private theorem regularizedGamma_eq_bessel {x : ℝ} (hx : 0 < x) (s : ℂ) :
    regularizedGamma s x =
      2 * ((x / 2 : ℝ) : ℂ) ^ s * modifiedBesselKOrder x s := by
  have hh := _root_.RHTower.integral_d4BMInverseGaussianMellinKernel_eq_bessel
    (a := (1 : ℝ)) (y := (1 : ℝ)) (xi := x / 2)
    (by norm_num) (by norm_num) (by positivity) s
  have he (t : ℝ) :
      gammaKernel s t * (Real.exp (-(x ^ 2 / (4 * t))) : ℂ) =
        _root_.RHTower.d4BMInverseGaussianMellinKernel 1 1 (x / 2) s t := by
    simp only [gammaKernel, _root_.RHTower.d4BMInverseGaussianMellinKernel,
      one_pow, one_mul, Complex.ofReal_exp]
    rw [mul_comm (Complex.exp ((-t : ℝ) : ℂ)) ((t : ℂ) ^ (s - 1)),
      mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  unfold regularizedGamma
  simp_rw [he]
  simpa only [div_one, one_mul, mul_one,
    show (2 : ℝ) * (x / 2) = x by ring] using hh

private theorem norm_regularizedGamma_half_sq {x : ℝ} (hx : 0 < x) (τ : ℝ) :
    ‖regularizedGamma (1 / 2 + (τ : ℂ) * I) x‖ ^ 2 =
      2 * besselHalfOrderSquare τ x := by
  rw [regularizedGamma_eq_bessel hx, norm_mul, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos (by positivity : 0 < x / 2)]
  have hre : (1 / 2 + (τ : ℂ) * I).re = (1 / 2 : ℝ) := by norm_num
  rw [hre, ← Real.sqrt_eq_rpow]
  norm_num only [norm_ofNat]
  rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity : 0 ≤ x / 2)]
  rw [besselHalfOrderSquare, besselHalfOrderValue, Complex.normSq_eq_norm_sq]
  ring

/-- The half-order square approaches its exact Gamma modulus at the origin. -/
theorem besselHalfOrderSquare_tendsto_zero_right (τ : ℝ) :
    Tendsto (besselHalfOrderSquare τ) (𝓝[>] (0 : ℝ))
      (𝓝 (Real.pi / (2 * Real.cosh (Real.pi * τ)))) := by
  have hs : 0 < (1 / 2 + (τ : ℂ) * I).re := by norm_num
  have hG := ((regularizedGamma_tendsto hs).norm.pow 2).div_const (2 : ℝ)
  have hlim : Tendsto (besselHalfOrderSquare τ) (𝓝[>] (0 : ℝ))
      (𝓝 (‖Complex.Gamma (1 / 2 + (τ : ℂ) * I)‖ ^ 2 / 2)) := by
    refine (hG.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    rw [norm_regularizedGamma_half_sq hx τ]
    ring
  have hΓ := GaloisForLFunctions.HTGeometry.normSq_Gamma_half_sub_mul_I (-τ)
  have he : (1 / 2 : ℂ) - ((-τ : ℝ) : ℂ) * I = 1 / 2 + (τ : ℂ) * I := by
    push_cast
    ring
  rw [he, mul_neg, Real.cosh_neg, Complex.normSq_eq_norm_sq] at hΓ
  rw [hΓ] at hlim
  convert hlim using 1
  ring

/-- The Gamma endpoint supplies an explicit floor at every frequency and argument. -/
theorem besselHalfOrderSquare_gamma_lower {x : ℝ} (hx : 0 < x) (τ : ℝ) :
    Real.pi * Real.exp (-2 * x) / (2 * Real.cosh (Real.pi * τ)) ≤
      besselHalfOrderSquare τ x := by
  have he : Tendsto (fun y : ℝ => Real.exp (2 * y)) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have hc : Continuous (fun y : ℝ => Real.exp (2 * y)) := by fun_prop
    simpa using (hc.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  have hlim := he.mul (besselHalfOrderSquare_tendsto_zero_right τ)
  simp only [one_mul] at hlim
  have hup : ∀ᶠ y in 𝓝[>] (0 : ℝ),
      Real.exp (2 * y) * besselHalfOrderSquare τ y ≤
        Real.exp (2 * x) * besselHalfOrderSquare τ x := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hx).filter_mono nhdsWithin_le_nhds] with y hy hyx
    exact monotoneOn_exp_mul_besselHalfOrderSquare τ hy hx hyx.le
  have hh := mul_le_mul_of_nonneg_left (le_of_tendsto hlim hup) (Real.exp_pos (-2 * x)).le
  have hcancel : Real.exp (-2 * x) * Real.exp (2 * x) = 1 := by
    rw [← Real.exp_add]
    norm_num
  calc
    _ = Real.exp (-2 * x) * (Real.pi / (2 * Real.cosh (Real.pi * τ))) := by ring
    _ ≤ _ := hh
    _ = _ := by rw [← mul_assoc, hcancel, one_mul]

/-- A fixed radial slice retains a uniform hyperbolic-secant reserve. -/
theorem besselFirstWeightedTail_gamma_lower {q : ℝ} (hq : 1 ≤ q) (τ : ℝ) :
    Real.exp (-2 * (q + 1)) / (2 * Real.cosh (Real.pi * τ)) ≤
      besselFirstWeightedTail τ q := by
  let C : ℝ := Real.pi * Real.exp (-2 * (q + 1)) / (2 * Real.cosh (Real.pi * τ))
  let f : ℝ → ℝ := fun v => besselHalfOrderSquare τ (Real.sqrt (q ^ 2 + v ^ 2))
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hr (v : ℝ) : 0 < Real.sqrt (q ^ 2 + v ^ 2) :=
    Real.sqrt_pos.mpr (add_pos_of_pos_of_nonneg (sq_pos_of_pos hq0) (sq_nonneg v))
  have hind : Integrable ((Icc (-1 : ℝ) 1).indicator (fun _ : ℝ => C)) :=
    (continuous_const.integrableOn_Icc).integrable_indicator measurableSet_Icc
  have hpoint (v : ℝ) : (Icc (-1 : ℝ) 1).indicator (fun _ : ℝ => C) v ≤ f v := by
    by_cases hv : v ∈ Icc (-1 : ℝ) 1
    · rw [Set.indicator_of_mem hv]
      have hrad : Real.sqrt (q ^ 2 + v ^ 2) ≤ q + 1 := by
        have hh : q ^ 2 + v ^ 2 ≤ (q + 1) ^ 2 := by nlinarith only [hv.1, hv.2, hq]
        have hh' := Real.sqrt_le_sqrt hh
        rwa [Real.sqrt_sq (by positivity : 0 ≤ q + 1)] at hh'
      have he := Real.exp_le_exp.mpr (by linarith only [hrad] :
        -2 * (q + 1) ≤ -2 * Real.sqrt (q ^ 2 + v ^ 2))
      exact (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left he Real.pi_pos.le)
        (by positivity : 0 ≤ 2 * Real.cosh (Real.pi * τ))).trans
          (besselHalfOrderSquare_gamma_lower (hr v) τ)
    · rw [Set.indicator_of_notMem hv]
      exact (besselHalfOrderSquare_pos (hr v) τ).le
  have hh := integral_mono hind (integrable_besselHalfOrderSquare_slice hq τ) hpoint
  rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hh
  rw [intervalIntegral.integral_const] at hh
  simp only [sub_neg_eq_add, smul_eq_mul] at hh
  change (1 + 1) * C ≤ ∫ v : ℝ, besselHalfOrderSquare τ (Real.sqrt (q ^ 2 + v ^ 2)) at hh
  rw [← two_pi_mul_besselFirstWeightedTail_eq_square_integral hq τ] at hh
  dsimp only [C] at hh
  have hh' : (2 * Real.pi) *
      (Real.exp (-2 * (q + 1)) / (2 * Real.cosh (Real.pi * τ))) ≤
        (2 * Real.pi) * besselFirstWeightedTail τ q := by
    convert hh using 1
    ring
  exact (mul_le_mul_iff_right₀ (by positivity : 0 < 2 * Real.pi)).mp hh'

/-- The complete signed first-atom tail pays the Gamma density pointwise. -/
theorem besselFirstAtomTailDensity_gamma_lower {q : ℝ} (hq : 3 ≤ q) (τ : ℝ) :
    2 * Real.sqrt q * (q ^ 2 - 2 * q - 1) * Real.exp (-2 * (q + 1)) /
      Real.cosh (Real.pi * τ) ≤ besselFirstAtomTailDensity τ q := by
  have hq1 : 1 < q := by linarith only [hq]
  have hD : 0 ≤ q ^ 2 - 2 * q - 1 := by nlinarith only [hq]
  have hp := first_tail_le_besselPowerTail hq1 (by norm_num : (1 : ℝ) < 3 / 2) τ
  norm_num only [show (3 / 2 : ℝ) - 1 = 1 / 2 by norm_num] at hp
  rw [besselPowerTail_one, ← Real.sqrt_eq_rpow] at hp
  calc
    _ = (4 * (q ^ 2 - 2 * q - 1)) * (Real.sqrt q *
        (Real.exp (-2 * (q + 1)) / (2 * Real.cosh (Real.pi * τ)))) := by ring
    _ ≤ (4 * (q ^ 2 - 2 * q - 1)) * (Real.sqrt q * besselFirstWeightedTail τ q) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (besselFirstWeightedTail_gamma_lower hq1.le τ) (Real.sqrt_nonneg q))
        (by positivity)
    _ ≤ (4 * (q ^ 2 - 2 * q - 1)) * besselPowerTail (3 / 2) τ q :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ ≤ _ := besselFirstAtomTailDensity_lower hq1 τ

/-- The positive reserve coefficient is independent of polynomial degree. -/
def firstAtomGammaReserve (q : ℝ) : ℝ :=
  2 * Real.sqrt q * (q ^ 2 - 2 * q - 1) * Real.exp (-2 * (q + 1))

theorem firstAtomGammaReserve_pos {q : ℝ} (hq : 3 ≤ q) : 0 < firstAtomGammaReserve q := by
  have hq0 : 0 < q := by linarith only [hq]
  have hD : 0 < q ^ 2 - 2 * q - 1 := by nlinarith only [hq]
  unfold firstAtomGammaReserve
  positivity

private theorem firstAtom_density_pos {q : ℝ} (hq : 3 ≤ q) (b : ℝ) :
    0 < besselFirstAtomTailDensity (b / 2) q := by
  have hh := besselFirstAtomTailDensity_gamma_lower hq (b / 2)
  exact (div_pos (firstAtomGammaReserve_pos hq) (Real.cosh_pos _)).trans_le hh

/-- Every raw first-atom moment is absolutely integrable. -/
theorem integrable_besselFirstAtomMoment {q : ℝ} (hq : 3 ≤ q) (k : ℕ) :
    Integrable (fun b : ℝ => b ^ k * besselFirstAtomTailDensity (b / 2) q) := by
  have hi0 : Integrable (fun b : ℝ => besselFirstAtomTailDensity (b / 2) q) := by
    simpa only [Nat.mul_zero, pow_zero, one_mul] using integrable_besselFirstAtomEvenMoment hq 0
  have hi2 := integrable_besselFirstAtomEvenMoment hq k
  apply (hi0.add hi2).mono'
    ((by fun_prop : Continuous fun b : ℝ => b ^ k).aestronglyMeasurable.mul hi0.aestronglyMeasurable)
  filter_upwards with b
  change ‖b ^ k * besselFirstAtomTailDensity (b / 2) q‖ ≤
    besselFirstAtomTailDensity (b / 2) q + b ^ (2 * k) * besselFirstAtomTailDensity (b / 2) q
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (firstAtom_density_pos hq b)]
  have hb : |b ^ k| ≤ 1 + b ^ (2 * k) := by
    have he : b ^ (2 * k) = (b ^ k) ^ 2 := by rw [← pow_mul, Nat.mul_comm k 2]
    rw [he]
    nlinarith only [sq_nonneg (|b ^ k| - 1), sq_abs (b ^ k)]
  have hh := mul_le_mul_of_nonneg_right hb (firstAtom_density_pos hq b).le
  simpa only [add_mul, one_mul, Pi.add_apply] using hh

/-- The complete first atom pays a fixed Gamma norm for every polynomial degree. -/
theorem firstAtom_polynomial_gamma_payment {q : ℝ} (hq : 3 ≤ q) (P : Polynomial ℝ) :
    firstAtomGammaReserve q * (∫ b : ℝ, P.eval b ^ 2 / Real.cosh (Real.pi * b / 2)) ≤
      ∫ b : ℝ, P.eval b ^ 2 * besselFirstAtomTailDensity (b / 2) q := by
  have hC := firstAtomGammaReserve_pos hq
  have hi : Integrable (fun b : ℝ => P.eval b ^ 2 * besselFirstAtomTailDensity (b / 2) q) := by
    have hh := _root_.RHTower.integrable_polynomial_mul_of_rawMoments
      (integrable_besselFirstAtomMoment hq) (P ^ 2)
    convert hh using 1
    funext b
    rw [_root_.Polynomial.eval_pow]
  have hpoint (b : ℝ) : firstAtomGammaReserve q * (P.eval b ^ 2 / Real.cosh (Real.pi * b / 2)) ≤
      P.eval b ^ 2 * besselFirstAtomTailDensity (b / 2) q := by
    have hh := mul_le_mul_of_nonneg_left (besselFirstAtomTailDensity_gamma_lower hq (b / 2))
      (sq_nonneg (P.eval b))
    rw [show Real.pi * (b / 2) = Real.pi * b / 2 by ring] at hh
    dsimp only [firstAtomGammaReserve]
    calc
      _ = P.eval b ^ 2 *
          (2 * Real.sqrt q * (q ^ 2 - 2 * q - 1) * Real.exp (-2 * (q + 1)) /
            Real.cosh (Real.pi * b / 2)) := by ring
      _ ≤ _ := hh
  have hgi : Integrable (fun b : ℝ => P.eval b ^ 2 / Real.cosh (Real.pi * b / 2)) := by
    have hc : Continuous fun b : ℝ => P.eval b ^ 2 / Real.cosh (Real.pi * b / 2) :=
      Continuous.div (by fun_prop) (by fun_prop) (fun b => (Real.cosh_pos _).ne')
    apply (hi.div_const (firstAtomGammaReserve q)).mono' hc.aestronglyMeasurable
    filter_upwards with b
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact (le_div_iff₀ hC).mpr (by nlinarith only [hpoint b])
  have hh := integral_mono (hgi.const_mul _) hi hpoint
  rwa [integral_const_mul] at hh

#print axioms besselHalfOrderSquare_tendsto_zero_right
#print axioms besselFirstAtomTailDensity_gamma_lower
#print axioms firstAtom_polynomial_gamma_payment

end GaloisForLFunctions.CompletedArithmeticForms

