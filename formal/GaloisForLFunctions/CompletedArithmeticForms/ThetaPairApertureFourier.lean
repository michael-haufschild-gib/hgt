import GaloisForLFunctions.CompletedArithmeticForms.ThetaPairApertureJets
import GaloisForLFunctions.CompletedArithmeticForms.ApertureTailFubini
import GaloisForLFunctions.CompletedArithmeticForms.ThetaPairApertureRemainder
import GaloisForLFunctions.HTGeometry.FourierIntegralDilation

/-!
# The exact aperture-weighted theta-pair Fourier spectrum

Radial Fubini and Fourier translation identify each ordered-pair Schwartz
transform with its literal weighted Wigner integral. The real transform
is exactly the aperture spectrum at frequency `-πξ`.
-/

set_option autoImplicit false

open Complex Filter Set MeasureTheory
open scoped Topology SchwartzMap FourierTransform
namespace GaloisForLFunctions.CompletedArithmeticForms
open HTGeometry _root_.RHTower
noncomputable section

private theorem pair_radial_half_coefficient {q : ℝ} (hq : 0 < q) (s : ℝ) :
    q ^ (-(1 / 2 : ℝ)) * (q * Real.exp s) *
      (q * Real.exp s) ^ (-(1 / 2 : ℝ)) = Real.exp (s / 2) := by
  have hu : 0 < q * Real.exp s := mul_pos hq (Real.exp_pos s)
  have hp : (q * Real.exp s) * (q * Real.exp s) ^ (-(1 / 2 : ℝ)) =
      (q * Real.exp s) ^ (1 / 2 : ℝ) := by
    calc
      _ = (q * Real.exp s) ^ (1 : ℝ) * (q * Real.exp s) ^ (-(1 / 2 : ℝ)) := by
        rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hu]; norm_num
  rw [mul_assoc, hp, Real.rpow_def_of_pos hq, Real.rpow_def_of_pos hu,
    ← Real.exp_add, Real.log_mul hq.ne' (Real.exp_pos s).ne', Real.log_exp]
  congr 1
  ring

/-- The literal ordered-pair Wigner function has the same radial normalization as its source. -/
theorem thetaPairWigner_eq_radialFourier {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (s b : ℝ) :
    thetaCuspSourcePairWigner n m (s / 2) b =
      thetaCuspWignerDivisorRatioPhase n m b *
        ((4 * (Real.pi * n * m) ^ (-(1 / 2 : ℝ)) * (Real.pi * n * m * Real.exp s) : ℝ) : ℂ) *
          ∫ t : ℝ, firstAtomRadialKernel (Real.pi * n * m * Real.exp s) (t : ℂ) *
            thetaWignerDifferencePhase b t := by
  let q : ℝ := Real.pi * n * m
  have hq : 0 < q := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2)
    (thetaPair_radialScale_ge_two hn hm)
  have hu : 0 < q * Real.exp s := mul_pos hq (Real.exp_pos s)
  rw [thetaCuspSourcePairWigner_eq_phase_mul_radial hn hm,
    integral_apertureRadialKernel_phase hu]
  have hscale : thetaCuspWignerAtomScale n m (s / 2) = 2 * (q * Real.exp s) := by
    unfold thetaCuspWignerAtomScale
    rw [show 2 * (s / 2) = s by ring]
    dsimp only [q]
    ring
  rw [hscale]
  have hc := pair_radial_half_coefficient hq s
  have hcC : (((4 * q ^ (-(1 / 2 : ℝ)) * (q * Real.exp s)) : ℝ) : ℂ) *
      (1 / 4 : ℂ) * ((q * Real.exp s) ^ (-(1 / 2 : ℝ)) : ℝ) = (Real.exp (s / 2) : ℂ) := by
    have hr : (4 * q ^ (-(1 / 2 : ℝ)) * (q * Real.exp s)) *
        (1 / 4 : ℝ) * (q * Real.exp s) ^ (-(1 / 2 : ℝ)) = Real.exp (s / 2) := by
      nlinarith only [hc]
    simpa only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_ofNat] using congrArg Complex.ofReal hr
  calc
    _ = thetaCuspWignerDivisorRatioPhase n m b *
        (Real.exp (s / 2) : ℂ) * thetaCuspWignerRadialTransform (2 * (q * Real.exp s)) b := by ring
    _ = _ := by rw [← hcC]; ring

private theorem aperture_weight_exp (a : ℝ) {q : ℝ} (hq : 0 < q) (s : ℝ) :
    apertureRadialWeight a q (q * Real.exp s) = s * Real.sinh (a * s) := by
  simp only [apertureRadialWeight, mul_div_cancel_left₀ _ hq.ne', Real.log_exp]

/-- The actual weighted pair Fourier integral is absolutely convergent. -/
theorem integrableOn_weighted_thetaPairWigner {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (b : ℝ) :
    IntegrableOn (fun s : ℝ => (s * Real.sinh (a * s) : ℂ) *
      thetaCuspSourcePairWigner n m (s / 2) b) (Ioi 0) := by
  let q : ℝ := Real.pi * n * m
  have hq : 2 ≤ q := thetaPair_radialScale_ge_two hn hm
  have hq0 : 0 < q := by linarith only [hq]
  have hi := integrableOn_apertureRadialWeight_mul_fourier ha0 ha1 hq b
  have hc := ((integrableOn_Ioi_expScale hq0 _).mp hi).const_mul
    (thetaCuspWignerDivisorRatioPhase n m b * ((4 * q ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))
  apply hc.congr
  filter_upwards with s
  rw [thetaPairWigner_eq_radialFourier hn hm, aperture_weight_exp a hq0]
  simp only [Complex.real_smul, q]
  push_cast
  ring

/-- The aperture primitive gives exactly the literal ordered-pair spectrum. -/
theorem thetaPairApertureSpectrum_eq_weighted_Wigner {n m : ℕ}
    (hn : 0 < n) (hm : 0 < m) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (b : ℝ) :
    thetaPairApertureSpectrum n m a b =
      ∫ s in Ioi (0 : ℝ), s * Real.sinh (a * s) *
        (thetaCuspSourcePairWigner n m (s / 2) b).re := by
  have hg : StronglyMeasurable (fun s : ℝ =>
      (thetaCuspSourcePairWigner n m (s / 2) b).re) := by
    let K : ℝ × ℝ → ℂ := fun p =>
      (thetaCuspSourceTerm (p.1 / 2 + p.2) n *
        thetaCuspSourceTerm (p.1 / 2 - p.2) m : ℂ) * thetaWignerDifferencePhase b p.2
    have hK : Continuous K := by
      unfold K thetaCuspSourceTerm thetaCuspSeed thetaWignerDifferencePhase
      fun_prop
    have hC := hK.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure ℝ))
    simpa only [K, thetaCuspSourcePairWigner] using
      Complex.continuous_re.comp_stronglyMeasurable hC
  have hi := Complex.reCLM.integrable_comp (integrableOn_weighted_thetaPairWigner hn hm ha0 ha1 b)
  simp only [Complex.reCLM_apply, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, mul_zero, add_zero, sub_zero] at hi
  exact integral_apertureWeight_mul_tail ha0 hg hi

/-- The ordered-pair Schwartz transform is the literal aperture-weighted Wigner integral. -/
theorem fourier_thetaPairApertureSchwartz_eq_Wigner {n m : ℕ}
    (hn : 0 < n) (hm : 0 < m) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (ξ : ℝ) :
    𝓕 (thetaPairApertureSchwartz n m hn hm a ha0 ha1 : ℝ → ℂ) ξ =
      ∫ s in Ioi (0 : ℝ), (s * Real.sinh (a * s) : ℂ) *
        thetaCuspSourcePairWigner n m (s / 2) (-Real.pi * ξ) := by
  let q : ℝ := Real.pi * n * m
  let δ : ℝ := (Real.log n - Real.log m) / 2
  let C : ℂ := ((4 * q ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
  let f := apertureRadialSchwartz a q ha0 ha1 (thetaPair_radialScale_ge_two hn hm)
  have hq : 2 ≤ q := thetaPair_radialScale_ge_two hn hm
  have hq0 : 0 < q := by linarith only [hq]
  have hf : (thetaPairApertureSchwartz n m hn hm a ha0 ha1 : ℝ → ℂ) =
      fun t : ℝ => C * f (t + δ) := by
    funext t
    change C * f (t - -δ) = C * f (t + δ)
    rw [sub_neg_eq_add]
  have hconst : 𝓕 (thetaPairApertureSchwartz n m hn hm a ha0 ha1 : ℝ → ℂ) ξ =
      C * 𝓕 (fun t : ℝ => f (t + δ)) ξ := by
    rw [hf]
    simp only [Real.fourier_eq', smul_eq_mul]
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with t
    ring
  have hphase : Complex.exp ((2 * Real.pi * δ * ξ : ℝ) * I) =
      thetaCuspWignerDivisorRatioPhase n m (-Real.pi * ξ) := by
    unfold thetaCuspWignerDivisorRatioPhase
    congr 1
    dsimp only [δ]
    push_cast
    ring
  rw [hconst, HTGeometry.fourierIntegral_comp_add_right, hphase, smul_eq_mul,
    fourier_apertureRadialSchwartz_eq_integral ha0 ha1 hq,
    integral_Ioi_expScale hq0, ← integral_const_mul, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro s _
  dsimp only
  rw [thetaPairWigner_eq_radialFourier hn hm, aperture_weight_exp a hq0]
  simp only [Complex.real_smul, C, q]
  push_cast
  ring

/-- Exact real Fourier spectrum of one aperture-weighted ordered pair. -/
theorem fourier_thetaPairApertureSchwartz_re {n m : ℕ}
    (hn : 0 < n) (hm : 0 < m) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (ξ : ℝ) :
    (𝓕 (thetaPairApertureSchwartz n m hn hm a ha0 ha1 : ℝ → ℂ) ξ).re =
      thetaPairApertureSpectrum n m a (-Real.pi * ξ) := by
  rw [fourier_thetaPairApertureSchwartz_eq_Wigner hn hm ha0 ha1,
    thetaPairApertureSpectrum_eq_weighted_Wigner hn hm ha0 ha1]
  have he := Complex.reCLM.integral_comp_comm
    (integrableOn_weighted_thetaPairWigner hn hm ha0 ha1 (-Real.pi * ξ))
  simp only [Complex.reCLM_apply, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, mul_zero, add_zero, sub_zero] at he
  exact he.symm

#print axioms thetaPairWigner_eq_radialFourier
#print axioms thetaPairApertureSpectrum_eq_weighted_Wigner
#print axioms fourier_thetaPairApertureSchwartz_re

end
end GaloisForLFunctions.CompletedArithmeticForms
