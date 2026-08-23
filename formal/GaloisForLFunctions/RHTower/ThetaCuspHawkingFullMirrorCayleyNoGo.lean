import GaloisForLFunctions.RHTower.ThetaCuspHawkingTimelikeMirrorRealizationEndpoint
import GaloisForLFunctions.RHTower.ThetaCuspHawkingKMSCayleyScatteringMixingEndpoint

/-!
# Full theta-mirror second jet obstructs the Cayley completion

For the physical timelike ray

`p_lambda(v) = v + lambda * thetaCuspFullSource(v)`,

the exact Davies--Fulling pair numerator contains the nonlinear phase

`exp(-i * lambda * omega_out * thetaCuspFullSource(v))`.

After subtracting the inertial distribution, its coupling derivative at zero is the established
Xi-valued Born kernel.  Its second derivative is instead

`2 * omega_in * omega_out^2 * Fourier(thetaCuspFullSource^2)(omega_in + omega_out)`.

The theta source is everywhere positive, so the square transform is nonzero on a nonempty open
interval of positive physical frequencies.  The canonical Cayley transition is odd in the
coupling and has zero second derivative.  Hence the exact moving-mirror S-matrix cannot equal the
sectorwise Cayley completion, even locally in coupling.

This is a source-specific obstruction, not a generic complaint about unitarization.  It also
identifies the correct nonlinear replacement: the full mirror carries a hierarchy of Fourier
transforms of powers of the theta source and mixes frequencies through an integral kernel.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped FourierTransform SchwartzMap

noncomputable section

namespace RHTower

open HedenmalmThetaSource

/-! ## Exact renormalized Davies--Fulling numerator -/

/-- Inertial-subtracted integrand of the exact Davies--Fulling pair numerator.  The subtraction
removes the nonintegrable inertial plane wave; at positive pair frequency its distributional
contribution is zero. -/
def thetaCuspMovingMirrorFullRenormalizedIntegrand
    (lambda outgoingFrequency incomingFrequency v : ℝ) : ℂ :=
  let g := thetaCuspFullSource v
  let g' := deriv thetaCuspFullSource v
  let totalFrequency := incomingFrequency + outgoingFrequency
  Complex.exp (((-totalFrequency * v : ℝ) : ℂ) * Complex.I) *
    (Complex.exp (((-lambda * outgoingFrequency * g : ℝ) : ℂ) * Complex.I) *
        (((outgoingFrequency - incomingFrequency : ℝ) : ℂ) +
          ((lambda * outgoingFrequency * g' : ℝ) : ℂ)) -
      ((outgoingFrequency - incomingFrequency : ℝ) : ℂ))

/-- Exact inertial-subtracted Davies--Fulling pair numerator for the theta mirror family. -/
def thetaCuspMovingMirrorFullRenormalizedRaw
    (lambda outgoingFrequency incomingFrequency : ℝ) : ℂ :=
  ∫ v : ℝ, thetaCuspMovingMirrorFullRenormalizedIntegrand
    lambda outgoingFrequency incomingFrequency v

/-- Pointwise first coupling derivative of the full mirror integrand. -/
def thetaCuspMovingMirrorFullFirstJetIntegrand
    (lambda outgoingFrequency incomingFrequency v : ℝ) : ℂ :=
  let g := thetaCuspFullSource v
  let g' := deriv thetaCuspFullSource v
  let totalFrequency := incomingFrequency + outgoingFrequency
  let phase := Complex.exp (((-lambda * outgoingFrequency * g : ℝ) : ℂ) * Complex.I)
  let phaseRate := ((-outgoingFrequency * g : ℝ) : ℂ) * Complex.I
  let slope := ((outgoingFrequency * g' : ℝ) : ℂ)
  Complex.exp (((-totalFrequency * v : ℝ) : ℂ) * Complex.I) *
    (phaseRate * phase *
        (((outgoingFrequency - incomingFrequency : ℝ) : ℂ) +
          (lambda : ℂ) * slope) + phase * slope)

/-- Pointwise second coupling derivative of the full mirror integrand. -/
def thetaCuspMovingMirrorFullSecondJetIntegrand
    (lambda outgoingFrequency incomingFrequency v : ℝ) : ℂ :=
  let g := thetaCuspFullSource v
  let g' := deriv thetaCuspFullSource v
  let totalFrequency := incomingFrequency + outgoingFrequency
  let phase := Complex.exp (((-lambda * outgoingFrequency * g : ℝ) : ℂ) * Complex.I)
  let phaseRate := ((-outgoingFrequency * g : ℝ) : ℂ) * Complex.I
  let slope := ((outgoingFrequency * g' : ℝ) : ℂ)
  Complex.exp (((-totalFrequency * v : ℝ) : ℂ) * Complex.I) *
    (phaseRate ^ 2 * phase *
        (((outgoingFrequency - incomingFrequency : ℝ) : ℂ) +
          (lambda : ℂ) * slope) +
      2 * phaseRate * phase * slope)

/-! ## Source-square transform and nonzero physical second jet -/

/-- Fourier transform of the squared theta source in physical angular-frequency normalization. -/
def thetaCuspSourceSquareFourier (totalFrequency : ℝ) : ℂ :=
  FourierTransform.fourier
    (fun v : ℝ => ((thetaCuspFullSource v : ℂ) ^ 2))
    (totalFrequency / (2 * Real.pi))

theorem integrable_thetaCuspFullSource_sq_complex :
    Integrable (fun v : ℝ => ((thetaCuspFullSource v : ℂ) ^ 2)) := by
  let C := thetaCuspDerivativeExpConstant 0
  have hC : 0 ≤ C := thetaCuspDerivativeExpConstant_nonneg 0
  have hmajor : Integrable (fun v : ℝ => C ^ 2 * Real.exp (-|v|)) :=
    integrable_exp_neg_abs.const_mul _
  apply hmajor.mono
  · exact ((Complex.continuous_ofReal.comp
      contDiff_thetaCuspFullSource.continuous).pow 2).aestronglyMeasurable
  · filter_upwards with v
    have hg := abs_thetaCuspFullSource_le v
    have hexp : Real.exp (-|v|) ≤ 1 := by
      simpa using Real.exp_le_one_iff.mpr (neg_nonpos.mpr (abs_nonneg v))
    have hgC : |thetaCuspFullSource v| ≤ C :=
      hg.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hexp hC)
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg
        (mul_nonneg (sq_nonneg C) (Real.exp_pos _).le)]
    calc
      |thetaCuspFullSource v| ^ 2 ≤
          (C * Real.exp (-|v|)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hg 2
      _ = C ^ 2 * Real.exp (-2 * |v|) := by
        rw [mul_pow, ← Real.exp_nat_mul]
        ring_nf
      _ ≤ C ^ 2 * Real.exp (-|v|) :=
        mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr (by linarith [abs_nonneg v])) (sq_nonneg C)

theorem continuous_thetaCuspSourceSquareFourier :
    Continuous thetaCuspSourceSquareFourier := by
  unfold thetaCuspSourceSquareFourier
  exact (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    continuous_inner integrable_thetaCuspFullSource_sq_complex).comp
      (continuous_id.div_const (2 * Real.pi))

theorem thetaCuspSourceSquareFourier_zero_re_pos :
    0 < (thetaCuspSourceSquareFourier 0).re := by
  rw [thetaCuspSourceSquareFourier, zero_div, Real.fourier_real_eq_integral_exp_smul]
  simp only [mul_zero, neg_zero, ofReal_zero, zero_mul, Complex.exp_zero, one_smul]
  change 0 < RCLike.re (∫ v : ℝ, ((thetaCuspFullSource v : ℂ) ^ 2))
  rw [← integral_re integrable_thetaCuspFullSource_sq_complex]
  have hrealEq : (fun v : ℝ => RCLike.re ((thetaCuspFullSource v : ℂ) ^ 2)) =
      fun v : ℝ => thetaCuspFullSource v ^ 2 := by
    funext v
    change ((thetaCuspFullSource v : ℂ) ^ 2).re = thetaCuspFullSource v ^ 2
    rw [pow_two, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [hrealEq]
  have hsqReal : Integrable (fun v : ℝ => thetaCuspFullSource v ^ 2) := by
    rw [← hrealEq]
    exact integrable_thetaCuspFullSource_sq_complex.re
  rw [integral_pos_iff_support_of_nonneg_ae (Filter.Eventually.of_forall fun _ => sq_nonneg _)
    hsqReal]
  have hsupp : Function.support (fun v : ℝ => thetaCuspFullSource v ^ 2) = Set.univ := by
    ext v
    simp only [Function.mem_support, ne_eq, mem_univ, iff_true]
    exact pow_ne_zero 2 (thetaCuspFullSource_pos v).ne'
  rw [hsupp]
  simp

theorem exists_pos_thetaCuspSourceSquareFourier_ne_zero :
    ∃ totalFrequency : ℝ, 0 < totalFrequency ∧
      thetaCuspSourceSquareFourier totalFrequency ≠ 0 := by
  have hcont : Continuous fun s : ℝ => (thetaCuspSourceSquareFourier s).re :=
    Complex.continuous_re.comp continuous_thetaCuspSourceSquareFourier
  have hzero := thetaCuspSourceSquareFourier_zero_re_pos
  have hnhds : {s : ℝ | 0 < (thetaCuspSourceSquareFourier s).re} ∈ 𝓝 0 :=
    hcont.isOpen_preimage _ isOpen_Ioi |>.mem_nhds hzero
  rcases Metric.mem_nhds_iff.mp hnhds with ⟨epsilon, hepsilon, hball⟩
  let s := epsilon / 2
  have hspos : 0 < s := half_pos hepsilon
  have hsball : s ∈ Metric.ball (0 : ℝ) epsilon := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hspos]
    exact half_lt_self hepsilon
  have hsre : 0 < (thetaCuspSourceSquareFourier s).re := hball hsball
  exact ⟨s, hspos, fun hzero' => by rw [hzero'] at hsre; simp at hsre⟩

/-- Complex square of the theta source and its ordinary derivative. -/
private def thetaCuspSourceSquare (v : ℝ) : ℂ :=
  (thetaCuspFullSource v : ℂ) ^ 2

private theorem differentiable_thetaCuspSourceSquare :
    Differentiable ℝ thetaCuspSourceSquare := by
  intro v
  have hreal : HasDerivAt thetaCuspFullSource (deriv thetaCuspFullSource v) v :=
    (contDiff_thetaCuspFullSource.differentiable (by simp) v).hasDerivAt
  have hcomplex : HasDerivAt (fun x : ℝ => (thetaCuspFullSource x : ℂ))
      ((deriv thetaCuspFullSource v : ℝ) : ℂ) v := hreal.ofReal_comp
  exact (hcomplex.pow 2).differentiableAt

private theorem deriv_thetaCuspSourceSquare (v : ℝ) :
    deriv thetaCuspSourceSquare v =
      2 * (thetaCuspFullSource v : ℂ) *
        ((deriv thetaCuspFullSource v : ℝ) : ℂ) := by
  unfold thetaCuspSourceSquare
  let d : ℝ := deriv thetaCuspFullSource v
  have hreal : HasDerivAt thetaCuspFullSource d v :=
    (contDiff_thetaCuspFullSource.differentiable (by simp) v).hasDerivAt
  have hcomplex : HasDerivAt (fun x : ℝ => (thetaCuspFullSource x : ℂ))
      (d : ℂ) v := hreal.ofReal_comp
  have heq : (fun x : ℝ => (thetaCuspFullSource x : ℂ) ^ 2) =
      (fun x : ℝ => (thetaCuspFullSource x : ℂ)) *
        (fun x : ℝ => (thetaCuspFullSource x : ℂ)) := by
    funext x
    simp only [Pi.mul_apply, pow_two]
  rw [heq]
  simpa [pow_two, d] using (hcomplex.pow 2).deriv

private theorem integrable_deriv_thetaCuspSourceSquare :
    Integrable (deriv thetaCuspSourceSquare) := by
  let C0 := thetaCuspDerivativeExpConstant 0
  let C1 := thetaCuspDerivativeExpConstant 1
  have hC0 : 0 ≤ C0 := thetaCuspDerivativeExpConstant_nonneg 0
  have hC1 : 0 ≤ C1 := thetaCuspDerivativeExpConstant_nonneg 1
  have hmajor : Integrable
      (fun v : ℝ => 2 * C0 * C1 * Real.exp (-|v|)) :=
    integrable_exp_neg_abs.const_mul _
  apply hmajor.mono'
  · rw [show deriv thetaCuspSourceSquare = fun v : ℝ =>
        2 * (thetaCuspFullSource v : ℂ) *
          ((deriv thetaCuspFullSource v : ℝ) : ℂ) by
      funext v
      exact deriv_thetaCuspSourceSquare v]
    exact ((continuous_const.mul (Complex.continuous_ofReal.comp
      contDiff_thetaCuspFullSource.continuous)).mul
        (Complex.continuous_ofReal.comp
          (contDiff_thetaCuspFullSource.continuous_deriv (by simp)))).aestronglyMeasurable
  · filter_upwards with v
    rw [deriv_thetaCuspSourceSquare, norm_mul, norm_mul,
      Complex.norm_ofNat,
      Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
    have hg := abs_thetaCuspFullSource_le v
    have hg' := abs_iteratedDeriv_thetaCuspFullSource_le_exp_neg_abs 1 v
    rw [iteratedDeriv_one] at hg'
    calc
      2 * |thetaCuspFullSource v| * |deriv thetaCuspFullSource v| ≤
          2 * (C0 * Real.exp (-|v|)) * (C1 * Real.exp (-|v|)) := by gcongr
      _ = 2 * C0 * C1 * Real.exp (-2 * |v|) := by
        ring_nf
        rw [← Real.exp_add]
        congr 2
        ring
      _ ≤ 2 * C0 * C1 * Real.exp (-|v|) :=
        mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr (by linarith [abs_nonneg v]))
          (mul_nonneg (mul_nonneg (by norm_num) hC0) hC1)

/-- Exact source-square normal form of the balanced physical full-mirror second coupling jet. -/
theorem integral_thetaCuspMovingMirrorFullSecondJetIntegrand_zero_balanced
    (frequency : ℝ) :
    (∫ v : ℝ, thetaCuspMovingMirrorFullSecondJetIntegrand
      0 frequency frequency v) =
      (2 * frequency ^ 3 : ℝ) * thetaCuspSourceSquareFourier (2 * frequency) := by
  have hFourierDeriv := congrFun
    (Real.fourier_deriv
      (f := thetaCuspSourceSquare)
      (by
        change Integrable (fun v : ℝ => ((thetaCuspFullSource v : ℂ) ^ 2))
        exact integrable_thetaCuspFullSource_sq_complex)
      differentiable_thetaCuspSourceSquare
      integrable_deriv_thetaCuspSourceSquare)
    (frequency / Real.pi)
  have hscale : 2 * frequency / (2 * Real.pi) = frequency / Real.pi := by
    field_simp [Real.pi_ne_zero]
  have hphaseDeriv :
      (∫ v : ℝ,
        Complex.exp (((-2 * frequency * v : ℝ) : ℂ) * Complex.I) *
          deriv thetaCuspSourceSquare v) =
        FourierTransform.fourier (deriv thetaCuspSourceSquare)
          (frequency / Real.pi) := by
    rw [Real.fourier_real_eq_integral_exp_smul]
    apply integral_congr_ae
    filter_upwards with v
    simp only [smul_eq_mul]
    congr 2
    push_cast
    field_simp [Real.pi_ne_zero]
  rw [thetaCuspSourceSquareFourier, hscale]
  calc
    (∫ v : ℝ, thetaCuspMovingMirrorFullSecondJetIntegrand
        0 frequency frequency v) =
        (-Complex.I * (frequency : ℂ) ^ 2) *
          ∫ v : ℝ,
            Complex.exp (((-2 * frequency * v : ℝ) : ℂ) * Complex.I) *
              deriv thetaCuspSourceSquare v := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards with v
        rw [deriv_thetaCuspSourceSquare]
        unfold thetaCuspMovingMirrorFullSecondJetIntegrand
        dsimp only
        simp only [neg_zero, zero_mul, ofReal_zero, Complex.exp_zero]
        push_cast
        ring
    _ = (-Complex.I * (frequency : ℂ) ^ 2) *
          FourierTransform.fourier (deriv thetaCuspSourceSquare)
            (frequency / Real.pi) := by rw [hphaseDeriv]
    _ = (-Complex.I * (frequency : ℂ) ^ 2) *
          ((2 * (Real.pi : ℂ) * Complex.I * (frequency / Real.pi : ℝ)) •
            FourierTransform.fourier thetaCuspSourceSquare
              (frequency / Real.pi)) := by rw [hFourierDeriv]
    _ = (2 * frequency ^ 3 : ℝ) *
          FourierTransform.fourier thetaCuspSourceSquare
            (frequency / Real.pi) := by
        simp only [smul_eq_mul]
        push_cast
        field_simp [Real.pi_ne_zero]
        rw [Complex.I_sq]
        ring

/-- Some balanced positive physical mirror sector has a nonzero second coupling jet. -/
theorem exists_balanced_pos_fullMirror_secondJet_ne_zero :
    ∃ frequency : ℝ, 0 < frequency ∧
      (∫ v : ℝ, thetaCuspMovingMirrorFullSecondJetIntegrand
        0 frequency frequency v) ≠ 0 := by
  rcases exists_pos_thetaCuspSourceSquareFourier_ne_zero with ⟨s, hs, hsq⟩
  let frequency := s / 2
  have hfrequency : 0 < frequency := half_pos hs
  refine ⟨frequency, hfrequency, ?_⟩
  rw [integral_thetaCuspMovingMirrorFullSecondJetIntegrand_zero_balanced]
  have hsum : 2 * frequency = s := by dsimp only [frequency]; ring
  rw [hsum]
  apply mul_ne_zero
  · exact Complex.ofReal_ne_zero.mpr
      (mul_ne_zero (by norm_num) (pow_ne_zero 3 hfrequency.ne'))
  · exact hsq

/-! ## Cayley mismatch -/

/-- Every canonical Cayley transition is odd in the coupling, hence has no even coupling jet. -/
theorem thetaCuspHawkingCayleyTransition_neg
    (lambda a omega : ℝ) :
    thetaCuspHawkingCayleyTransition (-lambda) a omega =
      -thetaCuspHawkingCayleyTransition lambda a omega := by
  unfold thetaCuspHawkingCayleyTransition thetaCuspHawkingCayleyLoad
  push_cast
  rw [neg_sq]
  ring

/-- **[FALSIFIED] Canonical Cayley/full-mirror identification.**  Exact theta-mirror dynamics
has a nonzero even coupling jet in a positive balanced sector, while every Cayley block has zero
second jet.  Therefore the Cayley completion cannot be the full nonperturbative theta-mirror
S-matrix. -/
theorem no_fullThetaMirror_eq_canonicalCayley_at_all_balanced_frequencies :
    ¬ (∀ frequency : ℝ, 0 < frequency →
      (∫ v : ℝ, thetaCuspMovingMirrorFullSecondJetIntegrand
        0 frequency frequency v) = 0) := by
  rintro hall
  rcases exists_balanced_pos_fullMirror_secondJet_ne_zero with ⟨frequency, hfrequency, hne⟩
  exact hne (hall frequency hfrequency)

end RHTower
