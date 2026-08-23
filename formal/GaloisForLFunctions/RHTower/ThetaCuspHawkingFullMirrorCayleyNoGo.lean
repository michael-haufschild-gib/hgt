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

theorem hasDerivAt_thetaCuspMovingMirrorFullRenormalizedIntegrand
    (lambda outgoingFrequency incomingFrequency v : ℝ) :
    HasDerivAt
      (fun q : ℝ => thetaCuspMovingMirrorFullRenormalizedIntegrand
        q outgoingFrequency incomingFrequency v)
      (thetaCuspMovingMirrorFullFirstJetIntegrand
        lambda outgoingFrequency incomingFrequency v) lambda := by
  unfold thetaCuspMovingMirrorFullRenormalizedIntegrand
    thetaCuspMovingMirrorFullFirstJetIntegrand
  dsimp only
  have hlin : HasDerivAt
      (fun q : ℝ => (((-q * outgoingFrequency * thetaCuspFullSource v : ℝ) : ℂ) * I))
      (((-outgoingFrequency * thetaCuspFullSource v : ℝ) : ℂ) * I) lambda := by
    convert (((hasDerivAt_id lambda).neg.mul_const outgoingFrequency).mul_const
      (thetaCuspFullSource v)).ofReal_comp.const_mul I using 1 <;> ring
  have hphase := hlin.cexp
  have hslope : HasDerivAt
      (fun q : ℝ => (((q * outgoingFrequency * deriv thetaCuspFullSource v : ℝ) : ℂ)))
      (((outgoingFrequency * deriv thetaCuspFullSource v : ℝ) : ℂ)) lambda := by
    convert (((hasDerivAt_id lambda).mul_const outgoingFrequency).mul_const
      (deriv thetaCuspFullSource v)).ofReal_comp using 1 <;> ring
  convert ((hphase.mul ((hasDerivAt_const lambda
      ((outgoingFrequency - incomingFrequency : ℝ) : ℂ)).add hslope)).sub_const
        ((outgoingFrequency - incomingFrequency : ℝ) : ℂ)).const_mul
          (Complex.exp (((-(incomingFrequency + outgoingFrequency) * v : ℝ) : ℂ) * I))
    using 1 <;> ring

theorem hasDerivAt_thetaCuspMovingMirrorFullFirstJetIntegrand
    (lambda outgoingFrequency incomingFrequency v : ℝ) :
    HasDerivAt
      (fun q : ℝ => thetaCuspMovingMirrorFullFirstJetIntegrand
        q outgoingFrequency incomingFrequency v)
      (thetaCuspMovingMirrorFullSecondJetIntegrand
        lambda outgoingFrequency incomingFrequency v) lambda := by
  unfold thetaCuspMovingMirrorFullFirstJetIntegrand
    thetaCuspMovingMirrorFullSecondJetIntegrand
  dsimp only
  let rate : ℂ := ((-outgoingFrequency * thetaCuspFullSource v : ℝ) : ℂ) * I
  let slope : ℂ := ((outgoingFrequency * deriv thetaCuspFullSource v : ℝ) : ℂ)
  have hlin : HasDerivAt
      (fun q : ℝ => (((-q * outgoingFrequency * thetaCuspFullSource v : ℝ) : ℂ) * I))
      rate lambda := by
    dsimp only [rate]
    convert (((hasDerivAt_id lambda).neg.mul_const outgoingFrequency).mul_const
      (thetaCuspFullSource v)).ofReal_comp.const_mul I using 1 <;> ring
  have hphase := hlin.cexp
  have hslope : HasDerivAt
      (fun q : ℝ => (((outgoingFrequency - incomingFrequency : ℝ) : ℂ) +
        (q : ℂ) * slope)) slope lambda := by
    convert (hasDerivAt_const lambda
      ((outgoingFrequency - incomingFrequency : ℝ) : ℂ)).add
        ((hasDerivAt_id lambda).ofReal_comp.const_mul slope) using 1 <;> ring
  convert (((hphase.const_mul rate).mul hslope).add
      (hphase.const_mul slope)).const_mul
        (Complex.exp (((-(incomingFrequency + outgoingFrequency) * v : ℝ) : ℂ) * I))
    using 1 <;> dsimp only [rate, slope] <;> ring

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
  · exact (contDiff_thetaCuspFullSource.continuous.ofReal.pow 2).aestronglyMeasurable
  · filter_upwards with v
    have hg := abs_thetaCuspFullSource_le v
    have hexp : Real.exp (-|v|) ≤ 1 := by
      simpa using Real.exp_le_one_iff.mpr (neg_nonpos.mpr (abs_nonneg v))
    have hgC : |thetaCuspFullSource v| ≤ C :=
      hg.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hexp hC)
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs]
    calc
      |thetaCuspFullSource v| ^ 2 ≤
          (C * Real.exp (-|v|)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hg 2
      _ = C ^ 2 * Real.exp (-2 * |v|) := by
        rw [mul_pow, ← Real.exp_nat_mul]
        ring_nf
      _ ≤ C ^ 2 * Real.exp (-|v|) := by
        gcongr
        exact Real.exp_le_exp.mpr (by linarith [abs_nonneg v])

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
  rw [Complex.integral_re]
  simp only [map_pow, ofReal_re]
  have hsqReal : Integrable (fun v : ℝ => thetaCuspFullSource v ^ 2) := by
    simpa only [Complex.ofReal_pow] using integrable_thetaCuspFullSource_sq_complex.re
  rw [integral_pos_iff_support_of_nonneg_ae (Filter.Eventually.of_forall fun _ => sq_nonneg _)
    hsqReal]
  have hsupp : Function.support (fun v : ℝ => thetaCuspFullSource v ^ 2) = Set.univ := by
    ext v
    simp only [Function.mem_support, ne_eq, mem_univ, iff_true]
    exact pow_ne_zero 2 (thetaCuspFullSource_pos v).ne'
  rw [hsupp, MeasureTheory.measure_univ]
  exact MeasureTheory.volume_real_pos

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

/-- Exact source-square normal form of the physical full-mirror second coupling jet. -/
theorem integral_thetaCuspMovingMirrorFullSecondJetIntegrand_zero
    (outgoingFrequency incomingFrequency : ℝ) :
    (∫ v : ℝ, thetaCuspMovingMirrorFullSecondJetIntegrand
      0 outgoingFrequency incomingFrequency v) =
      (2 * incomingFrequency * outgoingFrequency ^ 2 : ℝ) *
        thetaCuspSourceSquareFourier (incomingFrequency + outgoingFrequency) := by
  rw [thetaCuspSourceSquareFourier, Real.fourier_real_eq_integral_exp_smul]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with v
  unfold thetaCuspMovingMirrorFullSecondJetIntegrand
  dsimp only
  simp only [zero_mul, ofReal_zero, Complex.exp_zero, zero_smul]
  push_cast
  congr 1
  · congr 1
    field_simp [Real.pi_ne_zero]
    ring
  · ring

/-- Some balanced positive physical mirror sector has a nonzero second coupling jet. -/
theorem exists_balanced_pos_fullMirror_secondJet_ne_zero :
    ∃ frequency : ℝ, 0 < frequency ∧
      (∫ v : ℝ, thetaCuspMovingMirrorFullSecondJetIntegrand
        0 frequency frequency v) ≠ 0 := by
  rcases exists_pos_thetaCuspSourceSquareFourier_ne_zero with ⟨s, hs, hsq⟩
  let frequency := s / 2
  have hfrequency : 0 < frequency := half_pos hs
  refine ⟨frequency, hfrequency, ?_⟩
  rw [integral_thetaCuspMovingMirrorFullSecondJetIntegrand_zero]
  have hsum : frequency + frequency = s := by dsimp only [frequency]; ring
  rw [hsum]
  exact mul_ne_zero (by positivity) hsq

/-! ## Cayley mismatch -/

theorem hasDerivAt_thetaCuspHawkingCayleyTransition_zero
    (a omega : ℝ) :
    HasDerivAt (fun lambda : ℝ => thetaCuspHawkingCayleyTransition lambda a omega)
      (thetaCuspHawkingFriedrichsShellFormFactor a omega) 0 := by
  unfold thetaCuspHawkingCayleyTransition thetaCuspHawkingCayleyLoad
  convert (((hasDerivAt_id 0).ofReal_comp.mul_const
      (thetaCuspHawkingFriedrichsShellFormFactor a omega)).div
        ((hasDerivAt_const 0 (1 : ℂ)).add
          ((((hasDerivAt_id 0).pow 2).mul_const
            (Complex.normSq (thetaCuspHawkingFriedrichsShellFormFactor a omega))).div_const 4).ofReal_comp)
        (by norm_num)) using 1 <;> norm_num

theorem hasDerivAt_deriv_thetaCuspHawkingCayleyTransition_zero
    (a omega : ℝ) :
    HasDerivAt
      (fun lambda : ℝ => deriv
        (fun q : ℝ => thetaCuspHawkingCayleyTransition q a omega) lambda)
      0 0 := by
  have hnear : ∀ lambda : ℝ,
      HasDerivAt (fun q : ℝ => thetaCuspHawkingCayleyTransition q a omega)
        (((1 - thetaCuspHawkingCayleyLoad lambda a omega) /
          (1 + thetaCuspHawkingCayleyLoad lambda a omega) ^ 2 : ℝ) : ℂ) *
          thetaCuspHawkingFriedrichsShellFormFactor a omega lambda := by
    intro lambda
    unfold thetaCuspHawkingCayleyTransition thetaCuspHawkingCayleyLoad
    have hdenR : (1 + lambda ^ 2 *
        Complex.normSq (thetaCuspHawkingFriedrichsShellFormFactor a omega) / 4) ≠ 0 := by
      positivity
    convert (((hasDerivAt_id lambda).ofReal_comp.mul_const
      (thetaCuspHawkingFriedrichsShellFormFactor a omega)).div
        ((hasDerivAt_const lambda (1 : ℂ)).add
          ((((hasDerivAt_id lambda).pow 2).mul_const
            (Complex.normSq (thetaCuspHawkingFriedrichsShellFormFactor a omega))).div_const 4).ofReal_comp)
        (by exact_mod_cast hdenR)) using 1 <;> field_simp [hdenR] <;> ring
  have hderivEq : (fun lambda : ℝ => deriv
      (fun q : ℝ => thetaCuspHawkingCayleyTransition q a omega) lambda) =
      fun lambda : ℝ =>
        (((1 - thetaCuspHawkingCayleyLoad lambda a omega) /
          (1 + thetaCuspHawkingCayleyLoad lambda a omega) ^ 2 : ℝ) : ℂ) *
          thetaCuspHawkingFriedrichsShellFormFactor a omega := by
    funext lambda
    exact (hnear lambda).deriv
  rw [hderivEq]
  convert (hasDerivAt_const (0 : ℝ)
      (thetaCuspHawkingFriedrichsShellFormFactor a omega)).mul
    (((((hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub
      ((((hasDerivAt_id (0 : ℝ)).pow 2).mul_const
        (Complex.normSq (thetaCuspHawkingFriedrichsShellFormFactor a omega))).div_const 4)).mul
      (((hasDerivAt_const (0 : ℝ) (1 : ℝ)).add
        ((((hasDerivAt_id (0 : ℝ)).pow 2).mul_const
          (Complex.normSq (thetaCuspHawkingFriedrichsShellFormFactor a omega))).div_const 4)).pow 2).inv₀
        (by norm_num)).ofReal_comp) using 1 <;>
    simp [thetaCuspHawkingCayleyLoad]

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
