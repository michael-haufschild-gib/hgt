import GaloisForLFunctions.RHTower.CCM.CCMRationalArchimedeanSchwartzPoisson
import GaloisForLFunctions.HTGeometry.SchwartzPolynomialDifferentialFrame
import GaloisForLFunctions.HTGeometry.SchwartzCompactDiagonalFunctional
import GaloisForLFunctions.HTGeometry.SchwartzCompactPositiveFunctional
import Mathlib.Analysis.Fourier.Inversion

/-!
# Infinite local agreement with opposite quantum recurrence

A compactly supported Schwartz packet is autocorrelated inside one quarter of
a lattice cell.  Its Fourier transform is a nonnegative continuous energy
density; its integer samples are nonnegative lattice weights.  Poisson
summation makes the normalized continuous and lattice survival amplitudes
identical on an open interval.  At one full lattice period, the lattice
amplitude is one while the continuous amplitude is zero.
-/

open scoped BigOperators FourierTransform SchwartzMap Convolution Pointwise
open MeasureTheory Set Complex

noncomputable section

namespace RHTower.InfiniteLocal

/-- Explicit nonzero Schwartz packet supported inside `[-1/8,1/8]`. -/
def packet : SchwartzMap ℝ ℂ :=
  GaloisForLFunctions.RHTower.ccmRationalArchimedeanDilation
    (SchwartzMap.compactIntervalCutoff 0) 16 (by norm_num)

@[simp] theorem packet_apply (x : ℝ) :
    packet x = SchwartzMap.compactIntervalCutoff 0 (16 * x) :=
  GaloisForLFunctions.RHTower.ccmRationalArchimedeanDilation_apply
    (SchwartzMap.compactIntervalCutoff 0) 16 (by norm_num) x

@[simp] theorem packet_zero : packet 0 = 1 := by
  rw [packet_apply]
  norm_num

theorem packet_eq_zero_of_one_eighth_lt_abs
    {x : ℝ} (hx : (1 : ℝ) / 8 < |x|) :
    packet x = 0 := by
  rw [packet_apply]
  apply image_eq_zero_of_notMem_tsupport
  rw [SchwartzMap.compactIntervalCutoff_tsupport]
  simp only [Set.mem_setOf_eq, abs_zero, zero_add, not_le]
  rw [abs_mul]
  norm_num
  linarith

theorem packet_support_subset :
    Function.support packet ⊆ {x : ℝ | |x| ≤ (1 : ℝ) / 8} := by
  intro x hx
  simp only [Function.mem_support, Set.mem_setOf_eq] at hx ⊢
  by_contra hnot
  exact hx (packet_eq_zero_of_one_eighth_lt_abs (lt_of_not_ge hnot))

theorem packet_hasCompactSupport : HasCompactSupport packet := by
  apply HasCompactSupport.of_support_subset_isCompact
    (K := Set.Icc (-((1 : ℝ) / 8)) ((1 : ℝ) / 8)) isCompact_Icc
  intro x hx
  have habs := packet_support_subset hx
  exact (abs_le.mp habs)

/-- Compactly supported positive-definite local amplitude. -/
def localAmplitude : SchwartzMap ℝ ℂ :=
  SchwartzMap.autocorrelationSchwartz packet

theorem conjugateReflection_packet_support_subset :
    Function.support (SchwartzMap.conjugateReflection packet) ⊆
      {x : ℝ | |x| ≤ (1 : ℝ) / 8} := by
  intro x hx
  have hneg : -x ∈ Function.support packet := by
    simp only [Function.mem_support] at hx ⊢
    simpa [SchwartzMap.conjugateReflection] using hx
  simpa only [Set.mem_setOf_eq, abs_neg] using packet_support_subset hneg

theorem localAmplitude_support_subset :
    Function.support localAmplitude ⊆
      {t : ℝ | |t| ≤ (1 : ℝ) / 4} := by
  intro t ht
  have hconv :
      t ∈ Function.support (SchwartzMap.conjugateReflection packet) +
        Function.support packet := by
    have ht' : t ∈ Function.support (SchwartzMap.autocorrelation packet) := by
      simp only [Function.mem_support] at ht ⊢
      change SchwartzMap.autocorrelationSchwartz packet t ≠ 0 at ht
      rw [SchwartzMap.autocorrelationSchwartz_apply] at ht
      exact ht
    rw [SchwartzMap.autocorrelation] at ht'
    exact
      (MeasureTheory.support_convolution_subset_swap
        (ContinuousLinearMap.mul ℂ ℂ)) ht'
  rw [Set.mem_add] at hconv
  obtain ⟨x, hx, y, hy, hxy⟩ := hconv
  have hx' := conjugateReflection_packet_support_subset hx
  have hy' := packet_support_subset hy
  simp only [Set.mem_setOf_eq] at hx' hy' ⊢
  rw [← hxy]
  calc
    |x + y| ≤ |x| + |y| := abs_add_le _ _
    _ ≤ (1 : ℝ) / 8 + 1 / 8 := add_le_add hx' hy'
    _ = (1 : ℝ) / 4 := by ring

theorem localAmplitude_eq_zero_of_quarter_lt_abs
    {t : ℝ} (ht : (1 : ℝ) / 4 < |t|) :
    localAmplitude t = 0 := by
  rw [← Function.notMem_support]
  intro hmem
  have := localAmplitude_support_subset hmem
  change |t| ≤ (1 : ℝ) / 4 at this
  linarith

/-- Nonnegative continuous energy density dual to the local amplitude. -/
def spectralDensity : SchwartzMap ℝ ℝ :=
  SchwartzMap.pointwiseNormSqReal (𝓕 packet)

@[simp] theorem spectralDensity_apply (x : ℝ) :
    spectralDensity x = Complex.normSq ((𝓕 packet) x) :=
  SchwartzMap.pointwiseNormSqReal_apply _ _

theorem spectralDensity_nonneg (x : ℝ) :
    0 ≤ spectralDensity x := by
  rw [spectralDensity_apply]
  exact Complex.normSq_nonneg _

theorem fourier_localAmplitude_eq_spectralDensity (x : ℝ) :
    (𝓕 localAmplitude) x = (spectralDensity x : ℂ) := by
  rw [localAmplitude, SchwartzMap.fourier_autocorrelationSchwartz,
    spectralDensity_apply, Complex.mul_conj]

/-- Total continuous spectral mass. -/
def spectralMass : ℝ := ∫ x : ℝ, spectralDensity x

theorem localAmplitude_zero_eq_packetNormMass :
    localAmplitude 0 =
      ((∫ x : ℝ, SchwartzMap.pointwiseNormSqReal packet x : ℝ) : ℂ) := by
  rw [localAmplitude, SchwartzMap.autocorrelationSchwartz_apply,
    SchwartzMap.autocorrelation, MeasureTheory.convolution]
  calc
    ∫ t : ℝ, ((ContinuousLinearMap.mul ℂ ℂ) (packet t))
        (SchwartzMap.conjugateReflection packet (0 - t)) =
        ∫ x : ℝ,
          (SchwartzMap.pointwiseNormSqReal packet x : ℂ) := by
      apply integral_congr_ae
      filter_upwards with x
      simp [SchwartzMap.conjugateReflection,
        SchwartzMap.pointwiseNormSqReal_apply, Complex.mul_conj]
    _ = ((∫ x : ℝ,
        SchwartzMap.pointwiseNormSqReal packet x : ℝ) : ℂ) :=
      _root_.integral_ofReal

theorem packetNormMass_pos :
    0 < ∫ x : ℝ, SchwartzMap.pointwiseNormSqReal packet x := by
  let q := SchwartzMap.pointwiseNormSqReal packet
  have hqcont : Continuous fun x : ℝ => q x := q.continuous
  have hqcompact : HasCompactSupport q :=
    SchwartzMap.pointwiseNormSqReal_hasCompactSupport packet
      packet_hasCompactSupport
  have hqnonneg : 0 ≤ fun x : ℝ => q x :=
    fun x => SchwartzMap.pointwiseNormSqReal_nonnegative packet x
  have hqzero : q 0 ≠ 0 := by
    simp [q, SchwartzMap.pointwiseNormSqReal_apply]
  exact hqcont.integral_pos_of_hasCompactSupport_nonneg_nonzero
    hqcompact hqnonneg hqzero

theorem spectralMass_eq_packetNormMass :
    spectralMass =
      ∫ x : ℝ, SchwartzMap.pointwiseNormSqReal packet x := by
  have hinv :=
    congrFun
      (localAmplitude.continuous.fourierInv_fourier_eq
        localAmplitude.integrable (𝓕 localAmplitude).integrable) 0
  rw [Real.fourierInv_eq'] at hinv
  simp only [Real.inner_apply, mul_zero, ofReal_zero, zero_mul,
    Complex.exp_zero, one_smul] at hinv
  have hcomplex :
      (spectralMass : ℂ) =
        ((∫ x : ℝ, SchwartzMap.pointwiseNormSqReal packet x : ℝ) : ℂ) := by
    rw [spectralMass]
    calc
      ((∫ x : ℝ, spectralDensity x : ℝ) : ℂ) =
          ∫ x : ℝ, (spectralDensity x : ℂ) :=
        _root_.integral_ofReal.symm
      _ =
          ∫ x : ℝ, (𝓕 localAmplitude) x := by
        apply integral_congr_ae
        filter_upwards with x
        exact (fourier_localAmplitude_eq_spectralDensity x).symm
      _ = localAmplitude 0 := hinv
      _ = ((∫ x : ℝ,
          SchwartzMap.pointwiseNormSqReal packet x : ℝ) : ℂ) :=
        localAmplitude_zero_eq_packetNormMass
  exact_mod_cast hcomplex

theorem spectralMass_pos : 0 < spectralMass := by
  rw [spectralMass_eq_packetNormMass]
  exact packetNormMass_pos

theorem localAmplitude_zero_eq_spectralMass :
    localAmplitude 0 = (spectralMass : ℂ) := by
  rw [localAmplitude_zero_eq_packetNormMass, spectralMass_eq_packetNormMass]

theorem spectralDensity_lattice_summable :
    Summable (fun n : ℤ => spectralDensity (n : ℝ)) := by
  have h :=
    GaloisForLFunctions.RHTower.ccmRationalArchimedeanSchwartz_lattice_summable
      (SchwartzMap.realToComplexSchwartz spectralDensity)
      (a := 1) one_ne_zero
  simpa only [one_mul, SchwartzMap.realToComplexSchwartz_apply,
    norm_real, Real.norm_eq_abs,
    abs_of_nonneg (spectralDensity_nonneg _)] using h

theorem localAmplitude_int_eq_zero {n : ℤ} (hn : n ≠ 0) :
    localAmplitude (n : ℝ) = 0 := by
  apply localAmplitude_eq_zero_of_quarter_lt_abs
  have h1z : (1 : ℤ) ≤ |n| := Int.one_le_abs hn
  have h1 : (1 : ℝ) ≤ |(n : ℝ)| := by
    exact_mod_cast h1z
  linarith

theorem spectralDensity_lattice_tsum_eq_mass :
    ∑' n : ℤ, spectralDensity (n : ℝ) = spectralMass := by
  have hpoisson := SchwartzMap.tsum_eq_tsum_fourier localAmplitude 0
  have hzero (n : ℤ) :
      fourier n ((0 : ℝ) : UnitAddCircle) = 1 := by
    simpa only [← QuotientAddGroup.mk_zero] using fourier_eval_zero n
  simp_rw [zero_add, hzero, mul_one] at hpoisson
  have hleft :
      (∑' n : ℤ, localAmplitude (n : ℝ)) = localAmplitude 0 := by
    simpa using
      (tsum_eq_single
        (L := SummationFilter.unconditional ℤ)
        (f := fun n : ℤ => localAmplitude (n : ℝ)) 0
        (fun n hn => localAmplitude_int_eq_zero hn))
  have hc :
      (∑' n : ℤ, (spectralDensity (n : ℝ) : ℂ)) =
        (spectralMass : ℂ) := by
    calc
      (∑' n : ℤ, (spectralDensity (n : ℝ) : ℂ)) =
          ∑' n : ℤ, (𝓕 localAmplitude) (n : ℝ) := by
        apply tsum_congr
        intro n
        exact (fourier_localAmplitude_eq_spectralDensity (n : ℝ)).symm
      _ = ∑' n : ℤ, localAmplitude (n : ℝ) := hpoisson.symm
      _ = localAmplitude 0 := hleft
      _ = (spectralMass : ℂ) := localAmplitude_zero_eq_spectralMass
  rw [← Complex.ofReal_tsum] at hc
  exact Complex.ofReal_injective hc

/-- Normalized nonnegative continuous energy density. -/
def continuousDensity (x : ℝ) : ℝ :=
  spectralDensity x / spectralMass

/-- Normalized nonnegative weight on the integer energy lattice. -/
def latticeWeight (n : ℤ) : ℝ :=
  spectralDensity (n : ℝ) / spectralMass

theorem continuousDensity_nonneg (x : ℝ) :
    0 ≤ continuousDensity x :=
  div_nonneg (spectralDensity_nonneg x) spectralMass_pos.le

theorem continuousDensity_integrable :
    Integrable continuousDensity :=
  spectralDensity.integrable.div_const spectralMass

theorem continuousDensity_integral_eq_one :
    ∫ x : ℝ, continuousDensity x = 1 := by
  rw [show continuousDensity =
      fun x : ℝ => spectralDensity x / spectralMass by rfl,
    integral_div, ← spectralMass]
  exact div_self spectralMass_pos.ne'

theorem latticeWeight_nonneg (n : ℤ) :
    0 ≤ latticeWeight n :=
  div_nonneg (spectralDensity_nonneg (n : ℝ)) spectralMass_pos.le

theorem latticeWeight_summable :
    Summable latticeWeight :=
  spectralDensity_lattice_summable.div_const spectralMass

theorem latticeWeight_tsum_eq_one :
    ∑' n : ℤ, latticeWeight n = 1 := by
  change ∑' n : ℤ, spectralDensity (n : ℝ) / spectralMass = 1
  simp_rw [div_eq_mul_inv]
  rw [spectralDensity_lattice_summable.tsum_mul_right,
    spectralDensity_lattice_tsum_eq_mass]
  exact mul_inv_cancel₀ spectralMass_pos.ne'

/-- Survival amplitude of the normalized continuous spectral clock. -/
def continuousAmplitude (t : ℝ) : ℂ :=
  localAmplitude t / (spectralMass : ℂ)

/-- Survival amplitude of the normalized integer-lattice spectral clock. -/
def latticeAmplitude (t : ℝ) : ℂ :=
  (∑' n : ℤ,
      (spectralDensity (n : ℝ) : ℂ) *
        fourier n (t : UnitAddCircle)) /
    (spectralMass : ℂ)

theorem spectralDensity_fourier_lattice_summable (t : ℝ) :
    Summable (fun n : ℤ =>
      (spectralDensity (n : ℝ) : ℂ) *
        fourier n (t : UnitAddCircle)) := by
  apply Summable.of_norm
  simpa only [norm_mul, norm_real, Real.norm_eq_abs,
    abs_of_nonneg (spectralDensity_nonneg _), fourier_apply,
    Circle.norm_coe, mul_one] using spectralDensity_lattice_summable

theorem latticeAmplitude_eq_weighted_tsum (t : ℝ) :
    latticeAmplitude t =
      ∑' n : ℤ,
        (latticeWeight n : ℂ) *
          fourier n (t : UnitAddCircle) := by
  rw [latticeAmplitude]
  change
    (∑' n : ℤ,
      (spectralDensity (n : ℝ) : ℂ) *
        fourier n (t : UnitAddCircle)) *
        (spectralMass : ℂ)⁻¹ =
      ∑' n : ℤ,
        ((spectralDensity (n : ℝ) / spectralMass : ℝ) : ℂ) *
          fourier n (t : UnitAddCircle)
  rw [← (spectralDensity_fourier_lattice_summable t).tsum_mul_right]
  apply tsum_congr
  intro n
  push_cast
  field_simp

theorem continuousAmplitude_eq_spectralIntegral (t : ℝ) :
    continuousAmplitude t =
      ∫ x : ℝ,
        Complex.exp (((2 * Real.pi * (x * t) : ℝ) : ℂ) * I) *
          (continuousDensity x : ℂ) := by
  have hinv :=
    congrFun
      (localAmplitude.continuous.fourierInv_fourier_eq
        localAmplitude.integrable (𝓕 localAmplitude).integrable) t
  rw [Real.fourierInv_eq'] at hinv
  have hraw :
      localAmplitude t =
        ∫ x : ℝ,
          Complex.exp (((2 * Real.pi * (x * t) : ℝ) : ℂ) * I) *
            (spectralDensity x : ℂ) := by
    rw [← hinv]
    apply integral_congr_ae
    filter_upwards with x
    change
        Complex.exp (((2 * Real.pi * inner ℝ x t : ℝ) : ℂ) * I) •
          (𝓕 localAmplitude) x =
        Complex.exp (((2 * Real.pi * (x * t) : ℝ) : ℂ) * I) *
          (spectralDensity x : ℂ)
    rw [fourier_localAmplitude_eq_spectralDensity]
    simp only [Real.inner_apply, smul_eq_mul]
  rw [continuousAmplitude, hraw]
  change
    (∫ x : ℝ,
      Complex.exp (((2 * Real.pi * (x * t) : ℝ) : ℂ) * I) *
        (spectralDensity x : ℂ)) /
      (spectralMass : ℂ) =
    ∫ x : ℝ,
      Complex.exp (((2 * Real.pi * (x * t) : ℝ) : ℂ) * I) *
        ((spectralDensity x / spectralMass : ℝ) : ℂ)
  rw [← integral_div]
  apply integral_congr_ae
  filter_upwards with x
  push_cast
  field_simp

theorem latticeAmplitude_eq_periodization (t : ℝ) :
    latticeAmplitude t =
      (∑' k : ℤ, localAmplitude (t + (k : ℝ))) /
        (spectralMass : ℂ) := by
  have hpoisson := SchwartzMap.tsum_eq_tsum_fourier localAmplitude t
  rw [latticeAmplitude]
  congr 1
  rw [hpoisson]
  apply tsum_congr
  intro n
  rw [fourier_localAmplitude_eq_spectralDensity]

theorem shifted_localAmplitude_int_eq_zero
    {t : ℝ} (ht : |t| < (3 : ℝ) / 4)
    {n : ℤ} (hn : n ≠ 0) :
    localAmplitude (t + (n : ℝ)) = 0 := by
  apply localAmplitude_eq_zero_of_quarter_lt_abs
  have h1z : (1 : ℤ) ≤ |n| := Int.one_le_abs hn
  have h1 : (1 : ℝ) ≤ |(n : ℝ)| := by
    exact_mod_cast h1z
  have htri :
      |(n : ℝ)| ≤ |t + (n : ℝ)| + |t| := by
    have h := abs_sub_le (t + (n : ℝ)) 0 t
    simpa only [add_sub_cancel_left, sub_zero, zero_sub, abs_neg] using h
  linarith

theorem localAmplitude_periodization_eq_self
    {t : ℝ} (ht : |t| < (3 : ℝ) / 4) :
    (∑' k : ℤ, localAmplitude (t + (k : ℝ))) =
      localAmplitude t := by
  simpa using
    (tsum_eq_single
      (L := SummationFilter.unconditional ℤ)
      (f := fun k : ℤ => localAmplitude (t + (k : ℝ))) 0
      (fun n hn => shifted_localAmplitude_int_eq_zero ht hn))

/--
The normalized continuous and lattice survival amplitudes agree at every time
in the open interval `(-3/4,3/4)`.
-/
theorem amplitudes_eq_on_open_interval
    {t : ℝ} (ht : |t| < (3 : ℝ) / 4) :
    latticeAmplitude t = continuousAmplitude t := by
  rw [latticeAmplitude_eq_periodization,
    localAmplitude_periodization_eq_self ht]
  rfl

@[simp] theorem continuousAmplitude_zero_eq_one :
    continuousAmplitude 0 = 1 := by
  rw [continuousAmplitude, localAmplitude_zero_eq_spectralMass]
  exact div_self (Complex.ofReal_ne_zero.mpr spectralMass_pos.ne')

@[simp] theorem latticeAmplitude_zero_eq_one :
    latticeAmplitude 0 = 1 := by
  rw [amplitudes_eq_on_open_interval (by norm_num)]
  exact continuousAmplitude_zero_eq_one

theorem continuousAmplitude_one_eq_zero :
    continuousAmplitude 1 = 0 := by
  rw [continuousAmplitude,
    localAmplitude_eq_zero_of_quarter_lt_abs (by norm_num)]
  simp

theorem fourier_one_eq_one (n : ℤ) :
    fourier n ((1 : ℝ) : UnitAddCircle) = 1 := by
  rw [fourier_coe_apply]
  norm_num
  rw [show 2 * (Real.pi : ℂ) * I * (n : ℂ) =
      (n : ℂ) * (2 * Real.pi * I) by ring]
  exact Complex.exp_int_mul_two_pi_mul_I n

theorem latticeAmplitude_one_eq_one :
    latticeAmplitude 1 = 1 := by
  rw [latticeAmplitude_eq_weighted_tsum]
  simp_rw [fourier_one_eq_one, mul_one]
  rw [← Complex.ofReal_tsum, latticeWeight_tsum_eq_one]
  norm_num

/--
**Exact local-history/global-recurrence separation.**  Two normalized
nonnegative spectra have identical survival amplitude throughout an open time
interval, yet at time one the lattice clock has returned exactly while the
continuous clock is orthogonal to its initial state.
-/
theorem infinite_local_history_global_recurrence_separation :
    (∀ t : ℝ, |t| < (3 : ℝ) / 4 →
      latticeAmplitude t = continuousAmplitude t) ∧
    latticeAmplitude 1 = 1 ∧
    continuousAmplitude 1 = 0 :=
  ⟨fun _ ht => amplitudes_eq_on_open_interval ht,
    latticeAmplitude_one_eq_one,
    continuousAmplitude_one_eq_zero⟩

/-- Continuous clock amplitude after choosing an arbitrary positive time unit. -/
def scaledContinuousAmplitude (T t : ℝ) : ℂ :=
  continuousAmplitude (t / T)

/-- Lattice clock amplitude after choosing an arbitrary positive time unit. -/
def scaledLatticeAmplitude (T t : ℝ) : ℂ :=
  latticeAmplitude (t / T)

/--
The exact separation law holds at every positive time scale: the histories
agree through three quarters of the chosen return time, then at that return
time one clock returns exactly and the other is orthogonal.
-/
theorem separation_at_every_positive_time_scale
    (T : ℝ) (hT : 0 < T) :
    (∀ t : ℝ, |t| < 3 * T / 4 →
      scaledLatticeAmplitude T t = scaledContinuousAmplitude T t) ∧
    scaledLatticeAmplitude T T = 1 ∧
    scaledContinuousAmplitude T T = 0 := by
  constructor
  · intro t ht
    apply amplitudes_eq_on_open_interval
    rw [abs_div, abs_of_pos hT]
    apply (div_lt_iff₀ hT).2
    nlinarith
  · rw [scaledLatticeAmplitude, scaledContinuousAmplitude,
      div_self hT.ne']
    exact ⟨latticeAmplitude_one_eq_one,
      continuousAmplitude_one_eq_zero⟩

end RHTower.InfiniteLocal
