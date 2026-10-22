import GaloisForLFunctions.RHTower.XiPhysicalPrimeLogApertureHilbertMetric
import GaloisForLFunctions.RHTower.CCM.CCMRectangularAutocorrelation
import Mathlib.Analysis.Fourier.AddCircle

/-!
# Character tomography of the physical CCM prime aperture

The real physical fusion energy has an equivalent complex Hilbert realization.  This permits
projection onto aperture characters without losing the exact clipped prime intervals.
-/

open scoped BigOperators
open MeasureTheory Set Complex

namespace RHTower

noncomputable section

/-- The complex Hilbert space carrying aperture characters. -/
abbrev XiPhysicalComplexApertureL2 :=
  MeasureTheory.Lp ℂ 2 (volume : Measure ℝ)

/-- Complex indicator of one clipped physical prime interval. -/
def xiPhysicalPrimeLogComplexApertureIndicator
    (A m k : ℝ) (p : Nat.Primes) : XiPhysicalComplexApertureL2 :=
  indicatorConstLp (μ := (volume : Measure ℝ)) 2
    (s := xiPhysicalPrimeLogApertureSet A m k p) measurableSet_Ioc
    (measure_xiPhysicalPrimeLogApertureSet_ne_top A m k p) (1 : ℂ)

/-- Complex indicator of the whole aperture. -/
def xiPhysicalLogComplexApertureIndicator
    (A : ℝ) : XiPhysicalComplexApertureL2 :=
  indicatorConstLp (μ := (volume : Measure ℝ)) 2
    (s := xiPhysicalLogApertureSet A) measurableSet_Ioc
    (measure_xiPhysicalLogApertureSet_ne_top A) (1 : ℂ)

/-- Complexification of the centered clipped prime carrier. -/
def xiPhysicalPrimeLogComplexCenteredApertureCarrier
    (A m k : ℝ) (p : Nat.Primes) : XiPhysicalComplexApertureL2 :=
  xiPhysicalPrimeLogComplexApertureIndicator A m k p -
    ((xiPhysicalPrimeLogApertureLength A m k p / A : ℝ) : ℂ) •
      xiPhysicalLogComplexApertureIndicator A

theorem inner_xiPhysicalPrimeLogComplexApertureIndicator
    (A m k : ℝ) (p q : Nat.Primes) :
    inner ℂ (xiPhysicalPrimeLogComplexApertureIndicator A m k p)
        (xiPhysicalPrimeLogComplexApertureIndicator A m k q) =
      (xiPhysicalPrimeLogApertureOverlap A m k p q : ℂ) := by
  calc
    inner ℂ (xiPhysicalPrimeLogComplexApertureIndicator A m k p)
        (xiPhysicalPrimeLogComplexApertureIndicator A m k q) =
        (RCLike.ofReal (xiPhysicalPrimeLogApertureOverlap A m k p q) : ℂ) := by
      simpa only [xiPhysicalPrimeLogComplexApertureIndicator,
        volume_real_xiPhysicalPrimeLogApertureSet_inter] using
        (MeasureTheory.L2.inner_indicatorConstLp_one_indicatorConstLp_one
          (μ := (volume : Measure ℝ))
          (s := xiPhysicalPrimeLogApertureSet A m k p)
          (t := xiPhysicalPrimeLogApertureSet A m k q)
          measurableSet_Ioc measurableSet_Ioc
          (measure_xiPhysicalPrimeLogApertureSet_ne_top A m k p)
          (measure_xiPhysicalPrimeLogApertureSet_ne_top A m k q))
    _ = (xiPhysicalPrimeLogApertureOverlap A m k p q : ℂ) := rfl

theorem inner_xiPhysicalPrimeLogComplexApertureIndicator_aperture
    (A m k : ℝ) (p : Nat.Primes) :
    inner ℂ (xiPhysicalPrimeLogComplexApertureIndicator A m k p)
        (xiPhysicalLogComplexApertureIndicator A) =
      (xiPhysicalPrimeLogApertureLength A m k p : ℂ) := by
  have hinter : xiPhysicalPrimeLogApertureSet A m k p ∩
      xiPhysicalLogApertureSet A =
      xiPhysicalPrimeLogApertureSet A m k p :=
    Set.inter_eq_left.mpr (xiPhysicalPrimeLogApertureSet_subset A m k p)
  calc
    inner ℂ (xiPhysicalPrimeLogComplexApertureIndicator A m k p)
        (xiPhysicalLogComplexApertureIndicator A) =
        (RCLike.ofReal (xiPhysicalPrimeLogApertureLength A m k p) : ℂ) := by
      simpa only [xiPhysicalPrimeLogComplexApertureIndicator,
        xiPhysicalLogComplexApertureIndicator, hinter,
        volume_real_xiPhysicalPrimeLogApertureSet] using
        (MeasureTheory.L2.inner_indicatorConstLp_one_indicatorConstLp_one
          (μ := (volume : Measure ℝ))
          (s := xiPhysicalPrimeLogApertureSet A m k p)
          (t := xiPhysicalLogApertureSet A)
          measurableSet_Ioc measurableSet_Ioc
          (measure_xiPhysicalPrimeLogApertureSet_ne_top A m k p)
          (measure_xiPhysicalLogApertureSet_ne_top A))
    _ = (xiPhysicalPrimeLogApertureLength A m k p : ℂ) := rfl

theorem inner_xiPhysicalLogComplexApertureIndicator_prime
    (A m k : ℝ) (p : Nat.Primes) :
    inner ℂ (xiPhysicalLogComplexApertureIndicator A)
      (xiPhysicalPrimeLogComplexApertureIndicator A m k p) =
      (xiPhysicalPrimeLogApertureLength A m k p : ℂ) := by
  calc
    inner ℂ (xiPhysicalLogComplexApertureIndicator A)
        (xiPhysicalPrimeLogComplexApertureIndicator A m k p) =
        star (inner ℂ (xiPhysicalPrimeLogComplexApertureIndicator A m k p)
          (xiPhysicalLogComplexApertureIndicator A)) := (inner_conj_symm _ _).symm
    _ = (xiPhysicalPrimeLogApertureLength A m k p : ℂ) := by
      rw [inner_xiPhysicalPrimeLogComplexApertureIndicator_aperture]
      simp

theorem inner_xiPhysicalLogComplexApertureIndicator
    {A : ℝ} (hA : 0 < A) :
    inner ℂ (xiPhysicalLogComplexApertureIndicator A)
        (xiPhysicalLogComplexApertureIndicator A) = (A : ℂ) := by
  calc
    inner ℂ (xiPhysicalLogComplexApertureIndicator A)
        (xiPhysicalLogComplexApertureIndicator A) =
        (RCLike.ofReal A : ℂ) := by
      simpa only [xiPhysicalLogComplexApertureIndicator, inter_self,
        volume_real_xiPhysicalLogApertureSet hA] using
        (MeasureTheory.L2.inner_indicatorConstLp_one_indicatorConstLp_one
          (μ := (volume : Measure ℝ))
          (s := xiPhysicalLogApertureSet A) (t := xiPhysicalLogApertureSet A)
          measurableSet_Ioc measurableSet_Ioc
          (measure_xiPhysicalLogApertureSet_ne_top A)
          (measure_xiPhysicalLogApertureSet_ne_top A))
    _ = (A : ℂ) := rfl

/-- The complex centered carrier has exactly the same real Gram kernel as the original carrier. -/
theorem inner_xiPhysicalPrimeLogComplexCenteredApertureCarrier
    {A : ℝ} (hA : 0 < A) (m k : ℝ) (p q : Nat.Primes) :
    inner ℂ (xiPhysicalPrimeLogComplexCenteredApertureCarrier A m k p)
        (xiPhysicalPrimeLogComplexCenteredApertureCarrier A m k q) =
      (xiPhysicalPrimeLogApertureFusionKernel A m k p q : ℂ) := by
  simp only [xiPhysicalPrimeLogComplexCenteredApertureCarrier,
    inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    inner_xiPhysicalPrimeLogComplexApertureIndicator,
    inner_xiPhysicalPrimeLogComplexApertureIndicator_aperture,
    inner_xiPhysicalLogComplexApertureIndicator_prime,
    inner_xiPhysicalLogComplexApertureIndicator hA,
    xiPhysicalPrimeLogApertureFusionKernel,
    Complex.conj_ofReal]
  push_cast
  field_simp [hA.ne']
  ring

/-- Complex coherent carrier of a finite physical prime packet. -/
def xiPhysicalPrimeLogComplexAggregateApertureCarrier
    (P : Finset Nat.Primes) (A m k : ℝ) : XiPhysicalComplexApertureL2 :=
  ∑ p ∈ P, (physicalPrimeEndpointWeight p : ℂ) •
    xiPhysicalPrimeLogComplexCenteredApertureCarrier A m k p

/-- Exact complex Hilbert realization of the physical fusion energy. -/
theorem xiPhysicalPrimeLogApertureFusionEnergy_eq_complex_norm_sq
    (P : Finset Nat.Primes) {A : ℝ} (hA : 0 < A) (m k : ℝ) :
    xiPhysicalPrimeLogApertureFusionEnergy P A m k =
      ‖xiPhysicalPrimeLogComplexAggregateApertureCarrier P A m k‖ ^ 2 := by
  rw [← Complex.ofReal_inj]
  calc
    (xiPhysicalPrimeLogApertureFusionEnergy P A m k : ℂ) =
        inner ℂ (xiPhysicalPrimeLogComplexAggregateApertureCarrier P A m k)
          (xiPhysicalPrimeLogComplexAggregateApertureCarrier P A m k) := by
      rw [xiPhysicalPrimeLogComplexAggregateApertureCarrier, sum_inner,
        xiPhysicalPrimeLogApertureFusionEnergy]
      push_cast
      apply Finset.sum_congr rfl
      intro p hp
      rw [inner_sum]
      apply Finset.sum_congr rfl
      intro q hq
      rw [inner_smul_left, inner_smul_right,
        inner_xiPhysicalPrimeLogComplexCenteredApertureCarrier hA]
      simp only [Complex.conj_ofReal]
      ring
    _ = (‖xiPhysicalPrimeLogComplexAggregateApertureCarrier P A m k‖ : ℂ) ^ 2 :=
      inner_self_eq_norm_sq_to_K _
    _ = (‖xiPhysicalPrimeLogComplexAggregateApertureCarrier P A m k‖ ^ 2 : ℝ) := by
      push_cast
      rfl

/-- Every clipped interval is the interval starting at its clipped left endpoint with its
nonnegative clipped length.  This formula remains true when the raw endpoints are reversed. -/
theorem xiPhysicalPrimeLogApertureSet_eq_start_add_length
    (A m k : ℝ) (p : Nat.Primes) :
    xiPhysicalPrimeLogApertureSet A m k p =
      Ioc (xiPhysicalPrimeLogApertureStart m p)
        (xiPhysicalPrimeLogApertureStart m p +
          xiPhysicalPrimeLogApertureLength A m k p) := by
  rw [xiPhysicalPrimeLogApertureSet, xiPhysicalPrimeLogApertureLength]
  by_cases h : 0 ≤ xiPhysicalPrimeLogApertureEnd A k p -
      xiPhysicalPrimeLogApertureStart m p
  · rw [max_eq_right h]
    congr 1
    ring
  · have hlt : xiPhysicalPrimeLogApertureEnd A k p <
        xiPhysicalPrimeLogApertureStart m p := by linarith
    rw [max_eq_left (le_of_not_ge h)]
    ext x
    simp only [mem_Ioc, add_zero]
    constructor <;> intro hx
    · linarith
    · linarith

/-! ## All aperture characters -/

/-- Integer Fourier-character rate on an aperture of length `A`. -/
def xiPhysicalApertureCharacterRate (A : ℝ) (n : ℤ) : ℂ :=
  (((((n : ℝ) * (2 * Real.pi)) / A : ℝ) : ℂ) * Complex.I)

/-- Compactly supported integer aperture character. -/
def xiPhysicalApertureCharacterFun (A : ℝ) (n : ℤ) (u : ℝ) : ℂ :=
  (rectangularIntervalIndicator 0 A u : ℂ) *
    Complex.exp (xiPhysicalApertureCharacterRate A n * (u : ℂ))

theorem xiPhysicalApertureCharacterRate_ne_zero
    {A : ℝ} (hA : 0 < A) {n : ℤ} (hn : n ≠ 0) :
    xiPhysicalApertureCharacterRate A n ≠ 0 := by
  rw [xiPhysicalApertureCharacterRate]
  exact mul_ne_zero
    (Complex.ofReal_ne_zero.mpr
      (div_ne_zero
        (mul_ne_zero (Int.cast_ne_zero.mpr hn)
          (mul_ne_zero (by norm_num) Real.pi_ne_zero)) hA.ne'))
    Complex.I_ne_zero

theorem norm_exp_xiPhysicalApertureCharacterRate_mul
    (A : ℝ) (n : ℤ) (u : ℝ) :
    ‖Complex.exp (xiPhysicalApertureCharacterRate A n * (u : ℂ))‖ = 1 := by
  rw [show xiPhysicalApertureCharacterRate A n * (u : ℂ) =
      (((((n : ℝ) * (2 * Real.pi) / A) * u : ℝ) : ℂ) * Complex.I) by
        rw [xiPhysicalApertureCharacterRate]
        push_cast
        ring]
  exact Complex.norm_exp_ofReal_mul_I _

theorem xiPhysicalApertureCharacterFun_memLp (A : ℝ) (n : ℤ) :
    MemLp (xiPhysicalApertureCharacterFun A n) 2
      (volume : Measure ℝ) := by
  let g : ℝ → ℂ := (Ioc 0 A).indicator (fun _ => (1 : ℂ))
  have hg : MemLp g 2 (volume : Measure ℝ) := by
    simpa only [g] using
      (memLp_indicator_const (μ := (volume : Measure ℝ)) 2 measurableSet_Ioc
        (1 : ℂ) (Or.inr (ne_of_lt measure_Ioc_lt_top)))
  have hfmeas : AEStronglyMeasurable (xiPhysicalApertureCharacterFun A n)
      (volume : Measure ℝ) :=
    (integrable_rectangularIntervalIndicator_mul_exp
      0 A (xiPhysicalApertureCharacterRate A n)).aestronglyMeasurable
  exact (memLp_congr_norm hfmeas hg.1 (Filter.Eventually.of_forall fun u => by
    rw [xiPhysicalApertureCharacterFun, norm_mul,
      norm_exp_xiPhysicalApertureCharacterRate_mul, mul_one]
    by_cases hmem : u ∈ Ioc 0 A <;>
      simp [g, rectangularIntervalIndicator, hmem])).mpr hg

/-- Integer aperture character as a complex `L²` vector. -/
def xiPhysicalApertureCharacter (A : ℝ) (n : ℤ) :
    XiPhysicalComplexApertureL2 :=
  (xiPhysicalApertureCharacterFun_memLp A n).toLp
    (xiPhysicalApertureCharacterFun A n)

/-- Every nonconstant integer aperture character has zero aperture mean. -/
theorem integral_xiPhysicalApertureCharacterFun
    {A : ℝ} (hA : 0 < A) {n : ℤ} (hn : n ≠ 0) :
    (∫ u : ℝ, xiPhysicalApertureCharacterFun A n u) = 0 := by
  change (∫ u : ℝ, (rectangularIntervalIndicator 0 A u : ℂ) *
    Complex.exp (xiPhysicalApertureCharacterRate A n * (u : ℂ))) = 0
  rw [integral_rectangularIntervalIndicator_mul_exp hA.le]
  have hr := xiPhysicalApertureCharacterRate_ne_zero hA hn
  rw [rectangularWindowAmplitude_eq_div hr]
  have hperiod : Complex.exp (-(A : ℂ) *
      xiPhysicalApertureCharacterRate A n) = 1 := by
    rw [show -(A : ℂ) * xiPhysicalApertureCharacterRate A n =
        (-n) * (2 * (Real.pi : ℂ) * Complex.I) by
          rw [xiPhysicalApertureCharacterRate]
          push_cast
          field_simp [hA.ne']]
    simpa only [Int.cast_neg] using Complex.exp_int_mul_two_pi_mul_I (-n)
  rw [hperiod]
  simp

theorem inner_xiPhysicalLogComplexApertureIndicator_character
    {A : ℝ} (hA : 0 < A) {n : ℤ} (hn : n ≠ 0) :
    inner ℂ (xiPhysicalLogComplexApertureIndicator A)
      (xiPhysicalApertureCharacter A n) = 0 := by
  rw [xiPhysicalLogComplexApertureIndicator,
    xiPhysicalApertureCharacter,
    MeasureTheory.L2.inner_indicatorConstLp_one,
    xiPhysicalLogApertureSet]
  rw [← integral_indicator measurableSet_Ioc]
  rw [← integral_xiPhysicalApertureCharacterFun hA hn]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp
    (xiPhysicalApertureCharacterFun_memLp A n)] with u hu
  by_cases hmem : u ∈ Ioc 0 A
  · simp only [indicator_of_mem hmem, hu]
  · rw [indicator_of_notMem hmem]
    simp [xiPhysicalApertureCharacterFun,
      rectangularIntervalIndicator, hmem]

/-- Every integer aperture character, including the constant character, has squared norm `A`. -/
theorem norm_xiPhysicalApertureCharacter_sq
    {A : ℝ} (hA : 0 < A) (n : ℤ) :
    ‖xiPhysicalApertureCharacter A n‖ ^ 2 = A := by
  rw [← Complex.ofReal_inj, Complex.ofReal_pow]
  have hself : inner ℂ (xiPhysicalApertureCharacter A n)
      (xiPhysicalApertureCharacter A n) =
      (‖xiPhysicalApertureCharacter A n‖ : ℂ) ^ 2 :=
    inner_self_eq_norm_sq_to_K _
  rw [← hself, L2.inner_def]
  rw [show (A : ℂ) = ∫ u : ℝ,
      (Ioc 0 A).indicator (fun _ => (1 : ℂ)) u by
        rw [integral_indicator_const (1 : ℂ) measurableSet_Ioc,
          Measure.real, Real.volume_Ioc, sub_zero,
          ENNReal.toReal_ofReal hA.le]
        simp]
  apply integral_congr_ae
  rw [xiPhysicalApertureCharacter]
  filter_upwards [MemLp.coeFn_toLp
    (xiPhysicalApertureCharacterFun_memLp A n)] with u hu
  rw [hu]
  by_cases hmem : u ∈ Ioc 0 A
  · simp only [indicator_of_mem hmem]
    rw [xiPhysicalApertureCharacterFun, rectangularIntervalIndicator,
      zero_add, indicator_of_mem hmem]
    simp only [Complex.ofReal_one, one_mul, inner_self_eq_norm_sq_to_K,
      norm_exp_xiPhysicalApertureCharacterRate_mul]
    norm_num
  · simp only [indicator_of_notMem hmem]
    rw [xiPhysicalApertureCharacterFun, rectangularIntervalIndicator,
      zero_add, indicator_of_notMem hmem]
    simp

/-- Exact clipped-interval moment in Fourier channel `n`. -/
def xiPhysicalPrimeLogCharacterMoment
    (A : ℝ) (n : ℤ) (m k : ℝ) (p : Nat.Primes) : ℂ :=
  Complex.exp (((xiPhysicalPrimeLogApertureStart m p +
      xiPhysicalPrimeLogApertureLength A m k p : ℝ) : ℂ) *
        xiPhysicalApertureCharacterRate A n) *
    rectangularWindowAmplitude
      (xiPhysicalPrimeLogApertureLength A m k p)
      (xiPhysicalApertureCharacterRate A n)

theorem inner_xiPhysicalPrimeLogComplexApertureIndicator_character
    (A : ℝ) (n : ℤ) (m k : ℝ) (p : Nat.Primes) :
    inner ℂ (xiPhysicalPrimeLogComplexApertureIndicator A m k p)
      (xiPhysicalApertureCharacter A n) =
        xiPhysicalPrimeLogCharacterMoment A n m k p := by
  rw [xiPhysicalPrimeLogComplexApertureIndicator,
    MeasureTheory.L2.inner_indicatorConstLp_one,
    xiPhysicalPrimeLogApertureSet_eq_start_add_length]
  let s := xiPhysicalPrimeLogApertureStart m p
  let L := xiPhysicalPrimeLogApertureLength A m k p
  rw [← integral_indicator measurableSet_Ioc]
  change (∫ u : ℝ, (Ioc s (s + L)).indicator
    (fun u => (xiPhysicalApertureCharacter A n : ℝ → ℂ) u) u) =
      xiPhysicalPrimeLogCharacterMoment A n m k p
  rw [show (∫ u : ℝ,
      (Ioc s (s + L)).indicator
        (fun u => (xiPhysicalApertureCharacter A n : ℝ → ℂ) u) u) =
      ∫ u : ℝ, (rectangularIntervalIndicator s L u : ℂ) *
        Complex.exp (xiPhysicalApertureCharacterRate A n * (u : ℂ)) by
    apply integral_congr_ae
    rw [xiPhysicalApertureCharacter]
    filter_upwards [MemLp.coeFn_toLp
      (xiPhysicalApertureCharacterFun_memLp A n)] with u hu
    by_cases hmem : u ∈ Ioc s (s + L)
    · have hprime : u ∈ xiPhysicalPrimeLogApertureSet A m k p := by
        rw [xiPhysicalPrimeLogApertureSet_eq_start_add_length]
        exact hmem
      have hap := xiPhysicalPrimeLogApertureSet_subset A m k p hprime
      rw [indicator_of_mem hmem, hu]
      rw [xiPhysicalApertureCharacterFun, rectangularIntervalIndicator]
      rw [indicator_of_mem (show u ∈ Ioc 0 (0 + A) by
        simpa only [xiPhysicalLogApertureSet, zero_add] using hap)]
      simp [rectangularIntervalIndicator, hmem]
    · simp [rectangularIntervalIndicator, hmem]]
  rw [integral_rectangularIntervalIndicator_mul_exp
    (xiPhysicalPrimeLogApertureLength_nonneg A m k p)]
  rfl

theorem inner_xiPhysicalPrimeLogComplexCenteredApertureCarrier_character
    {A : ℝ} (hA : 0 < A) {n : ℤ} (hn : n ≠ 0)
    (m k : ℝ) (p : Nat.Primes) :
    inner ℂ (xiPhysicalPrimeLogComplexCenteredApertureCarrier A m k p)
      (xiPhysicalApertureCharacter A n) =
        xiPhysicalPrimeLogCharacterMoment A n m k p := by
  rw [xiPhysicalPrimeLogComplexCenteredApertureCarrier, inner_sub_left,
    inner_smul_left,
    inner_xiPhysicalPrimeLogComplexApertureIndicator_character A,
    inner_xiPhysicalLogComplexApertureIndicator_character hA hn]
  simp

/-- Exact prime amplitude in Fourier channel `n`. -/
def xiPhysicalPrimeLogCharacterAmplitude
    (P : Finset Nat.Primes) (A : ℝ) (n : ℤ) (m k : ℝ) : ℂ :=
  ∑ p ∈ P, (physicalPrimeEndpointWeight p : ℂ) *
    xiPhysicalPrimeLogCharacterMoment A n m k p

theorem inner_xiPhysicalPrimeLogComplexAggregate_character
    (P : Finset Nat.Primes) {A : ℝ} (hA : 0 < A)
    {n : ℤ} (hn : n ≠ 0) (m k : ℝ) :
    inner ℂ (xiPhysicalPrimeLogComplexAggregateApertureCarrier P A m k)
      (xiPhysicalApertureCharacter A n) =
        xiPhysicalPrimeLogCharacterAmplitude P A n m k := by
  rw [xiPhysicalPrimeLogComplexAggregateApertureCarrier,
    xiPhysicalPrimeLogCharacterAmplitude, sum_inner]
  apply Finset.sum_congr rfl
  intro p hp
  rw [inner_smul_left,
    inner_xiPhysicalPrimeLogComplexCenteredApertureCarrier_character hA hn]
  simp

/-- **Universal character tomography law.**  Every nonconstant integer aperture character is a
simultaneously valid scalar channel of the exact physical CCM producer. -/
theorem normSq_xiPhysicalPrimeLogCharacterAmplitude_le_energy
    (P : Finset Nat.Primes) {A : ℝ} (hA : 0 < A)
    {n : ℤ} (hn : n ≠ 0) (m k : ℝ) :
    Complex.normSq (xiPhysicalPrimeLogCharacterAmplitude P A n m k) ≤
      A * xiPhysicalPrimeLogApertureFusionEnergy P A m k := by
  let x := xiPhysicalPrimeLogComplexAggregateApertureCarrier P A m k
  let e := xiPhysicalApertureCharacter A n
  have hinner : inner ℂ x e =
      xiPhysicalPrimeLogCharacterAmplitude P A n m k :=
    inner_xiPhysicalPrimeLogComplexAggregate_character P hA hn m k
  have hcs : ‖inner ℂ x e‖ ≤ ‖x‖ * ‖e‖ := norm_inner_le_norm _ _
  have hsquare : ‖inner ℂ x e‖ ^ 2 ≤ (‖x‖ * ‖e‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hcs 2
  rw [hinner, Complex.sq_norm, mul_pow,
    ← xiPhysicalPrimeLogApertureFusionEnergy_eq_complex_norm_sq P hA m k,
    norm_xiPhysicalApertureCharacter_sq hA n] at hsquare
  nlinarith

theorem star_xiPhysicalApertureCharacterRate
    (A : ℝ) (n : ℤ) :
    (starRingEnd ℂ) (xiPhysicalApertureCharacterRate A n) =
      -xiPhysicalApertureCharacterRate A n := by
  rw [starRingEnd_apply, xiPhysicalApertureCharacterRate]
  simp

theorem conj_exp_character_mul_exp_character
    (A u : ℝ) (n j : ℤ) :
    (starRingEnd ℂ)
        (Complex.exp (xiPhysicalApertureCharacterRate A n * (u : ℂ))) *
      Complex.exp (xiPhysicalApertureCharacterRate A j * (u : ℂ)) =
        Complex.exp (xiPhysicalApertureCharacterRate A (j - n) * (u : ℂ)) := by
  rw [← Complex.exp_conj, map_mul, star_xiPhysicalApertureCharacterRate,
    ← Complex.exp_add]
  congr 1
  rw [xiPhysicalApertureCharacterRate,
    xiPhysicalApertureCharacterRate,
    xiPhysicalApertureCharacterRate]
  push_cast
  have hu : (starRingEnd ℂ) (u : ℂ) = (u : ℂ) := by
    change star (u : ℂ) = (u : ℂ)
    exact RCLike.conj_ofReal u
  rw [hu]
  ring

/-- Distinct integer aperture characters are orthogonal. -/
theorem inner_xiPhysicalApertureCharacter_eq_zero
    {A : ℝ} (hA : 0 < A) {n j : ℤ} (hnj : n ≠ j) :
    inner ℂ (xiPhysicalApertureCharacter A n)
      (xiPhysicalApertureCharacter A j) = 0 := by
  rw [L2.inner_def]
  have hsub : j - n ≠ 0 := sub_ne_zero.mpr (Ne.symm hnj)
  rw [← integral_xiPhysicalApertureCharacterFun hA hsub]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp
      (xiPhysicalApertureCharacterFun_memLp A n),
    MemLp.coeFn_toLp
      (xiPhysicalApertureCharacterFun_memLp A j)] with u hun huj
  simp only [xiPhysicalApertureCharacter]
  rw [hun, huj]
  by_cases hmem : u ∈ Ioc 0 A
  · rw [xiPhysicalApertureCharacterFun,
      xiPhysicalApertureCharacterFun,
      xiPhysicalApertureCharacterFun,
      rectangularIntervalIndicator, zero_add,
      indicator_of_mem hmem]
    simp only [Complex.ofReal_one, one_mul]
    simpa only [RCLike.inner_apply, mul_comm] using
      conj_exp_character_mul_exp_character A u n j
  · simp [xiPhysicalApertureCharacterFun,
      rectangularIntervalIndicator, hmem]

/-- Unit-normalized integer aperture character. -/
def xiPhysicalNormalizedApertureCharacter (A : ℝ) (n : ℤ) :
    XiPhysicalComplexApertureL2 :=
  ((Real.sqrt A : ℝ) : ℂ)⁻¹ • xiPhysicalApertureCharacter A n

theorem norm_xiPhysicalApertureCharacter_eq_sqrt
    {A : ℝ} (hA : 0 < A) (n : ℤ) :
    ‖xiPhysicalApertureCharacter A n‖ = Real.sqrt A := by
  have hsquare := norm_xiPhysicalApertureCharacter_sq hA n
  nlinarith [norm_nonneg (xiPhysicalApertureCharacter A n),
    Real.sqrt_nonneg A, Real.sq_sqrt hA.le]

theorem norm_xiPhysicalNormalizedApertureCharacter
    {A : ℝ} (hA : 0 < A) (n : ℤ) :
    ‖xiPhysicalNormalizedApertureCharacter A n‖ = 1 := by
  have hsqrt : ‖((Real.sqrt A : ℝ) : ℂ)‖ = Real.sqrt A := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.sqrt_pos.2 hA)]
  rw [xiPhysicalNormalizedApertureCharacter, norm_smul,
    norm_inv, hsqrt,
    norm_xiPhysicalApertureCharacter_eq_sqrt hA]
  exact inv_mul_cancel₀ (Real.sqrt_ne_zero'.mpr hA)

/-- All nonzero integer aperture characters form one orthonormal family. -/
theorem orthonormal_xiPhysicalNormalizedApertureCharacters
    {A : ℝ} (hA : 0 < A) :
    Orthonormal ℂ (fun n : {n : ℤ // n ≠ 0} =>
      xiPhysicalNormalizedApertureCharacter A n) := by
  constructor
  · intro n
    exact norm_xiPhysicalNormalizedApertureCharacter hA n
  · intro n j hnj
    have hval : (n : ℤ) ≠ (j : ℤ) := by
      intro h
      exact hnj (Subtype.ext h)
    simp only [xiPhysicalNormalizedApertureCharacter,
      inner_smul_left, inner_smul_right]
    rw [inner_xiPhysicalApertureCharacter_eq_zero hA hval]
    simp

theorem norm_inner_normalizedCharacter_aggregate_sq
    (P : Finset Nat.Primes) {A : ℝ} (hA : 0 < A)
    (n : {n : ℤ // n ≠ 0}) (m k : ℝ) :
    ‖inner ℂ (xiPhysicalNormalizedApertureCharacter A n)
        (xiPhysicalPrimeLogComplexAggregateApertureCarrier P A m k)‖ ^ 2 =
      Complex.normSq (xiPhysicalPrimeLogCharacterAmplitude P A n m k) / A := by
  let x := xiPhysicalPrimeLogComplexAggregateApertureCarrier P A m k
  let e := xiPhysicalApertureCharacter A (n : ℤ)
  have hamp : inner ℂ x e =
      xiPhysicalPrimeLogCharacterAmplitude P A n m k :=
    inner_xiPhysicalPrimeLogComplexAggregate_character P hA n.property m k
  have hsymm : ‖inner ℂ e x‖ =
      ‖xiPhysicalPrimeLogCharacterAmplitude P A n m k‖ := by
    rw [norm_inner_symm, hamp]
  have hsqrt : ‖((Real.sqrt A : ℝ) : ℂ)‖ = Real.sqrt A := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.sqrt_pos.2 hA)]
  rw [xiPhysicalNormalizedApertureCharacter, inner_smul_left,
    norm_mul, starRingEnd_apply, norm_star, norm_inv, hsqrt, hsymm,
    mul_pow, Complex.sq_norm]
  rw [inv_pow]
  field_simp [Real.sqrt_ne_zero'.mpr hA, hA.ne']
  rw [Real.sq_sqrt hA.le]
  ring

/-- **Finite simultaneous character law.**  Any finite collection of distinct nonconstant
aperture channels has total squared prime amplitude at most `A` times the exact CCM fusion energy.
Thus cancellation cannot move between Fourier channels. -/
theorem sum_normSq_xiPhysicalPrimeLogCharacterAmplitude_le_energy
    (P : Finset Nat.Primes) {A : ℝ} (hA : 0 < A)
    (S : Finset {n : ℤ // n ≠ 0}) (m k : ℝ) :
    (∑ n ∈ S,
      Complex.normSq (xiPhysicalPrimeLogCharacterAmplitude P A n m k)) ≤
        A * xiPhysicalPrimeLogApertureFusionEnergy P A m k := by
  let x := xiPhysicalPrimeLogComplexAggregateApertureCarrier P A m k
  have hB := (orthonormal_xiPhysicalNormalizedApertureCharacters hA).sum_inner_products_le
    x (s := S)
  rw [show (∑ n ∈ S,
      ‖inner ℂ (xiPhysicalNormalizedApertureCharacter A n) x‖ ^ 2) =
      (∑ n ∈ S,
        Complex.normSq (xiPhysicalPrimeLogCharacterAmplitude P A n m k)) / A by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro n hn
    exact norm_inner_normalizedCharacter_aggregate_sq P hA n m k] at hB
  rw [← xiPhysicalPrimeLogApertureFusionEnergy_eq_complex_norm_sq P hA m k] at hB
  simpa only [mul_comm] using (div_le_iff₀ hA).mp hB

/-! ## Bulk twisted-prime factorization with exact edge remainder -/

/-- Scalar prime sum selected by aperture character `n`. -/
def xiPhysicalPrimeLogTwistedCharacterSum
    (P : Finset Nat.Primes) (A : ℝ) (n : ℤ) : ℂ :=
  ∑ p ∈ P, (physicalPrimeEndpointWeight p : ℂ) *
    Complex.exp (-(Real.log (p : ℝ) : ℂ) *
      xiPhysicalApertureCharacterRate A n)

theorem xiPhysicalPrimeLogCharacterMoment_eq_bulk
    {A m k : ℝ} (n : ℤ) (p : Nat.Primes)
    (hstart : 0 ≤ m - Real.log (p : ℝ))
    (hend : k - Real.log (p : ℝ) ≤ A)
    (hmk : m ≤ k) :
    xiPhysicalPrimeLogCharacterMoment A n m k p =
      Complex.exp (((k - Real.log (p : ℝ) : ℝ) : ℂ) *
        xiPhysicalApertureCharacterRate A n) *
      rectangularWindowAmplitude (k - m)
        (xiPhysicalApertureCharacterRate A n) := by
  rw [xiPhysicalPrimeLogCharacterMoment,
    xiPhysicalPrimeLogApertureStart, max_eq_right hstart,
    xiPhysicalPrimeLogApertureLength_eq_bulk p hstart hend hmk]
  congr 2
  push_cast
  ring

theorem exp_bulk_character_eq_common_mul_twist
    (A k : ℝ) (n : ℤ) (p : Nat.Primes) :
    Complex.exp (((k - Real.log (p : ℝ) : ℝ) : ℂ) *
        xiPhysicalApertureCharacterRate A n) =
      Complex.exp ((k : ℂ) * xiPhysicalApertureCharacterRate A n) *
        Complex.exp (-(Real.log (p : ℝ) : ℂ) *
          xiPhysicalApertureCharacterRate A n) := by
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- On a packet whose intervals do not meet either aperture edge, the complete character
amplitude is one common rectangular multiplier times one scalar twisted prime sum. -/
theorem xiPhysicalPrimeLogCharacterAmplitude_eq_bulk_twistedSum
    (P : Finset Nat.Primes) {A m k : ℝ} (n : ℤ)
    (hbulk : ∀ p ∈ P,
      0 ≤ m - Real.log (p : ℝ) ∧ k - Real.log (p : ℝ) ≤ A)
    (hmk : m ≤ k) :
    xiPhysicalPrimeLogCharacterAmplitude P A n m k =
      Complex.exp ((k : ℂ) * xiPhysicalApertureCharacterRate A n) *
        rectangularWindowAmplitude (k - m)
          (xiPhysicalApertureCharacterRate A n) *
        xiPhysicalPrimeLogTwistedCharacterSum P A n := by
  rw [xiPhysicalPrimeLogCharacterAmplitude,
    xiPhysicalPrimeLogTwistedCharacterSum]
  calc
    (∑ p ∈ P, (physicalPrimeEndpointWeight p : ℂ) *
        xiPhysicalPrimeLogCharacterMoment A n m k p) =
        ∑ p ∈ P,
          (Complex.exp ((k : ℂ) * xiPhysicalApertureCharacterRate A n) *
              rectangularWindowAmplitude (k - m)
                (xiPhysicalApertureCharacterRate A n)) *
            ((physicalPrimeEndpointWeight p : ℂ) *
              Complex.exp (-(Real.log (p : ℝ) : ℂ) *
                xiPhysicalApertureCharacterRate A n)) := by
          apply Finset.sum_congr rfl
          intro p hp
          rw [xiPhysicalPrimeLogCharacterMoment_eq_bulk n p
            (hbulk p hp).1 (hbulk p hp).2 hmk,
            exp_bulk_character_eq_common_mul_twist]
          ring
    _ = Complex.exp ((k : ℂ) * xiPhysicalApertureCharacterRate A n) *
          rectangularWindowAmplitude (k - m)
            (xiPhysicalApertureCharacterRate A n) *
          ∑ p ∈ P, (physicalPrimeEndpointWeight p : ℂ) *
            Complex.exp (-(Real.log (p : ℝ) : ℂ) *
              xiPhysicalApertureCharacterRate A n) := by
          rw [Finset.mul_sum]

/-- **Exact bulk/edge channel decomposition.**  For a disjoint partition into bulk primes `B`
and clipped edge primes `E`, the physical amplitude is a common twisted-prime sum plus the exact
edge amplitude.  No edge is dropped or estimated. -/
theorem xiPhysicalPrimeLogCharacterAmplitude_union_eq_bulk_add_edge
    (B E : Finset Nat.Primes) (hBE : Disjoint B E)
    {A m k : ℝ} (n : ℤ)
    (hbulk : ∀ p ∈ B,
      0 ≤ m - Real.log (p : ℝ) ∧ k - Real.log (p : ℝ) ≤ A)
    (hmk : m ≤ k) :
    xiPhysicalPrimeLogCharacterAmplitude (B ∪ E) A n m k =
      Complex.exp ((k : ℂ) * xiPhysicalApertureCharacterRate A n) *
        rectangularWindowAmplitude (k - m)
          (xiPhysicalApertureCharacterRate A n) *
        xiPhysicalPrimeLogTwistedCharacterSum B A n +
      xiPhysicalPrimeLogCharacterAmplitude E A n m k := by
  rw [xiPhysicalPrimeLogCharacterAmplitude]
  rw [Finset.sum_union hBE]
  change xiPhysicalPrimeLogCharacterAmplitude B A n m k +
      xiPhysicalPrimeLogCharacterAmplitude E A n m k = _
  rw [xiPhysicalPrimeLogCharacterAmplitude_eq_bulk_twistedSum B n hbulk hmk]

/-! ## Complete character Parseval law -/

/-- The character amplitude including the centered zero channel.  This definition keeps the
constant channel in the same complete Fourier family; centering will force it to vanish. -/
def xiPhysicalPrimeLogCenteredCharacterAmplitude
    (P : Finset Nat.Primes) (A : ℝ) (n : ℤ) (m k : ℝ) : ℂ :=
  inner ℂ (xiPhysicalPrimeLogComplexAggregateApertureCarrier P A m k)
    (xiPhysicalApertureCharacter A n)

theorem xiPhysicalPrimeLogCenteredCharacterAmplitude_eq
    (P : Finset Nat.Primes) {A : ℝ} (hA : 0 < A)
    {n : ℤ} (hn : n ≠ 0) (m k : ℝ) :
    xiPhysicalPrimeLogCenteredCharacterAmplitude P A n m k =
      xiPhysicalPrimeLogCharacterAmplitude P A n m k := by
  exact inner_xiPhysicalPrimeLogComplexAggregate_character P hA hn m k

/-- The zero character is exactly the ambient aperture indicator. -/
theorem xiPhysicalApertureCharacter_zero (A : ℝ) :
    xiPhysicalApertureCharacter A 0 =
      xiPhysicalLogComplexApertureIndicator A := by
  apply Lp.ext
  filter_upwards [MemLp.coeFn_toLp
      (xiPhysicalApertureCharacterFun_memLp A 0),
    indicatorConstLp_coeFn (p := 2) (μ := (volume : Measure ℝ))
      (s := xiPhysicalLogApertureSet A) (hs := measurableSet_Ioc)
      (hμs := measure_xiPhysicalLogApertureSet_ne_top A) (c := (1 : ℂ))]
      with u hchar haperture
  rw [xiPhysicalApertureCharacter, hchar,
    xiPhysicalLogComplexApertureIndicator, haperture,
    xiPhysicalApertureCharacterFun, xiPhysicalApertureCharacterRate,
    xiPhysicalLogApertureSet]
  by_cases hu : u ∈ Ioc 0 A <;>
    simp [rectangularIntervalIndicator, hu]

theorem inner_xiPhysicalPrimeLogComplexCenteredApertureCarrier_aperture
    {A : ℝ} (hA : 0 < A) (m k : ℝ) (p : Nat.Primes) :
    inner ℂ (xiPhysicalPrimeLogComplexCenteredApertureCarrier A m k p)
      (xiPhysicalLogComplexApertureIndicator A) = 0 := by
  rw [xiPhysicalPrimeLogComplexCenteredApertureCarrier, inner_sub_left,
    inner_smul_left,
    inner_xiPhysicalPrimeLogComplexApertureIndicator_aperture,
    inner_xiPhysicalLogComplexApertureIndicator hA]
  simp only [Complex.conj_ofReal]
  push_cast
  field_simp [hA.ne']
  ring

/-- Centering removes the zero Fourier channel exactly. -/
theorem xiPhysicalPrimeLogCenteredCharacterAmplitude_zero
    (P : Finset Nat.Primes) {A : ℝ} (hA : 0 < A) (m k : ℝ) :
    xiPhysicalPrimeLogCenteredCharacterAmplitude P A 0 m k = 0 := by
  rw [xiPhysicalPrimeLogCenteredCharacterAmplitude,
    xiPhysicalApertureCharacter_zero,
    xiPhysicalPrimeLogComplexAggregateApertureCarrier, sum_inner]
  apply Finset.sum_eq_zero
  intro p hp
  rw [inner_smul_left,
    inner_xiPhysicalPrimeLogComplexCenteredApertureCarrier_aperture hA]
  simp

/-- A centered prime carrier vanishes almost everywhere outside the physical aperture. -/
theorem xiPhysicalPrimeLogComplexCenteredApertureCarrier_zero_outside
    (A m k : ℝ) (p : Nat.Primes) :
    ∀ᵐ u : ℝ ∂volume, u ∉ Ioc 0 A →
      (xiPhysicalPrimeLogComplexCenteredApertureCarrier A m k p : ℝ → ℂ) u = 0 := by
  filter_upwards [Lp.coeFn_sub
      (xiPhysicalPrimeLogComplexApertureIndicator A m k p)
      (((xiPhysicalPrimeLogApertureLength A m k p / A : ℝ) : ℂ) •
        xiPhysicalLogComplexApertureIndicator A),
    Lp.coeFn_smul
      ((xiPhysicalPrimeLogApertureLength A m k p / A : ℝ) : ℂ)
      (xiPhysicalLogComplexApertureIndicator A),
    indicatorConstLp_coeFn (p := 2) (μ := (volume : Measure ℝ))
      (s := xiPhysicalPrimeLogApertureSet A m k p) (hs := measurableSet_Ioc)
      (hμs := measure_xiPhysicalPrimeLogApertureSet_ne_top A m k p) (c := (1 : ℂ)),
    indicatorConstLp_coeFn (p := 2) (μ := (volume : Measure ℝ))
      (s := xiPhysicalLogApertureSet A) (hs := measurableSet_Ioc)
      (hμs := measure_xiPhysicalLogApertureSet_ne_top A) (c := (1 : ℂ))]
      with u hsub hsmul hprime haperture
  intro hu
  have hprimeOut : u ∉ xiPhysicalPrimeLogApertureSet A m k p :=
    fun hmem => hu (xiPhysicalPrimeLogApertureSet_subset A m k p hmem)
  rw [xiPhysicalPrimeLogComplexCenteredApertureCarrier, hsub]
  simp only [Pi.sub_apply]
  rw [hsmul]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [xiPhysicalPrimeLogComplexApertureIndicator, hprime,
    xiPhysicalLogComplexApertureIndicator, haperture,
    indicator_of_notMem hprimeOut]
  simp [xiPhysicalLogApertureSet, hu]

/-- The complete finite prime carrier is supported in the physical aperture. -/
theorem xiPhysicalPrimeLogComplexAggregateApertureCarrier_zero_outside
    (P : Finset Nat.Primes) (A m k : ℝ) :
    ∀ᵐ u : ℝ ∂volume, u ∉ Ioc 0 A →
      (xiPhysicalPrimeLogComplexAggregateApertureCarrier P A m k : ℝ → ℂ) u = 0 := by
  classical
  rw [xiPhysicalPrimeLogComplexAggregateApertureCarrier]
  induction P using Finset.induction_on with
  | empty => simp
  | @insert p P hp ih =>
      rw [Finset.sum_insert hp]
      filter_upwards [Lp.coeFn_add
          ((physicalPrimeEndpointWeight p : ℂ) •
            xiPhysicalPrimeLogComplexCenteredApertureCarrier A m k p)
          (∑ q ∈ P, (physicalPrimeEndpointWeight q : ℂ) •
            xiPhysicalPrimeLogComplexCenteredApertureCarrier A m k q),
        Lp.coeFn_smul (physicalPrimeEndpointWeight p : ℂ)
          (xiPhysicalPrimeLogComplexCenteredApertureCarrier A m k p),
        xiPhysicalPrimeLogComplexCenteredApertureCarrier_zero_outside A m k p,
        ih] with u hadd hsmul hpout hPout
      intro hu
      rw [hadd]
      simp only [Pi.add_apply]
      rw [hsmul]
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [hpout hu, hPout hu]
      simp

private theorem xiPhysicalComplexL2_norm_sq_eq_integral
    (f : XiPhysicalComplexApertureL2) :
    ‖f‖ ^ 2 = ∫ u : ℝ, ‖(f : ℝ → ℂ) u‖ ^ 2 := by
  have hinner := MeasureTheory.L2.inner_def (𝕜 := ℂ) f f
  rw [inner_self_eq_norm_sq_to_K] at hinner
  have hpoint : ∀ u : ℝ,
      inner ℂ ((f : ℝ → ℂ) u) ((f : ℝ → ℂ) u) =
        ((‖(f : ℝ → ℂ) u‖ ^ 2 : ℝ) : ℂ) := by
    intro u
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  simp_rw [hpoint] at hinner
  rw [integral_complex_ofReal] at hinner
  rw [← Complex.ofReal_inj, Complex.ofReal_pow]
  exact hinner

/-- The interval integral of the carrier's pointwise squared norm is its exact fusion energy. -/
theorem intervalIntegral_norm_sq_xiPhysicalPrimeLogComplexAggregateApertureCarrier
    (P : Finset Nat.Primes) {A : ℝ} (hA : 0 < A) (m k : ℝ) :
    (∫ u : ℝ in 0..A,
      ‖(xiPhysicalPrimeLogComplexAggregateApertureCarrier P A m k : ℝ → ℂ) u‖ ^ 2) =
        xiPhysicalPrimeLogApertureFusionEnergy P A m k := by
  let x := xiPhysicalPrimeLogComplexAggregateApertureCarrier P A m k
  rw [intervalIntegral.integral_of_le hA.le]
  calc
    (∫ u : ℝ in Ioc 0 A, ‖(x : ℝ → ℂ) u‖ ^ 2) =
        ∫ u : ℝ, ‖(x : ℝ → ℂ) u‖ ^ 2 := by
      rw [← integral_indicator measurableSet_Ioc]
      apply integral_congr_ae
      filter_upwards [xiPhysicalPrimeLogComplexAggregateApertureCarrier_zero_outside
          P A m k] with u hout
      by_cases hu : u ∈ Ioc 0 A
      · simp [hu]
      · rw [indicator_of_notMem hu, hout hu]
        simp
    _ = ‖x‖ ^ 2 := (xiPhysicalComplexL2_norm_sq_eq_integral x).symm
    _ = xiPhysicalPrimeLogApertureFusionEnergy P A m k := by
      exact (xiPhysicalPrimeLogApertureFusionEnergy_eq_complex_norm_sq P hA m k).symm

/-- Pointwise conjugate of the complete aperture carrier, used by the standard Fourier
coefficient convention. -/
def xiPhysicalPrimeLogAggregateConjugateFun
    (P : Finset Nat.Primes) (A m k : ℝ) (u : ℝ) : ℂ :=
  (starRingEnd ℂ)
    ((xiPhysicalPrimeLogComplexAggregateApertureCarrier P A m k : ℝ → ℂ) u)

theorem xiPhysicalPrimeLogAggregateConjugateFun_memLp
    (P : Finset Nat.Primes) (A m k : ℝ) :
    MemLp (xiPhysicalPrimeLogAggregateConjugateFun P A m k) 2
      (volume : Measure ℝ) := by
  change MemLp
    (star ((xiPhysicalPrimeLogComplexAggregateApertureCarrier P A m k :
      XiPhysicalComplexApertureL2) : ℝ → ℂ)) 2 (volume : Measure ℝ)
  exact (Lp.memLp
    (xiPhysicalPrimeLogComplexAggregateApertureCarrier P A m k)).star

theorem fourier_coe_eq_xiPhysicalApertureCharacterExp
    {A : ℝ} (hA : 0 < A) (n : ℤ) (u : ℝ) :
    fourier n (u : AddCircle A) =
      Complex.exp (xiPhysicalApertureCharacterRate A n * (u : ℂ)) := by
  rw [fourier_coe_apply]
  congr 1
  rw [xiPhysicalApertureCharacterRate]
  push_cast
  field_simp [hA.ne']

/-- Standard interval Fourier coefficients are precisely normalized centered CCM amplitudes. -/
theorem fourierCoeffOn_xiPhysicalPrimeLogAggregateConjugateFun
    (P : Finset Nat.Primes) {A : ℝ} (hA : 0 < A)
    (n : ℤ) (m k : ℝ) :
    fourierCoeffOn hA (xiPhysicalPrimeLogAggregateConjugateFun P A m k) (-n) =
      (1 / A : ℝ) • xiPhysicalPrimeLogCenteredCharacterAmplitude P A n m k := by
  rw [fourierCoeffOn_eq_integral]
  simp only [sub_zero, neg_neg]
  congr 1
  rw [xiPhysicalPrimeLogCenteredCharacterAmplitude, L2.inner_def,
    intervalIntegral.integral_of_le hA.le]
  rw [← integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp
      (xiPhysicalApertureCharacterFun_memLp A n)] with u hcharacter
  by_cases hu : u ∈ Ioc 0 A
  · rw [indicator_of_mem hu, xiPhysicalApertureCharacter, hcharacter,
      xiPhysicalApertureCharacterFun, rectangularIntervalIndicator,
      zero_add, indicator_of_mem hu]
    simp only [smul_eq_mul]
    have hA0 : 0 < A - 0 := by simpa using hA
    have hfourier : fourier n (u : AddCircle (A - 0)) =
        Complex.exp (xiPhysicalApertureCharacterRate A n * (u : ℂ)) :=
      calc
        fourier n (u : AddCircle (A - 0)) =
            Complex.exp
              (xiPhysicalApertureCharacterRate (A - 0) n * (u : ℂ)) :=
          fourier_coe_eq_xiPhysicalApertureCharacterExp hA0 n u
        _ = Complex.exp
              (xiPhysicalApertureCharacterRate A n * (u : ℂ)) := by simp
    rw [hfourier]
    simp only [Complex.ofReal_one, one_mul,
      xiPhysicalPrimeLogAggregateConjugateFun, RCLike.inner_apply]
  · rw [indicator_of_notMem hu, xiPhysicalApertureCharacter, hcharacter,
      xiPhysicalApertureCharacterFun, rectangularIntervalIndicator,
      zero_add, indicator_of_notMem hu]
    simp

/-- **Complete CCM character Parseval law.**  The exact physical prime fusion energy is neither
merely bounded below by selected channels nor able to hide cancellation between them: it is the
sum of all centered integer-character energies, with exact constant `A`. -/
theorem hasSum_normSq_xiPhysicalPrimeLogCenteredCharacterAmplitude_neg
    (P : Finset Nat.Primes) {A : ℝ} (hA : 0 < A) (m k : ℝ) :
    HasSum (fun n : ℤ =>
      Complex.normSq
        (xiPhysicalPrimeLogCenteredCharacterAmplitude P A (-n) m k))
      (A * xiPhysicalPrimeLogApertureFusionEnergy P A m k) := by
  let f := xiPhysicalPrimeLogAggregateConjugateFun P A m k
  have hf : MemLp f 2 (volume.restrict (Ioc 0 A)) :=
    (xiPhysicalPrimeLogAggregateConjugateFun_memLp P A m k).mono_measure
      Measure.restrict_le_self
  have hparseval := hasSum_sq_fourierCoeffOn hA hf
  have hnorm : (∫ u : ℝ in 0..A, ‖f u‖ ^ 2) =
      xiPhysicalPrimeLogApertureFusionEnergy P A m k := by
    simpa only [f, xiPhysicalPrimeLogAggregateConjugateFun,
      starRingEnd_apply, norm_star] using
      intervalIntegral_norm_sq_xiPhysicalPrimeLogComplexAggregateApertureCarrier P hA m k
  have hcoeff (n : ℤ) :
      fourierCoeffOn hA f n =
        (1 / A : ℝ) •
          xiPhysicalPrimeLogCenteredCharacterAmplitude P A (-n) m k := by
    simpa only [f, neg_neg] using
      (fourierCoeffOn_xiPhysicalPrimeLogAggregateConjugateFun P hA (-n) m k)
  have hterm (n : ℤ) :
      ‖fourierCoeffOn hA f n‖ ^ 2 =
        (1 / A) ^ 2 * Complex.normSq
          (xiPhysicalPrimeLogCenteredCharacterAmplitude P A (-n) m k) := by
    rw [hcoeff, norm_smul, Real.norm_eq_abs,
      abs_of_pos (one_div_pos.mpr hA), mul_pow, Complex.sq_norm]
  have hbase : HasSum (fun n : ℤ =>
      (1 / A) ^ 2 * Complex.normSq
        (xiPhysicalPrimeLogCenteredCharacterAmplitude P A (-n) m k))
      ((1 / A) * xiPhysicalPrimeLogApertureFusionEnergy P A m k) := by
    simp_rw [hterm] at hparseval
    rw [hnorm] at hparseval
    simpa only [sub_zero, smul_eq_mul, inv_eq_one_div] using hparseval
  have hscaled := hbase.mul_left (A ^ 2)
  have hfactor : A ^ 2 * (1 / A) ^ 2 = 1 := by
    field_simp [hA.ne']
  have hvalue : A ^ 2 * (1 / A) = A := by
    field_simp [hA.ne']
  simpa only [← mul_assoc, hfactor, hvalue, one_mul] using hscaled

/-- Tsum form of the complete CCM character Parseval law. -/
theorem tsum_normSq_xiPhysicalPrimeLogCenteredCharacterAmplitude
    (P : Finset Nat.Primes) {A : ℝ} (hA : 0 < A) (m k : ℝ) :
    (∑' n : ℤ,
      Complex.normSq
        (xiPhysicalPrimeLogCenteredCharacterAmplitude P A n m k)) =
      A * xiPhysicalPrimeLogApertureFusionEnergy P A m k := by
  calc
    (∑' n : ℤ, Complex.normSq
        (xiPhysicalPrimeLogCenteredCharacterAmplitude P A n m k)) =
        ∑' n : ℤ, Complex.normSq
          (xiPhysicalPrimeLogCenteredCharacterAmplitude P A (-n) m k) :=
      ((Equiv.neg ℤ).tsum_eq (fun n : ℤ => Complex.normSq
        (xiPhysicalPrimeLogCenteredCharacterAmplitude P A n m k))).symm
    _ = A * xiPhysicalPrimeLogApertureFusionEnergy P A m k :=
      (hasSum_normSq_xiPhysicalPrimeLogCenteredCharacterAmplitude_neg P hA m k).tsum_eq

/-- The zero mode removed, Parseval becomes an exact sum of the explicit clipped prime
amplitudes.  This is the arithmetic form of the complete character law. -/
theorem tsum_normSq_xiPhysicalPrimeLogCharacterAmplitude
    (P : Finset Nat.Primes) {A : ℝ} (hA : 0 < A) (m k : ℝ) :
    (∑' n : {n : ℤ // n ≠ 0},
      Complex.normSq
        (xiPhysicalPrimeLogCharacterAmplitude P A n m k)) =
      A * xiPhysicalPrimeLogApertureFusionEnergy P A m k := by
  let F : ℤ → ℝ := fun n => Complex.normSq
    (xiPhysicalPrimeLogCenteredCharacterAmplitude P A n m k)
  let S : Set ℤ := {n | n ≠ 0}
  have hneg : Summable (F ∘ (Equiv.neg ℤ)) := by
    change Summable (fun n : ℤ => F (-n))
    simpa only [F] using
      (hasSum_normSq_xiPhysicalPrimeLogCenteredCharacterAmplitude_neg P hA m k).summable
  have hsum : Summable F := ((Equiv.neg ℤ).summable_iff).mp hneg
  have hsplit := hsum.tsum_subtype_add_tsum_subtype_compl S
  have hcomp : (∑' n : (Sᶜ : Set ℤ), F n) = 0 := by
    have hz : ∀ n : (Sᶜ : Set ℤ), F n = 0 := by
      intro n
      have hn : (n : ℤ) = 0 := by
        simpa only [S, Set.mem_compl_iff, Set.mem_setOf_eq, not_ne_iff] using n.property
      simp only [F]
      rw [hn, xiPhysicalPrimeLogCenteredCharacterAmplitude_zero P hA]
      exact Complex.normSq_zero
    simp only [hz, tsum_zero]
  have hsub : (∑' n : S, F n) = ∑' n : ℤ, F n := by
    rw [hcomp, add_zero] at hsplit
    exact hsplit
  calc
    (∑' n : {n : ℤ // n ≠ 0},
        Complex.normSq
          (xiPhysicalPrimeLogCharacterAmplitude P A n m k)) =
        ∑' n : S, F n := by
      apply tsum_congr
      intro n
      simp only [F, xiPhysicalPrimeLogCenteredCharacterAmplitude_eq P hA n.property]
    _ = ∑' n : ℤ, F n := hsub
    _ = A * xiPhysicalPrimeLogApertureFusionEnergy P A m k := by
      simpa only [F] using
        tsum_normSq_xiPhysicalPrimeLogCenteredCharacterAmplitude P hA m k

/-- **Bulk twisted-prime Parseval law.**  When every interval avoids the aperture edges, the
entire physical fusion energy is exactly the all-character squared energy of one scalar twisted
prime sum multiplied by the common rectangular transfer function. -/
theorem tsum_normSq_bulkTwistedSum_eq_energy
    (P : Finset Nat.Primes) {A m k : ℝ} (hA : 0 < A)
    (hbulk : ∀ p ∈ P,
      0 ≤ m - Real.log (p : ℝ) ∧ k - Real.log (p : ℝ) ≤ A)
    (hmk : m ≤ k) :
    (∑' n : {n : ℤ // n ≠ 0}, Complex.normSq
      (Complex.exp ((k : ℂ) * xiPhysicalApertureCharacterRate A n) *
        rectangularWindowAmplitude (k - m)
          (xiPhysicalApertureCharacterRate A n) *
        xiPhysicalPrimeLogTwistedCharacterSum P A n)) =
      A * xiPhysicalPrimeLogApertureFusionEnergy P A m k := by
  rw [← tsum_normSq_xiPhysicalPrimeLogCharacterAmplitude P hA m k]
  apply tsum_congr
  intro n
  rw [xiPhysicalPrimeLogCharacterAmplitude_eq_bulk_twistedSum P n hbulk hmk]

/-- **Exact bulk/edge Parseval law.**  For every disjoint physical partition, all possible CCM
cancellation is exhausted by the displayed sum of a scalar bulk twisted-prime channel and the
exact clipped-edge channel.  No residual Hilbert-space term remains. -/
theorem tsum_normSq_bulk_add_edge_eq_energy
    (B E : Finset Nat.Primes) (hBE : Disjoint B E)
    {A m k : ℝ} (hA : 0 < A)
    (hbulk : ∀ p ∈ B,
      0 ≤ m - Real.log (p : ℝ) ∧ k - Real.log (p : ℝ) ≤ A)
    (hmk : m ≤ k) :
    (∑' n : {n : ℤ // n ≠ 0}, Complex.normSq
      (Complex.exp ((k : ℂ) * xiPhysicalApertureCharacterRate A n) *
          rectangularWindowAmplitude (k - m)
            (xiPhysicalApertureCharacterRate A n) *
          xiPhysicalPrimeLogTwistedCharacterSum B A n +
        xiPhysicalPrimeLogCharacterAmplitude E A n m k)) =
      A * xiPhysicalPrimeLogApertureFusionEnergy (B ∪ E) A m k := by
  rw [← tsum_normSq_xiPhysicalPrimeLogCharacterAmplitude (B ∪ E) hA m k]
  apply tsum_congr
  intro n
  rw [xiPhysicalPrimeLogCharacterAmplitude_union_eq_bulk_add_edge
    B E hBE n hbulk hmk]

end

end RHTower
