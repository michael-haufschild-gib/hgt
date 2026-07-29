import GaloisForLFunctions.RHTower.InfiniteJetQuantumRecurrenceSeparationLaw
import GaloisForLFunctions.RHTower.SummablePurePointPhaseRecurrence
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# Positive-energy infinite-jet recurrence separation

An explicit lognormal probability spectrum and an explicit geometric-lattice
probability spectrum have the same moment of every natural order.  Their
characteristic functions therefore have the same complete Taylor jet at time
zero.  Both spectra are carried by strictly positive energies, but the
geometric-lattice spectrum has persistent mean recurrence whereas the
lognormal spectrum has vanishing mean recurrence and zero density at every
positive return threshold.
-/

open Filter MeasureTheory Set
open scoped BigOperators ENNReal Topology

noncomputable section

namespace RHTower

/-- Gaussian weight on the integer logarithmic-energy lattice. -/
def integerLogGaussianWeight (v : NNReal) (k : ℤ) : ℝ :=
  Real.exp (-((v : ℝ) * (k : ℝ) ^ 2) / 2)

/-- Partition function of the integer logarithmic-energy Gaussian. -/
def integerLogGaussianPartition (v : NNReal) : ℝ :=
  ∑' k : ℤ, integerLogGaussianWeight v k

/-- Positive geometric energy lattice. -/
def geometricEnergy (v : NNReal) (k : ℤ) : ℝ :=
  Real.exp ((v : ℝ) * (k : ℝ))

/-- Normalized Gaussian weight on the integer logarithmic-energy lattice. -/
def normalizedIntegerLogGaussianWeight (v : NNReal) (k : ℤ) : ℝ :=
  integerLogGaussianWeight v k / integerLogGaussianPartition v

theorem integerLogGaussianWeight_pos (v : NNReal) (k : ℤ) :
    0 < integerLogGaussianWeight v k :=
  Real.exp_pos _

theorem geometricEnergy_pos (v : NNReal) (k : ℤ) :
    0 < geometricEnergy v k :=
  Real.exp_pos _

/-- The integer Gaussian partition function converges at every positive
variance. -/
theorem summable_integerLogGaussianWeight {v : NNReal} (hv : 0 < v) :
    Summable (integerLogGaussianWeight v) := by
  rw [summable_int_iff_summable_nat_and_neg]
  have hvR : 0 < (v : ℝ) := by exact_mod_cast hv
  have hr0 : 0 ≤ Real.exp (-(v : ℝ) / 2) :=
    (Real.exp_pos _).le
  have hr1 : Real.exp (-(v : ℝ) / 2) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have hgeom :
      Summable (fun n : ℕ => (Real.exp (-(v : ℝ) / 2)) ^ n) :=
    summable_geometric_of_lt_one hr0 hr1
  have hnat :
      Summable
        (fun n : ℕ =>
          Real.exp (-((v : ℝ) * (n : ℝ) ^ 2) / 2)) := by
    refine Summable.of_nonneg_of_le (fun n => (Real.exp_pos _).le) (fun n => ?_) hgeom
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have hn : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
      cases n with
      | zero => norm_num
      | succ n =>
          have h1 : (1 : ℝ) ≤ (n.succ : ℕ) := by exact_mod_cast n.succ_pos
          nlinarith
    have hmul :
        0 ≤ (v : ℝ) * ((n : ℝ) ^ 2 - (n : ℝ)) :=
      mul_nonneg hvR.le (sub_nonneg.mpr hn)
    nlinarith
  constructor
  · simpa [integerLogGaussianWeight] using hnat
  · simpa [integerLogGaussianWeight] using hnat

theorem integerLogGaussianPartition_pos {v : NNReal} (hv : 0 < v) :
    0 < integerLogGaussianPartition v := by
  exact (summable_integerLogGaussianWeight hv).tsum_pos
    (fun k => (integerLogGaussianWeight_pos v k).le) 0
    (integerLogGaussianWeight_pos v 0)

theorem summable_normalizedIntegerLogGaussianWeight {v : NNReal} (hv : 0 < v) :
    Summable (normalizedIntegerLogGaussianWeight v) := by
  simpa [normalizedIntegerLogGaussianWeight, div_eq_mul_inv] using
    (summable_integerLogGaussianWeight hv).mul_right
      (integerLogGaussianPartition v)⁻¹

theorem hasSum_normalizedIntegerLogGaussianWeight_one {v : NNReal} (hv : 0 < v) :
    HasSum (normalizedIntegerLogGaussianWeight v) 1 := by
  have hZne := (integerLogGaussianPartition_pos hv).ne'
  have hscaled :=
    (summable_integerLogGaussianWeight hv).hasSum.mul_right
      (integerLogGaussianPartition v)⁻¹
  convert hscaled using 1
  rw [← integerLogGaussianPartition]
  exact (mul_inv_cancel₀ hZne).symm

theorem normalizedIntegerLogGaussianWeight_nonneg {v : NNReal} (hv : 0 < v) (k : ℤ) :
    0 ≤ normalizedIntegerLogGaussianWeight v k := by
  exact div_nonneg (integerLogGaussianWeight_pos v k).le
    (integerLogGaussianPartition_pos hv).le

/-- Probability spectrum on the positive geometric lattice. -/
def positiveGeometricSpectrum (v : NNReal) (hv : 0 < v) :
    ProbabilityMeasure ℝ :=
  ⟨Measure.sum fun k : ℤ =>
      ENNReal.ofReal (normalizedIntegerLogGaussianWeight v k) •
        Measure.dirac (geometricEnergy v k),
    HasSum.isProbabilityMeasure_sum_dirac
      (normalizedIntegerLogGaussianWeight_nonneg hv)
      (hasSum_normalizedIntegerLogGaussianWeight_one hv)⟩

/-- Lognormal probability spectrum: exponential pushforward of a centered
Gaussian in logarithmic energy. -/
def positiveLognormalSpectrum (v : NNReal) :
    ProbabilityMeasure ℝ :=
  ⟨(ProbabilityTheory.gaussianReal 0 v).map Real.exp,
    Measure.isProbabilityMeasure_map (by fun_prop)⟩

/-- Completing the square translates the integer lattice, so every
unnormalized energy moment is the Gaussian moment times the same partition
function. -/
theorem tsum_integerLogGaussianWeight_mul_geometricEnergy_pow
    {v : NNReal} (hv : 0 < v) (n : ℕ) :
    ∑' k : ℤ,
        integerLogGaussianWeight v k * geometricEnergy v k ^ n =
      Real.exp ((v : ℝ) * (n : ℝ) ^ 2 / 2) *
        integerLogGaussianPartition v := by
  have hpoint :
      ∀ k : ℤ,
        integerLogGaussianWeight v k * geometricEnergy v k ^ n =
          Real.exp ((v : ℝ) * (n : ℝ) ^ 2 / 2) *
            integerLogGaussianWeight v (k - (n : ℤ)) := by
    intro k
    simp only [integerLogGaussianWeight, geometricEnergy]
    rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
    congr 1
    push_cast
    ring
  have hshift :
      Summable
        (fun k : ℤ =>
          integerLogGaussianWeight v (k - (n : ℤ))) :=
    (Equiv.subRight (n : ℤ)).summable_iff.mpr
      (summable_integerLogGaussianWeight hv)
  calc
    ∑' k : ℤ,
        integerLogGaussianWeight v k * geometricEnergy v k ^ n =
        ∑' k : ℤ,
          Real.exp ((v : ℝ) * (n : ℝ) ^ 2 / 2) *
            integerLogGaussianWeight v (k - (n : ℤ)) :=
      tsum_congr hpoint
    _ = Real.exp ((v : ℝ) * (n : ℝ) ^ 2 / 2) *
          ∑' k : ℤ, integerLogGaussianWeight v (k - (n : ℤ)) :=
      hshift.tsum_mul_left _
    _ = Real.exp ((v : ℝ) * (n : ℝ) ^ 2 / 2) *
          integerLogGaussianPartition v := by
      rw [integerLogGaussianPartition]
      congr 1
      exact (Equiv.subRight (n : ℤ)).tsum_eq
        (integerLogGaussianWeight v)

theorem summable_normalizedIntegerLogGaussianWeight_mul_geometricEnergy_pow
    {v : NNReal} (hv : 0 < v) (n : ℕ) :
    Summable
      (fun k : ℤ =>
        normalizedIntegerLogGaussianWeight v k *
          geometricEnergy v k ^ n) := by
  have hpoint :
      ∀ k : ℤ,
        integerLogGaussianWeight v k * geometricEnergy v k ^ n =
          Real.exp ((v : ℝ) * (n : ℝ) ^ 2 / 2) *
            integerLogGaussianWeight v (k - (n : ℤ)) := by
    intro k
    simp only [integerLogGaussianWeight, geometricEnergy]
    rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
    congr 1
    push_cast
    ring
  have hshift :
      Summable
        (fun k : ℤ =>
          Real.exp ((v : ℝ) * (n : ℝ) ^ 2 / 2) *
            integerLogGaussianWeight v (k - (n : ℤ))) := by
    exact ((Equiv.subRight (n : ℤ)).summable_iff.mpr
      (summable_integerLogGaussianWeight hv)).mul_left
      (Real.exp ((v : ℝ) * (n : ℝ) ^ 2 / 2))
  have hraw :
      Summable
        (fun k : ℤ =>
          integerLogGaussianWeight v k *
            geometricEnergy v k ^ n) := by
    exact hshift.congr (fun k => (hpoint k).symm)
  apply (hraw.mul_right (integerLogGaussianPartition v)⁻¹).congr
  intro k
  rw [normalizedIntegerLogGaussianWeight]
  ring

/-- Every natural energy moment of the discrete positive spectrum has the
closed lognormal value. -/
theorem integral_pow_positiveGeometricSpectrum
    {v : NNReal} (hv : 0 < v) (n : ℕ) :
    ∫ x : ℝ, x ^ n ∂(positiveGeometricSpectrum v hv : Measure ℝ) =
      Real.exp ((v : ℝ) * (n : ℝ) ^ 2 / 2) := by
  let mu : Measure ℝ :=
    Measure.sum fun k : ℤ =>
      ENNReal.ofReal (normalizedIntegerLogGaussianWeight v k) •
        Measure.dirac (geometricEnergy v k)
  have hint :
      Integrable (fun x : ℝ => x ^ n) mu := by
    apply integrable_sum_dirac
    · intro k
      exact ENNReal.ofReal_ne_top
    · convert
        (summable_normalizedIntegerLogGaussianWeight_mul_geometricEnergy_pow hv n)
      using 1
      funext k
      rw [ENNReal.toReal_ofReal
        (normalizedIntegerLogGaussianWeight_nonneg hv k),
        Real.norm_eq_abs, abs_pow,
        abs_of_pos (geometricEnergy_pos v k)]
  change ∫ x : ℝ, x ^ n ∂mu = _
  rw [integral_sum_dirac (fun k => ENNReal.ofReal_ne_top)]
  simp_rw [ENNReal.toReal_ofReal
    (normalizedIntegerLogGaussianWeight_nonneg hv _), smul_eq_mul]
  have hraw :
      Summable
        (fun k : ℤ =>
          integerLogGaussianWeight v k *
            geometricEnergy v k ^ n) := by
    have hnorm :=
      summable_normalizedIntegerLogGaussianWeight_mul_geometricEnergy_pow hv n
    have hZpos := integerLogGaussianPartition_pos hv
    apply
      (hnorm.mul_right (integerLogGaussianPartition v)).congr
    intro k
    rw [normalizedIntegerLogGaussianWeight]
    field_simp
  have hnormalizedTsum :
      (∑' k : ℤ,
        normalizedIntegerLogGaussianWeight v k *
          geometricEnergy v k ^ n) =
        (∑' k : ℤ,
          integerLogGaussianWeight v k *
            geometricEnergy v k ^ n) *
          (integerLogGaussianPartition v)⁻¹ := by
    calc
      _ = ∑' k : ℤ,
          (integerLogGaussianWeight v k *
            geometricEnergy v k ^ n) *
              (integerLogGaussianPartition v)⁻¹ := by
        apply tsum_congr
        intro k
        rw [normalizedIntegerLogGaussianWeight]
        ring
      _ = _ := hraw.tsum_mul_right _
  rw [hnormalizedTsum,
    tsum_integerLogGaussianWeight_mul_geometricEnergy_pow hv n]
  simp [(integerLogGaussianPartition_pos hv).ne']

/-- Every natural energy moment of the continuous positive spectrum has the
same closed lognormal value. -/
theorem integral_pow_positiveLognormalSpectrum
    (v : NNReal) (n : ℕ) :
    ∫ x : ℝ, x ^ n ∂(positiveLognormalSpectrum v : Measure ℝ) =
      Real.exp ((v : ℝ) * (n : ℝ) ^ 2 / 2) := by
  change
    ∫ x : ℝ, x ^ n
        ∂(ProbabilityTheory.gaussianReal 0 v).map Real.exp =
      _
  rw [integral_map (by fun_prop) (by fun_prop)]
  have hmgf :=
    congrFun
      (ProbabilityTheory.mgf_fun_id_gaussianReal
        (μ := 0) (v := v))
      (n : ℝ)
  rw [ProbabilityTheory.mgf] at hmgf
  simpa [← Real.exp_nat_mul, mul_comm] using hmgf

/-- All polynomial energy observables are integrable for the discrete
positive spectrum. -/
theorem integrable_pow_positiveGeometricSpectrum
    {v : NNReal} (hv : 0 < v) (n : ℕ) :
    Integrable (fun x : ℝ => x ^ n)
      (positiveGeometricSpectrum v hv : Measure ℝ) := by
  change
    Integrable (fun x : ℝ => x ^ n)
      (Measure.sum fun k : ℤ =>
        ENNReal.ofReal (normalizedIntegerLogGaussianWeight v k) •
          Measure.dirac (geometricEnergy v k))
  apply integrable_sum_dirac
  · intro k
    exact ENNReal.ofReal_ne_top
  · convert
      (summable_normalizedIntegerLogGaussianWeight_mul_geometricEnergy_pow hv n)
    using 1
    funext k
    rw [ENNReal.toReal_ofReal
      (normalizedIntegerLogGaussianWeight_nonneg hv k),
      Real.norm_eq_abs, abs_pow,
      abs_of_pos (geometricEnergy_pos v k)]

/-- All polynomial energy observables are integrable for the continuous
positive spectrum. -/
theorem integrable_pow_positiveLognormalSpectrum
    (v : NNReal) (n : ℕ) :
    Integrable (fun x : ℝ => x ^ n)
      (positiveLognormalSpectrum v : Measure ℝ) := by
  change
    Integrable (fun x : ℝ => x ^ n)
      ((ProbabilityTheory.gaussianReal 0 v).map Real.exp)
  apply
    (integrable_map_measure (by fun_prop) (by fun_prop)).mpr
  convert
    ProbabilityTheory.integrable_exp_mul_gaussianReal
      (μ := 0) (v := v) (n : ℝ)
    using 1
  funext x
  simp only [Function.comp_apply]
  rw [← Real.exp_nat_mul]

/-- Shared Stieltjes--Wigert moment sequence of the two positive spectra. -/
def positiveRecurrenceSeparationMoments
    (v : NNReal) (n : ℕ) : ℝ :=
  Real.exp ((v : ℝ) * (n : ℝ) ^ 2 / 2)

theorem positiveGeometricSpectrum_hasHamburgerMoments
    {v : NNReal} (hv : 0 < v) :
    GaloisForLFunctions.HTGeometry.HasHamburgerMoments
      (positiveRecurrenceSeparationMoments v)
      (positiveGeometricSpectrum v hv : Measure ℝ) := by
  intro n
  exact
    ⟨integrable_pow_positiveGeometricSpectrum hv n,
      integral_pow_positiveGeometricSpectrum hv n⟩

theorem positiveLognormalSpectrum_hasHamburgerMoments
    (v : NNReal) :
    GaloisForLFunctions.HTGeometry.HasHamburgerMoments
      (positiveRecurrenceSeparationMoments v)
      (positiveLognormalSpectrum v : Measure ℝ) := by
  intro n
  exact
    ⟨integrable_pow_positiveLognormalSpectrum v n,
      integral_pow_positiveLognormalSpectrum v n⟩

/-- The discrete and continuous positive-energy survival amplitudes have the
same derivative of every natural order at the initial instant. -/
theorem allLocalDerivativesEqual_positiveSpectra
    {v : NNReal} (hv : 0 < v) (n : ℕ) :
    iteratedDeriv n
        (charFun (positiveGeometricSpectrum v hv : Measure ℝ)) 0 =
      iteratedDeriv n
        (charFun (positiveLognormalSpectrum v : Measure ℝ)) 0 := by
  exact
    iteratedDeriv_charFun_zero_eq_of_hasHamburgerMoments
      (positiveGeometricSpectrum_hasHamburgerMoments hv)
      (positiveLognormalSpectrum_hasHamburgerMoments v) n

/-- The discrete spectrum assigns no mass to nonpositive energies. -/
theorem positiveGeometricSpectrum_Iic_zero
    {v : NNReal} (hv : 0 < v) :
    (positiveGeometricSpectrum v hv : Measure ℝ) (Iic 0) = 0 := by
  change
    (Measure.sum fun k : ℤ =>
      ENNReal.ofReal (normalizedIntegerLogGaussianWeight v k) •
        Measure.dirac (geometricEnergy v k)) (Iic 0) = 0
  rw [Measure.sum_apply _ measurableSet_Iic]
  simp [Measure.smul_apply, Measure.dirac_apply',
    not_le.mpr (geometricEnergy_pos v _)]

/-- The lognormal spectrum assigns no mass to nonpositive energies. -/
theorem positiveLognormalSpectrum_Iic_zero
    (v : NNReal) :
    (positiveLognormalSpectrum v : Measure ℝ) (Iic 0) = 0 := by
  change
    (ProbabilityTheory.gaussianReal 0 v).map Real.exp (Iic 0) = 0
  rw [Measure.map_apply_of_aemeasurable (by fun_prop) measurableSet_Iic]
  have hpre : Real.exp ⁻¹' Iic (0 : ℝ) = ∅ := by
    ext x
    simp [not_le.mpr (Real.exp_pos x)]
  rw [hpre, measure_empty]

/-- The lognormal spectrum is atomless at every positive variance. -/
theorem noAtoms_positiveLognormalSpectrum
    {v : NNReal} (hv : 0 < v) :
    NoAtoms (positiveLognormalSpectrum v : Measure ℝ) := by
  have hvne : v ≠ 0 := ne_of_gt hv
  letI : NoAtoms (ProbabilityTheory.gaussianReal 0 v) :=
    ProbabilityTheory.noAtoms_gaussianReal hvne
  constructor
  intro x
  change
    (ProbabilityTheory.gaussianReal 0 v).map Real.exp {x} = 0
  rw [Measure.map_apply_of_aemeasurable
    (by fun_prop) (measurableSet_singleton x)]
  exact
    ((Set.countable_singleton x).preimage
      Real.exp_injective).measure_zero _

theorem normalizedIntegerLogGaussianWeight_pos
    {v : NNReal} (hv : 0 < v) (k : ℤ) :
    0 < normalizedIntegerLogGaussianWeight v k :=
  div_pos (integerLogGaussianWeight_pos v k)
    (integerLogGaussianPartition_pos hv)

/-- The discrete positive spectrum has a strictly positive atom. -/
theorem positiveGeometricSpectrum_atom_pos
    {v : NNReal} (hv : 0 < v) :
    0 <
      (positiveGeometricSpectrum v hv : Measure ℝ)
        {geometricEnergy v 0} := by
  let family : ℤ → Measure ℝ := fun k =>
    ENNReal.ofReal (normalizedIntegerLogGaussianWeight v k) •
      Measure.dirac (geometricEnergy v k)
  have hmass :
      0 < family 0 {geometricEnergy v 0} := by
    simp [family, ENNReal.ofReal_pos.mpr
      (normalizedIntegerLogGaussianWeight_pos hv 0)]
  exact hmass.trans_le
    ((Measure.le_sum family 0) {geometricEnergy v 0})

theorem not_noAtoms_positiveGeometricSpectrum
    {v : NNReal} (hv : 0 < v) :
    ¬NoAtoms (positiveGeometricSpectrum v hv : Measure ℝ) := by
  intro hno
  letI : NoAtoms (positiveGeometricSpectrum v hv : Measure ℝ) :=
    hno
  exact
    (ne_of_gt (positiveGeometricSpectrum_atom_pos hv))
      (measure_singleton (geometricEnergy v 0))

/-- Natural-number enumeration of the geometric spectrum's weights. -/
def enumeratedPositiveGeometricWeight
    (v : NNReal) (n : ℕ) : ℝ :=
  normalizedIntegerLogGaussianWeight v
    (Equiv.intEquivNat.symm n)

/-- Natural-number enumeration of the geometric spectrum's energies. -/
def enumeratedPositiveGeometricEnergy
    (v : NNReal) (n : ℕ) : ℝ :=
  geometricEnergy v (Equiv.intEquivNat.symm n)

theorem enumeratedPositiveGeometricWeight_nonneg
    {v : NNReal} (hv : 0 < v) (n : ℕ) :
    0 ≤ enumeratedPositiveGeometricWeight v n :=
  normalizedIntegerLogGaussianWeight_nonneg hv _

theorem summable_enumeratedPositiveGeometricWeight
    {v : NNReal} (hv : 0 < v) :
    Summable (enumeratedPositiveGeometricWeight v) := by
  exact
    Equiv.intEquivNat.symm.summable_iff.mpr
      (summable_normalizedIntegerLogGaussianWeight hv)

/-- The discrete positive-energy clock returns arbitrarily close to its
initial full pure state at arbitrarily late integer times. -/
theorem exists_arbitrarilyLate_positiveGeometricPhaseRecurrence
    {v : NNReal} (hv : 0 < v)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (N : ℕ) :
    ∃ t : ℕ, N ≤ t ∧
      summablePhaseEnergy
        (enumeratedPositiveGeometricWeight v)
        (enumeratedPositiveGeometricEnergy v) t < epsilon := by
  let M : ℕ := max 1 N
  let scaledEnergy : ℕ → ℝ := fun p =>
    (M : ℝ) * enumeratedPositiveGeometricEnergy v p
  obtain ⟨n, hn, hreturn⟩ :=
    exists_summablePhaseEnergy_recurrence
      (enumeratedPositiveGeometricWeight v)
      scaledEnergy
      (enumeratedPositiveGeometricWeight_nonneg hv)
      (summable_enumeratedPositiveGeometricWeight hv)
      hepsilon
  refine ⟨M * n, ?_, ?_⟩
  · have hNM : N ≤ M := le_max_right 1 N
    have hn1 : 1 ≤ n := hn
    exact hNM.trans (by nlinarith)
  · rw [summablePhaseEnergy] at hreturn ⊢
    convert hreturn using 1
    apply tsum_congr
    intro p
    dsimp only [scaledEnergy]
    congr 4
    push_cast
    ring

/-- Complete positive-energy local-time data with incompatible global
recurrence phases. -/
structure PositiveEnergyInfiniteJetRecurrenceSeparation
    (v : NNReal) (hv : 0 < v) where
  allEnergyMomentsEqual :
    ∀ n : ℕ,
      (∫ x : ℝ, x ^ n
        ∂(positiveGeometricSpectrum v hv : Measure ℝ)) =
      ∫ x : ℝ, x ^ n
        ∂(positiveLognormalSpectrum v : Measure ℝ)
  allLocalDerivativesEqual :
    ∀ n : ℕ,
      iteratedDeriv n
          (charFun
            (positiveGeometricSpectrum v hv : Measure ℝ)) 0 =
        iteratedDeriv n
          (charFun
            (positiveLognormalSpectrum v : Measure ℝ)) 0
  discretePositiveEnergy :
    (positiveGeometricSpectrum v hv : Measure ℝ) (Iic 0) = 0
  continuousPositiveEnergy :
    (positiveLognormalSpectrum v : Measure ℝ) (Iic 0) = 0
  discreteCollisionMassPositive :
    0 <
      (spectralDifferenceMeasure
        (positiveGeometricSpectrum v hv : Measure ℝ)).real {0}
  discreteMeanReturn :
    Tendsto
      (spectralReturnMeanReal
        (positiveGeometricSpectrum v hv : Measure ℝ))
      atTop
      (𝓝
        ((spectralDifferenceMeasure
          (positiveGeometricSpectrum v hv : Measure ℝ)).real {0}))
  discreteArbitrarilyLateFullRecurrence :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ N : ℕ,
      ∃ t : ℕ, N ≤ t ∧
        summablePhaseEnergy
          (enumeratedPositiveGeometricWeight v)
          (enumeratedPositiveGeometricEnergy v) t < epsilon
  continuousTemporalDimension :
    SpectralMemory.measureTemporalDimension
      (positiveLognormalSpectrum v : Measure ℝ) =
        Cardinal.continuum
  continuousMeanReturn :
    Tendsto
      (spectralReturnMeanReal
        (positiveLognormalSpectrum v : Measure ℝ))
      atTop (𝓝 0)
  continuousPositiveThresholdDensity :
    ∀ eta : ℝ, 0 < eta →
      Tendsto
        (highFidelityWindowDensity
          (positiveLognormalSpectrum v : Measure ℝ) eta)
        atTop (𝓝 0)

/-- **Positive-energy infinite-jet recurrence separation law.**  At every
positive log-energy variance, two strictly positive probability spectra have
the same complete local survival jet but opposite global mean-recurrence
phases. -/
theorem positiveEnergyInfiniteJetRecurrenceSeparation
    (v : NNReal) (hv : 0 < v) :
    PositiveEnergyInfiniteJetRecurrenceSeparation v hv := by
  have hdiscreteNotNoAtoms :=
    not_noAtoms_positiveGeometricSpectrum hv
  have hcollisionNe :
      spectralDifferenceMeasure
          (positiveGeometricSpectrum v hv : Measure ℝ) {0} ≠ 0 := by
    intro hzero
    exact hdiscreteNotNoAtoms
      ((spectralDifferenceMeasure_singleton_zero_iff_noAtoms
        (positiveGeometricSpectrum v hv : Measure ℝ)).mp hzero)
  have hcollisionPositive :
      0 <
        (spectralDifferenceMeasure
          (positiveGeometricSpectrum v hv : Measure ℝ)).real {0} := by
    rw [Measure.real]
    exact ENNReal.toReal_pos hcollisionNe
      (measure_ne_top _ _)
  have hcontinuousNoAtoms :=
    noAtoms_positiveLognormalSpectrum hv
  letI : NoAtoms (positiveLognormalSpectrum v : Measure ℝ) :=
    hcontinuousNoAtoms
  exact {
    allEnergyMomentsEqual := fun n =>
      (integral_pow_positiveGeometricSpectrum hv n).trans
        (integral_pow_positiveLognormalSpectrum v n).symm
    allLocalDerivativesEqual :=
      allLocalDerivativesEqual_positiveSpectra hv
    discretePositiveEnergy :=
      positiveGeometricSpectrum_Iic_zero hv
    continuousPositiveEnergy :=
      positiveLognormalSpectrum_Iic_zero v
    discreteCollisionMassPositive :=
      hcollisionPositive
    discreteMeanReturn :=
      spectralReturnMeanReal_tendsto_collision
        (positiveGeometricSpectrum v hv : Measure ℝ)
    discreteArbitrarilyLateFullRecurrence :=
      fun epsilon hepsilon N =>
        exists_arbitrarilyLate_positiveGeometricPhaseRecurrence
          hv hepsilon N
    continuousTemporalDimension :=
      SpectralMemory.measureTemporalDimension_eq_continuum_of_noAtoms
        (positiveLognormalSpectrum v : Measure ℝ)
    continuousMeanReturn :=
      spectralReturnMeanReal_tendsto_zero_of_noAtoms
        (positiveLognormalSpectrum v : Measure ℝ)
    continuousPositiveThresholdDensity := fun eta heta =>
      highFidelityWindowDensity_tendsto_zero_of_noAtoms
        (positiveLognormalSpectrum v : Measure ℝ) heta
  }

end RHTower
