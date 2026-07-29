import GaloisForLFunctions.RHTower.CyclicHilbertQuantumRecurrenceNoGoLaw
import GaloisForLFunctions.RHTower.LocalJacobiNonperturbativeRecurrenceLaw
import GaloisForLFunctions.HTGeometry.MomentDeterminacyStep

/-!
# Jacobi-boundary quantum recurrence law

Moment-indeterminate quantum clocks can share more than every derivative of
one survival amplitude.  They share every polynomial Krylov Gram matrix and
every polynomial matrix element of energy multiplication.  Equivalently,
their complete connected Jacobi nearest-neighbour law is identical at every
finite depth.

Nevertheless, one realization can have countable temporal dimension and
persistent mean recurrence while another has continuum temporal dimension,
vanishing mean recurrence, and zero density at every positive return
threshold.  The separation holds in every normalized indeterminate
Hamburger class covered by the Nevanlinna boundary construction, and an
explicit strictly-positive-energy family realizes it at every positive
log-energy variance.
-/

open Complex Filter MeasureTheory Set
open scoped Cardinal ENNReal OnePoint Topology

noncomputable section

namespace RHTower

/-- Polynomial Krylov Gram matrix element of a spectral law. -/
def spectralPolynomialGram
    (mu : Measure ℝ) (p q : Polynomial ℝ) : ℝ :=
  ∫ x, p.eval x * q.eval x ∂mu

/-- Polynomial matrix element of energy multiplication. -/
def spectralPolynomialEnergyMatrix
    (mu : Measure ℝ) (p q : Polynomial ℝ) : ℝ :=
  ∫ x, x * p.eval x * q.eval x ∂mu

/-- Complete equality of Hamburger moments gives equality of every
polynomial Krylov Gram matrix element, not merely equality of monomial
moments. -/
theorem spectralPolynomialGram_eq_of_hasHamburgerMoments
    {s : ℕ → ℝ} {mu nu : Measure ℝ}
    (hmu : GaloisForLFunctions.HTGeometry.HasHamburgerMoments s mu)
    (hnu : GaloisForLFunctions.HTGeometry.HasHamburgerMoments s nu)
    (p q : Polynomial ℝ) :
    spectralPolynomialGram mu p q =
      spectralPolynomialGram nu p q := by
  have h :=
    HTGeometry.integral_eval_eq_of_hasMoments
      hmu hnu (p * q)
  simpa [spectralPolynomialGram] using h

/-- Complete equality of moments also gives equality of every polynomial
matrix element of multiplication by energy.  Thus the complete local
operator rule agrees, not only the Hilbert geometry of the Krylov vectors. -/
theorem spectralPolynomialEnergyMatrix_eq_of_hasHamburgerMoments
    {s : ℕ → ℝ} {mu nu : Measure ℝ}
    (hmu : GaloisForLFunctions.HTGeometry.HasHamburgerMoments s mu)
    (hnu : GaloisForLFunctions.HTGeometry.HasHamburgerMoments s nu)
    (p q : Polynomial ℝ) :
    spectralPolynomialEnergyMatrix mu p q =
      spectralPolynomialEnergyMatrix nu p q := by
  have h :=
    HTGeometry.integral_eval_eq_of_hasMoments
      hmu hnu (Polynomial.X * p * q)
  simpa [spectralPolynomialEnergyMatrix] using h

/-- Complete polynomially local data of a cyclic energy law: all Krylov Gram
matrix elements together with all matrix elements of energy multiplication. -/
@[ext] structure CompletePolynomialLocalData where
  gram : Polynomial ℝ → Polynomial ℝ → ℝ
  energyMatrix : Polynomial ℝ → Polynomial ℝ → ℝ

/-- Complete local data selected by a spectral probability law. -/
def completePolynomialLocalData
    (mu : Measure ℝ) : CompletePolynomialLocalData where
  gram := spectralPolynomialGram mu
  energyMatrix := spectralPolynomialEnergyMatrix mu

theorem completePolynomialLocalData_eq_of_hasHamburgerMoments
    {s : ℕ → ℝ} {mu nu : Measure ℝ}
    (hmu : GaloisForLFunctions.HTGeometry.HasHamburgerMoments s mu)
    (hnu : GaloisForLFunctions.HTGeometry.HasHamburgerMoments s nu) :
    completePolynomialLocalData mu =
      completePolynomialLocalData nu := by
  apply CompletePolynomialLocalData.ext
  · funext p q
    exact spectralPolynomialGram_eq_of_hasHamburgerMoments
      hmu hnu p q
  · funext p q
    exact spectralPolynomialEnergyMatrix_eq_of_hasHamburgerMoments
      hmu hnu p q

/-- **No complete-local-Jacobi recurrence classifier.**  Even an arbitrary
classifier given every polynomial Krylov inner product and every polynomial
matrix element of energy multiplication cannot decide recurrence for all
strictly-positive-energy probability spectra with all moments.  No
continuity, computability, or finite-data restriction is imposed on the
classifier. -/
theorem no_universal_positiveEnergy_completePolynomialLocalData_recurrenceClassifier
    (v : NNReal) (hv : 0 < v) :
    ¬ ∃ classifier : CompletePolynomialLocalData → Prop,
      ∀ mu : ProbabilityMeasure ℝ,
        HasStrictlyPositiveEnergy (mu : Measure ℝ) →
        HasAllEnergyMoments (mu : Measure ℝ) →
        (classifier
            (completePolynomialLocalData (mu : Measure ℝ)) ↔
          HasPersistentMeanRecurrence (mu : Measure ℝ)) := by
  rintro ⟨classifier, hclassifier⟩
  have hdiscrete :=
    hclassifier (positiveGeometricSpectrum v hv)
      (positiveGeometricSpectrum_Iic_zero hv)
      (integrable_pow_positiveGeometricSpectrum hv)
  have hcontinuous :=
    hclassifier (positiveLognormalSpectrum v)
      (positiveLognormalSpectrum_Iic_zero v)
      (integrable_pow_positiveLognormalSpectrum v)
  have hlocal :
      completePolynomialLocalData
          (positiveGeometricSpectrum v hv : Measure ℝ) =
        completePolynomialLocalData
          (positiveLognormalSpectrum v : Measure ℝ) :=
    completePolynomialLocalData_eq_of_hasHamburgerMoments
      (positiveGeometricSpectrum_hasHamburgerMoments hv)
      (positiveLognormalSpectrum_hasHamburgerMoments v)
  have hdiscreteClassified :
      classifier
        (completePolynomialLocalData
          (positiveGeometricSpectrum v hv : Measure ℝ)) :=
    hdiscrete.mpr (recurrencePlateau_positiveGeometric_pos hv)
  have hcontinuousClassified :
      classifier
        (completePolynomialLocalData
          (positiveLognormalSpectrum v : Measure ℝ)) := by
    rw [← hlocal]
    exact hdiscreteClassified
  have hcontinuousRecurrence :=
    hcontinuous.mp hcontinuousClassified
  have hzero :=
    recurrencePlateau_positiveLognormal_eq_zero hv
  rw [HasPersistentMeanRecurrence, hzero] at hcontinuousRecurrence
  exact (lt_irrefl 0) hcontinuousRecurrence

/-- Diagonal coefficient of the common monic Jacobi law. -/
def momentJacobiDiagonal (s : ℕ → ℝ) (n : ℕ) : ℝ :=
  HTGeometry.momentInner s
      (Polynomial.X * HTGeometry.monicOrtho s (n + 1))
      (HTGeometry.monicOrtho s (n + 1)) /
    HTGeometry.momentInner s
      (HTGeometry.monicOrtho s (n + 1))
      (HTGeometry.monicOrtho s (n + 1))

/-- Strictly positive lower coefficient of the common monic Jacobi law. -/
def momentJacobiLower (s : ℕ → ℝ) (n : ℕ) : ℝ :=
  HTGeometry.momentInner s
      (HTGeometry.monicOrtho s (n + 1))
      (HTGeometry.monicOrtho s (n + 1)) /
    HTGeometry.momentInner s
      (HTGeometry.monicOrtho s n)
      (HTGeometry.monicOrtho s n)

theorem momentJacobiLower_pos
    {s : ℕ → ℝ} (h : HTGeometry.PositiveMomentForm s)
    (n : ℕ) :
    0 < momentJacobiLower s n := by
  exact div_pos
    (HTGeometry.monicOrtho_inner_self_pos h (n + 1))
    (HTGeometry.monicOrtho_inner_self_pos h n)

/-- Exact connected nearest-neighbour law determined by one positive moment
form. -/
theorem momentJacobi_threeTerm
    {s : ℕ → ℝ} (h : HTGeometry.PositiveMomentForm s)
    (n : ℕ) :
    Polynomial.X * HTGeometry.monicOrtho s (n + 1) =
      HTGeometry.monicOrtho s (n + 2)
        + momentJacobiDiagonal s n •
            HTGeometry.monicOrtho s (n + 1)
        + momentJacobiLower s n •
            HTGeometry.monicOrtho s n := by
  simpa [momentJacobiDiagonal, momentJacobiLower] using
    HTGeometry.monicOrtho_three_term h n

/-- Complete local Jacobi data with incompatible global recurrence phases. -/
structure CompleteLocalJacobiRecurrenceSeparation
    (s : ℕ → ℝ) where
  temporalSeparation : InfiniteJetQuantumRecurrenceSeparation s
  allPolynomialGramsEqual :
    ∀ p q : Polynomial ℝ,
      spectralPolynomialGram
          (temporalSeparation.recurrentSpectrum : Measure ℝ) p q =
        spectralPolynomialGram
          (temporalSeparation.dispersiveSpectrum : Measure ℝ) p q
  allPolynomialEnergyMatricesEqual :
    ∀ p q : Polynomial ℝ,
      spectralPolynomialEnergyMatrix
          (temporalSeparation.recurrentSpectrum : Measure ℝ) p q =
        spectralPolynomialEnergyMatrix
          (temporalSeparation.dispersiveSpectrum : Measure ℝ) p q
  connectedAtEveryDepth :
    ∀ n : ℕ, 0 < momentJacobiLower s n
  commonJacobiLaw :
    ∀ n : ℕ,
      Polynomial.X * HTGeometry.monicOrtho s (n + 1) =
        HTGeometry.monicOrtho s (n + 2)
          + momentJacobiDiagonal s n •
              HTGeometry.monicOrtho s (n + 1)
          + momentJacobiLower s n •
              HTGeometry.monicOrtho s n

/-- **Universal Jacobi-boundary recurrence law.**  Every normalized
indeterminate Hamburger class in the Nevanlinna regime contains two cyclic
quantum spectra with identical complete local Jacobi data and incompatible
global recurrence phases. -/
theorem exists_completeLocalJacobiRecurrenceSeparation
    {s : ℕ → ℝ} (h : HTGeometry.PositiveMomentForm s)
    (h0b : HTGeometry.BoundedKernel s 0) (h0 : s 0 = 1) :
    Nonempty (CompleteLocalJacobiRecurrenceSeparation s) := by
  obtain ⟨separation⟩ :=
    exists_infiniteJetQuantumRecurrenceSeparation h h0b h0
  exact ⟨{
    temporalSeparation := separation
    allPolynomialGramsEqual := fun p q =>
      spectralPolynomialGram_eq_of_hasHamburgerMoments
        separation.recurrentMoments
        separation.dispersiveMoments p q
    allPolynomialEnergyMatricesEqual := fun p q =>
      spectralPolynomialEnergyMatrix_eq_of_hasHamburgerMoments
        separation.recurrentMoments
        separation.dispersiveMoments p q
    connectedAtEveryDepth := momentJacobiLower_pos h
    commonJacobiLaw := momentJacobi_threeTerm h
  }⟩

/-- The explicit positive lognormal moment sequence is strictly positive as
a polynomial moment form. -/
theorem positiveMomentForm_positiveRecurrenceSeparationMoments
    {v : NNReal} (hv : 0 < v) :
    HTGeometry.PositiveMomentForm
      (positiveRecurrenceSeparationMoments v) := by
  letI : NoAtoms (positiveLognormalSpectrum v : Measure ℝ) :=
    noAtoms_positiveLognormalSpectrum hv
  exact HTGeometry.positiveMomentForm_of_infiniteSupport
    (positiveRecurrenceSeparationMoments v)
    (fun n =>
      (positiveLognormalSpectrum_hasHamburgerMoments v n).2.symm)
    (fun n =>
      (positiveLognormalSpectrum_hasHamburgerMoments v n).1)
    (atomlessProbability_compl_finset_pos
      (positiveLognormalSpectrum v))

/-- Strictly-positive-energy realization of complete local Jacobi agreement
and opposite global recurrence. -/
structure PositiveEnergyCompleteLocalJacobiRecurrenceSeparation
    (v : NNReal) (hv : 0 < v) where
  temporalSeparation :
    PositiveEnergyInfiniteJetRecurrenceSeparation v hv
  allPolynomialGramsEqual :
    ∀ p q : Polynomial ℝ,
      spectralPolynomialGram
          (positiveGeometricSpectrum v hv : Measure ℝ) p q =
        spectralPolynomialGram
          (positiveLognormalSpectrum v : Measure ℝ) p q
  allPolynomialEnergyMatricesEqual :
    ∀ p q : Polynomial ℝ,
      spectralPolynomialEnergyMatrix
          (positiveGeometricSpectrum v hv : Measure ℝ) p q =
        spectralPolynomialEnergyMatrix
          (positiveLognormalSpectrum v : Measure ℝ) p q
  connectedAtEveryDepth :
    ∀ n : ℕ,
      0 < momentJacobiLower
        (positiveRecurrenceSeparationMoments v) n
  commonJacobiLaw :
    ∀ n : ℕ,
      Polynomial.X *
          HTGeometry.monicOrtho
            (positiveRecurrenceSeparationMoments v) (n + 1) =
        HTGeometry.monicOrtho
            (positiveRecurrenceSeparationMoments v) (n + 2)
          + momentJacobiDiagonal
              (positiveRecurrenceSeparationMoments v) n •
              HTGeometry.monicOrtho
                (positiveRecurrenceSeparationMoments v) (n + 1)
          + momentJacobiLower
              (positiveRecurrenceSeparationMoments v) n •
              HTGeometry.monicOrtho
                (positiveRecurrenceSeparationMoments v) n

/-- **Positive-energy Jacobi-boundary recurrence separation.**  At every
positive log-energy variance, two strictly-positive-energy cyclic quantum
histories have the same complete connected Jacobi nearest-neighbour rule,
yet one returns with positive long-time mean and arbitrarily late full
revivals while the other has continuum temporal dimension, zero mean return,
and zero density at every positive return threshold. -/
theorem positiveEnergy_completeLocalJacobiRecurrenceSeparation
    (v : NNReal) (hv : 0 < v) :
    PositiveEnergyCompleteLocalJacobiRecurrenceSeparation v hv := by
  let h :=
    positiveMomentForm_positiveRecurrenceSeparationMoments hv
  exact {
    temporalSeparation :=
      positiveEnergyInfiniteJetRecurrenceSeparation v hv
    allPolynomialGramsEqual := fun p q =>
      spectralPolynomialGram_eq_of_hasHamburgerMoments
        (positiveGeometricSpectrum_hasHamburgerMoments hv)
        (positiveLognormalSpectrum_hasHamburgerMoments v) p q
    allPolynomialEnergyMatricesEqual := fun p q =>
      spectralPolynomialEnergyMatrix_eq_of_hasHamburgerMoments
        (positiveGeometricSpectrum_hasHamburgerMoments hv)
        (positiveLognormalSpectrum_hasHamburgerMoments v) p q
    connectedAtEveryDepth := momentJacobiLower_pos h
    commonJacobiLaw := momentJacobi_threeTerm h
  }

end RHTower
