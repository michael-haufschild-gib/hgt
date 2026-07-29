import GaloisForLFunctions.RHTower.PositiveEnergyInfiniteJetRecurrenceSeparationLaw

/-!
# Complete-local-data quantum recurrence forecast no-go law

The positive-energy infinite-jet recurrence pair rules out every universal
forecast of the late-time return plateau from the complete energy-moment
profile.  It also rules out every recurrent/dispersive classifier whose input
is the complete local survival-amplitude jet.  The forecasting rules are
arbitrary functions: no continuity, computability, finite-dimensionality, or
perturbative assumption is imposed.
-/

open Filter MeasureTheory Set
open scoped ENNReal Topology

noncomputable section

namespace RHTower

/-- Complex survival form factor.  For a probability spectrum this is the
usual survival fidelity, regarded as a complex-valued function. -/
def survivalFormFactor (mu : Measure ℝ) (t : ℝ) : ℂ :=
  charFun mu t * charFun mu (-t)

theorem survivalFormFactor_eq_normSq
    (mu : Measure ℝ) [IsFiniteMeasure mu] (t : ℝ) :
    survivalFormFactor mu t =
      (Complex.normSq (charFun mu t) : ℂ) := by
  rw [survivalFormFactor, charFun_neg]
  exact Complex.mul_conj _

/-- Moment-identical probability spectra have identical survival-form-factor
derivatives of every order at the observation instant. -/
theorem iteratedDeriv_survivalFormFactor_zero_eq_of_hasHamburgerMoments
    {s : ℕ → ℝ} {mu nu : Measure ℝ}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (hmu : GaloisForLFunctions.HTGeometry.HasHamburgerMoments s mu)
    (hnu : GaloisForLFunctions.HTGeometry.HasHamburgerMoments s nu)
    (n : ℕ) :
    iteratedDeriv n (survivalFormFactor mu) 0 =
      iteratedDeriv n (survivalFormFactor nu) 0 := by
  have hmuDiff : ContDiff ℝ n (charFun mu) :=
    contDiff_charFun (hasHamburgerMoments_memLp_id hmu n)
  have hnuDiff : ContDiff ℝ n (charFun nu) :=
    contDiff_charFun (hasHamburgerMoments_memLp_id hnu n)
  have hmuNegDiff :
      ContDiff ℝ n (fun t : ℝ => charFun mu (-t)) := by
    fun_prop
  have hnuNegDiff :
      ContDiff ℝ n (fun t : ℝ => charFun nu (-t)) := by
    fun_prop
  have hjet :
      ∀ k : ℕ,
        iteratedDeriv k (charFun mu) 0 =
          iteratedDeriv k (charFun nu) 0 :=
    fun k =>
      iteratedDeriv_charFun_zero_eq_of_hasHamburgerMoments hmu hnu k
  change
    iteratedDeriv n
        ((charFun mu) * fun t : ℝ => charFun mu (-t)) 0 =
      iteratedDeriv n
        ((charFun nu) * fun t : ℝ => charFun nu (-t)) 0
  rw [iteratedDeriv_mul hmuDiff.contDiffAt hmuNegDiff.contDiffAt,
      iteratedDeriv_mul hnuDiff.contDiffAt hnuNegDiff.contDiffAt]
  apply Finset.sum_congr rfl
  intro k hk
  rw [iteratedDeriv_comp_neg, iteratedDeriv_comp_neg]
  simp only [neg_zero]
  rw [hjet k, hjet (n - k)]

/-- Complete energy-moment profile of a spectral probability law. -/
def energyMomentProfile (mu : Measure ℝ) : ℕ → ℝ :=
  fun n => ∫ x : ℝ, x ^ n ∂mu

/-- Exact long-window survival-fidelity plateau. -/
def recurrencePlateau (mu : Measure ℝ) : ℝ :=
  (spectralDifferenceMeasure mu).real {0}

/-- The spectrum assigns zero mass to nonpositive energy. -/
def HasStrictlyPositiveEnergy (mu : Measure ℝ) : Prop :=
  mu (Iic 0) = 0

/-- Every natural energy moment is integrable. -/
def HasAllEnergyMoments (mu : Measure ℝ) : Prop :=
  ∀ n : ℕ, Integrable (fun x : ℝ => x ^ n) mu

/-- The recurrent phase is the phase with a strictly positive long-window
survival-fidelity plateau. -/
def HasPersistentMeanRecurrence (mu : Measure ℝ) : Prop :=
  0 < recurrencePlateau mu

theorem energyMomentProfile_positiveGeometric_eq_positiveLognormal
    {v : NNReal} (hv : 0 < v) :
    energyMomentProfile
        (positiveGeometricSpectrum v hv : Measure ℝ) =
      energyMomentProfile
        (positiveLognormalSpectrum v : Measure ℝ) := by
  funext n
  exact
    (integral_pow_positiveGeometricSpectrum hv n).trans
      (integral_pow_positiveLognormalSpectrum v n).symm

theorem allLocalFormFactorDerivativesEqual_positiveSpectra
    {v : NNReal} (hv : 0 < v) :
    ∀ n : ℕ,
      iteratedDeriv n
          (survivalFormFactor
            (positiveGeometricSpectrum v hv : Measure ℝ)) 0 =
        iteratedDeriv n
          (survivalFormFactor
            (positiveLognormalSpectrum v : Measure ℝ)) 0 :=
  fun n =>
    iteratedDeriv_survivalFormFactor_zero_eq_of_hasHamburgerMoments
      (positiveGeometricSpectrum_hasHamburgerMoments hv)
      (positiveLognormalSpectrum_hasHamburgerMoments v) n

theorem recurrencePlateau_positiveGeometric_pos
    {v : NNReal} (hv : 0 < v) :
    HasPersistentMeanRecurrence
      (positiveGeometricSpectrum v hv : Measure ℝ) :=
  (positiveEnergyInfiniteJetRecurrenceSeparation v hv).discreteCollisionMassPositive

theorem recurrencePlateau_positiveLognormal_eq_zero
    {v : NNReal} (hv : 0 < v) :
    recurrencePlateau
        (positiveLognormalSpectrum v : Measure ℝ) = 0 := by
  letI : NoAtoms
      (positiveLognormalSpectrum v : Measure ℝ) :=
    noAtoms_positiveLognormalSpectrum hv
  rw [recurrencePlateau, Measure.real,
    spectralDifferenceMeasure_singleton_zero_of_noAtoms]
  simp

/-- **No complete-moment recurrence-plateau predictor.**  At every positive
log-energy variance, there is no universal rule from the entire energy-moment
sequence to the exact late-time survival plateau, even after restricting the
rule to strictly positive-energy probability spectra with all moments. -/
theorem no_universal_positiveEnergy_completeMoment_plateauPredictor
    (v : NNReal) (hv : 0 < v) :
    ¬ ∃ predictor : (ℕ → ℝ) → ℝ,
      ∀ mu : ProbabilityMeasure ℝ,
        HasStrictlyPositiveEnergy (mu : Measure ℝ) →
        HasAllEnergyMoments (mu : Measure ℝ) →
        predictor (energyMomentProfile (mu : Measure ℝ)) =
          recurrencePlateau (mu : Measure ℝ) := by
  rintro ⟨predictor, hpredictor⟩
  have hdiscrete :=
    hpredictor (positiveGeometricSpectrum v hv)
      (positiveGeometricSpectrum_Iic_zero hv)
      (integrable_pow_positiveGeometricSpectrum hv)
  have hcontinuous :=
    hpredictor (positiveLognormalSpectrum v)
      (positiveLognormalSpectrum_Iic_zero v)
      (integrable_pow_positiveLognormalSpectrum v)
  have hplateauEq :
      recurrencePlateau
          (positiveGeometricSpectrum v hv : Measure ℝ) =
        recurrencePlateau
          (positiveLognormalSpectrum v : Measure ℝ) := by
    rw [← hdiscrete, ← hcontinuous,
      energyMomentProfile_positiveGeometric_eq_positiveLognormal hv]
  have hpositive :=
    recurrencePlateau_positiveGeometric_pos hv
  have hzero :=
    recurrencePlateau_positiveLognormal_eq_zero hv
  rw [hzero] at hplateauEq
  exact (not_lt_of_ge (le_of_eq hplateauEq)) hpositive

/-- **No complete-present-jet recurrence classifier.**  At every positive
log-energy variance, no predicate on the complete survival-amplitude jet can
correctly decide the positive-plateau recurrence phase of every strictly
positive-energy probability spectrum with all moments. -/
theorem no_universal_positiveEnergy_completeJet_recurrenceClassifier
    (v : NNReal) (hv : 0 < v) :
    ¬ ∃ classifier : (ℕ → ℂ) → Prop,
      ∀ mu : ProbabilityMeasure ℝ,
        HasStrictlyPositiveEnergy (mu : Measure ℝ) →
        HasAllEnergyMoments (mu : Measure ℝ) →
        (classifier
            (fun n =>
              iteratedDeriv n (charFun (mu : Measure ℝ)) 0) ↔
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
  have hjet :
      (fun n =>
        iteratedDeriv n
          (charFun
            (positiveGeometricSpectrum v hv : Measure ℝ)) 0) =
      fun n =>
        iteratedDeriv n
          (charFun
            (positiveLognormalSpectrum v : Measure ℝ)) 0 := by
    funext n
    exact allLocalDerivativesEqual_positiveSpectra hv n
  have hdiscreteClassified :
      classifier
        (fun n =>
          iteratedDeriv n
            (charFun
              (positiveGeometricSpectrum v hv : Measure ℝ)) 0) :=
    hdiscrete.mpr (recurrencePlateau_positiveGeometric_pos hv)
  have hcontinuousClassified :
      classifier
        (fun n =>
          iteratedDeriv n
            (charFun
              (positiveLognormalSpectrum v : Measure ℝ)) 0) := by
    rw [← hjet]
    exact hdiscreteClassified
  have hcontinuousRecurrence :=
    hcontinuous.mp hcontinuousClassified
  have hzero :=
    recurrencePlateau_positiveLognormal_eq_zero hv
  rw [HasPersistentMeanRecurrence, hzero] at hcontinuousRecurrence
  exact (lt_irrefl 0) hcontinuousRecurrence

end RHTower
