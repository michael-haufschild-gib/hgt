import GaloisForLFunctions.HTGeometry.ActivePauliShellRateLaw
import GaloisForLFunctions.HTGeometry.AnalyticObserverMinorSublevelLaw
import GaloisForLFunctions.HTGeometry.AutonomousExponentialObserverCarrierLaw
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Local-Pauli autonomous observer law

For every qubit number and every locality cutoff, the active nonidentity Pauli
words form an injective real coefficient dictionary.  At unit laboratory time
the Schrödinger generator is `-iH`.  A finite-dimensional continuous linear
left inverse gives a coefficient reporter.

The reporter composed with the generator is exactly the identity.  Hence the
selected Jacobian minor at the zero Hamiltonian is the identity matrix, with
determinant one.  The autonomous exponential observer law then applies with no
genericity assumption: its common critical carrier is Gaussian-null, every
regular exact target carrier is zero-dimensional, and every fixed confidence
admits a positive robust determinant threshold.
-/

open MeasureTheory ProbabilityTheory Metric Set Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped Matrix.Norms.L2Operator

/-- A continuous linear left inverse selected for a linear map with
finite-dimensional codomain.  Its inverse law is stated separately under
injectivity. -/
def continuousLinearLeftInverse
    {E A : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup A] [NormedSpace ℝ A]
    [FiniteDimensional ℝ A]
    (L : E →L[ℝ] A) : A →L[ℝ] E :=
  LinearMap.toContinuousLinearMap L.toLinearMap.leftInverse

theorem continuousLinearLeftInverse_apply
    {E A : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup A] [NormedSpace ℝ A]
    [FiniteDimensional ℝ A]
    (L : E →L[ℝ] A) (hL : Function.Injective L) (x : E) :
    continuousLinearLeftInverse L (L x) = x := by
  exact LinearMap.leftInverse_apply_of_inj
    (LinearMap.ker_eq_bot_of_injective hL) x

/-- Canonical finite coordinate index for all active nonidentity Pauli words
of weight at most `q`. -/
abbrev ActivePauliCoefficientIndex (n q : ℕ) :=
  Fin (Fintype.card (PauliTracelessLabel n q))

def activePauliIndexEquiv (n q : ℕ) :
    PauliTracelessLabel n q ≃ ActivePauliCoefficientIndex n q :=
  Fintype.equivFin _

/-- Unit-time Schrödinger generator assembly `x ↦ -i H(x)` as a real linear
map on the complete active `q`-local Pauli dictionary. -/
def unitTimeActivePauliGeneratorLinear (n q : ℕ) :
    EuclideanSpace ℝ (ActivePauliCoefficientIndex n q) →ₗ[ℝ]
      Matrix (Fin n → Bool) (Fin n → Bool) ℂ where
  toFun x := (-Complex.I) • activePauliHamiltonian
    (fun P => (x (activePauliIndexEquiv n q P) : ℂ))
  map_add' x y := by
    classical
    have hH :
        activePauliHamiltonian
            (fun P => ((x + y) (activePauliIndexEquiv n q P) : ℂ)) =
          activePauliHamiltonian
              (fun P => (x (activePauliIndexEquiv n q P) : ℂ)) +
            activePauliHamiltonian
              (fun P => (y (activePauliIndexEquiv n q P) : ℂ)) := by
      rw [activePauliHamiltonian, activePauliHamiltonian,
        activePauliHamiltonian, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro P _
      rw [← add_smul]
      simp
    rw [hH, smul_add]
  map_smul' r x := by
    classical
    have hH :
        activePauliHamiltonian
            (fun P => ((r • x) (activePauliIndexEquiv n q P) : ℂ)) =
          (r : ℂ) • activePauliHamiltonian
            (fun P => (x (activePauliIndexEquiv n q P) : ℂ)) := by
      rw [activePauliHamiltonian, activePauliHamiltonian, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro P _
      rw [smul_smul]
      simp
    rw [hH]
    ext a b
    simp [smul_eq_mul]
    ring

/-- Continuous unit-time Schrödinger generator assembly. -/
def unitTimeActivePauliGenerator (n q : ℕ) :
    EuclideanSpace ℝ (ActivePauliCoefficientIndex n q) →L[ℝ]
      Matrix (Fin n → Bool) (Fin n → Bool) ℂ :=
  LinearMap.toContinuousLinearMap (unitTimeActivePauliGeneratorLinear n q)

/-- The complete active `q`-local Pauli generator dictionary is injective for
every `n` and `q`, including empty dictionaries. -/
theorem unitTimeActivePauliGenerator_injective (n q : ℕ) :
    Function.Injective (unitTimeActivePauliGenerator n q) := by
  classical
  intro x y hxy
  ext i
  let P : PauliTracelessLabel n q := (activePauliIndexEquiv n q).symm i
  have hH :
      activePauliHamiltonian
          (fun Q => (x (activePauliIndexEquiv n q Q) : ℂ)) =
        activePauliHamiltonian
          (fun Q => (y (activePauliIndexEquiv n q Q) : ℂ)) := by
    have hi := congrArg (fun M => Complex.I • M) hxy
    simpa [unitTimeActivePauliGenerator, unitTimeActivePauliGeneratorLinear,
      smul_smul] using hi
  have hsum :
      ∑ Q : PauliTracelessLabel n q,
          (((x (activePauliIndexEquiv n q Q) : ℝ) : ℂ) -
            ((y (activePauliIndexEquiv n q Q) : ℝ) : ℂ)) • finitePauliMatrix Q.1 = 0 := by
    have hdiff :
        activePauliHamiltonian
            (fun Q => (x (activePauliIndexEquiv n q Q) : ℂ)) -
          activePauliHamiltonian
            (fun Q => (y (activePauliIndexEquiv n q Q) : ℂ)) = 0 :=
      sub_eq_zero.mpr hH
    simpa [activePauliHamiltonian, Finset.sum_sub_distrib, sub_smul] using hdiff
  have hlin := Fintype.linearIndependent_iff.mp
    ((finitePauliMatrix_linearIndependent (σ := Fin n)).comp
      (fun Q : PauliTracelessLabel n q => Q.1) Subtype.val_injective)
    (fun Q => (((x (activePauliIndexEquiv n q Q) : ℝ) : ℂ) -
      ((y (activePauliIndexEquiv n q Q) : ℝ) : ℂ))) hsum P
  have hre : x i - y i = 0 := by
    have hre' := congrArg Complex.re hlin
    simpa [P] using hre'
  linarith

/-- A continuous coefficient reporter chosen as a left inverse to the complete
active local-Pauli generator dictionary. -/
def unitTimeActivePauliReporter (n q : ℕ) :
    Matrix (Fin n → Bool) (Fin n → Bool) ℂ →L[ℝ]
      EuclideanSpace ℝ (ActivePauliCoefficientIndex n q) :=
  continuousLinearLeftInverse
    (E := EuclideanSpace ℝ (ActivePauliCoefficientIndex n q))
    (A := Matrix (Fin n → Bool) (Fin n → Bool) ℂ)
    (unitTimeActivePauliGenerator n q)

theorem unitTimeActivePauliReporter_generator (n q : ℕ)
    (x : EuclideanSpace ℝ (ActivePauliCoefficientIndex n q)) :
    unitTimeActivePauliReporter n q (unitTimeActivePauliGenerator n q x) = x := by
  exact continuousLinearLeftInverse_apply
    (unitTimeActivePauliGenerator n q)
    (unitTimeActivePauliGenerator_injective n q) x

/-- Canonical coefficient directions used for the square observer minor. -/
def unitTimeActivePauliDirections (n q : ℕ) :
    ActivePauliCoefficientIndex n q →
      EuclideanSpace ℝ (ActivePauliCoefficientIndex n q) :=
  fun j => EuclideanSpace.single j 1

/-- The visible generator minor is exactly identity, not merely nonsingular. -/
theorem unitTimeActivePauli_generatorMinor_eq_one (n q : ℕ) :
    autonomousGeneratorMinor
        (unitTimeActivePauliGenerator n q)
        (unitTimeActivePauliReporter n q)
        (unitTimeActivePauliDirections n q) = 1 := by
  classical
  ext i j
  rw [autonomousGeneratorMinor]
  rw [unitTimeActivePauliReporter_generator]
  simp [unitTimeActivePauliDirections, Matrix.one_apply]

theorem unitTimeActivePauli_generatorMinor_det_ne_zero (n q : ℕ) :
    (autonomousGeneratorMinor
        (unitTimeActivePauliGenerator n q)
        (unitTimeActivePauliReporter n q)
        (unitTimeActivePauliDirections n q)).det ≠ 0 := by
  rw [unitTimeActivePauli_generatorMinor_eq_one]
  simp

/-- **Unconditional local-Pauli autonomous exact-carrier law.**  For every
qubit count and every locality cutoff, one target-independent Gaussian-null
set contains every critical unit-time coefficient.  Every exact adaptive
target carrier on its complement is zero-dimensional. -/
theorem unitTimeActivePauli_universal_exactCarrierLaw (n q : ℕ) :
    stdGaussian
        (EuclideanSpace ℝ (ActivePauliCoefficientIndex n q))
        {x | ¬ Function.Surjective
          (fderiv ℝ
            (autonomousExponentialEndpoint
              (unitTimeActivePauliGenerator n q)
              (unitTimeActivePauliReporter n q)) x)} = 0 ∧
      ∀ (y : EuclideanSpace ℝ (ActivePauliCoefficientIndex n q))
        (M : Set (EuclideanSpace ℝ (ActivePauliCoefficientIndex n q))),
        M ⊆ {x | autonomousExponentialEndpoint
                (unitTimeActivePauliGenerator n q)
                (unitTimeActivePauliReporter n q) x = y} ∩
          {x | Function.Surjective
            (fderiv ℝ
              (autonomousExponentialEndpoint
                (unitTimeActivePauliGenerator n q)
                (unitTimeActivePauliReporter n q)) x)} →
        dimH M ≤ (0 : ℕ) := by
  simpa using autonomousExponential_universal_exactCarrierLaw
    (unitTimeActivePauliGenerator n q)
    (unitTimeActivePauliReporter n q)
    (unitTimeActivePauliDirections n q)
    (unitTimeActivePauli_generatorMinor_det_ne_zero n q)

/-- **Unconditional fixed-confidence local-Pauli observer lower tail.**  For
every positive error budget, every `n`, and every `q`, a positive determinant
threshold leaves smaller Gaussian mass below it. -/
theorem unitTimeActivePauli_exists_small_observerMinor_sublevel (n q : ℕ) :
    ∀ ε : ℝ, 0 < ε →
      ∃ g : ℝ, 0 < g ∧
        (stdGaussian
          (EuclideanSpace ℝ (ActivePauliCoefficientIndex n q))).real
          {x |
            |(observerMinor
              (fun z => fderiv ℝ
                (autonomousExponentialEndpoint
                  (unitTimeActivePauliGenerator n q)
                  (unitTimeActivePauliReporter n q)) z)
              (unitTimeActivePauliDirections n q) x).det| ≤ g} < ε := by
  apply analytic_observerMinor_exists_small_stdGaussian_sublevel
    (autonomousExponentialEndpoint_analyticOnNhd
      (unitTimeActivePauliGenerator n q)
      (unitTimeActivePauliReporter n q))
    (unitTimeActivePauliDirections n q)
  have hminor :
      observerMinor
          (fun z => fderiv ℝ
            (autonomousExponentialEndpoint
              (unitTimeActivePauliGenerator n q)
              (unitTimeActivePauliReporter n q)) z)
          (unitTimeActivePauliDirections n q) 0 =
        autonomousGeneratorMinor
          (unitTimeActivePauliGenerator n q)
          (unitTimeActivePauliReporter n q)
          (unitTimeActivePauliDirections n q) := by
    ext i j
    simp only [observerMinor, autonomousGeneratorMinor]
    rw [autonomousExponentialEndpoint_fderiv_zero]
    rfl
  rw [hminor]
  exact unitTimeActivePauli_generatorMinor_det_ne_zero n q

/-- Schrödinger generator at an arbitrary nonzero real laboratory time.  A
real unit packages nonzeroness without adding a theorem premise. -/
def nonzeroTimeActivePauliGenerator (n q : ℕ) (t : ℝˣ) :
    EuclideanSpace ℝ (ActivePauliCoefficientIndex n q) →L[ℝ]
      Matrix (Fin n → Bool) (Fin n → Bool) ℂ :=
  (t : ℝ) • unitTimeActivePauliGenerator n q

/-- Every nonzero-time active local-Pauli generator dictionary is injective. -/
theorem nonzeroTimeActivePauliGenerator_injective (n q : ℕ) (t : ℝˣ) :
    Function.Injective (nonzeroTimeActivePauliGenerator n q t) := by
  intro x y hxy
  apply unitTimeActivePauliGenerator_injective n q
  apply (smul_right_injective
    (Matrix (Fin n → Bool) (Fin n → Bool) ℂ) (Units.ne_zero t))
  exact hxy

/-- Continuous coefficient reporter for an arbitrary nonzero laboratory
time. -/
def nonzeroTimeActivePauliReporter (n q : ℕ) (t : ℝˣ) :
    Matrix (Fin n → Bool) (Fin n → Bool) ℂ →L[ℝ]
      EuclideanSpace ℝ (ActivePauliCoefficientIndex n q) :=
  continuousLinearLeftInverse (nonzeroTimeActivePauliGenerator n q t)

theorem nonzeroTimeActivePauliReporter_generator (n q : ℕ) (t : ℝˣ)
    (x : EuclideanSpace ℝ (ActivePauliCoefficientIndex n q)) :
    nonzeroTimeActivePauliReporter n q t
      (nonzeroTimeActivePauliGenerator n q t x) = x := by
  exact continuousLinearLeftInverse_apply _
    (nonzeroTimeActivePauliGenerator_injective n q t) x

/-- At every nonzero time, the reporter-normalized generator minor remains
exactly identity. -/
theorem nonzeroTimeActivePauli_generatorMinor_eq_one
    (n q : ℕ) (t : ℝˣ) :
    autonomousGeneratorMinor
        (nonzeroTimeActivePauliGenerator n q t)
        (nonzeroTimeActivePauliReporter n q t)
        (unitTimeActivePauliDirections n q) = 1 := by
  classical
  ext i j
  rw [autonomousGeneratorMinor]
  rw [nonzeroTimeActivePauliReporter_generator]
  simp [unitTimeActivePauliDirections, Matrix.one_apply]

/-- **All-nonzero-times local-Pauli exact-carrier law.**  For every qubit
count, every locality cutoff, and every nonzero laboratory time, the common
critical carrier is Gaussian-null and every regular exact target carrier is
zero-dimensional. -/
theorem nonzeroTimeActivePauli_universal_exactCarrierLaw
    (n q : ℕ) (t : ℝˣ) :
    stdGaussian
        (EuclideanSpace ℝ (ActivePauliCoefficientIndex n q))
        {x | ¬ Function.Surjective
          (fderiv ℝ
            (autonomousExponentialEndpoint
              (nonzeroTimeActivePauliGenerator n q t)
              (nonzeroTimeActivePauliReporter n q t)) x)} = 0 ∧
      ∀ (y : EuclideanSpace ℝ (ActivePauliCoefficientIndex n q))
        (M : Set (EuclideanSpace ℝ (ActivePauliCoefficientIndex n q))),
        M ⊆ {x | autonomousExponentialEndpoint
                (nonzeroTimeActivePauliGenerator n q t)
                (nonzeroTimeActivePauliReporter n q t) x = y} ∩
          {x | Function.Surjective
            (fderiv ℝ
              (autonomousExponentialEndpoint
                (nonzeroTimeActivePauliGenerator n q t)
                (nonzeroTimeActivePauliReporter n q t)) x)} →
        dimH M ≤ (0 : ℕ) := by
  simpa using autonomousExponential_universal_exactCarrierLaw
    (nonzeroTimeActivePauliGenerator n q t)
    (nonzeroTimeActivePauliReporter n q t)
    (unitTimeActivePauliDirections n q)
    (by
      rw [nonzeroTimeActivePauli_generatorMinor_eq_one]
      simp)

/-- Every nonzero laboratory time also has a fixed-confidence positive
observer-minor threshold. -/
theorem nonzeroTimeActivePauli_exists_small_observerMinor_sublevel
    (n q : ℕ) (t : ℝˣ) :
    ∀ ε : ℝ, 0 < ε →
      ∃ g : ℝ, 0 < g ∧
        (stdGaussian
          (EuclideanSpace ℝ (ActivePauliCoefficientIndex n q))).real
          {x |
            |(observerMinor
              (fun z => fderiv ℝ
                (autonomousExponentialEndpoint
                  (nonzeroTimeActivePauliGenerator n q t)
                  (nonzeroTimeActivePauliReporter n q t)) z)
              (unitTimeActivePauliDirections n q) x).det| ≤ g} < ε := by
  apply analytic_observerMinor_exists_small_stdGaussian_sublevel
    (autonomousExponentialEndpoint_analyticOnNhd
      (nonzeroTimeActivePauliGenerator n q t)
      (nonzeroTimeActivePauliReporter n q t))
    (unitTimeActivePauliDirections n q)
  have hminor :
      observerMinor
          (fun z => fderiv ℝ
            (autonomousExponentialEndpoint
              (nonzeroTimeActivePauliGenerator n q t)
              (nonzeroTimeActivePauliReporter n q t)) z)
          (unitTimeActivePauliDirections n q) 0 = 1 := by
    ext i j
    simp only [observerMinor]
    rw [autonomousExponentialEndpoint_fderiv_zero]
    change nonzeroTimeActivePauliReporter n q t
        (nonzeroTimeActivePauliGenerator n q t
          (unitTimeActivePauliDirections n q j)) i =
            (1 : Matrix (ActivePauliCoefficientIndex n q)
              (ActivePauliCoefficientIndex n q) ℝ) i j
    rw [nonzeroTimeActivePauliReporter_generator]
    simp [unitTimeActivePauliDirections, Matrix.one_apply]
  rw [hminor]
  simp

end

end GaloisForLFunctions.HTGeometry
