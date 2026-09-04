import GaloisForLFunctions.HTGeometry.CollectiveQuantumFisherCorrelation
import GaloisForLFunctions.HTGeometry.TwoReplicaGlobalCliffordTwirlRange

/-!
# Exact finite-spin identities behind a discrete time-crystal protocol

This module isolates exact algebraic statements from the finite XXZ-chain protocol of
Formicola--Di Bello--de Candia--De Filippis--Perroni,
*Discrete time crystals in disordered anisotropic Heisenberg chains*, arXiv:2609.04037.

The paper's phase diagram is numerical and is not asserted here.  What is exact is that a global
Pauli-X half turn negates every longitudinal Pauli-Z observable and hence every weighted
longitudinal collective observable, including staggered imbalance.  The module also records the
period-two signal identities, order-parameter extraction, subharmonic frequency ladder, and the
collective-magnetization QFI/correlation formula.
-/

open scoped BigOperators Matrix
open Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Pauli label for the simultaneous X half turn on every site. -/
def globalXPauliLabel (σ : Type*) : σ → Option (Fin 3) :=
  fun _ => some 0

/-- Pauli-Z label supported at one site. -/
def localZPauliLabel
    {σ : Type*} [DecidableEq σ] (i : σ) : σ → Option (Fin 3) :=
  fun j => if j = i then some 2 else none

/-- Matrix of the phase-free global X kick. -/
def globalXPauliKick
    (σ : Type*) [Fintype σ] [DecidableEq σ] :
    Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ :=
  finitePauliMatrix (globalXPauliLabel σ)

/-- Longitudinal Pauli-Z observable at one site. -/
def localZPauliObservable
    {σ : Type*} [Fintype σ] [DecidableEq σ] (i : σ) :
    Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ :=
  finitePauliMatrix (localZPauliLabel i)

/-- Global X has odd conjugation character against every local Z. -/
theorem finitePauliConjugationSign_globalX_localZ
    {σ : Type*} [Fintype σ] [DecidableEq σ] (i : σ) :
    finitePauliConjugationSign (globalXPauliLabel σ) (localZPauliLabel i) = -1 := by
  rw [finitePauliConjugationSign]
  refine (Finset.prod_eq_single i ?_ ?_).trans ?_
  · intro j _hj hji
    simp [globalXPauliLabel, localZPauliLabel, hji,
      boolPauliConjugationSign]
  · intro hnot
    exact absurd (Finset.mem_univ i) hnot
  · simp [globalXPauliLabel, localZPauliLabel,
      boolPauliConjugationSign]

/-- A perfect global X half turn flips one local longitudinal spin. -/
theorem globalXPauliKick_conj_localZ
    {σ : Type*} [Fintype σ] [DecidableEq σ] (i : σ) :
    globalXPauliKick σ * localZPauliObservable i * globalXPauliKick σ =
      -localZPauliObservable i := by
  rw [globalXPauliKick, localZPauliObservable,
    finitePauliMatrix_conj,
    finitePauliConjugationSign_globalX_localZ]
  simp

/-- Arbitrary weighted longitudinal collective observable. -/
def weightedLongitudinalObservable
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (c : σ → ℂ) :
    Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ :=
  ∑ i, c i • localZPauliObservable i

/-- A perfect global X half turn flips every weighted longitudinal collective observable. -/
theorem globalXPauliKick_conj_weightedLongitudinal
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (c : σ → ℂ) :
    globalXPauliKick σ * weightedLongitudinalObservable c * globalXPauliKick σ =
      -weightedLongitudinalObservable c := by
  classical
  unfold weightedLongitudinalObservable
  rw [Matrix.mul_sum, Finset.sum_mul]
  simp_rw [Matrix.mul_smul, Matrix.smul_mul,
    globalXPauliKick_conj_localZ]
  simp

/-- Staggered longitudinal imbalance on an `N`-site chain, with totalized normalization at
`N = 0`. -/
def finiteSpinStaggeredImbalance (N : ℕ) :
    Matrix (FiniteQubitConfiguration (Fin N))
      (FiniteQubitConfiguration (Fin N)) ℂ :=
  weightedLongitudinalObservable fun i =>
    (((N : ℝ)⁻¹ * (-1 : ℝ) ^ (i.val + 1) : ℝ) : ℂ)

/-- The ideal global half turn negates staggered imbalance exactly. -/
theorem globalXPauliKick_conj_finiteSpinStaggeredImbalance (N : ℕ) :
    globalXPauliKick (Fin N) * finiteSpinStaggeredImbalance N *
        globalXPauliKick (Fin N) =
      -finiteSpinStaggeredImbalance N := by
  exact globalXPauliKick_conj_weightedLongitudinal _

/-- Strict product-Clifford implementation of the global X half turn. -/
def globalXCliffordHalfTurnGate
    (σ : Type*) [Fintype σ] [DecidableEq σ] :
    Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ :=
  finiteProductCliffordGate
    (finitePauliHalfTurnCode (globalXPauliLabel σ))

/-- The strict Clifford half-turn implementation flips every local Z after its global phase
cancels against the adjoint. -/
theorem globalXCliffordHalfTurnGate_conj_localZ
    {σ : Type*} [Fintype σ] [DecidableEq σ] (i : σ) :
    globalXCliffordHalfTurnGate σ * localZPauliObservable i *
        (globalXCliffordHalfTurnGate σ)ᴴ =
      -localZPauliObservable i := by
  rw [globalXCliffordHalfTurnGate,
    finiteProductCliffordGate_pauliHalfTurn]
  rw [Matrix.conjTranspose_smul,
    finitePauliMatrix_isHermitian]
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul,
    smul_smul]
  simp only [localZPauliObservable]
  rw [finitePauliMatrix_conj,
    finitePauliConjugationSign_globalX_localZ]
  rw [mul_comm, finitePauliHalfTurnPhase_mul_conj]
  simp

/-- Strict global X half turn flips the full staggered imbalance. -/
theorem globalXCliffordHalfTurnGate_conj_finiteSpinStaggeredImbalance
    (N : ℕ) :
    globalXCliffordHalfTurnGate (Fin N) * finiteSpinStaggeredImbalance N *
        (globalXCliffordHalfTurnGate (Fin N))ᴴ =
      -finiteSpinStaggeredImbalance N := by
  classical
  unfold finiteSpinStaggeredImbalance weightedLongitudinalObservable
  rw [Matrix.mul_sum, Finset.sum_mul]
  simp_rw [Matrix.mul_smul, Matrix.smul_mul,
    globalXCliffordHalfTurnGate_conj_localZ]
  simp

/-- Exact period-doubled scalar response with amplitude `a`. -/
def periodDoubledSignal (a : ℝ) (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n * a

@[simp] theorem periodDoubledSignal_zero (a : ℝ) :
    periodDoubledSignal a 0 = a := by
  simp [periodDoubledSignal]

/-- Every cycle reverses an exact period-doubled signal. -/
theorem periodDoubledSignal_succ (a : ℝ) (n : ℕ) :
    periodDoubledSignal a (n + 1) = -periodDoubledSignal a n := by
  rw [periodDoubledSignal, periodDoubledSignal, pow_succ]
  ring

/-- Two cycles restore an exact period-doubled signal. -/
theorem periodDoubledSignal_add_two (a : ℝ) (n : ℕ) :
    periodDoubledSignal a (n + 2) = periodDoubledSignal a n := by
  rw [show n + 2 = (n + 1) + 1 by omega,
    periodDoubledSignal_succ, periodDoubledSignal_succ]
  simp only [neg_neg]

/-- Finite-window DTC indicator, using a manifestly nonempty window of `N + 1` cycles. -/
def finiteDTCIndicator (N : ℕ) (signal : ℕ → ℝ) : ℝ :=
  ((N + 1 : ℕ) : ℝ)⁻¹ *
    ∑ n ∈ Finset.range (N + 1), (-1 : ℝ) ^ n * signal n

/-- Finite-window localization-memory indicator. -/
def finiteMBLIndicator (N : ℕ) (signal : ℕ → ℝ) : ℝ :=
  ((N + 1 : ℕ) : ℝ)⁻¹ *
    ∑ n ∈ Finset.range (N + 1), |signal n|

/-- DTC demodulation recovers the exact amplitude of a period-doubled signal. -/
theorem finiteDTCIndicator_periodDoubledSignal (N : ℕ) (a : ℝ) :
    finiteDTCIndicator N (periodDoubledSignal a) = a := by
  unfold finiteDTCIndicator periodDoubledSignal
  have hterm : ∀ n : ℕ,
      (-1 : ℝ) ^ n * ((-1 : ℝ) ^ n * a) = a := by
    intro n
    rw [← mul_assoc, ← mul_pow]
    simp
  simp_rw [hterm]
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hne : (((N + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  field_simp

/-- The memory indicator of an exact period-doubled signal is its absolute amplitude. -/
theorem finiteMBLIndicator_periodDoubledSignal (N : ℕ) (a : ℝ) :
    finiteMBLIndicator N (periodDoubledSignal a) = |a| := by
  unfold finiteMBLIndicator periodDoubledSignal
  have hterm : ∀ n : ℕ, |(-1 : ℝ) ^ n * a| = |a| := by
    intro n
    rw [abs_mul, abs_pow]
    simp
  simp_rw [hterm]
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hne : (((N + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  field_simp

/-- Angular drive frequency. -/
def discreteDriveFrequency (T : ℝ) : ℝ :=
  2 * Real.pi / T

/-- Fundamental period-doubled subharmonic frequency. -/
def discreteTimeCrystalFrequency (T : ℝ) : ℝ :=
  Real.pi / T

/-- Period doubling halves the drive frequency, including under Lean's totalized division at
`T = 0`. -/
theorem discreteTimeCrystalFrequency_eq_drive_div_two (T : ℝ) :
    discreteTimeCrystalFrequency T = discreteDriveFrequency T / 2 := by
  unfold discreteTimeCrystalFrequency discreteDriveFrequency
  ring

/-- Odd harmonic ladder of a period-doubled response. -/
def discreteTimeCrystalOddHarmonic (T : ℝ) (m : ℕ) : ℝ :=
  (2 * (m : ℝ) + 1) * Real.pi / T

@[simp] theorem discreteTimeCrystalOddHarmonic_zero (T : ℝ) :
    discreteTimeCrystalOddHarmonic T 0 = discreteTimeCrystalFrequency T := by
  simp [discreteTimeCrystalOddHarmonic, discreteTimeCrystalFrequency]

/-- Adjacent odd harmonics differ by one drive frequency. -/
theorem discreteTimeCrystalOddHarmonic_succ (T : ℝ) (m : ℕ) :
    discreteTimeCrystalOddHarmonic T (m + 1) =
      discreteTimeCrystalOddHarmonic T m + discreteDriveFrequency T := by
  unfold discreteTimeCrystalOddHarmonic discreteDriveFrequency
  push_cast
  ring

/-- Connected longitudinal spin correlation. -/
def longitudinalSpinConnectedCorrelation
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (ψ : FiniteQubitConfiguration σ → ℂ) (i j : σ) : ℝ :=
  QuantumAlg.qCov ψ (localZPauliObservable i) (localZPauliObservable j)

/-- Uniform-magnetization QFI per spin. -/
def uniformMagnetizationQuantumFisherPerSite
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (ψ : FiniteQubitConfiguration σ → ℂ) : ℝ :=
  finiteHalfCollectiveQuantumFisherPerSite ψ
    (fun i : σ => localZPauliObservable i)

/-- Uniform-magnetization QFI per spin equals normalized sum of longitudinal connected
correlations. -/
theorem uniformMagnetizationQuantumFisherPerSite_eq_correlationSum
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (ψ : FiniteQubitConfiguration σ → ℂ) :
    uniformMagnetizationQuantumFisherPerSite ψ =
      (Fintype.card σ : ℝ)⁻¹ *
        ∑ i, ∑ j, longitudinalSpinConnectedCorrelation ψ i j := by
  exact finiteHalfCollectiveQuantumFisherPerSite_eq_correlationSum ψ _

end

end GaloisForLFunctions.HTGeometry
