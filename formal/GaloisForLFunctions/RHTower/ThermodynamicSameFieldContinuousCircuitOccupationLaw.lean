import GaloisForLFunctions.HTGeometry.ContinuousCircuitCompletedOccupationLaw
import GaloisForLFunctions.HTGeometry.ThermodynamicProjectiveRecurrenceDesertLaw

/-!
# One-field thermodynamic continuous-circuit occupation extinction

One countable absolutely summable static nearest-neighbour qubit Pauli field is selected before
system size, time, circuit architecture and continuous gate parameters.  Every literal finite
prefix has a maximally projective spectrum and spends an explicitly bounded completed-time
fraction within operator distance `1/20` of all circuits with at most
`2^n / (64 * (n + 1))` arbitrary `SU(4)` two-qubit gates.  The bound tends to zero along every
literal prefix while the same field retains its recurrence-desert, laboratory-ramp and UHF
thermodynamic lifecycle.
-/

open Filter MeasureTheory Set Topology Matrix
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- Projective spectral dimension of literal `(k+3)`-qubit prefix. -/
def thermodynamicLiteralPrefixProjectiveDimension (k : ℕ) : ℕ :=
  2 ^ (k + 3) - 1

theorem thermodynamicLiteralPrefixProjectiveDimension_add_one (k : ℕ) :
    thermodynamicLiteralPrefixProjectiveDimension k + 1 = 2 ^ (k + 3) := by
  rw [thermodynamicLiteralPrefixProjectiveDimension,
    Nat.sub_add_cancel (one_le_pow₀ (by norm_num : 1 ≤ 2))]

/-- Canonical enumeration of literal prefix configurations. -/
def thermodynamicLiteralPrefixConfigEquiv (k : ℕ) :
    (Fin (k + 3) → Bool) ≃ Fin (thermodynamicLiteralPrefixProjectiveDimension k + 1) :=
  (qubitConfigFin (k + 3)).trans
    (finCongr (thermodynamicLiteralPrefixProjectiveDimension_add_one k).symm)

/-- Canonical physical eigenvalues of one literal prefix, reindexed by the projective carrier. -/
def thermodynamicLiteralPrefixCanonicalEnergy
    (p : InfinitePathLabel → ℝ) (k : ℕ) :
    Fin (thermodynamicLiteralPrefixProjectiveDimension k + 1) → ℝ :=
  let hH : (pathHamiltonian (infinitePathPrefixShell k p)).IsHermitian := by
    exact isSelfAdjoint_pathHamiltonian _
  fun i => hH.eigenvalues ((thermodynamicLiteralPrefixConfigEquiv k).symm i)

/-- Canonical unitary eigenbasis of one physical literal prefix. -/
def thermodynamicLiteralPrefixCanonicalEigenbasisUnitary
    (p : InfinitePathLabel → ℝ) (k : ℕ) :
    Matrix.unitaryGroup (Fin (k + 3) → Bool) ℂ :=
  hermitianEigenbasisUnitary (isSelfAdjoint_pathHamiltonian
    (infinitePathPrefixShell k p))

theorem maximallyProjectiveEnergy_thermodynamicLiteralPrefixCanonicalEnergy
    {p : InfinitePathLabel → ℝ} (hp : ThermodynamicSameFieldLifecycle p) (k : ℕ) :
    MaximallyProjectiveEnergy (thermodynamicLiteralPrefixCanonicalEnergy p k) := by
  let H := pathHamiltonian (infinitePathPrefixShell k p)
  let hH : H.IsHermitian := by
    exact isSelfAdjoint_pathHamiltonian _
  have hcanonical : MaximallyProjectiveEnergy hH.eigenvalues :=
    maximallyProjectiveEnergy_eigenvalues_of_orthoEigenBasis hH
      (isOrthoEigenBasis_pathEigenBasis k (infinitePathPrefixShell k p))
      (hp.prefix_maximallyProjective k)
  simpa [thermodynamicLiteralPrefixCanonicalEnergy, H, hH] using
    hcanonical.comp_equiv_relabel (thermodynamicLiteralPrefixConfigEquiv k).symm

/-- Complete continuous-circuit capture target of one physical literal prefix. -/
def thermodynamicLiteralPrefixContinuousCircuitCaptureTarget
    (p : InfinitePathLabel → ℝ) (k : ℕ) :
    Set (Fin (thermodynamicLiteralPrefixProjectiveDimension k) → UnitAddCircle) :=
  projectiveContinuousCircuitCaptureTarget
    (thermodynamicLiteralPrefixConfigEquiv k)
    (thermodynamicLiteralPrefixCanonicalEigenbasisUnitary p k)
    (nearHilbertContinuousCircuitBudget (k + 3)) (1 / 20 : ℝ)

/-- Membership in the spectral target is exactly physical operator-norm approximation of the
literal-prefix Schrödinger evolution, modulo global phase. -/
theorem thermodynamicLiteralPrefixContinuousCircuitCaptureTarget_physical_iff
    (p : InfinitePathLabel → ℝ) (k : ℕ) (t : ℝ) :
    projectivePhysicalPhaseFlow (thermodynamicLiteralPrefixCanonicalEnergy p k) t ∈
        thermodynamicLiteralPrefixContinuousCircuitCaptureTarget p k ↔
      ∃ c : ℂ, ‖c‖ = 1 ∧ ∃ C : TwoQubitCircuit (k + 3),
        C.gateCount ≤ nearHilbertContinuousCircuitBudget (k + 3) ∧
        ‖unitaryEvolution (pathHamiltonian (infinitePathPrefixShell k p)) t -
          c • (C.eval : Matrix (Fin (k + 3) → Bool) (Fin (k + 3) → Bool) ℂ)‖ ≤
            (1 / 20 : ℝ) := by
  let e := thermodynamicLiteralPrefixConfigEquiv k
  let H := pathHamiltonian (infinitePathPrefixShell k p)
  let hH : H.IsHermitian := by exact isSelfAdjoint_pathHamiltonian _
  let energy : Fin (thermodynamicLiteralPrefixProjectiveDimension k + 1) → ℝ :=
    fun i => hH.eigenvalues (e.symm i)
  let V := hermitianEigenbasisUnitary hH
  let x := projectivePhysicalPhaseFlow energy t
  let P := projectiveSpectralMatrix e V x
  let anchor : ℂ := Complex.exp (-(Complex.I * (t * hH.eigenvalues (e.symm 0))))
  have hanchor : ‖anchor‖ = 1 := by
    unfold anchor
    rw [Complex.norm_exp]
    simp
  have hanchor0 : anchor ≠ 0 := norm_ne_zero_iff.mp (by rw [hanchor]; norm_num)
  have hphysical : unitaryEvolution H t = anchor • P := by
    simpa [anchor, P, x, energy, V] using
      (unitaryEvolution_eq_anchorPhase_smul_projectiveSpectralMatrix e hH t)
  rw [thermodynamicLiteralPrefixContinuousCircuitCaptureTarget,
    mem_projectiveContinuousCircuitCaptureTarget_iff]
  change (∃ c : ℂ, ‖c‖ = 1 ∧ ∃ C : TwoQubitCircuit (k + 3),
      C.gateCount ≤ nearHilbertContinuousCircuitBudget (k + 3) ∧
      ‖P - c • (C.eval : Matrix (Fin (k + 3) → Bool)
        (Fin (k + 3) → Bool) ℂ)‖ ≤ (1 / 20 : ℝ)) ↔ _
  constructor
  · rintro ⟨c, hc, C, hCs, hdist⟩
    refine ⟨anchor * c, by rw [norm_mul, hanchor, hc, one_mul], C, hCs, ?_⟩
    rw [show unitaryEvolution
        (pathHamiltonian (infinitePathPrefixShell k p)) t = anchor • P by
          simpa [H] using hphysical]
    have hfactor : anchor • P - (anchor * c) •
          (C.eval : Matrix (Fin (k + 3) → Bool) (Fin (k + 3) → Bool) ℂ) =
        anchor • (P - c •
          (C.eval : Matrix (Fin (k + 3) → Bool) (Fin (k + 3) → Bool) ℂ)) := by
      module
    rw [hfactor, norm_smul, hanchor, one_mul]
    exact hdist
  · rintro ⟨c, hc, C, hCs, hdist⟩
    refine ⟨anchor⁻¹ * c, by
      rw [norm_mul, norm_inv, hanchor, inv_one, hc, one_mul], C, hCs, ?_⟩
    rw [show unitaryEvolution
        (pathHamiltonian (infinitePathPrefixShell k p)) t = anchor • P by
          simpa [H] using hphysical] at hdist
    have hfactor : P - (anchor⁻¹ * c) •
          (C.eval : Matrix (Fin (k + 3) → Bool) (Fin (k + 3) → Bool) ℂ) =
        anchor⁻¹ • (anchor • P - c •
          (C.eval : Matrix (Fin (k + 3) → Bool) (Fin (k + 3) → Bool) ℂ)) := by
      rw [smul_sub, smul_smul, inv_mul_cancel₀ hanchor0, one_smul,
        smul_smul]
    rw [hfactor, norm_smul, norm_inv, hanchor, inv_one, one_mul]
    exact hdist

theorem ThermodynamicSameFieldLifecycle.thermodynamicLiteralPrefix_continuousCircuitOccupation
    {p : InfinitePathLabel → ℝ} (hp : ThermodynamicSameFieldLifecycle p) (k : ℕ) :
    atTop.limsup (fun T =>
        (finiteTorusPhaseProbabilityMeasure
          (zeroProjectiveFrequency (thermodynamicLiteralPrefixCanonicalEnergy p k)) T :
            Measure (Fin (thermodynamicLiteralPrefixProjectiveDimension k) → UnitAddCircle))
          (thermodynamicLiteralPrefixContinuousCircuitCaptureTarget p k)) ≤
      ENNReal.ofReal (nearHilbertContinuousCircuitOccupationCost (k + 3)) := by
  have h := maximallyProjective_continuousCircuitCapture_completedTime_le
    (thermodynamicLiteralPrefixCanonicalEnergy p k)
    (maximallyProjectiveEnergy_thermodynamicLiteralPrefixCanonicalEnergy hp k)
    (thermodynamicLiteralPrefixConfigEquiv k)
    (thermodynamicLiteralPrefixCanonicalEigenbasisUnitary p k)
    (s := nearHilbertContinuousCircuitBudget (k + 3))
  have hEntropy : 0 ≤ atMostQuarterCircuitEntropyBound (k + 3)
      (nearHilbertContinuousCircuitBudget (k + 3)) := by
    unfold atMostQuarterCircuitEntropyBound
    exact Finset.sum_nonneg fun R _hR => by positivity
  rw [nearHilbertContinuousCircuitOccupationCost,
    ENNReal.ofReal_mul hEntropy,
    ENNReal.ofReal_pow continuousCircuitOccupationBase_nonneg]
  simpa [thermodynamicLiteralPrefixContinuousCircuitCaptureTarget,
    thermodynamicLiteralPrefixProjectiveDimension] using h

theorem tendsto_thermodynamicLiteralPrefixContinuousCircuitOccupationCost_atTop :
    Tendsto (fun k : ℕ => nearHilbertContinuousCircuitOccupationCost (k + 3))
      atTop (nhds 0) := by
  exact tendsto_nearHilbertContinuousCircuitOccupationCost_atTop.comp
    (tendsto_add_atTop_nat 3)

theorem exists_thermodynamicSameFieldContinuousCircuitOccupationLaw :
    ∃ p : InfinitePathLabel → ℝ,
      ThermodynamicRecurrenceDesertLifecycle p ∧
      Tendsto (fun k : ℕ => nearHilbertContinuousCircuitOccupationCost (k + 3))
        atTop (nhds 0) ∧
      ∀ k : ℕ,
        atTop.limsup (fun T =>
            (finiteTorusPhaseProbabilityMeasure
              (zeroProjectiveFrequency (thermodynamicLiteralPrefixCanonicalEnergy p k)) T :
                Measure (Fin (thermodynamicLiteralPrefixProjectiveDimension k) → UnitAddCircle))
              (thermodynamicLiteralPrefixContinuousCircuitCaptureTarget p k)) ≤
          ENNReal.ofReal (nearHilbertContinuousCircuitOccupationCost (k + 3)) := by
  obtain ⟨p, hp⟩ := exists_thermodynamicRecurrenceDesertLifecycle
  exact ⟨p, hp, tendsto_thermodynamicLiteralPrefixContinuousCircuitOccupationCost_atTop,
    fun k => ThermodynamicSameFieldLifecycle.thermodynamicLiteralPrefix_continuousCircuitOccupation
      hp.toThermodynamicSameFieldLifecycle k⟩

end

end RHTower

