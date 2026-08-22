import GaloisForLFunctions.HTGeometry.GateWordDictionary
import GaloisForLFunctions.HTGeometry.PureConjugationChannel
import GaloisForLFunctions.HTGeometry.ReplicaProjectionIncidenceLaw
import GaloisForLFunctions.RHTower.AutonomousReturnReflection
import GaloisForLFunctions.RHTower.StaticChoiOptimalDesignWeightedCrowdingFirstReturnLaw

open scoped BigOperators
open Matrix
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- Vectorized unitary conjugation transports normalized Choi vectors
exactly, including their dimension normalization. -/
theorem pureConjugationChannel_mulVec_choiVector
    {α : Type*} [Fintype α]
    (A X : Matrix α α ℂ) :
    pureConjugationChannel A *ᵥ
        (GaloisForLFunctions.RHTower.choiVector X).ofLp =
      (GaloisForLFunctions.RHTower.choiVector (A * X * Aᴴ)).ofLp := by
  let z : ℂ := (Real.sqrt (Fintype.card α) : ℂ)⁻¹
  have hscale (Y : Matrix α α ℂ) :
      (GaloisForLFunctions.RHTower.choiVector Y).ofLp =
        z • matrixVectorization Y := by
    funext p
    simp only [GaloisForLFunctions.RHTower.choiVector,
      WithLp.ofLp_toLp, Pi.smul_apply, matrixVectorization]
    dsimp [z]
    rw [div_eq_mul_inv, mul_comm]
  rw [hscale X, Matrix.mulVec_smul,
    pureConjugationChannel_mulVec, ← hscale]

/-- Conjugation by a physical unitary, represented as a unitary on the
vectorized operator (Choi) space. -/
def pureConjugationUnitary
    {α : Type*} [Fintype α] [DecidableEq α]
    (U : Matrix.unitaryGroup α ℂ) :
    Matrix.unitaryGroup (α × α) ℂ := by
  refine ⟨pureConjugationChannel (U : Matrix α α ℂ), ?_⟩
  constructor
  · rw [Matrix.star_eq_conjTranspose,
      pureConjugationChannel_conjTranspose,
      pureConjugationChannel_mul]
    have hstarU :
        (U : Matrix α α ℂ)ᴴ * (U : Matrix α α ℂ) = 1 := by
      simpa only [Matrix.star_eq_conjTranspose] using U.property.1
    rw [hstarU, pureConjugationChannel_one]
  · rw [Matrix.star_eq_conjTranspose,
      pureConjugationChannel_conjTranspose,
      pureConjugationChannel_mul]
    have hUstar :
        (U : Matrix α α ℂ) * (U : Matrix α α ℂ)ᴴ = 1 := by
      simpa only [Matrix.star_eq_conjTranspose] using U.property.2
    rw [hUstar, pureConjugationChannel_one]

/-- Common unitary transport of a finite pure-state target dictionary. -/
def unitaryTransportTarget
    {C α : Type*} [Fintype α] [DecidableEq α]
    (U : Matrix.unitaryGroup α ℂ) (target : C → α → ℂ) :
    C → α → ℂ :=
  fun c => (U : Matrix α α ℂ) *ᵥ target c

theorem finitePureStateFidelity_unitary_mulVec
    {α : Type*} [Fintype α] [DecidableEq α]
    (U : Matrix.unitaryGroup α ℂ) (ψ φ : α → ℂ) :
    finitePureStateFidelity
        ((U : Matrix α α ℂ) *ᵥ ψ)
        ((U : Matrix α α ℂ) *ᵥ φ) =
      finitePureStateFidelity ψ φ := by
  rw [finitePureStateFidelity, finitePureStateFidelity,
    finiteComplexInner_mulVec_unitary
      (Unitary.coe_star_mul_self U)]

theorem finitePureStateFidelity_unitary_pull
    {α : Type*} [Fintype α] [DecidableEq α]
    (U : Matrix.unitaryGroup α ℂ) (ψ φ : α → ℂ) :
    finitePureStateFidelity
        ((U : Matrix α α ℂ)ᴴ *ᵥ ψ) φ =
      finitePureStateFidelity ψ
        ((U : Matrix α α ℂ) *ᵥ φ) := by
  have hUUstar :
      (U : Matrix α α ℂ) * (U : Matrix α α ℂ)ᴴ = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using U.property.2
  have h := finitePureStateFidelity_unitary_mulVec U
    ((U : Matrix α α ℂ)ᴴ *ᵥ ψ) φ
  simpa only [Matrix.mulVec_mulVec, hUUstar, Matrix.one_mulVec] using h.symm

/-- A common unitary coordinate change preserves the exact occupied
replica-span dimension, including all target collisions. -/
theorem finrank_replicaTargetSpan_unitaryTransportTarget
    {C α : Type*} [Fintype α] [DecidableEq α]
    (r : ℕ) (U : Matrix.unitaryGroup α ℂ)
    (target : C → α → ℂ) :
    Module.finrank ℂ
        (replicaTargetSpan r (unitaryTransportTarget U target)) =
      Module.finrank ℂ (replicaTargetSpan r target) := by
  change Module.finrank ℂ
      (replicaTargetSpan r
        (fun c => (U : Matrix α α ℂ) *ᵥ target c)) = _
  apply Nat.le_antisymm
  · have hforward :=
      finrank_projectedReplicaTargetSpan_le r
        (Matrix.toLpLin 2 2 (U : Matrix α α ℂ)) target
    simp only [Matrix.toLpLin_apply] at hforward
    change Module.finrank ℂ
        (replicaTargetSpan r
          (fun c => (U : Matrix α α ℂ) *ᵥ target c)) ≤ _ at hforward
    exact hforward
  · have hreverse :=
      finrank_projectedReplicaTargetSpan_le r
        (Matrix.toLpLin 2 2
          ((U : Matrix α α ℂ)ᴴ))
        (fun c => (U : Matrix α α ℂ) *ᵥ target c)
    have hstarU :
        (U : Matrix α α ℂ)ᴴ * (U : Matrix α α ℂ) = 1 := by
      simpa only [Matrix.star_eq_conjTranspose] using U.property.1
    simp only [Matrix.toLpLin_apply] at hreverse
    change Module.finrank ℂ
        (replicaTargetSpan r
          (fun c => (U : Matrix α α ℂ)ᴴ *ᵥ
            ((U : Matrix α α ℂ) *ᵥ target c))) ≤ _ at hreverse
    have hback :
        (fun c => (U : Matrix α α ℂ)ᴴ *ᵥ
          ((U : Matrix α α ℂ) *ᵥ target c)) = target := by
      funext c
      rw [Matrix.mulVec_mulVec, hstarU, Matrix.one_mulVec]
    rw [hback] at hreverse
    exact hreverse

/-- **Draw-independent optimal-design transport.** Determinant-optimal
weights selected once from a normalized physical target dictionary obey
the exact same leverage inequality after every common unitary coordinate
change. The weights are not reselected after the unitary is known. -/
theorem replicaTargetOptimalDesignWeight_pointwise_unitaryTransport
    {C α : Type*} [Fintype C] [Nonempty C] [DecidableEq C]
    [Fintype α] [DecidableEq α]
    (r : ℕ) (target : C → α → ℂ)
    (htarget : ∀ c, finiteComplexInner (target c) (target c) = 1)
    (U : Matrix.unitaryGroup α ℂ)
    (ψ : α → ℂ) (c : C) :
    finitePureStateFidelity ψ (unitaryTransportTarget U target c) ^ r ≤
      (Module.finrank ℂ
        (replicaTargetSpan r (unitaryTransportTarget U target)) : ℝ) *
        ∑ j, replicaTargetOptimalDesignWeight r target htarget j *
          finitePureStateFidelity ψ
            (unitaryTransportTarget U target j) ^ r := by
  have hbase :=
    replicaTargetOptimalDesignWeight_pointwise r target htarget
      ((U : Matrix α α ℂ)ᴴ *ᵥ ψ) c
  rw [finrank_replicaTargetSpan_unitaryTransportTarget r U target]
  change finitePureStateFidelity ψ
        ((U : Matrix α α ℂ) *ᵥ target c) ^ r ≤
      (Module.finrank ℂ (replicaTargetSpan r target) : ℝ) *
        ∑ j, replicaTargetOptimalDesignWeight r target htarget j *
          finitePureStateFidelity ψ
            ((U : Matrix α α ℂ) *ᵥ target j) ^ r
  simpa only [finitePureStateFidelity_unitary_pull U] using hbase

end

end RHTower
