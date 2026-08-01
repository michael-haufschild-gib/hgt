import GaloisForLFunctions.HTGeometry.FiniteSpectralHaarRecurrenceLaw
import GaloisForLFunctions.RHTower.ProjectiveWeightedTargetVolumeLower

/-!
# Long-time frequency law for finite spectral recurrence

For every rationally independent finite frequency packet, centered
continuous-time sampling converges to Haar measure on the full phase torus.
This file transfers that weak convergence to high-fidelity recurrence
targets without imposing a boundary-null hypothesis: a slightly smaller
closed target supplies the lower frequency bound, while the original closed
target supplies the upper bound.
-/

open Filter MeasureTheory Set Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Canonical finite reindexing of a frequency family on an arbitrary
finite carrier. -/
def finReindexedFrequency {I : Type*} [Fintype I]
    (frequency : I → ℝ) : Fin (Fintype.card I) → ℝ :=
  frequency ∘ (Fintype.equivFin I).symm

/-- Rational independence is invariant under canonical finite reindexing. -/
theorem rationallyIndependentFrequency_finReindexed
    {I : Type*} [Fintype I] (frequency : I → ℝ)
    (hindependent : RationallyIndependentFrequency frequency) :
    RationallyIndependentFrequency (finReindexedFrequency frequency) := by
  intro n hdetuning
  let e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  let k : I → ℤ := n ∘ e
  have hsum : finiteTorusCharacterDetuning k frequency =
      finiteTorusCharacterDetuning n
        (finReindexedFrequency frequency) := by
    rw [finiteTorusCharacterDetuning, finiteTorusCharacterDetuning]
    simpa [k, e, finReindexedFrequency] using
      e.sum_comp (fun i ↦
        (n i : ℝ) * finReindexedFrequency frequency i)
  have hk : k = 0 := hindependent k (hsum.trans hdetuning)
  funext i
  have hi := congrFun hk (e.symm i)
  simpa [k, e] using hi

/-- Strict high-fidelity recurrence target for a weighted phase packet. -/
def strictProjectiveWeightedCoherenceTarget {d : ℕ}
    (weight : Fin d → ℝ) (η : ℝ) : Set (UnitAddTorus (Fin d)) :=
  {x | 1 - η < ‖RHTower.projectiveWeightedPhaseAmplitude weight
    (fun j ↦ fourier 1 (x j))‖}

theorem isOpen_strictProjectiveWeightedCoherenceTarget
    {d : ℕ} (weight : Fin d → ℝ) (η : ℝ) :
    IsOpen (strictProjectiveWeightedCoherenceTarget weight η) := by
  rw [strictProjectiveWeightedCoherenceTarget]
  exact isOpen_lt continuous_const
    (RHTower.continuous_torusProjectiveWeightedCoherenceAmplitude weight)

theorem isClosed_torusProjectiveWeightedCoherenceTarget
    {d : ℕ} (weight : Fin d → ℝ) (η : ℝ) :
    IsClosed (RHTower.torusProjectiveWeightedCoherenceTarget weight η) := by
  rw [RHTower.torusProjectiveWeightedCoherenceTarget]
  exact isClosed_le continuous_const
    (RHTower.continuous_torusProjectiveWeightedCoherenceAmplitude weight)

/-- Normalized product Haar measure is the canonical volume measure on the
finite unit torus. -/
theorem finiteTorusHaarProbabilityMeasure_toMeasure_eq_volume
    {d : Type*} [Fintype d] :
    (finiteTorusHaarProbabilityMeasure d : Measure (UnitAddTorus d)) =
      volume := by
  change Measure.pi (fun _ : d ↦ AddCircle.haarAddCircle) =
    (volume : Measure (UnitAddTorus d))
  rw [MeasureTheory.volume_pi]
  congr 1
  funext i
  rw [AddCircle.volume_eq_smul_haarAddCircle]
  simp

/-- At every positive tolerance, the closed half-tolerance target lies
inside the strict full-tolerance target. -/
theorem halfTarget_subset_strictTarget
    {d : ℕ} (weight : Fin d → ℝ) {η : ℝ} (hη : 0 < η) :
    RHTower.torusProjectiveWeightedCoherenceTarget weight (η / 2) ⊆
      strictProjectiveWeightedCoherenceTarget weight η := by
  intro x hx
  rw [RHTower.torusProjectiveWeightedCoherenceTarget,
    Set.mem_setOf_eq] at hx
  rw [strictProjectiveWeightedCoherenceTarget, Set.mem_setOf_eq]
  linarith

/-- Every closed target inherits its Haar upper bound as a completed-time
upper frequency under a rationally independent finite phase flow. -/
theorem rationallyIndependent_closedTarget_limsup_le_volume
    {d : Type*} [Fintype d]
    (frequency : d → ℝ)
    (hindependent : RationallyIndependentFrequency frequency)
    {A : Set (UnitAddTorus d)} (hA : IsClosed A) :
    atTop.limsup (fun T ↦
        (finiteTorusPhaseProbabilityMeasure frequency T :
          Measure (UnitAddTorus d)) A) ≤ volume A := by
  have hlim := finiteTorusPhaseProbabilityMeasure_tendsto_haar
    frequency hindependent
  have hclosed :=
    ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hlim hA
  rw [finiteTorusHaarProbabilityMeasure_toMeasure_eq_volume] at hclosed
  exact hclosed

/-- **Long-time recurrence-frequency law.** For every rationally independent
finite frequency packet and every positive fidelity tolerance, the lower
completed-time frequency of strict returns is at least the Haar volume of
the half-tolerance target, while the upper completed-time frequency of weak
returns is at most the Haar volume of the full target.

The tolerance separation removes every regular-value or null-boundary
assumption. -/
theorem rationallyIndependent_projectiveCoherenceFrequency_sandwich
    {d : ℕ} (frequency weight : Fin d → ℝ)
    (hindependent : RationallyIndependentFrequency frequency)
    {η : ℝ} (hη : 0 < η) :
    volume
        (RHTower.torusProjectiveWeightedCoherenceTarget weight (η / 2)) ≤
      atTop.liminf (fun A ↦
        (finiteTorusPhaseProbabilityMeasure frequency A :
          Measure (UnitAddTorus (Fin d)))
            (strictProjectiveWeightedCoherenceTarget weight η)) ∧
    atTop.limsup (fun A ↦
        (finiteTorusPhaseProbabilityMeasure frequency A :
          Measure (UnitAddTorus (Fin d)))
            (RHTower.torusProjectiveWeightedCoherenceTarget weight η)) ≤
      volume
        (RHTower.torusProjectiveWeightedCoherenceTarget weight η) := by
  have hlim := finiteTorusPhaseProbabilityMeasure_tendsto_haar
    frequency hindependent
  have hopen :=
    ProbabilityMeasure.le_liminf_measure_open_of_tendsto hlim
      (isOpen_strictProjectiveWeightedCoherenceTarget weight η)
  have hclosed :=
    ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hlim
      (isClosed_torusProjectiveWeightedCoherenceTarget weight η)
  rw [finiteTorusHaarProbabilityMeasure_toMeasure_eq_volume]
    at hopen hclosed
  exact
    ⟨(measure_mono (halfTarget_subset_strictTarget weight hη)).trans hopen,
      hclosed⟩

end

end GaloisForLFunctions.HTGeometry
