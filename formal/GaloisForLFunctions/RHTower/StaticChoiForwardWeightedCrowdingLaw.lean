import GaloisForLFunctions.RHTower.DirectAdaptiveStaticChoiWeightedCrowdingLaw
import GaloisForLFunctions.RHTower.StaticChoiForwardSpectralDimensionLaw

/-!
# Forward hard time from target-weighted resonance mass

Spectral phase translation preserves every target's diagonal weight profile and therefore the
entire adaptive near-action partition function.  The exact target-weighted centered-window law
thus yields a forward hard endpoint in `(0, 2T]` without paying a worst-spectrum crowding degree.
-/

open scoped BigOperators ComplexConjugate Interval ENNReal NNReal
open MeasureTheory ProbabilityTheory

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry

theorem directStaticChoiTargetWeight_phaseShift
    {d : ℕ} (energy : Fin d → ℝ) (a : ℝ)
    (target : EuclideanSpace ℂ (Fin d × Fin d)) :
    directStaticChoiTargetWeight d (staticChoiPhaseShift energy a target) =
      directStaticChoiTargetWeight d target := by
  funext i
  unfold directStaticChoiTargetWeight
  rw [staticChoiPhaseShift_apply, norm_mul,
    finiteObserverHamiltonianVertexPhase_norm, one_mul]

theorem directStaticChoiTargetNearActionMass_phaseShift
    {d : ℕ} (energy : Fin d → ℝ) (a : ℝ)
    (target : EuclideanSpace ℂ (Fin d × Fin d))
    (n : ℕ) (δ : ℝ) :
    directStaticChoiTargetNearActionMass
        (staticChoiPhaseShift energy a target) energy n δ =
      directStaticChoiTargetNearActionMass target energy n δ := by
  unfold directStaticChoiTargetNearActionMass
  rw [directStaticChoiTargetWeight_phaseShift]

theorem directAdaptiveChoiNearActionPartition_phaseShift
    {d : ℕ} {W : Type*} [Fintype W]
    (energy : Fin d → ℝ) (a : ℝ)
    (target : W → EuclideanSpace ℂ (Fin d × Fin d))
    (n : ℕ) (δ : ℝ) :
    directAdaptiveChoiNearActionPartition
        (fun w => staticChoiPhaseShift energy a (target w)) energy n δ =
      directAdaptiveChoiNearActionPartition target energy n δ := by
  unfold directAdaptiveChoiNearActionPartition
  apply Finset.sum_congr rfl
  intro w hw
  exact directStaticChoiTargetNearActionMass_phaseShift
    energy a (target w) n δ

theorem exists_forward_directAdaptivePaddedCircuitHardTime_of_weightedCrowdingBudget
    {d : ℕ} (hd : 0 < d)
    {gate : Type*} [Fintype gate] {energy : Fin d → ℝ}
    (hmax : MaximallyProjectiveEnergy energy)
    (s : ℕ)
    (target : PaddedCircuitWord gate s → EuclideanSpace ℂ (Fin d × Fin d))
    (htarget : ∀ w, ‖target w‖ = 1)
    (n : ℕ) (hn : 0 < n) {T δ epsilon : ℝ}
    (hT : 0 < T) (hδ : 0 < δ) (hepsilon : 0 ≤ epsilon)
    (hepsilonOne : epsilon ≤ 1)
    (hbudget :
      (Fintype.card gate : ℝ) ^ (s + 1) *
          ((n.factorial : ℝ) * (d : ℝ)⁻¹ ^ n +
            min 1 (T * δ)⁻¹) +
          directAdaptiveChoiNearActionPartition target energy n δ <
        (1 - epsilon ^ 2) ^ n) :
    ∃ t ∈ Set.Ioc 0 (2 * T),
      ∀ w : PaddedCircuitWord gate s,
        t ∉ staticChoiTargetCaptureSet energy (target w) epsilon := by
  let shiftedTarget : PaddedCircuitWord gate s →
      EuclideanSpace ℂ (Fin d × Fin d) := fun w =>
    staticChoiPhaseShift energy (-T) (target w)
  have hshiftedNorm : ∀ w, ‖shiftedTarget w‖ = 1 := by
    intro w
    change ‖staticChoiPhaseShift energy (-T) (target w)‖ = 1
    rw [norm_staticChoiPhaseShift, htarget]
  have hpartition :
      directAdaptiveChoiNearActionPartition shiftedTarget energy n δ =
        directAdaptiveChoiNearActionPartition target energy n δ := by
    change
      directAdaptiveChoiNearActionPartition
          (fun w => staticChoiPhaseShift energy (-T) (target w)) energy n δ =
        directAdaptiveChoiNearActionPartition target energy n δ
    exact directAdaptiveChoiNearActionPartition_phaseShift
      energy (-T) target n δ
  have hshiftedBudget :
      (Fintype.card gate : ℝ) ^ (s + 1) *
          ((n.factorial : ℝ) * (d : ℝ)⁻¹ ^ n +
            min 1 (T * δ)⁻¹) +
          directAdaptiveChoiNearActionPartition shiftedTarget energy n δ <
        (1 - epsilon ^ 2) ^ n := by
    rw [hpartition]
    exact hbudget
  obtain ⟨u, hu, hhard⟩ :=
    exists_directAdaptivePaddedCircuitHardTime_of_weightedCrowdingBudget
      hd hmax s shiftedTarget hshiftedNorm n hn hT hδ hepsilon
        hepsilonOne hshiftedBudget
  refine ⟨u + T, ?_, ?_⟩
  · constructor <;> linarith [hu.1, hu.2]
  · intro w hw
    apply hhard w
    change u ∈ staticChoiTargetCaptureSet energy
      (staticChoiPhaseShift energy (-T) (target w)) epsilon
    rw [staticChoiTargetCaptureSet_shift_iff]
    exact hw

end RHTower
