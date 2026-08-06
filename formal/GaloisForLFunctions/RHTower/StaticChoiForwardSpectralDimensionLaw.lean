import GaloisForLFunctions.RHTower.DirectAdaptiveStaticChoiSpectralDimensionLaw

/-!
# Forward hard-time law from finite-window spectral dimension

Diagonal spectral phase translation is an exact isometry of the full Choi space and preserves
pure-state trace distance.  It converts the centered spectral-dimension shortcut estimate into a
strictly forward-time theorem: whenever the explicit replica/circuit budget is below threshold,
some time in `(0, 2T]` evades every padded circuit target.
-/

open scoped BigOperators ComplexConjugate Interval ENNReal NNReal
open MeasureTheory ProbabilityTheory

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry

def staticChoiPhaseShift
    {d : ℕ} (energy : Fin d → ℝ) (a : ℝ)
    (target : EuclideanSpace ℂ (Fin d × Fin d)) :
    EuclideanSpace ℂ (Fin d × Fin d) :=
  WithLp.toLp 2 fun ij =>
    finiteObserverHamiltonianVertexPhase a energy ij.1 * target ij

@[simp] theorem staticChoiPhaseShift_apply
    {d : ℕ} (energy : Fin d → ℝ) (a : ℝ)
    (target : EuclideanSpace ℂ (Fin d × Fin d))
    (ij : Fin d × Fin d) :
    staticChoiPhaseShift energy a target ij =
      finiteObserverHamiltonianVertexPhase a energy ij.1 * target ij := rfl

theorem norm_staticChoiPhaseShift
    {d : ℕ} (energy : Fin d → ℝ) (a : ℝ)
    (target : EuclideanSpace ℂ (Fin d × Fin d)) :
    ‖staticChoiPhaseShift energy a target‖ = ‖target‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl
  intro ij hij
  rw [staticChoiPhaseShift_apply, norm_mul,
    finiteObserverHamiltonianVertexPhase_norm, one_mul]

theorem inner_staticChoiPhaseShift
    {d : ℕ} (energy : Fin d → ℝ) (a : ℝ)
    (x y : EuclideanSpace ℂ (Fin d × Fin d)) :
    inner ℂ (staticChoiPhaseShift energy a x)
        (staticChoiPhaseShift energy a y) = inner ℂ x y := by
  rw [EuclideanSpace.inner_toLp_toLp,
    EuclideanSpace.inner_toLp_toLp]
  change
    (∑ ij : Fin d × Fin d,
      (finiteObserverHamiltonianVertexPhase a energy ij.1 * y ij) *
        starRingEnd ℂ
          (finiteObserverHamiltonianVertexPhase a energy ij.1 * x ij)) =
      ∑ ij : Fin d × Fin d, y ij * starRingEnd ℂ (x ij)
  apply Finset.sum_congr rfl
  intro ij hij
  rw [map_mul]
  have hunit :
      finiteObserverHamiltonianVertexPhase a energy ij.1 *
          starRingEnd ℂ
            (finiteObserverHamiltonianVertexPhase a energy ij.1) = 1 := by
    rw [starRingEnd_apply, Complex.star_def, Complex.mul_conj,
      Complex.normSq_eq_norm_sq,
      finiteObserverHamiltonianVertexPhase_norm]
    norm_num
  calc
    (finiteObserverHamiltonianVertexPhase a energy ij.1 * y ij) *
        (starRingEnd ℂ
            (finiteObserverHamiltonianVertexPhase a energy ij.1) *
          starRingEnd ℂ (x ij)) =
      (finiteObserverHamiltonianVertexPhase a energy ij.1 *
          starRingEnd ℂ
            (finiteObserverHamiltonianVertexPhase a energy ij.1)) *
        (y ij * starRingEnd ℂ (x ij)) := by ring_nf
    _ = y ij * starRingEnd ℂ (x ij) := by rw [hunit, one_mul]

theorem pureStateTraceDistance_staticChoiPhaseShift
    {d : ℕ} (energy : Fin d → ℝ) (a : ℝ)
    (x y : EuclideanSpace ℂ (Fin d × Fin d)) :
    pureStateTraceDistance (staticChoiPhaseShift energy a x)
        (staticChoiPhaseShift energy a y) =
      pureStateTraceDistance x y := by
  unfold pureStateTraceDistance
  rw [inner_staticChoiPhaseShift]

theorem staticChoiPhaseShift_staticSpectralChoiVector
    {d : ℕ} (energy : Fin d → ℝ) (a t : ℝ) :
    staticChoiPhaseShift energy a
        (staticSpectralChoiVector d t energy) =
      staticSpectralChoiVector d (t + a) energy := by
  ext ij
  simp only [staticChoiPhaseShift_apply, staticSpectralChoiVector,
    fullUniformPhaseChoiVector_apply]
  split_ifs with hij
  · rw [fourier_finiteHamiltonianAddCirclePhase,
      fourier_finiteHamiltonianAddCirclePhase]
    unfold finiteObserverHamiltonianVertexPhase
    rw [show
      Complex.exp (Complex.I * (a * energy ij.1 : ℝ)) *
          (((Real.sqrt (d : ℝ))⁻¹ : ℂ) *
            Complex.exp (Complex.I * (t * energy ij.1 : ℝ))) =
        ((Real.sqrt (d : ℝ))⁻¹ : ℂ) *
          (Complex.exp (Complex.I * (a * energy ij.1 : ℝ)) *
            Complex.exp (Complex.I * (t * energy ij.1 : ℝ))) by ring_nf]
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring_nf
  · rw [mul_zero]

theorem staticChoiPhaseShift_add_neg
    {d : ℕ} (energy : Fin d → ℝ) (a : ℝ)
    (target : EuclideanSpace ℂ (Fin d × Fin d)) :
    staticChoiPhaseShift energy a
        (staticChoiPhaseShift energy (-a) target) = target := by
  ext ij
  simp only [staticChoiPhaseShift_apply]
  have hphase :
      finiteObserverHamiltonianVertexPhase a energy ij.1 *
          finiteObserverHamiltonianVertexPhase (-a) energy ij.1 = 1 := by
    unfold finiteObserverHamiltonianVertexPhase
    rw [← Complex.exp_add]
    rw [show
      Complex.I * (a * energy ij.1 : ℝ) +
          Complex.I * ((-a) * energy ij.1 : ℝ) = 0 by
            push_cast
            ring_nf,
      Complex.exp_zero]
  calc
    finiteObserverHamiltonianVertexPhase a energy ij.1 *
        (finiteObserverHamiltonianVertexPhase (-a) energy ij.1 * target ij) =
      (finiteObserverHamiltonianVertexPhase a energy ij.1 *
        finiteObserverHamiltonianVertexPhase (-a) energy ij.1) * target ij := by
          ring_nf
    _ = target ij := by rw [hphase, one_mul]

theorem staticChoiTargetCaptureSet_shift_iff
    {d : ℕ} (energy : Fin d → ℝ) (a t epsilon : ℝ)
    (target : EuclideanSpace ℂ (Fin d × Fin d)) :
    t ∈ staticChoiTargetCaptureSet energy
        (staticChoiPhaseShift energy (-a) target) epsilon ↔
      t + a ∈ staticChoiTargetCaptureSet energy target epsilon := by
  unfold staticChoiTargetCaptureSet
  have hdistance :
      pureStateTraceDistance (staticSpectralChoiVector d (t + a) energy)
          target =
        pureStateTraceDistance (staticSpectralChoiVector d t energy)
          (staticChoiPhaseShift energy (-a) target) := by
    calc
      pureStateTraceDistance (staticSpectralChoiVector d (t + a) energy)
          target =
        pureStateTraceDistance
          (staticChoiPhaseShift energy a
            (staticSpectralChoiVector d t energy)) target := by
              rw [staticChoiPhaseShift_staticSpectralChoiVector]
      _ = pureStateTraceDistance
          (staticChoiPhaseShift energy a
            (staticSpectralChoiVector d t energy))
          (staticChoiPhaseShift energy a
            (staticChoiPhaseShift energy (-a) target)) := by
              rw [staticChoiPhaseShift_add_neg]
      _ = pureStateTraceDistance (staticSpectralChoiVector d t energy)
          (staticChoiPhaseShift energy (-a) target) :=
            pureStateTraceDistance_staticChoiPhaseShift _ _ _ _
  change
    pureStateTraceDistance (staticSpectralChoiVector d t energy)
        (staticChoiPhaseShift energy (-a) target) ≤ epsilon ↔
      pureStateTraceDistance (staticSpectralChoiVector d (t + a) energy)
        target ≤ epsilon
  rw [hdistance]

theorem exists_forward_directAdaptivePaddedCircuitHardTime_of_spectralDimensionBudget
    {d : ℕ} (hd : 0 < d)
    {gate : Type*} [Fintype gate] {energy : Fin d → ℝ}
    (hmax : MaximallyProjectiveEnergy energy)
    (s : ℕ)
    (target : PaddedCircuitWord gate s →
      EuclideanSpace ℂ (Fin d × Fin d))
    (htarget : ∀ w, ‖target w‖ = 1)
    (n : ℕ) (hn : 0 < n) {T δ epsilon : ℝ}
    (hT : 0 < T) (hδ : 0 < δ) (hepsilon : 0 ≤ epsilon)
    (hepsilonOne : epsilon ≤ 1)
    (hbudget :
      (Fintype.card gate : ℝ) ^ (s + 1) *
          ((n.factorial : ℝ) * (d : ℝ)⁻¹ ^ n +
            (((2 * n + 1) ^ replicaNearActionRank energy n δ : ℕ) : ℝ) *
              ((n.factorial : ℝ) * (d : ℝ)⁻¹ ^ n) +
            min 1 (T * δ)⁻¹) <
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
  obtain ⟨u, hu, hhard⟩ :=
    exists_directAdaptivePaddedCircuitHardTime_of_spectralDimensionBudget
      hd hmax s shiftedTarget hshiftedNorm n hn hT hδ hepsilon
        hepsilonOne hbudget
  refine ⟨u + T, ?_, ?_⟩
  · constructor <;> linarith [hu.1, hu.2]
  · intro w hw
    apply hhard w
    change u ∈ staticChoiTargetCaptureSet energy
      (staticChoiPhaseShift energy (-T) (target w)) epsilon
    rw [staticChoiTargetCaptureSet_shift_iff]
    exact hw

end RHTower
