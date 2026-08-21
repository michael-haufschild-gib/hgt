import GaloisForLFunctions.RHTower.NearestNeighborGaussianSameDrawGrowthPlateauRecurrenceLaw
import GaloisForLFunctions.RHTower.StaticChoiCircuitExcursionFirstReturnLaw

/-!
# Same-draw growth and complete-circuit excursion first returns

One parameter draw from the ordinary Gaussian nearest-neighbour Hamiltonian ensemble supplies the
proved laboratory-time complexity ramp.  Maximal projective rank of that same draw supplies
completed hard blocks, syndetic recurrence, and genuine consecutive visits to the entire finite
circuit dictionary bracketing each hard block.

This closes the logical difference between a hard interval and a first re-entry to the complete
circuit set.  It does not prove Brown-scale onset or a typical-draw Brown ramp.
-/

open Set Topology
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw

noncomputable section

namespace RHTower

/-- Arbitrarily late complete-circuit hard blocks for one nearest-neighbour Choi orbit, upgraded to
excursions between consecutive visits of the complete circuit capture set. -/
def NearestNeighborPathCircuitExcursionFirstReturnGaps
    (L : ℕ) {gate : Type*} [Fintype gate] (s : ℕ)
    (p : Fin (nearestNeighborPathLocalParameterCount L) → ℝ)
    (target : PaddedCircuitWord gate s →
      EuclideanSpace ℂ
        (Fin (nearestNeighborPathProjectiveDimension L + 1) ×
          Fin (nearestNeighborPathProjectiveDimension L + 1)))
    (epsn epsw : ℝ) : Prop :=
  ∃ mesh B : ℝ, 0 < mesh ∧ 0 ≤ B ∧ ∀ {W : ℝ}, 0 ≤ W →
    (Fintype.card gate : ℝ) ^ (s + 1) *
        ((((nearestNeighborPathProjectiveDimension L + 1 : ℕ) : ℝ) *
          Real.exp
            (((nearestNeighborPathProjectiveDimension L + 1 : ℕ) : ℝ) / 2) *
          Real.sqrt (Real.pi * (2 * (Real.sqrt 2 * epsw) ^ 2) / 2) ^
            ((nearestNeighborPathProjectiveDimension L + 1 : ℕ) - 1))) <
      mesh / (W + mesh) →
    ∀ A0 : ℝ, 0 ≤ A0 → ∃ u tExit tReturn : ℝ,
      A0 ≤ u ∧ tExit ∈ Icc (u - B) u ∧
        tReturn ∈ Icc (u + W) (u + W + B) ∧
        (∃ w, pureStateTraceDistance
          (fullUniformPhaseChoiVector
            (nearestNeighborPathProjectiveDimension L + 1)
            (zeroAnchoredPhase (nearestNeighborPathProjectiveDimension L)
              (projectivePhysicalPhaseFlow
                (nearestNeighborPathChoiEnergy L p) tExit)))
          (target w) ≤ epsn) ∧
        (∃ w, pureStateTraceDistance
          (fullUniformPhaseChoiVector
            (nearestNeighborPathProjectiveDimension L + 1)
            (zeroAnchoredPhase (nearestNeighborPathProjectiveDimension L)
              (projectivePhysicalPhaseFlow
                (nearestNeighborPathChoiEnergy L p) tReturn)))
          (target w) ≤ epsn) ∧
        tExit < tReturn ∧ W ≤ tReturn - tExit ∧
        ∀ t ∈ Ioo tExit tReturn,
          ¬ ∃ w, pureStateTraceDistance
            (fullUniformPhaseChoiVector
              (nearestNeighborPathProjectiveDimension L + 1)
              (zeroAnchoredPhase (nearestNeighborPathProjectiveDimension L)
                (projectivePhysicalPhaseFlow
                  (nearestNeighborPathChoiEnergy L p) t)))
            (target w) ≤ epsn

/-- One certified width of complete-circuit avoidance, bracketed by consecutive captures for the
same nearest-neighbour Hamiltonian orbit. -/
def NearestNeighborPathExplicitCircuitExcursionFirstReturnGap
    (L : ℕ) {gate : Type*} [Fintype gate] (s : ℕ)
    (p : Fin (nearestNeighborPathLocalParameterCount L) → ℝ)
    (target : PaddedCircuitWord gate s →
      EuclideanSpace ℂ
        (Fin (nearestNeighborPathProjectiveDimension L + 1) ×
          Fin (nearestNeighborPathProjectiveDimension L + 1)))
    (epsn W : ℝ) : Prop :=
  ∃ B : ℝ, 0 ≤ B ∧ ∀ A0 : ℝ, 0 ≤ A0 → ∃ u tExit tReturn : ℝ,
    A0 ≤ u ∧ tExit ∈ Icc (u - B) u ∧
      tReturn ∈ Icc (u + W) (u + W + B) ∧
      (∃ w, pureStateTraceDistance
        (fullUniformPhaseChoiVector
          (nearestNeighborPathProjectiveDimension L + 1)
          (zeroAnchoredPhase (nearestNeighborPathProjectiveDimension L)
            (projectivePhysicalPhaseFlow
              (nearestNeighborPathChoiEnergy L p) tExit)))
        (target w) ≤ epsn) ∧
      (∃ w, pureStateTraceDistance
        (fullUniformPhaseChoiVector
          (nearestNeighborPathProjectiveDimension L + 1)
          (zeroAnchoredPhase (nearestNeighborPathProjectiveDimension L)
            (projectivePhysicalPhaseFlow
              (nearestNeighborPathChoiEnergy L p) tReturn)))
        (target w) ≤ epsn) ∧
      tExit < tReturn ∧ W ≤ tReturn - tExit ∧
      ∀ t ∈ Ioo tExit tReturn,
        ¬ ∃ w, pureStateTraceDistance
          (fullUniformPhaseChoiVector
            (nearestNeighborPathProjectiveDimension L + 1)
            (zeroAnchoredPhase (nearestNeighborPathProjectiveDimension L)
              (projectivePhysicalPhaseFlow
                (nearestNeighborPathChoiEnergy L p) t)))
          (target w) ≤ epsn

/-- **Same-draw growth and complete-circuit first-reentry gaps.** The one ordinary static-local
Hamiltonian draw supplying robust laboratory-time operator-complexity growth also has arbitrarily
late continuous excursions from the complete padded circuit capture set.  Each excursion is
bracketed by consecutive captures, so its right endpoint is a literal first re-entry to the entire
circuit dictionary, and its duration is at least the certified hard-block width. -/
theorem nearestNeighborPath_sameDraw_growth_consecutiveCircuitFirstReturnGaps
    {L : ℕ} {T εGrow : ℝ}
    {p : Fin (nearestNeighborPathLocalParameterCount L) → ℝ}
    (hp : p ∈ nearestNeighborPathGaussianGrowthMaximalEvent L T εGrow)
    {gate : Type*} [Fintype gate] (s : ℕ)
    (target : PaddedCircuitWord gate s →
      EuclideanSpace ℂ
        (Fin (nearestNeighborPathProjectiveDimension L + 1) ×
          Fin (nearestNeighborPathProjectiveDimension L + 1)))
    (htarget : ∀ w, ‖target w‖ = 1)
    (identity : PaddedCircuitWord gate s)
    (hidentity : target identity =
      fullUniformPhaseChoiVector
        (nearestNeighborPathProjectiveDimension L + 1)
        (zeroAnchoredPhase (nearestNeighborPathProjectiveDimension L)
          (0 : Fin (nearestNeighborPathProjectiveDimension L) → UnitAddCircle)))
    {epsn epsw : ℝ} (hepsn : 0 < epsn) (hgap : epsn < epsw) :
    (∀ t : ℝ,
      2048 * Real.pi * εGrow ≤ t →
      t ≤ εGrow * L →
      t ≤ T →
      ((⌊t / (256 * Real.pi * εGrow)⌋₊ : ℕ) : ℕ∞) ≤
        operatorTwoGateComplexityTo L εGrow
          (unitaryEvolution (nearestNeighborPathLocalHamiltonian L p) t)) ∧
    NearestNeighborPathCircuitExcursionFirstReturnGaps
      L s p target epsn epsw := by
  refine ⟨hp.2, ?_⟩
  exact maximallyProjective_pureChoiCircuitTarget_consecutiveVisitGaps
    (nearestNeighborPathChoiEnergy L p)
    (maximallyProjectiveEnergy_nearestNeighborPathChoiEnergy hp.1)
    s target htarget identity hidentity hepsn hgap

/-- **Quantitative same-draw complete-circuit first re-entry.**  The ordinary static-local draw
supplying the laboratory ramp also has arbitrarily late consecutive circuit-capture pairs whose
first-reentry gap is at least `W`, whenever the explicit completed-occupation/speed inequality
certifies that width. -/
theorem nearestNeighborPath_sameDraw_growth_explicitConsecutiveCircuitFirstReturnGap
    {L : ℕ} {T εGrow : ℝ}
    {p : Fin (nearestNeighborPathLocalParameterCount L) → ℝ}
    (hp : p ∈ nearestNeighborPathGaussianGrowthMaximalEvent L T εGrow)
    {gate : Type*} [Fintype gate] (s : ℕ)
    (target : PaddedCircuitWord gate s →
      EuclideanSpace ℂ
        (Fin (nearestNeighborPathProjectiveDimension L + 1) ×
          Fin (nearestNeighborPathProjectiveDimension L + 1)))
    (htarget : ∀ w, ‖target w‖ = 1)
    (identity : PaddedCircuitWord gate s)
    (hidentity : target identity =
      fullUniformPhaseChoiVector
        (nearestNeighborPathProjectiveDimension L + 1)
        (zeroAnchoredPhase (nearestNeighborPathProjectiveDimension L)
          (0 : Fin (nearestNeighborPathProjectiveDimension L) → UnitAddCircle)))
    {epsn epsw W : ℝ} (hepsn : 0 < epsn) (hgap : epsn < epsw) (hW : 0 ≤ W)
    (hpack :
      (Fintype.card gate : ℝ) ^ (s + 1) *
          ((((nearestNeighborPathProjectiveDimension L + 1 : ℕ) : ℝ) *
            Real.exp
              (((nearestNeighborPathProjectiveDimension L + 1 : ℕ) : ℝ) / 2) *
            Real.sqrt (Real.pi * (2 * (Real.sqrt 2 * epsw) ^ 2) / 2) ^
              ((nearestNeighborPathProjectiveDimension L + 1 : ℕ) - 1))) <
        ((epsw - epsn) /
            projectiveChoiSpeed (nearestNeighborPathChoiEnergy L p)) /
          (W + (epsw - epsn) /
            projectiveChoiSpeed (nearestNeighborPathChoiEnergy L p))) :
    (∀ t : ℝ,
      2048 * Real.pi * εGrow ≤ t →
      t ≤ εGrow * L →
      t ≤ T →
      ((⌊t / (256 * Real.pi * εGrow)⌋₊ : ℕ) : ℕ∞) ≤
        operatorTwoGateComplexityTo L εGrow
          (unitaryEvolution (nearestNeighborPathLocalHamiltonian L p) t)) ∧
    NearestNeighborPathExplicitCircuitExcursionFirstReturnGap
      L s p target epsn W := by
  refine ⟨hp.2, ?_⟩
  exact maximallyProjective_pureChoiCircuitTarget_explicit_consecutiveVisitGap
    (nearestNeighborPathChoiEnergy L p)
    (maximallyProjectiveEnergy_nearestNeighborPathChoiEnergy hp.1)
    s target htarget identity hidentity hepsn hgap hW hpack

end RHTower
