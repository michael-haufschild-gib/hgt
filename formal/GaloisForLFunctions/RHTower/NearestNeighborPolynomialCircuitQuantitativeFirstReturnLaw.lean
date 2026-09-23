import GaloisForLFunctions.RHTower.NearestNeighborPolynomialCircuitPermanentHaarSeparationLaw
import GaloisForLFunctions.RHTower.StaticChoiQuantitativeCircuitFirstReturnLaw

/-!
# Quantitative circuit first re-entry for one ordinary static local draw

The existing same-draw theorem supplies arbitrarily late circuit-free
excursions of width `(3/2)^(4^L)` for one ordinary nearest-neighbour Gaussian
Hamiltonian.  The rank-only quantitative recurrence law now bounds the first
re-entry after a half-width closed sub-block.  At fixed operational resolution
`1/200`, choosing `Q = 10000` gives deadline base `10001` in projective
spectral dimension `4^L - 1`.

Thus the same draw has laboratory-time growth, arbitrarily late
double-exponential circuit-free plateaux, a literal bounded first re-entry to
the complete polynomial-depth circuit dictionary, and permanent efficient
separation from Haar randomness.
-/

open Filter Set Topology
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw

noncomputable section

namespace RHTower

/-- `Q = 10000` resolves a projective Choi return inside trace distance
`1/200`; the crude universal bound `pi ≤ 4` already suffices. -/
lemma quantitativeRecurrenceResolution_one_div_twoHundred :
    2 * (2 * Real.pi / (10001 : ℝ)) ^ (2 : ℕ) ≤
      (1 / 200 : ℝ) ^ (2 : ℕ) := by
  have htwoPi : 0 ≤ 2 * Real.pi := by positivity
  have htwoPiLe : 2 * Real.pi ≤ 8 := by
    linarith [Real.pi_le_four]
  calc
    2 * (2 * Real.pi / (10001 : ℝ)) ^ (2 : ℕ) ≤
        2 * (8 / 10001 : ℝ) ^ (2 : ℕ) := by
      gcongr
    _ ≤ (1 / 200 : ℝ) ^ (2 : ℕ) := by norm_num

/-- Arbitrarily late circuit-free blocks whose bracketing first re-entry has
an explicit dimension-rank deadline. -/
def NearestNeighborPathQuantitativeCircuitExcursionFirstReturnGap
    (L : ℕ) {gate : Type*} [Fintype gate] (s : ℕ)
    (p : Fin (nearestNeighborPathLocalParameterCount L) → ℝ)
    (target : PaddedCircuitWord gate s →
      EuclideanSpace ℂ
        (Fin (nearestNeighborPathProjectiveDimension L + 1) ×
          Fin (nearestNeighborPathProjectiveDimension L + 1)))
    (eps W : ℝ) (Q : ℕ) : Prop :=
  ∀ A0 : ℝ, 0 ≤ A0 → ∃ u tExit tReturn : ℝ,
    A0 ≤ u ∧ tExit ∈ Icc 0 u ∧
      tReturn ∈ Icc (u + W)
        ((((Nat.ceil (u + W) + 1) *
          (Q + 1) ^ nearestNeighborPathProjectiveDimension L : ℕ) : ℝ)) ∧
      (∃ w, pureStateTraceDistance
        (fullUniformPhaseChoiVector
          (nearestNeighborPathProjectiveDimension L + 1)
          (zeroAnchoredPhase (nearestNeighborPathProjectiveDimension L)
            (projectivePhysicalPhaseFlow
              (nearestNeighborPathChoiEnergy L p) tExit)))
        (target w) ≤ eps) ∧
      (∃ w, pureStateTraceDistance
        (fullUniformPhaseChoiVector
          (nearestNeighborPathProjectiveDimension L + 1)
          (zeroAnchoredPhase (nearestNeighborPathProjectiveDimension L)
            (projectivePhysicalPhaseFlow
              (nearestNeighborPathChoiEnergy L p) tReturn)))
        (target w) ≤ eps) ∧
      tExit < tReturn ∧ W ≤ tReturn - tExit ∧
      ∀ t ∈ Ioo tExit tReturn,
        ¬ ∃ w, pureStateTraceDistance
          (fullUniformPhaseChoiVector
            (nearestNeighborPathProjectiveDimension L + 1)
            (zeroAnchoredPhase (nearestNeighborPathProjectiveDimension L)
              (projectivePhysicalPhaseFlow
                (nearestNeighborPathChoiEnergy L p) t)))
          (target w) ≤ eps

/-- **Same-draw quantitative growth--plateau--first-reentry law.**  For every
finite gate alphabet and polynomial depth exponent, all sufficiently long
ordinary static nearest-neighbour chains admit one draw with the certified
laboratory ramp, arbitrarily late circuit-free blocks of width
`(3/2)^(4^L)/2`, a literal first re-entry bounded by the rank-only recurrence
deadline with base `10001`, and permanent two-query separation from Haar. -/
theorem eventually_exists_nearestNeighborPath_polynomial_sameDraw_quantitativeExponentialCircuitFirstReturn
    (gate : Type*) [Fintype gate] (k : ℕ) :
    ∀ᶠ L : ℕ in atTop,
      ∀ (target : PaddedCircuitWord gate (L ^ k) →
          EuclideanSpace ℂ
            (Fin (nearestNeighborPathProjectiveDimension L + 1) ×
              Fin (nearestNeighborPathProjectiveDimension L + 1))),
        (∀ w, ‖target w‖ = 1) →
        ∀ identityWord : PaddedCircuitWord gate (L ^ k),
          target identityWord =
            fullUniformPhaseChoiVector (nearestNeighborPathProjectiveDimension L + 1)
              (zeroAnchoredPhase (nearestNeighborPathProjectiveDimension L)
                (0 : Fin (nearestNeighborPathProjectiveDimension L) → UnitAddCircle)) →
          ∃ p : Fin (nearestNeighborPathLocalParameterCount L) → ℝ,
            p ∈ nearestNeighborPathGaussianGrowthMaximalEvent L
              ((1 / 10000 : ℝ) * L) (1 / 10000 : ℝ) ∧
            NearestNeighborPathQuantitativeCircuitExcursionFirstReturnGap
              L (L ^ k) p target (1 / 200 : ℝ)
                (((3 / 2 : ℝ) ^ (4 ^ L)) / 2) 10000 ∧
            NearestNeighborPathPermanentLocalityHaarSeparation L p := by
  filter_upwards [
    eventually_exists_nearestNeighborPath_polynomial_sameDraw_exponentialCircuitExcursion_and_permanentHaarSeparation
      gate k] with L hL
  intro target htarget identityWord hidentity
  obtain ⟨p, hgrowth, _hball, hexcursion, _hfloor, hhaar⟩ :=
    hL target htarget identityWord hidentity
  refine ⟨p, hgrowth, ?_, hhaar⟩
  obtain ⟨B, hB, hlate⟩ := hexcursion
  intro A0 hA0
  let Wfull : ℝ := (3 / 2 : ℝ) ^ (4 ^ L)
  have hWfull : 0 < Wfull := by positivity
  obtain ⟨uOld, tOldExit, tOldReturn, huOld, htOldExit,
      _htOldReturn, _htOldExitCapture, _htOldReturnCapture,
      _htOldLt, htOldWidth, htOldBetween⟩ :=
    hlate (A0 + B) (add_nonneg hA0 hB)
  let uHard : ℝ := tOldExit + Wfull / 4
  let W : ℝ := Wfull / 2
  have htOldExitA0 : A0 ≤ tOldExit := by
    linarith [huOld, htOldExit.1]
  have huHardA0 : A0 ≤ uHard := by
    dsimp [uHard]
    linarith
  have huHard0 : 0 ≤ uHard := le_trans hA0 huHardA0
  have hW0 : 0 ≤ W := by positivity
  have havoid : ∀ t ∈ Icc uHard (uHard + W),
      ∀ w, (1 / 200 : ℝ) < pureStateTraceDistance
        (fullUniformPhaseChoiVector
          (nearestNeighborPathProjectiveDimension L + 1)
          (zeroAnchoredPhase (nearestNeighborPathProjectiveDimension L)
            (projectivePhysicalPhaseFlow
              (nearestNeighborPathChoiEnergy L p) t)))
        (target w) := by
    intro t ht w
    have htInterior : t ∈ Ioo tOldExit tOldReturn := by
      constructor
      · have hstart : tOldExit < uHard := by
          dsimp [uHard]
          linarith [hWfull]
        exact hstart.trans_le ht.1
      · have hupper : t ≤ tOldExit + 3 * Wfull / 4 := by
          dsimp [uHard, W] at ht
          linarith [ht.2]
        have hfullEnd : tOldExit + Wfull ≤ tOldReturn := by
          linarith [htOldWidth]
        linarith
    by_contra hnot
    push Not at hnot
    exact htOldBetween t htInterior ⟨w, hnot⟩
  obtain ⟨tExit, tReturn, htExit, htReturn, hExitCapture,
      hReturnCapture, hlt, hwidth, hbetween⟩ :=
    pureChoiCircuitTarget_quantitativeConsecutiveVisitGap
      (nearestNeighborPathChoiEnergy L p) (L ^ k) target identityWord
      hidentity (by norm_num) huHard0 hW0 havoid 10000
      (by convert quantitativeRecurrenceResolution_one_div_twoHundred using 1 <;> norm_num)
  exact ⟨uHard, tExit, tReturn, huHardA0, htExit, htReturn,
    hExitCapture, hReturnCapture, hlt, hwidth, hbetween⟩

end RHTower
