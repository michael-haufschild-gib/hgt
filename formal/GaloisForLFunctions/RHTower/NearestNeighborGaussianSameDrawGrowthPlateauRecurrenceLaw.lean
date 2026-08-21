import GaloisForLFunctions.HTGeometry.NearestNeighborGaussianSameDrawGrowthLaw
import GaloisForLFunctions.HTGeometry.PauliBoundedHamiltonianLocalityLaw
import GaloisForLFunctions.RHTower.StaticChoiComplexityAlternationLaw
import GaloisForLFunctions.RHTower.StaticChoiContinuousHardGapLaw
import GaloisForLFunctions.RHTower.StaticChoiQuantitativeHardGapLaw
import GaloisForLFunctions.RHTower.StaticChoiFiniteOnsetHardBlockLaw
import GaloisForLFunctions.RHTower.StaticChoiGaussianFirstReturnLaw
import GaloisForLFunctions.RHTower.StaticChoiReturnExcisedGaussianFirstReturnLaw

/-!
# One-draw nearest-neighbour growth, completed plateau, and recurrence alternation

A single Hamiltonian from the centred Gaussian ensemble on the complete Hermitian onsite-plus-edge
space of a qubit path can simultaneously have robust linear laboratory-time operator complexity
growth and maximal projective spectral rank. Maximal rank supplies both a completed-time small
occupation law for every bounded circuit dictionary and perpetual low--hard--low Choi recurrence
alternation. Together with the positive-measure theorem in the imported module, all three regimes
occur for one fixed ordinary nearest-neighbour Hamiltonian drawn once.

The plateau is a completed-time occupation theorem and recurrence is qualitative syndetic
alternation. No typical-draw ramp, quantitative plateau onset, or exponential first-return scale is
claimed.
-/

open Filter MeasureTheory Set Topology
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw

noncomputable section

namespace RHTower

def nearestNeighborPathProjectiveDimension (L : ℕ) : ℕ :=
  Fintype.card (Config (PairQubit L)) - 1

def nearestNeighborPathConfigChoiEquiv (L : ℕ) :
    Config (PairQubit L) ≃ Fin (nearestNeighborPathProjectiveDimension L + 1) :=
  (Fintype.equivFin _).trans (finCongr (by
    have hcard : 1 ≤ Fintype.card (Config (PairQubit L)) :=
      Fintype.card_pos_iff.mpr inferInstance
    exact (Nat.sub_add_cancel hcard).symm))

def nearestNeighborPathChoiEnergy (L : ℕ)
    (p : Fin (nearestNeighborPathLocalParameterCount L) → ℝ) :
    Fin (nearestNeighborPathProjectiveDimension L + 1) → ℝ :=
  fun i => (nearestNeighborPathLocalHamiltonian_isHermitian L p).eigenvalues
    ((nearestNeighborPathConfigChoiEquiv L).symm i)

theorem maximallyProjectiveEnergy_nearestNeighborPathChoiEnergy
    {L : ℕ} {p : Fin (nearestNeighborPathLocalParameterCount L) → ℝ}
    (hp : p ∈ nearestNeighborPathLocalMaximalSet L) :
    MaximallyProjectiveEnergy (nearestNeighborPathChoiEnergy L p) := by
  exact (maximallyProjectiveEnergy_nearestNeighborPathLocalHamiltonian hp).comp_equiv
    (nearestNeighborPathConfigChoiEquiv L).symm

def nearestNeighborPathProjectedChoiCircuitTarget
    (L : ℕ) {gate : Type*} {s : ℕ}
    (target : PaddedCircuitWord gate s →
      EuclideanSpace ℂ
        (Fin (nearestNeighborPathProjectiveDimension L + 1) ×
          Fin (nearestNeighborPathProjectiveDimension L + 1))) :
    PaddedCircuitWord gate s →
      EuclideanSpace ℂ
        (Fin (nearestNeighborPathProjectiveDimension L + 1) ×
          Fin (nearestNeighborPathProjectiveDimension L + 1)) :=
  fun w => diagonalDensityRestriction
    (nearestNeighborPathProjectiveDimension L + 1) (pureStateDensity (target w))

def NearestNeighborPathCompletedPlateau
    (L : ℕ) {gate : Type*} [Fintype gate] (s : ℕ)
    (p : Fin (nearestNeighborPathLocalParameterCount L) → ℝ)
    (target : PaddedCircuitWord gate s →
      EuclideanSpace ℂ
        (Fin (nearestNeighborPathProjectiveDimension L + 1) ×
          Fin (nearestNeighborPathProjectiveDimension L + 1)))
    (δ : ℝ) : Prop :=
  let A := zeroAnchoredPaddedCircuitTarget
    (nearestNeighborPathProjectiveDimension L) s
    (nearestNeighborPathProjectedChoiCircuitTarget L target) δ
  atTop.limsup (fun U ↦
      (finiteTorusPhaseProbabilityMeasure
        (zeroProjectiveFrequency (nearestNeighborPathChoiEnergy L p)) U :
          Measure (UnitAddTorus (Fin (nearestNeighborPathProjectiveDimension L)))) A) ≤
      volume A ∧
    volume.real A ≤
      (Fintype.card gate : ℝ) ^ (s + 1) *
        (((nearestNeighborPathProjectiveDimension L + 1 : ℕ) : ℝ) *
          Real.exp (((nearestNeighborPathProjectiveDimension L + 1 : ℕ) : ℝ) / 2) *
          Real.sqrt (Real.pi * (2 * δ ^ 2) / 2) ^
            ((nearestNeighborPathProjectiveDimension L + 1 : ℕ) - 1))

theorem nearestNeighborPath_sameDraw_growth_plateau_recurrence
    {L : ℕ} {T εGrow : ℝ}
    {p : Fin (nearestNeighborPathLocalParameterCount L) → ℝ}
    (hp : p ∈ nearestNeighborPathGaussianGrowthMaximalEvent L T εGrow)
    {gate : Type*} [Fintype gate] (s : ℕ)
    (target : PaddedCircuitWord gate s →
      EuclideanSpace ℂ
        (Fin (nearestNeighborPathProjectiveDimension L + 1) ×
          Fin (nearestNeighborPathProjectiveDimension L + 1)))
    (htarget : ∀ w, ‖target w‖ = 1)
    (identityWord : PaddedCircuitWord gate s)
    (hidentity : target identityWord =
      fullUniformPhaseChoiVector (nearestNeighborPathProjectiveDimension L + 1)
        (zeroAnchoredPhase (nearestNeighborPathProjectiveDimension L)
          (0 : Fin (nearestNeighborPathProjectiveDimension L) → UnitAddCircle)))
    {εChoi : ℝ} (hεChoi : 0 < εChoi)
    (hentropy :
      (Fintype.card gate : ℝ) ^ (s + 1) *
          (((nearestNeighborPathProjectiveDimension L + 1 : ℕ) : ℝ) *
            Real.exp (((nearestNeighborPathProjectiveDimension L + 1 : ℕ) : ℝ) / 2) *
            Real.sqrt (Real.pi * (2 * (Real.sqrt 2 * εChoi) ^ 2) / 2) ^
              ((nearestNeighborPathProjectiveDimension L + 1 : ℕ) - 1)) < 1) :
    (∀ t : ℝ,
      2048 * Real.pi * εGrow ≤ t →
      t ≤ εGrow * L →
      t ≤ T →
      ((⌊t / (256 * Real.pi * εGrow)⌋₊ : ℕ) : ℕ∞) ≤
        operatorTwoGateComplexityTo L εGrow
          (unitaryEvolution (nearestNeighborPathLocalHamiltonian L p) t)) ∧
    NearestNeighborPathCompletedPlateau L s p target (Real.sqrt 2 * εChoi) ∧
    ∃ B : ℝ, 0 ≤ B ∧ ∀ a : ℝ,
      ∃ tLow ∈ Set.Icc a (a + B),
      ∃ tHigh ∈ Set.Ioc tLow (tLow + B),
      ∃ tLow' ∈ Set.Ioc tHigh (tHigh + B),
        pureStateTraceDistance
            (fullUniformPhaseChoiVector
              (nearestNeighborPathProjectiveDimension L + 1)
              (zeroAnchoredPhase (nearestNeighborPathProjectiveDimension L)
                (projectivePhysicalPhaseFlow
                  (nearestNeighborPathChoiEnergy L p) tLow)))
            (fullUniformPhaseChoiVector
              (nearestNeighborPathProjectiveDimension L + 1)
              (zeroAnchoredPhase (nearestNeighborPathProjectiveDimension L)
                (0 : Fin (nearestNeighborPathProjectiveDimension L) → UnitAddCircle))) < εChoi ∧
        (∀ w : PaddedCircuitWord gate s,
          εChoi < pureStateTraceDistance
            (fullUniformPhaseChoiVector
              (nearestNeighborPathProjectiveDimension L + 1)
              (zeroAnchoredPhase (nearestNeighborPathProjectiveDimension L)
                (projectivePhysicalPhaseFlow
                  (nearestNeighborPathChoiEnergy L p) tHigh)))
            (target w)) ∧
        pureStateTraceDistance
            (fullUniformPhaseChoiVector
              (nearestNeighborPathProjectiveDimension L + 1)
              (zeroAnchoredPhase (nearestNeighborPathProjectiveDimension L)
                (projectivePhysicalPhaseFlow
                  (nearestNeighborPathChoiEnergy L p) tLow')))
            (fullUniformPhaseChoiVector
              (nearestNeighborPathProjectiveDimension L + 1)
              (zeroAnchoredPhase (nearestNeighborPathProjectiveDimension L)
                (0 : Fin (nearestNeighborPathProjectiveDimension L) → UnitAddCircle))) < εChoi := by
  have hmax := maximallyProjectiveEnergy_nearestNeighborPathChoiEnergy hp.1
  refine ⟨hp.2, ?_, ?_⟩
  · simpa [NearestNeighborPathCompletedPlateau] using
      (completedTime_zeroAnchoredPaddedCircuitTargets
        (nearestNeighborPathChoiEnergy L p) hmax s
        (nearestNeighborPathProjectedChoiCircuitTarget L target)
        (mul_pos (Real.sqrt_pos.2 (by norm_num)) hεChoi))
  · exact maximallyProjective_pureChoiComplexity_alternates_syndetically
      (nearestNeighborPathChoiEnergy L p) hmax s target htarget
      identityWord hidentity hεChoi hentropy

/-- **One-draw laboratory growth and arbitrarily late continuous circuit-hard blocks.**  The same
ordinary nearest-neighbour Hamiltonian that obeys the robust laboratory-time growth law has a
strictly positive visit-thickness scale.  Whenever the complete wide-radius circuit-union entropy
is below the displayed packing threshold, this one Hamiltonian avoids every padded depth-`s`
circuit continuously on arbitrarily late intervals of length `W`. -/
theorem nearestNeighborPath_sameDraw_growth_continuous_hard_intervals
    {L : ℕ} {T εGrow : ℝ}
    {p : Fin (nearestNeighborPathLocalParameterCount L) → ℝ}
    (hp : p ∈ nearestNeighborPathGaussianGrowthMaximalEvent L T εGrow)
    {gate : Type*} [Fintype gate] (s : ℕ)
    (target : PaddedCircuitWord gate s →
      EuclideanSpace ℂ
        (Fin (nearestNeighborPathProjectiveDimension L + 1) ×
          Fin (nearestNeighborPathProjectiveDimension L + 1)))
    (htarget : ∀ w, ‖target w‖ = 1)
    {epsn epsw : ℝ} (hgap : epsn < epsw) (hepsn : 0 ≤ epsn) :
    (∀ t : ℝ,
      2048 * Real.pi * εGrow ≤ t →
      t ≤ εGrow * L →
      t ≤ T →
      ((⌊t / (256 * Real.pi * εGrow)⌋₊ : ℕ) : ℕ∞) ≤
        operatorTwoGateComplexityTo L εGrow
          (unitaryEvolution (nearestNeighborPathLocalHamiltonian L p) t)) ∧
    ∃ mesh : ℝ, 0 < mesh ∧ ∀ {W : ℝ}, 0 ≤ W →
      (Fintype.card gate : ℝ) ^ (s + 1) *
          ((((nearestNeighborPathProjectiveDimension L + 1 : ℕ) : ℝ) *
            Real.exp
              (((nearestNeighborPathProjectiveDimension L + 1 : ℕ) : ℝ) / 2) *
            Real.sqrt (Real.pi * (2 * (Real.sqrt 2 * epsw) ^ 2) / 2) ^
              ((nearestNeighborPathProjectiveDimension L + 1 : ℕ) - 1))) <
        mesh / (W + mesh) →
      ∀ A0 : ℝ, 0 ≤ A0 → ∃ u : ℝ, A0 ≤ u ∧
        ∀ t ∈ Set.Icc u (u + W), ∀ w,
          epsn < pureStateTraceDistance
            (fullUniformPhaseChoiVector
              (nearestNeighborPathProjectiveDimension L + 1)
              (zeroAnchoredPhase (nearestNeighborPathProjectiveDimension L)
                (projectivePhysicalPhaseFlow
                  (nearestNeighborPathChoiEnergy L p) t)))
            (target w) := by
  have hmax := maximallyProjectiveEnergy_nearestNeighborPathChoiEnergy hp.1
  exact ⟨hp.2,
    maximallyProjective_pureChoiCircuitTargets_late_hard_intervals
      (nearestNeighborPathChoiEnergy L p) hmax s target htarget hgap hepsn⟩

/-- **Quantitative one-draw growth--hard-block law.**  The visit thickness is explicit: trace-radius
gap divided by `1 + ∑ᵢ |E₀-Eᵢ|`.  Thus the same ordinary nearest-neighbour Hamiltonian has robust
laboratory growth and arbitrarily late continuous circuit-hard blocks of every length `W` allowed
by the inverse completed-occupation inequality below. -/
theorem nearestNeighborPath_sameDraw_growth_quantitative_continuous_hard_intervals
    {L : ℕ} {T εGrow : ℝ}
    {p : Fin (nearestNeighborPathLocalParameterCount L) → ℝ}
    (hp : p ∈ nearestNeighborPathGaussianGrowthMaximalEvent L T εGrow)
    {gate : Type*} [Fintype gate] (s : ℕ)
    (target : PaddedCircuitWord gate s →
      EuclideanSpace ℂ
        (Fin (nearestNeighborPathProjectiveDimension L + 1) ×
          Fin (nearestNeighborPathProjectiveDimension L + 1)))
    (htarget : ∀ w, ‖target w‖ = 1)
    {epsn epsw W : ℝ} (hgap : epsn < epsw) (hepsn : 0 ≤ epsn) (hW : 0 ≤ W)
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
    ∀ A0 : ℝ, 0 ≤ A0 → ∃ u : ℝ, A0 ≤ u ∧
      ∀ t ∈ Set.Icc u (u + W), ∀ w,
        epsn < pureStateTraceDistance
          (fullUniformPhaseChoiVector
            (nearestNeighborPathProjectiveDimension L + 1)
            (zeroAnchoredPhase (nearestNeighborPathProjectiveDimension L)
              (projectivePhysicalPhaseFlow
                (nearestNeighborPathChoiEnergy L p) t)))
          (target w) := by
  have hmax := maximallyProjectiveEnergy_nearestNeighborPathChoiEnergy hp.1
  exact ⟨hp.2,
    maximallyProjective_pureChoiCircuitTargets_explicit_late_hard_intervals
      (nearestNeighborPathChoiEnergy L p) hmax s target htarget hgap hepsn hW hpack⟩

/-- Continuous avoidance of the complete padded circuit dictionary on arbitrarily late blocks. -/
def NearestNeighborPathContinuousCircuitHardBlocks
    (L : ℕ) {gate : Type*} [Fintype gate] (s : ℕ)
    (p : Fin (nearestNeighborPathLocalParameterCount L) → ℝ)
    (target : PaddedCircuitWord gate s →
      EuclideanSpace ℂ
        (Fin (nearestNeighborPathProjectiveDimension L + 1) ×
          Fin (nearestNeighborPathProjectiveDimension L + 1)))
    (eps W : ℝ) : Prop :=
  ∀ A0 : ℝ, 0 ≤ A0 → ∃ u : ℝ, A0 ≤ u ∧
    ∀ t ∈ Set.Icc u (u + W), ∀ w,
      eps < pureStateTraceDistance
        (fullUniformPhaseChoiVector
          (nearestNeighborPathProjectiveDimension L + 1)
          (zeroAnchoredPhase (nearestNeighborPathProjectiveDimension L)
            (projectivePhysicalPhaseFlow
              (nearestNeighborPathChoiEnergy L p) t)))
        (target w)

/-- Perpetual recurrence--hardness--recurrence alternation for one projective Choi orbit. -/
def NearestNeighborPathChoiRecurrenceHardAlternation
    (L : ℕ) {gate : Type*} [Fintype gate] (s : ℕ)
    (p : Fin (nearestNeighborPathLocalParameterCount L) → ℝ)
    (target : PaddedCircuitWord gate s →
      EuclideanSpace ℂ
        (Fin (nearestNeighborPathProjectiveDimension L + 1) ×
          Fin (nearestNeighborPathProjectiveDimension L + 1)))
    (eps : ℝ) : Prop :=
  ∃ B : ℝ, 0 ≤ B ∧ ∀ a : ℝ,
    ∃ tLow ∈ Set.Icc a (a + B),
    ∃ tHigh ∈ Set.Ioc tLow (tLow + B),
    ∃ tLow' ∈ Set.Ioc tHigh (tHigh + B),
      pureStateTraceDistance
          (fullUniformPhaseChoiVector
            (nearestNeighborPathProjectiveDimension L + 1)
            (zeroAnchoredPhase (nearestNeighborPathProjectiveDimension L)
              (projectivePhysicalPhaseFlow
                (nearestNeighborPathChoiEnergy L p) tLow)))
          (fullUniformPhaseChoiVector
            (nearestNeighborPathProjectiveDimension L + 1)
            (zeroAnchoredPhase (nearestNeighborPathProjectiveDimension L)
              (0 : Fin (nearestNeighborPathProjectiveDimension L) → UnitAddCircle))) < eps ∧
      (∀ w : PaddedCircuitWord gate s,
        eps < pureStateTraceDistance
          (fullUniformPhaseChoiVector
            (nearestNeighborPathProjectiveDimension L + 1)
            (zeroAnchoredPhase (nearestNeighborPathProjectiveDimension L)
              (projectivePhysicalPhaseFlow
                (nearestNeighborPathChoiEnergy L p) tHigh)))
          (target w)) ∧
      pureStateTraceDistance
          (fullUniformPhaseChoiVector
            (nearestNeighborPathProjectiveDimension L + 1)
            (zeroAnchoredPhase (nearestNeighborPathProjectiveDimension L)
              (projectivePhysicalPhaseFlow
                (nearestNeighborPathChoiEnergy L p) tLow')))
          (fullUniformPhaseChoiVector
            (nearestNeighborPathProjectiveDimension L + 1)
            (zeroAnchoredPhase (nearestNeighborPathProjectiveDimension L)
              (0 : Fin (nearestNeighborPathProjectiveDimension L) → UnitAddCircle))) < eps

/-- **Same-draw growth, quantitative hard blocks, and perpetual recurrence alternation.**  One
ordinary nearest-neighbour Hamiltonian supports all three regimes.  Hard-block duration is governed
by completed circuit occupation divided by the explicit projective spectral speed; recurrence uses
the same Hamiltonian and the same complete circuit dictionary. -/
theorem nearestNeighborPath_sameDraw_growth_hardBlocks_recurrence
    {L : ℕ} {T εGrow : ℝ}
    {p : Fin (nearestNeighborPathLocalParameterCount L) → ℝ}
    (hp : p ∈ nearestNeighborPathGaussianGrowthMaximalEvent L T εGrow)
    {gate : Type*} [Fintype gate] (s : ℕ)
    (target : PaddedCircuitWord gate s →
      EuclideanSpace ℂ
        (Fin (nearestNeighborPathProjectiveDimension L + 1) ×
          Fin (nearestNeighborPathProjectiveDimension L + 1)))
    (htarget : ∀ w, ‖target w‖ = 1)
    (identityWord : PaddedCircuitWord gate s)
    (hidentity : target identityWord =
      fullUniformPhaseChoiVector (nearestNeighborPathProjectiveDimension L + 1)
        (zeroAnchoredPhase (nearestNeighborPathProjectiveDimension L)
          (0 : Fin (nearestNeighborPathProjectiveDimension L) → UnitAddCircle)))
    {epsn epsw W : ℝ} (hgap : epsn < epsw) (hepsn : 0 < epsn) (hW : 0 ≤ W)
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
            projectiveChoiSpeed (nearestNeighborPathChoiEnergy L p)))
    (hentropy :
      (Fintype.card gate : ℝ) ^ (s + 1) *
          (((nearestNeighborPathProjectiveDimension L + 1 : ℕ) : ℝ) *
            Real.exp (((nearestNeighborPathProjectiveDimension L + 1 : ℕ) : ℝ) / 2) *
            Real.sqrt (Real.pi * (2 * (Real.sqrt 2 * epsn) ^ 2) / 2) ^
              ((nearestNeighborPathProjectiveDimension L + 1 : ℕ) - 1)) < 1) :
    (∀ t : ℝ,
      2048 * Real.pi * εGrow ≤ t →
      t ≤ εGrow * L →
      t ≤ T →
      ((⌊t / (256 * Real.pi * εGrow)⌋₊ : ℕ) : ℕ∞) ≤
        operatorTwoGateComplexityTo L εGrow
          (unitaryEvolution (nearestNeighborPathLocalHamiltonian L p) t)) ∧
    NearestNeighborPathContinuousCircuitHardBlocks L s p target epsn W ∧
    NearestNeighborPathChoiRecurrenceHardAlternation L s p target epsn := by
  have hgaps := nearestNeighborPath_sameDraw_growth_quantitative_continuous_hard_intervals
    hp s target htarget hgap hepsn.le hW hpack
  have halt := nearestNeighborPath_sameDraw_growth_plateau_recurrence
    hp s target htarget identityWord hidentity hepsn hentropy
  refine ⟨hgaps.1, ?_, ?_⟩
  · exact hgaps.2
  · exact halt.2.2

/-- **Same-draw laboratory growth and finite-onset continuous hard block.**  The finite-window
spectral-dimension estimate supplies a hard point by time `2 * Twindow`; the full spectral Choi
speed thickens that point into a continuous interval against every padded circuit word. -/
theorem nearestNeighborPath_sameDraw_growth_finiteOnset_hardBlock
    {L : ℕ} {T εGrow : ℝ}
    {p : Fin (nearestNeighborPathLocalParameterCount L) → ℝ}
    (hp : p ∈ nearestNeighborPathGaussianGrowthMaximalEvent L T εGrow)
    {gate : Type*} [Fintype gate] (s : ℕ)
    (target : PaddedCircuitWord gate s →
      EuclideanSpace ℂ
        (Fin (nearestNeighborPathProjectiveDimension L + 1) ×
          Fin (nearestNeighborPathProjectiveDimension L + 1)))
    (htarget : ∀ w, ‖target w‖ = 1)
    (r : ℕ) (hr : 0 < r) {Twindow δ epsn epsw : ℝ}
    (hTwindow : 0 < Twindow) (hδ : 0 < δ) (hepsn : 0 ≤ epsn)
    (hgap : epsn < epsw) (hepswOne : epsw ≤ 1)
    (hbudget :
      (Fintype.card gate : ℝ) ^ (s + 1) *
          ((r.factorial : ℝ) *
              ((nearestNeighborPathProjectiveDimension L + 1 : ℕ) : ℝ)⁻¹ ^ r +
            (((2 * r + 1) ^ replicaNearActionRank
              (nearestNeighborPathChoiEnergy L p) r δ : ℕ) : ℝ) *
              ((r.factorial : ℝ) *
                ((nearestNeighborPathProjectiveDimension L + 1 : ℕ) : ℝ)⁻¹ ^ r) +
            min 1 (Twindow * δ)⁻¹) <
        (1 - epsw ^ 2) ^ r) :
    (∀ t : ℝ,
      2048 * Real.pi * εGrow ≤ t →
      t ≤ εGrow * L →
      t ≤ T →
      ((⌊t / (256 * Real.pi * εGrow)⌋₊ : ℕ) : ℕ∞) ≤
        operatorTwoGateComplexityTo L εGrow
          (unitaryEvolution (nearestNeighborPathLocalHamiltonian L p) t)) ∧
    ∃ u ∈ Set.Ioc 0 (2 * Twindow),
      ∀ t ∈ Set.Icc u
          (u + (epsw - epsn) /
            staticChoiSpeed (nearestNeighborPathChoiEnergy L p)),
        ∀ w, epsn < pureStateTraceDistance
          (staticSpectralChoiVector
            (nearestNeighborPathProjectiveDimension L + 1) t
            (nearestNeighborPathChoiEnergy L p))
          (target w) := by
  refine ⟨hp.2, ?_⟩
  exact exists_forward_pureChoiCircuitHardBlock_of_spectralDimensionBudget
    (Nat.succ_pos (nearestNeighborPathProjectiveDimension L))
    (maximallyProjectiveEnergy_nearestNeighborPathChoiEnergy hp.1)
    s target htarget r hr hTwindow hδ hepsn hgap hepswOne hbudget

/-- **Same-draw laboratory growth and Gaussian-window first circuit return.**  The same ordinary
nearest-neighbour Hamiltonian draw obeys the robust laboratory ramp and, under the explicit
growing-replica spectral-action budget, has no later narrow Choi capture by any padded depth-`s`
circuit between the end of the common identity-return cluster and `Treturn`. -/
theorem nearestNeighborPath_sameDraw_growth_firstCircuitReturn_of_gaussianSpectralBudget
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
      staticSpectralChoiVector
        (nearestNeighborPathProjectiveDimension L + 1) 0
        (nearestNeighborPathChoiEnergy L p))
    (r : ℕ) (hr : 0 < r) {Treturn δ epsn epsw : ℝ}
    (hTreturn : 0 < Treturn) (hδ : 0 < δ) (hepsn : 0 ≤ epsn)
    (hgap : epsn < epsw) (hepswOne : epsw < 1)
    (honset : epsw / staticChoiSpeed (nearestNeighborPathChoiEnergy L p) ≤ Treturn)
    (hbudget :
      (Fintype.card gate : ℝ) ^ (s + 1) *
          ((r.factorial : ℝ) *
              ((nearestNeighborPathProjectiveDimension L + 1 : ℕ) : ℝ)⁻¹ ^ r +
            (((2 * r + 1) ^ replicaNearActionRank
              (nearestNeighborPathChoiEnergy L p) r δ : ℕ) : ℝ) *
              ((r.factorial : ℝ) *
                ((nearestNeighborPathProjectiveDimension L + 1 : ℕ) : ℝ)⁻¹ ^ r) +
            Real.exp (-((Treturn * δ) ^ 2) / 2)) <
        (1 - epsw ^ 2) ^ r * gaussianFloorTwo *
          (epsw / staticChoiSpeed (nearestNeighborPathChoiEnergy L p) / Treturn +
            (epsw - epsn) /
              staticChoiSpeed (nearestNeighborPathChoiEnergy L p) / (2 * Treturn))) :
    (∀ t : ℝ,
      2048 * Real.pi * εGrow ≤ t →
      t ≤ εGrow * L →
      t ≤ T →
      ((⌊t / (256 * Real.pi * εGrow)⌋₊ : ℕ) : ℕ∞) ≤
        operatorTwoGateComplexityTo L εGrow
          (unitaryEvolution (nearestNeighborPathLocalHamiltonian L p) t)) ∧
    ¬ ∃ t ∈ Set.Icc
        (epsw / staticChoiSpeed (nearestNeighborPathChoiEnergy L p) +
          (epsw - epsn) / staticChoiSpeed (nearestNeighborPathChoiEnergy L p))
        Treturn,
      ∃ w, pureStateTraceDistance
        (staticSpectralChoiVector
          (nearestNeighborPathProjectiveDimension L + 1) t
          (nearestNeighborPathChoiEnergy L p))
        (target w) ≤ epsn := by
  refine ⟨hp.2, ?_⟩
  exact no_forward_pureChoiCircuitReturn_of_gaussianSpectralBudget
    (Nat.succ_pos (nearestNeighborPathProjectiveDimension L))
    (maximallyProjectiveEnergy_nearestNeighborPathChoiEnergy hp.1)
    s target htarget identity hidentity r hr hTreturn hδ hepsn hgap
    hepswOne honset hbudget

/-- **Same-draw growth and return-excised incidence first-return law.**  For the ordinary
nearest-neighbour Hamiltonian draw supplying the laboratory ramp, the exact occupied-image coarea
action is sufficient to exclude first return to the complete padded depth-`s` circuit family.
All regularity inputs are automatic for the static Choi orbit. -/
theorem nearestNeighborPath_sameDraw_growth_firstCircuitReturn_of_returnExcisedIncidenceAction_lt
    {L : ℕ} {Tgrow εGrow : ℝ}
    {p : Fin (nearestNeighborPathLocalParameterCount L) → ℝ}
    (hp : p ∈ nearestNeighborPathGaussianGrowthMaximalEvent L Tgrow εGrow)
    {gate : Type*} [Fintype gate] (s : ℕ)
    (target : PaddedCircuitWord gate s →
      EuclideanSpace ℂ
        (Fin (nearestNeighborPathProjectiveDimension L + 1) ×
          Fin (nearestNeighborPathProjectiveDimension L + 1)))
    (htarget : ∀ w, ‖target w‖ = 1)
    {r : ℕ} (hr : 0 < r)
    {Treturn epsn epsw : ℝ}
    (hTreturn : 0 < Treturn) (hepsn : 0 ≤ epsn) (hgap : epsn < epsw)
    (hepswOne : epsw < 1)
    (honset : epsw / staticChoiSpeed (nearestNeighborPathChoiEnergy L p) ≤ Treturn)
    (haction :
      (returnExcisedReplicaIncidenceNumber r (fun w => (target w).ofLp)
          (fun x => (staticSpectralChoiVector
            (nearestNeighborPathProjectiveDimension L + 1) (Treturn * x)
            (nearestNeighborPathChoiEnergy L p)).ofLp)
          (Set.Icc
            (-(epsw / staticChoiSpeed (nearestNeighborPathChoiEnergy L p) / Treturn))
            (epsw / staticChoiSpeed (nearestNeighborPathChoiEnergy L p) / Treturn)) : ℝ) *
        returnExcisedReplicaIncidenceAction (ProbabilityTheory.gaussianReal 0 1) r
          (fun w => (target w).ofLp)
          (fun x => (staticSpectralChoiVector
            (nearestNeighborPathProjectiveDimension L + 1) (Treturn * x)
            (nearestNeighborPathChoiEnergy L p)).ofLp)
          (Set.Icc
            (-(epsw / staticChoiSpeed (nearestNeighborPathChoiEnergy L p) / Treturn))
            (epsw / staticChoiSpeed (nearestNeighborPathChoiEnergy L p) / Treturn)) <
      (gaussianFloorTwo *
          ((epsw - epsn) / staticChoiSpeed (nearestNeighborPathChoiEnergy L p) /
            (2 * Treturn)) *
        (1 - epsw ^ 2) ^ r) ^ 2) :
    (∀ t : ℝ,
      2048 * Real.pi * εGrow ≤ t →
      t ≤ εGrow * L →
      t ≤ Tgrow →
      ((⌊t / (256 * Real.pi * εGrow)⌋₊ : ℕ) : ℕ∞) ≤
        operatorTwoGateComplexityTo L εGrow
          (unitaryEvolution (nearestNeighborPathLocalHamiltonian L p) t)) ∧
    ¬ ∃ t ∈ Set.Icc
        (epsw / staticChoiSpeed (nearestNeighborPathChoiEnergy L p) +
          (epsw - epsn) / staticChoiSpeed (nearestNeighborPathChoiEnergy L p))
        Treturn,
      ∃ w, pureStateTraceDistance
        (staticSpectralChoiVector
          (nearestNeighborPathProjectiveDimension L + 1) t
          (nearestNeighborPathChoiEnergy L p))
        (target w) ≤ epsn := by
  refine ⟨hp.2, ?_⟩
  exact no_forward_pureChoiCircuitReturn_of_returnExcisedGaussianIncidenceAction_lt
    (Nat.succ_pos (nearestNeighborPathProjectiveDimension L))
    (nearestNeighborPathChoiEnergy L p) target htarget hr hTreturn hepsn hgap
    hepswOne honset haction

end RHTower
