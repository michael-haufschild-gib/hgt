import GaloisForLFunctions.HTGeometry.ThermodynamicProjectiveRecurrenceDesertLaw
import GaloisForLFunctions.RHTower.NearestNeighborPolynomialCircuitSameDrawLaw

/-!
# Same-field thermodynamic polynomial-circuit plateau

One countable static nearest-neighbour field already carrying the recurrence-desert lifecycle also
has vanishing completed-time occupation of every fixed-alphabet polynomial-depth Choi circuit
dictionary along a cofinal paired-prefix sequence.  The field is selected once, before alphabet,
depth exponent, target family, system size, or time horizon.
-/

open Filter MeasureTheory Set Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- Prefix `2L+1` contains exactly `2(L+2)` qubits. -/
def thermodynamicPairedPrefixIndex (L : ℕ) : ℕ := L * 2 + 1

theorem thermodynamicPairedPrefix_qubitCount (L : ℕ) :
    thermodynamicPairedPrefixIndex L + 3 = 2 * (L + 2) := by
  simp [thermodynamicPairedPrefixIndex]
  omega

theorem thermodynamicPairedPrefix_dimension (L : ℕ) :
    2 ^ (thermodynamicPairedPrefixIndex L + 3) = 4 ^ (L + 2) := by
  rw [thermodynamicPairedPrefix_qubitCount]
  rw [pow_mul]
  norm_num

/-- Projective phase-torus dimension of the paired prefix. -/
def thermodynamicPairedPrefixProjectiveDimension (L : ℕ) : ℕ :=
  4 ^ (L + 2) - 1

theorem thermodynamicPairedPrefixProjectiveDimension_add_one (L : ℕ) :
    thermodynamicPairedPrefixProjectiveDimension L + 1 = 4 ^ (L + 2) := by
  rw [thermodynamicPairedPrefixProjectiveDimension,
    Nat.sub_add_cancel (one_le_pow₀ (by norm_num : 1 ≤ 4))]

/-- Canonical enumeration of the paired literal-prefix Hilbert space. -/
def thermodynamicPairedPrefixConfigEquiv (L : ℕ) :
    (Fin (thermodynamicPairedPrefixIndex L + 3) → Bool) ≃
      Fin (thermodynamicPairedPrefixProjectiveDimension L + 1) :=
  (qubitConfigFin (thermodynamicPairedPrefixIndex L + 3)).trans
    (finCongr ((thermodynamicPairedPrefix_dimension L).trans
      (thermodynamicPairedPrefixProjectiveDimension_add_one L).symm))

/-- Physical eigenvalue list of the paired literal prefix, enumerated on its full Hilbert space. -/
def thermodynamicPairedPrefixChoiEnergy
    (p : InfinitePathLabel → ℝ) (L : ℕ) :
      Fin (thermodynamicPairedPrefixProjectiveDimension L + 1) → ℝ :=
  fun i => pathEigenValues (thermodynamicPairedPrefixIndex L)
    (infinitePathPrefixShell (thermodynamicPairedPrefixIndex L) p)
      ((thermodynamicPairedPrefixConfigEquiv L).symm i)

theorem maximallyProjectiveEnergy_thermodynamicPairedPrefixChoiEnergy
    {p : InfinitePathLabel → ℝ} (hp : ThermodynamicSameFieldLifecycle p) (L : ℕ) :
    MaximallyProjectiveEnergy (thermodynamicPairedPrefixChoiEnergy p L) := by
  exact (hp.prefix_maximallyProjective (thermodynamicPairedPrefixIndex L)).comp_equiv_relabel
    (thermodynamicPairedPrefixConfigEquiv L).symm

/-- Project physical Choi target vectors onto spectral diagonal coordinates controlled by the
completed-time theorem. -/
def thermodynamicPairedPrefixProjectedChoiTarget
    (g r L : ℕ)
    (target : PaddedCircuitWord (Fin g) ((L + 2) ^ r) →
      EuclideanSpace ℂ
        (Fin (thermodynamicPairedPrefixProjectiveDimension L + 1) ×
          Fin (thermodynamicPairedPrefixProjectiveDimension L + 1))) :
    PaddedCircuitWord (Fin g) ((L + 2) ^ r) →
      EuclideanSpace ℂ
        (Fin (thermodynamicPairedPrefixProjectiveDimension L + 1) ×
          Fin (thermodynamicPairedPrefixProjectiveDimension L + 1)) :=
  fun w => diagonalDensityRestriction
    (thermodynamicPairedPrefixProjectiveDimension L + 1) (pureStateDensity (target w))

/-- Completed-time target set for a fixed alphabet and polynomial word budget on paired prefix
`L`. -/
def thermodynamicPairedPrefixCircuitTarget
    (g r L : ℕ)
    (target : PaddedCircuitWord (Fin g) ((L + 2) ^ r) →
      EuclideanSpace ℂ
        (Fin (thermodynamicPairedPrefixProjectiveDimension L + 1) ×
          Fin (thermodynamicPairedPrefixProjectiveDimension L + 1))) :
    Set (UnitAddTorus (Fin (thermodynamicPairedPrefixProjectiveDimension L))) :=
  zeroAnchoredPaddedCircuitTarget (thermodynamicPairedPrefixProjectiveDimension L)
    ((L + 2) ^ r) (thermodynamicPairedPrefixProjectedChoiTarget g r L target)
    (Real.sqrt 2 * (1 / 100 : ℝ))

/-- Every maximally projective lifecycle field obeys the exact completed-time bound on every
paired literal prefix. -/
theorem ThermodynamicSameFieldLifecycle.thermodynamicPairedPrefix_polynomialCircuitPlateau
    {p : InfinitePathLabel → ℝ} (hp : ThermodynamicSameFieldLifecycle p)
    (g r L : ℕ)
    (target : PaddedCircuitWord (Fin g) ((L + 2) ^ r) →
      EuclideanSpace ℂ
        (Fin (thermodynamicPairedPrefixProjectiveDimension L + 1) ×
          Fin (thermodynamicPairedPrefixProjectiveDimension L + 1))) :
    let A := thermodynamicPairedPrefixCircuitTarget g r L target
    atTop.limsup (fun T ↦
        (finiteTorusPhaseProbabilityMeasure
          (zeroProjectiveFrequency (thermodynamicPairedPrefixChoiEnergy p L)) T :
            Measure (UnitAddTorus (Fin (thermodynamicPairedPrefixProjectiveDimension L)))) A) ≤
              volume A ∧
      volume.real A ≤ polynomialCircuitChoiEntropyCost g r (L + 2) := by
  dsimp only
  simpa [thermodynamicPairedPrefixCircuitTarget,
    thermodynamicPairedPrefixProjectedChoiTarget,
    polynomialCircuitChoiEntropyCost,
    thermodynamicPairedPrefixProjectiveDimension_add_one] using
    (completedTime_zeroAnchoredPaddedCircuitTargets
      (thermodynamicPairedPrefixChoiEnergy p L)
      (maximallyProjectiveEnergy_thermodynamicPairedPrefixChoiEnergy hp L)
      ((L + 2) ^ r)
      (thermodynamicPairedPrefixProjectedChoiTarget g r L target)
      (mul_pos (Real.sqrt_pos.2 (by norm_num)) (by norm_num : (0 : ℝ) < 1 / 100)))

/-- Explicit polynomial-circuit occupation envelope vanishes along paired prefixes. -/
theorem tendsto_thermodynamicPairedPrefixPolynomialCircuitCost_atTop (g r : ℕ) :
    Tendsto (fun L : ℕ => polynomialCircuitChoiEntropyCost g r (L + 2))
      atTop (nhds 0) := by
  exact (tendsto_polynomialCircuitChoiEntropyCost_atTop g r).comp
    (tendsto_add_atTop_nat 2)

/-- **Unconditional same-field thermodynamic polynomial-circuit plateau law.** One countable,
absolutely summable static nearest-neighbour field simultaneously has the full recurrence-desert
lifecycle and, for every fixed finite gate alphabet and polynomial depth exponent, completed-time
occupation of every padded circuit dictionary bounded by one explicit envelope tending to zero. -/
theorem exists_thermodynamicSameFieldPolynomialCircuitPlateauLaw :
    ∃ p : InfinitePathLabel → ℝ,
      ThermodynamicRecurrenceDesertLifecycle p ∧
      ∀ g r : ℕ,
        Tendsto (fun L : ℕ => polynomialCircuitChoiEntropyCost g r (L + 2))
          atTop (nhds 0) ∧
        ∀ (L : ℕ)
          (target : PaddedCircuitWord (Fin g) ((L + 2) ^ r) →
            EuclideanSpace ℂ
              (Fin (thermodynamicPairedPrefixProjectiveDimension L + 1) ×
                Fin (thermodynamicPairedPrefixProjectiveDimension L + 1))),
          let A := thermodynamicPairedPrefixCircuitTarget g r L target
          atTop.limsup (fun T ↦
              (finiteTorusPhaseProbabilityMeasure
                (zeroProjectiveFrequency (thermodynamicPairedPrefixChoiEnergy p L)) T :
                  Measure (UnitAddTorus
                    (Fin (thermodynamicPairedPrefixProjectiveDimension L)))) A) ≤ volume A ∧
            volume.real A ≤ polynomialCircuitChoiEntropyCost g r (L + 2) := by
  obtain ⟨p, hp⟩ := exists_thermodynamicRecurrenceDesertLifecycle
  refine ⟨p, hp, fun g r => ⟨
    tendsto_thermodynamicPairedPrefixPolynomialCircuitCost_atTop g r, ?_⟩⟩
  intro L target
  exact ThermodynamicSameFieldLifecycle.thermodynamicPairedPrefix_polynomialCircuitPlateau
    hp.toThermodynamicSameFieldLifecycle g r L target

end

end RHTower
