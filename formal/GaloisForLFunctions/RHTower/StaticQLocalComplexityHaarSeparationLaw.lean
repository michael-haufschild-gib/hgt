import GaloisForLFunctions.HTGeometry.PauliBoundedHamiltonianLocalityLaw
import GaloisForLFunctions.RHTower.StaticChoiComplexityAlternationLaw

/-!
# Static local complexity alternation without Haar randomization

This file proves a same-Hamiltonian coexistence law for ordinary autonomous
finite-qubit systems.  Generic bounded-weight Pauli Hamiltonians return
syndetically near the identity channel and subsequently enter bounded-circuit
hard Choi regimes.  Nevertheless a fixed local two-query experiment stays
strictly above the exact Haar benchmark at every real time, including every
hard epoch.
-/

open Filter MeasureTheory Set Topology

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-- Finite indexing matched to the anchored projective Choi torus. -/
def finiteQubitConfigurationChoiEquiv (n : ℕ) :
    FiniteQubitConfiguration (Fin n) ≃ Fin ((2 ^ n - 1) + 1) :=
  Fintype.equivFinOfCardEq (by
    have hpos : 0 < 2 ^ n := pow_pos (by norm_num) n
    have hpow : 1 ≤ 2 ^ n := by omega
    simp [FiniteQubitConfiguration, Nat.sub_add_cancel hpow])

/-- Ordered spectrum of a bounded-weight Pauli Hamiltonian, reindexed for
the anchored Choi phase flow. -/
def pauliBoundedChoiEnergy {n q : ℕ}
    (p : Fin (Fintype.card (PauliBoundedLabel n q)) → ℝ) :
    Fin ((2 ^ n - 1) + 1) → ℝ :=
  fun i => (isHermitian_pauliBoundedFinEval p).eigenvalues
    ((finiteQubitConfigurationChoiEquiv n).symm i)

theorem maximallyProjectiveEnergy_pauliBoundedChoiEnergy
    {n q : ℕ}
    (p : Fin (Fintype.card (PauliBoundedLabel n q)) → ℝ)
    (hmax : MaximallyProjectiveEnergy
      (isHermitian_pauliBoundedFinEval p).eigenvalues) :
    MaximallyProjectiveEnergy (pauliBoundedChoiEnergy p) := by
  exact hmax.comp_equiv (finiteQubitConfigurationChoiEquiv n).symm

/-- **Same-Hamiltonian complexity--locality coexistence.** Every generic
bounded-weight Pauli Hamiltonian has syndetically recurring Choi-channel
returns and bounded-circuit-hard epochs, while its exact local two-query
signal stays strictly above the Haar benchmark at every real time. -/
theorem pauliBounded_complexityAlternation_and_permanentHaarSeparation
    (n q : ℕ) (hn : 0 < n) (hq : 2 ≤ q)
    (p : Fin (Fintype.card (PauliBoundedLabel n q)) → ℝ)
    (hp : p ∈ polynomialMatrixProjectiveGenericSet
      (pauliBoundedFinPolynomialMatrix n q))
    {gate : Type*} [Fintype gate] (s : ℕ)
    (target : PaddedCircuitWord gate s →
      EuclideanSpace ℂ
        (Fin ((2 ^ n - 1) + 1) × Fin ((2 ^ n - 1) + 1)))
    (htarget : ∀ w, ‖target w‖ = 1)
    (identityWord : PaddedCircuitWord gate s)
    (hidentity : target identityWord =
      fullUniformPhaseChoiVector ((2 ^ n - 1) + 1)
        (zeroAnchoredPhase (2 ^ n - 1)
          (0 : Fin (2 ^ n - 1) → UnitAddCircle)))
    {ε : ℝ} (hε : 0 < ε)
    (hentropy :
      (Fintype.card gate : ℝ) ^ (s + 1) *
          (((((2 ^ n - 1) + 1 : ℕ)) : ℝ) *
            Real.exp (((((2 ^ n - 1) + 1 : ℕ)) : ℝ) / 2) *
            Real.sqrt
              (Real.pi * (2 * (Real.sqrt 2 * ε) ^ (2 : ℕ)) / 2) ^
                ((((2 ^ n - 1) + 1 : ℕ)) - 1)) < 1)
    (hsep :
      Fintype.card (FiniteQLocalPauliLabel (Fin n) q) * 3 ^ q <
        2 ^ n + 1) :
    (∃ L : ℝ, 0 ≤ L ∧ ∀ a : ℝ,
      ∃ tLow ∈ Set.Icc a (a + L),
      ∃ tHigh ∈ Set.Ioc tLow (tLow + L),
      ∃ tLow' ∈ Set.Ioc tHigh (tHigh + L),
        pureStateTraceDistance
            (fullUniformPhaseChoiVector ((2 ^ n - 1) + 1)
              (zeroAnchoredPhase (2 ^ n - 1)
                (projectivePhysicalPhaseFlow
                  (pauliBoundedChoiEnergy p) tLow)))
            (fullUniformPhaseChoiVector ((2 ^ n - 1) + 1)
              (zeroAnchoredPhase (2 ^ n - 1)
                (0 : Fin (2 ^ n - 1) → UnitAddCircle))) < ε ∧
        (∀ w : PaddedCircuitWord gate s,
          ε < pureStateTraceDistance
            (fullUniformPhaseChoiVector ((2 ^ n - 1) + 1)
              (zeroAnchoredPhase (2 ^ n - 1)
                (projectivePhysicalPhaseFlow
                  (pauliBoundedChoiEnergy p) tHigh)))
            (target w)) ∧
        pureStateTraceDistance
            (fullUniformPhaseChoiVector ((2 ^ n - 1) + 1)
              (zeroAnchoredPhase (2 ^ n - 1)
                (projectivePhysicalPhaseFlow
                  (pauliBoundedChoiEnergy p) tLow')))
            (fullUniformPhaseChoiVector ((2 ^ n - 1) + 1)
              (zeroAnchoredPhase (2 ^ n - 1)
                (0 : Fin (2 ^ n - 1) → UnitAddCircle))) < ε) ∧
      ∀ t : ℝ,
        1 / (((2 ^ n + 1 : ℕ) : ℝ)) <
          productStabilizerTwoQueryProtocolSignal
            (fun P : FiniteQLocalPauliLabel (Fin n) q => P.1)
            (finiteQLocalPauliTransferMatrix (Fin n) q
              (pauliBoundedHamiltonian p) t) := by
  obtain ⟨-, -, -, hgeneric⟩ :=
    pauliBounded_simple_and_projectivelyIndependent_generically n hq
  have hmax := (hgeneric p hp).2
  constructor
  · exact maximallyProjective_pureChoiComplexity_alternates_syndetically
      (pauliBoundedChoiEnergy p)
      (maximallyProjectiveEnergy_pauliBoundedChoiEnergy p hmax)
      s target htarget identityWord hidentity hε hentropy
  · intro t
    simpa using (finiteQLocalAutonomousTransferSignal_gt_haarBenchmark
      (Fin n) q (pauliBoundedHamiltonian p)
      (pauliBoundedHamiltonian_ne_zero_of_maximallyProjective hn p hmax)
      (pauliBoundedHamiltonian_hasPauliWeightAtMost p)
      t (by simpa using hsep))

end RHTower
