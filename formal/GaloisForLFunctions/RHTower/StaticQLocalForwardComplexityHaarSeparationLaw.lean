import GaloisForLFunctions.RHTower.StaticChoiForwardSpectralDimensionLaw
import GaloisForLFunctions.RHTower.StaticChoiForwardWeightedCrowdingLaw
import GaloisForLFunctions.RHTower.StaticQLocalComplexityHaarSeparationLaw

/-!
# Forward circuit hardness with permanent local separation from Haar

For the ordinary time-independent bounded-weight Pauli family, generic coefficients give maximal
projective spectrum.  Whenever the explicit finite-window spectral-dimension budget closes, the
same Hamiltonian reaches a future Choi endpoint outside every supplied padded circuit target while
its fixed local two-query signal remains strictly above the Haar benchmark at every real time.
-/

open Filter MeasureTheory Set Topology

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry

theorem pauliBounded_forwardCircuitHardness_and_permanentHaarSeparation
    (n q : ℕ) (hn : 0 < n) (hq : 2 ≤ q)
    (p : Fin (Fintype.card (PauliBoundedLabel n q)) → ℝ)
    (hp : p ∈ polynomialMatrixProjectiveGenericSet
      (pauliBoundedFinPolynomialMatrix n q))
    {gate : Type*} [Fintype gate] (s : ℕ)
    (target : PaddedCircuitWord gate s →
      EuclideanSpace ℂ
        (Fin ((2 ^ n - 1) + 1) × Fin ((2 ^ n - 1) + 1)))
    (htarget : ∀ w, ‖target w‖ = 1)
    (r : ℕ) (hr : 0 < r) {T δ epsilon : ℝ}
    (hT : 0 < T) (hδ : 0 < δ) (hepsilon : 0 ≤ epsilon)
    (hepsilonOne : epsilon ≤ 1)
    (hbudget :
      (Fintype.card gate : ℝ) ^ (s + 1) *
          ((r.factorial : ℝ) *
              (((((2 ^ n - 1) + 1 : ℕ)) : ℝ))⁻¹ ^ r +
            (((2 * r + 1) ^
                replicaNearActionRank (pauliBoundedChoiEnergy p) r δ : ℕ) : ℝ) *
              ((r.factorial : ℝ) *
                (((((2 ^ n - 1) + 1 : ℕ)) : ℝ))⁻¹ ^ r) +
            min 1 (T * δ)⁻¹) <
        (1 - epsilon ^ (2 : ℕ)) ^ r)
    (hsep :
      Fintype.card (FiniteQLocalPauliLabel (Fin n) q) * 3 ^ q <
        2 ^ n + 1) :
    (∃ t ∈ Set.Ioc 0 (2 * T),
      ∀ w : PaddedCircuitWord gate s,
        t ∉ staticChoiTargetCaptureSet
          (pauliBoundedChoiEnergy p) (target w) epsilon) ∧
      ∀ t : ℝ,
        1 / (((2 ^ n + 1 : ℕ) : ℝ)) <
          productStabilizerTwoQueryProtocolSignal
            (fun P : FiniteQLocalPauliLabel (Fin n) q => P.1)
            (finiteQLocalPauliTransferMatrix (Fin n) q
              (pauliBoundedHamiltonian p) t) := by
  obtain ⟨-, -, -, hgeneric⟩ :=
    pauliBounded_simple_and_projectivelyIndependent_generically n hq
  have hmax := (hgeneric p hp).2
  have hdChoi : 0 < (2 ^ n - 1) + 1 := by
    have hpow : 0 < 2 ^ n := pow_pos (by omega) n
    omega
  constructor
  · exact
      exists_forward_directAdaptivePaddedCircuitHardTime_of_spectralDimensionBudget
        hdChoi (maximallyProjectiveEnergy_pauliBoundedChoiEnergy p hmax)
        s target htarget r hr hT hδ hepsilon hepsilonOne hbudget
  · intro t
    simpa using (finiteQLocalAutonomousTransferSignal_gt_haarBenchmark
      (Fin n) q (pauliBoundedHamiltonian p)
      (pauliBoundedHamiltonian_ne_zero_of_maximallyProjective hn p hmax)
      (pauliBoundedHamiltonian_hasPauliWeightAtMost p)
      t (by simpa using hsep))

theorem pauliBounded_forwardWeightedCircuitHardness_and_permanentHaarSeparation
    (n q : ℕ) (hn : 0 < n) (hq : 2 ≤ q)
    (p : Fin (Fintype.card (PauliBoundedLabel n q)) → ℝ)
    (hp : p ∈ polynomialMatrixProjectiveGenericSet
      (pauliBoundedFinPolynomialMatrix n q))
    {gate : Type*} [Fintype gate] (s : ℕ)
    (target : PaddedCircuitWord gate s →
      EuclideanSpace ℂ
        (Fin ((2 ^ n - 1) + 1) × Fin ((2 ^ n - 1) + 1)))
    (htarget : ∀ w, ‖target w‖ = 1)
    (r : ℕ) (hr : 0 < r) {T δ epsilon : ℝ}
    (hT : 0 < T) (hδ : 0 < δ) (hepsilon : 0 ≤ epsilon)
    (hepsilonOne : epsilon ≤ 1)
    (hbudget :
      (Fintype.card gate : ℝ) ^ (s + 1) *
          ((r.factorial : ℝ) *
              (((((2 ^ n - 1) + 1 : ℕ)) : ℝ))⁻¹ ^ r +
            min 1 (T * δ)⁻¹) +
          directAdaptiveChoiNearActionPartition target
            (pauliBoundedChoiEnergy p) r δ <
        (1 - epsilon ^ (2 : ℕ)) ^ r)
    (hsep :
      Fintype.card (FiniteQLocalPauliLabel (Fin n) q) * 3 ^ q <
        2 ^ n + 1) :
    (∃ t ∈ Set.Ioc 0 (2 * T),
      ∀ w : PaddedCircuitWord gate s,
        t ∉ staticChoiTargetCaptureSet
          (pauliBoundedChoiEnergy p) (target w) epsilon) ∧
      ∀ t : ℝ,
        1 / (((2 ^ n + 1 : ℕ) : ℝ)) <
          productStabilizerTwoQueryProtocolSignal
            (fun P : FiniteQLocalPauliLabel (Fin n) q => P.1)
            (finiteQLocalPauliTransferMatrix (Fin n) q
              (pauliBoundedHamiltonian p) t) := by
  obtain ⟨-, -, -, hgeneric⟩ :=
    pauliBounded_simple_and_projectivelyIndependent_generically n hq
  have hmax := (hgeneric p hp).2
  have hdChoi : 0 < (2 ^ n - 1) + 1 := by
    have hpow : 0 < 2 ^ n := pow_pos (by omega) n
    omega
  constructor
  · exact
      exists_forward_directAdaptivePaddedCircuitHardTime_of_weightedCrowdingBudget
        hdChoi (maximallyProjectiveEnergy_pauliBoundedChoiEnergy p hmax)
        s target htarget r hr hT hδ hepsilon hepsilonOne hbudget
  · intro t
    simpa using (finiteQLocalAutonomousTransferSignal_gt_haarBenchmark
      (Fin n) q (pauliBoundedHamiltonian p)
      (pauliBoundedHamiltonian_ne_zero_of_maximallyProjective hn p hmax)
      (pauliBoundedHamiltonian_hasPauliWeightAtMost p)
      t (by simpa using hsep))

end RHTower
