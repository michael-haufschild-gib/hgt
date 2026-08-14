import GaloisForLFunctions.RHTower.PrimeTorsionAutonomousCircuitPolygon
import GaloisForLFunctions.RHTower.StaticQLocalComplexityHaarSeparationLaw

/-!
# Hard recurrence polygons with permanent locality for ordinary Pauli Hamiltonians

The autonomous complete-polygon law is specialized to ordinary bounded-weight
Pauli Hamiltonians.  The same fixed local Hamiltonian shadows an arbitrarily
late complete hard prime polygon, returns near the identity at its endpoint,
and remains operationally distinguishable from Haar randomness at every real
time.
-/

open Set

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-- **Ordinary local-Hamiltonian hard-polygon and permanent-Haar law.**
For every generic nonzero bounded-weight Pauli Hamiltonian satisfying the
explicit separator dimension bound, one fixed autonomous Hamiltonian has
syndetically recurring complete circuit-hard prime polygons while its local
two-query signal stays strictly above the exact Haar benchmark forever. -/
theorem pauliBounded_completeCircuitPolygon_and_permanentHaarSeparation
    (n q k : ℕ) (hn : 0 < n) (hq : 2 ≤ q) [Fact k.Prime]
    (coeff : Fin (Fintype.card (PauliBoundedLabel n q)) → ℝ)
    (hcoeff : coeff ∈ polynomialMatrixProjectiveGenericSet
      (pauliBoundedFinPolynomialMatrix n q))
    {Y : Type*} [Fintype Y] [DecidableEq Y]
    (target : Y → EuclideanSpace ℂ
      (Fin ((2 ^ n - 1) + 1) × Fin ((2 ^ n - 1) + 1)))
    (htarget : ∀ y, ‖target y‖ = 1)
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    (hepsilonHalf : epsilon < 1 / 2)
    {rho : ℝ} (hrho : 0 < rho)
    (replica : ℕ) (hreplica : 2 * replica < k)
    (hbudget :
      (((k - 1) * Fintype.card Y : ℕ) : ℝ) *
          (replica.factorial : ℝ) *
          (((((2 ^ n - 1) + 1 : ℕ)) : ℝ)⁻¹) ^ replica <
        (Real.sqrt (1 - 4 * epsilon ^ 2)) ^ (2 * replica))
    (hsep :
      Fintype.card (FiniteQLocalPauliLabel (Fin n) q) * 3 ^ q <
        2 ^ n + 1) :
    (∃ L : ℝ, 0 ≤ L ∧ ∀ A : ℝ, ∃ tau ∈ Set.Icc A (A + L),
      (∀ a : ZMod k, a ≠ 0 → ∀ y : Y,
        epsilon < pureStateTraceDistance
          (projectivePhaseChoiVector (2 ^ n - 1)
            (projectivePhysicalPhaseFlow (pauliBoundedChoiEnergy coeff)
              ((a.val : ℝ) * tau)))
          (target y)) ∧
      pureStateTraceDistance
        (projectivePhaseChoiVector (2 ^ n - 1)
          (projectivePhysicalPhaseFlow (pauliBoundedChoiEnergy coeff)
            ((k : ℝ) * tau)))
        (projectivePhaseChoiVector (2 ^ n - 1) 0) < rho) ∧
    ∀ t : ℝ,
      1 / (((2 ^ n + 1 : ℕ) : ℝ)) <
        productStabilizerTwoQueryProtocolSignal
          (fun P : FiniteQLocalPauliLabel (Fin n) q => P.1)
          (finiteQLocalPauliTransferMatrix (Fin n) q
            (pauliBoundedHamiltonian coeff) t) := by
  obtain ⟨-, -, -, hgeneric⟩ :=
    pauliBounded_simple_and_projectivelyIndependent_generically n hq
  have hmax := (hgeneric coeff hcoeff).2
  constructor
  · exact maximallyProjective_exists_complete_circuitPolygon_of_replicaBudget
      k (2 ^ n - 1) (pauliBoundedChoiEnergy coeff)
      (maximallyProjectiveEnergy_pauliBoundedChoiEnergy coeff hmax)
      target htarget hepsilon hepsilonHalf hrho replica hreplica hbudget
  · intro t
    simpa using (finiteQLocalAutonomousTransferSignal_gt_haarBenchmark
      (Fin n) q (pauliBoundedHamiltonian coeff)
      (pauliBoundedHamiltonian_ne_zero_of_maximallyProjective hn coeff hmax)
      (pauliBoundedHamiltonian_hasPauliWeightAtMost coeff)
      t (by simpa using hsep))

end RHTower
