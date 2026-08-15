import GaloisForLFunctions.HTGeometry.NearestNeighborQuditPathGenericityLaw
import GaloisForLFunctions.HTGeometry.FiniteEntropyPlateauFutureLaw

/-!
# Generic local collision extremality on a qudit path

Membership in the canonical maximal-rank parameter locus of a real-affine Hermitian family is, by
definition, maximal projective rationality of the spectrum, so the all-order collision-floor
equivalence applies to every parameter of that locus.

For an open path of at least two levels the locus is dense, residual and of full Lebesgue measure.
Almost every onsite-plus-nearest-neighbour Hermitian Hamiltonian therefore attains, at every replica
order and for every positive spectral weight, the unavoidable permutation collision floor, and every
long-time survival-fidelity moment converges to that floor.
-/

open Filter MeasureTheory Set Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

section AffineMembership

/-- Membership in the real-affine maximal-rank locus is maximal projective rationality. -/
theorem maximallyProjective_of_mem_realAffineHermitianMaximalSet
    {m : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (base : Matrix I I ℂ) (generator : Fin m → Matrix I I ℂ)
    (hbase : base.IsHermitian) (hgenerator : ∀ t, (generator t).IsHermitian)
    {p : Fin m → ℝ}
    (hp : p ∈ realAffineHermitianMaximalSet base generator hbase hgenerator) :
    MaximallyProjectiveEnergy
      (realAffineMatrix_isHermitian base generator hbase hgenerator p).eigenvalues := by
  have hpoly : ((realAffineMatrixPolynomial base generator).map
      (MvPolynomial.eval₂Hom (RingHom.id ℂ) (fun t => (p t : ℂ)))).IsHermitian := by
    rw [eval_realAffineMatrixPolynomial]
    exact realAffineMatrix_isHermitian base generator hbase hgenerator p
  have hmem : MaximallyProjectiveEnergy hpoly.eigenvalues := hp
  have heig : hpoly.eigenvalues =
      (realAffineMatrix_isHermitian base generator hbase hgenerator p).eigenvalues := by
    apply (Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff hpoly
      (realAffineMatrix_isHermitian base generator hbase hgenerator p)).2
    rw [eval_realAffineMatrixPolynomial]
  rwa [heig] at hmem

end AffineMembership

section LocalHamiltonian

/-- The architecture-local Hamiltonian at one coefficient vector. -/
def PhysicallyRealizedTensorTreeSystem.localHamiltonianAt
    (Z : PhysicallyRealizedTensorTreeSystem.{u})
    (p : Fin Z.localHamiltonianParameterCount → ℝ) :
    Matrix Z.PhysicalState Z.PhysicalState ℂ := by
  letI : Fintype Z.PhysicalState := Z.physicalFintype
  letI : DecidableEq Z.PhysicalState := Z.physicalDecidableEq
  exact realAffineMatrix 0 Z.localHamiltonianGenerator p

theorem PhysicallyRealizedTensorTreeSystem.localHamiltonianAt_isHermitian
    (Z : PhysicallyRealizedTensorTreeSystem.{u})
    (p : Fin Z.localHamiltonianParameterCount → ℝ) :
    letI : Fintype Z.PhysicalState := Z.physicalFintype
    letI : DecidableEq Z.PhysicalState := Z.physicalDecidableEq
    (Z.localHamiltonianAt p).IsHermitian := by
  letI : Fintype Z.PhysicalState := Z.physicalFintype
  letI : DecidableEq Z.PhysicalState := Z.physicalDecidableEq
  exact realAffineMatrix_isHermitian 0 Z.localHamiltonianGenerator
    Matrix.isHermitian_zero Z.localHamiltonianGenerator_isHermitian p

/-- The energy spectrum of the architecture-local Hamiltonian at one coefficient vector. -/
def PhysicallyRealizedTensorTreeSystem.localHamiltonianEnergy
    (Z : PhysicallyRealizedTensorTreeSystem.{u})
    (p : Fin Z.localHamiltonianParameterCount → ℝ) :
    Z.PhysicalState → ℝ := by
  letI : Fintype Z.PhysicalState := Z.physicalFintype
  letI : DecidableEq Z.PhysicalState := Z.physicalDecidableEq
  exact (Z.localHamiltonianAt_isHermitian p).eigenvalues

theorem PhysicallyRealizedTensorTreeSystem.maximallyProjective_of_mem_localHamiltonianMaximalSet
    (Z : PhysicallyRealizedTensorTreeSystem.{u})
    {p : Fin Z.localHamiltonianParameterCount → ℝ}
    (hp : p ∈ Z.localHamiltonianMaximalSet) :
    letI : Fintype Z.PhysicalState := Z.physicalFintype
    letI : DecidableEq Z.PhysicalState := Z.physicalDecidableEq
    MaximallyProjectiveEnergy (Z.localHamiltonianEnergy p) := by
  letI : Fintype Z.PhysicalState := Z.physicalFintype
  letI : DecidableEq Z.PhysicalState := Z.physicalDecidableEq
  exact maximallyProjective_of_mem_realAffineHermitianMaximalSet
    0 Z.localHamiltonianGenerator Matrix.isHermitian_zero
    Z.localHamiltonianGenerator_isHermitian hp

end LocalHamiltonian

section GenericExtremality

/-- **Generic local collision extremality.**  For every open path of at least two `q`-level sites
there is an exact onsite-plus-nearest-neighbour Hermitian coefficient space in which the set of
Hamiltonians attaining the unavoidable permutation collision floor, at every replica order and for
every positive spectral weight, is dense, residual and of full Lebesgue measure. -/
theorem exists_quditPath_generic_collisionFloor (n q : ℕ) (hn : 2 ≤ n) (hq : 2 ≤ q) :
    ∃ Z : PhysicallyRealizedTensorTreeSystem.{0},
    ∃ e : Z.spectral.Observer ≃ Fin n,
      Z.architectureGraph = SimpleGraph.comap e (SimpleGraph.pathGraph n) ∧
      Z.spectral.stateCard = q ^ n ∧
      Dense Z.localHamiltonianMaximalSet ∧
      Z.localHamiltonianMaximalSet ∈
        residual (Fin Z.localHamiltonianParameterCount → ℝ) ∧
      volume Z.localHamiltonianMaximalSetᶜ = 0 ∧
      ∀ p ∈ Z.localHamiltonianMaximalSet,
        letI : Fintype Z.PhysicalState := Z.physicalFintype
        letI : DecidableEq Z.PhysicalState := Z.physicalDecidableEq
        ∀ weight : Z.PhysicalState → ℝ, (∀ i, 0 < weight i) → ∀ m : ℕ,
          fidelityReplicaCollisionMass weight (Z.localHamiltonianEnergy p) m =
            fidelityReplicaPermutationFloor weight m := by
  obtain ⟨Z, e, hgraph, hstate, hdense, hresidual, hnull⟩ :=
    exists_uniformQuditPathLocalHamiltonianMaximalSet_dense_residual_fullMeasure n q hn hq
  refine ⟨Z, e, hgraph, hstate, hdense, hresidual, hnull, ?_⟩
  intro p hp
  letI : Fintype Z.PhysicalState := Z.physicalFintype
  letI : DecidableEq Z.PhysicalState := Z.physicalDecidableEq
  intro weight hweight m
  exact (all_fidelityReplicaCollisionMass_eq_floor_iff hweight (Z.localHamiltonianEnergy p)).2
    (Z.maximallyProjective_of_mem_localHamiltonianMaximalSet hp) m

/-- Observable form of generic local collision extremality: every long-time survival-fidelity
moment of a generic local Hamiltonian converges to its permutation floor. -/
theorem exists_quditPath_generic_survivalFidelityFloor (n q : ℕ) (hn : 2 ≤ n) (hq : 2 ≤ q) :
    ∃ Z : PhysicallyRealizedTensorTreeSystem.{0},
    ∃ e : Z.spectral.Observer ≃ Fin n,
      Z.architectureGraph = SimpleGraph.comap e (SimpleGraph.pathGraph n) ∧
      Z.spectral.stateCard = q ^ n ∧
      Dense Z.localHamiltonianMaximalSet ∧
      Z.localHamiltonianMaximalSet ∈
        residual (Fin Z.localHamiltonianParameterCount → ℝ) ∧
      volume Z.localHamiltonianMaximalSetᶜ = 0 ∧
      ∀ p ∈ Z.localHamiltonianMaximalSet,
        letI : Fintype Z.PhysicalState := Z.physicalFintype
        letI : DecidableEq Z.PhysicalState := Z.physicalDecidableEq
        ∀ weight : Z.PhysicalState → ℝ, (∀ i, 0 < weight i) → ∀ m : ℕ,
          Tendsto
            (finiteSpectralSurvivalFidelityMean weight (Z.localHamiltonianEnergy p) m)
            atTop
            (𝓝 (fidelityReplicaPermutationFloor weight m : ℂ)) := by
  obtain ⟨Z, e, hgraph, hstate, hdense, hresidual, hnull⟩ :=
    exists_uniformQuditPathLocalHamiltonianMaximalSet_dense_residual_fullMeasure n q hn hq
  refine ⟨Z, e, hgraph, hstate, hdense, hresidual, hnull, ?_⟩
  intro p hp
  letI : Fintype Z.PhysicalState := Z.physicalFintype
  letI : DecidableEq Z.PhysicalState := Z.physicalDecidableEq
  intro weight hweight m
  exact (all_finiteSpectralSurvivalFidelityMean_tendsto_floor_iff hweight
    (Z.localHamiltonianEnergy p)).2
    (Z.maximallyProjective_of_mem_localHamiltonianMaximalSet hp) m

end GenericExtremality

end

end GaloisForLFunctions.HTGeometry
