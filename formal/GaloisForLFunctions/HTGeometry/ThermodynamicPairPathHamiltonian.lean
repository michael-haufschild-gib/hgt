import GaloisForLFunctions.HTGeometry.NestedPathCutWitness
import GaloisForLFunctions.HTGeometry.SiteSupportedOffMatrixLift
import GaloisForLFunctions.HTGeometry.SiteSupportedReindex
import GaloisForLFunctions.HTGeometry.ThermodynamicPathMobileReference

/-!
# One thermodynamic path field on the paired circuit register

The `(2N+4)`-site prefix is relabelled as `N+2` adjacent qubit pairs.  This module transports the
selected path Hamiltonian, its exact mobile prefix/tail reference, intrinsic support, and the
Duhamel approximation to the circuit-complexity register.
-/

open scoped BigOperators Matrix Matrix.Norms.L2Operator
open Matrix

namespace GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw

open GaloisForLFunctions.HTGeometry

noncomputable section

local instance instCStarAlgebraMatrixThermodynamicPair
    {d : Type*} [Fintype d] [DecidableEq d] : CStarAlgebra (Matrix d d ℂ) where

theorem thermodynamicPairSiteCount (N : ℕ) :
    (N + 2) * 2 = (N * 2 + 1) + 3 := by omega

/-- Physical path order on `N+2` adjacent qubit pairs. -/
def thermodynamicPairSiteEquiv (N : ℕ) :
    PairQubit (N + 2) ≃ Fin ((N * 2 + 1) + 3) :=
  (pairQubitPathEquiv (N + 2)).trans (finCongr (thermodynamicPairSiteCount N))

@[simp] theorem thermodynamicPairSiteEquiv_false (N : ℕ) (j : Fin (N + 2)) :
    (thermodynamicPairSiteEquiv N (j, false)).val = 2 * j.val := by
  simp [thermodynamicPairSiteEquiv]

@[simp] theorem thermodynamicPairSiteEquiv_true (N : ℕ) (j : Fin (N + 2)) :
    (thermodynamicPairSiteEquiv N (j, true)).val = 2 * j.val + 1 := by
  simp [thermodynamicPairSiteEquiv]

/-- Pull a path-site matrix to the paired circuit register. -/
def pullThermodynamicPathMatrix (N : ℕ)
    (H : Matrix (FiniteQubitConfiguration (Fin ((N * 2 + 1) + 3)))
      (FiniteQubitConfiguration (Fin ((N * 2 + 1) + 3))) ℂ) :
    Matrix (Config (PairQubit (N + 2))) (Config (PairQubit (N + 2))) ℂ :=
  Matrix.reindexAlgEquiv ℂ ℂ
    (qubitConfigurationEquiv (thermodynamicPairSiteEquiv N).symm) H

/-- One selected finite Hamiltonian from the single infinite coefficient field. -/
def thermodynamicPairHamiltonian (N : ℕ) (p : InfinitePathLabel → ℝ) :
    Matrix (Config (PairQubit (N + 2))) (Config (PairQubit (N + 2))) ℂ :=
  pullThermodynamicPathMatrix N
    (pathHamiltonian (infinitePathPrefixShell (N * 2 + 1) p))

def thermodynamicPairInitialSites (N K : ℕ) : Finset (PairQubit (N + 2)) :=
  (mobileInitialPathSites (N * 2 + 1) K).map
    (thermodynamicPairSiteEquiv N).symm.toEmbedding

def thermodynamicPairTailSites (N K : ℕ) : Finset (PairQubit (N + 2)) :=
  (mobileTailPathSites (N * 2 + 1) K).map
    (thermodynamicPairSiteEquiv N).symm.toEmbedding

def thermodynamicPairPrefixHamiltonian
    (N K : ℕ) (p : InfinitePathLabel → ℝ) :
    Matrix (Config (PairQubit (N + 2))) (Config (PairQubit (N + 2))) ℂ :=
  pullThermodynamicPathMatrix N
    (pathHamiltonianOnSites (mobileInitialPathSites (N * 2 + 1) K)
      (infinitePathPrefixShell (N * 2 + 1) p))

def thermodynamicPairTailCenterHamiltonian (N K : ℕ) :
    Matrix (Config (PairQubit (N + 2))) (Config (PairQubit (N + 2))) ℂ :=
  pullThermodynamicPathMatrix N
    (pathHamiltonianOnSites (mobileTailPathSites (N * 2 + 1) K)
      (infinitePathPrefixShell (N * 2 + 1) nestedInfinitePathCenter))

/-- Classical energy of the diagonal late center after paired-site relabelling. -/
def thermodynamicPairTailCenterEnergy (N K : ℕ)
    (x : Config (PairQubit (N + 2))) : ℝ :=
  pathDiagEnergy
    (pathShellOnSites (mobileTailPathSites (N * 2 + 1) K)
      (infinitePathPrefixShell (N * 2 + 1) nestedInfinitePathCenter))
    (qubitConfigurationEquiv (thermodynamicPairSiteEquiv N) x)

def thermodynamicPairMobileReference
    (N K : ℕ) (p : InfinitePathLabel → ℝ) :
    Matrix (Config (PairQubit (N + 2))) (Config (PairQubit (N + 2))) ℂ :=
  thermodynamicPairPrefixHamiltonian N K p +
    thermodynamicPairTailCenterHamiltonian N K

theorem thermodynamicPairInitial_disjoint_tail (N K : ℕ) :
    Disjoint (thermodynamicPairInitialSites N K) (thermodynamicPairTailSites N K) := by
  exact (Finset.disjoint_map _).mpr
    (mobileInitialPathSites_disjoint_mobileTailPathSites (N * 2 + 1) K)

@[simp] theorem mem_thermodynamicPairInitialSites_iff
    {N K : ℕ} {q : PairQubit (N + 2)} :
    q ∈ thermodynamicPairInitialSites N K ↔
      (thermodynamicPairSiteEquiv N q).val < 4 * K := by
  constructor
  · intro hq
    rw [thermodynamicPairInitialSites, Finset.mem_map] at hq
    obtain ⟨s, hs, heq⟩ := hq
    have hsite : thermodynamicPairSiteEquiv N q = s := by
      rw [← heq]
      exact (thermodynamicPairSiteEquiv N).apply_symm_apply s
    rw [hsite]
    exact mem_mobileInitialPathSites_iff.mp hs
  · intro hq
    rw [thermodynamicPairInitialSites, Finset.mem_map]
    refine ⟨thermodynamicPairSiteEquiv N q, ?_, ?_⟩
    · exact mem_mobileInitialPathSites_iff.mpr hq
    · exact (thermodynamicPairSiteEquiv N).symm_apply_apply q

theorem thermodynamicPairInitial_disjoint_firstEndpointSites
    {N K : ℕ} (hKL : 8 * K ≤ N + 2)
    {S : Finset (Fin (N + 2))} (hS : S ⊆ inverseSquareBlock hKL) :
    Disjoint (thermodynamicPairInitialSites N K) (firstEndpointSites S) := by
  rw [Finset.disjoint_left]
  intro q hqPrefix hqS
  have hqS' := mem_firstEndpointSites.mp hqS
  have hbound := inverseSquareBlock_index_bounds hKL (hS hqS'.1)
  have hbit : q.2 = false := hqS'.2
  obtain ⟨j, b⟩ := q
  simp only at hbit
  subst b
  change 4 * K < j.val + 1 ∧ j.val + 1 ≤ 8 * K at hbound
  have hprefix := mem_thermodynamicPairInitialSites_iff.mp hqPrefix
  rw [thermodynamicPairSiteEquiv_false] at hprefix
  omega

theorem thermodynamicPairPrefix_isSiteSupported (N K : ℕ)
    (p : InfinitePathLabel → ℝ) :
    IsSiteSupported (thermodynamicPairInitialSites N K)
      (thermodynamicPairPrefixHamiltonian N K p) := by
  exact isSiteSupported_reindexAlgEquiv (thermodynamicPairSiteEquiv N).symm _
    (pathHamiltonianOnSites_isSiteSupported _ _)

theorem thermodynamicPairPrefix_isSelfAdjoint (N K : ℕ)
    (p : InfinitePathLabel → ℝ) :
    IsSelfAdjoint (thermodynamicPairPrefixHamiltonian N K p) := by
  exact isSelfAdjoint_reindexAlgEquiv _ (isSelfAdjoint_pathHamiltonianOnSites _ _)

theorem thermodynamicPairTailCenter_isSiteSupported (N K : ℕ) :
    IsSiteSupported (thermodynamicPairTailSites N K)
      (thermodynamicPairTailCenterHamiltonian N K) := by
  exact isSiteSupported_reindexAlgEquiv (thermodynamicPairSiteEquiv N).symm _
    (pathHamiltonianOnSites_isSiteSupported _ _)

theorem thermodynamicPairTailCenterHamiltonian_eq_diagonal (N K : ℕ) :
    thermodynamicPairTailCenterHamiltonian N K =
      Matrix.diagonal (fun x => ((thermodynamicPairTailCenterEnergy N K x : ℝ) : ℂ)) := by
  unfold thermodynamicPairTailCenterHamiltonian pullThermodynamicPathMatrix
  rw [pathHamiltonianOnSites_eq_diagonal _ _
    (infinitePathPrefixShell_nestedCenter_isDiag (N * 2 + 1))]
  ext x y
  simp only [Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply]
  by_cases hxy : x = y
  · subst y
    simp [thermodynamicPairTailCenterEnergy, qubitConfigurationEquiv]
  · have hmap : qubitConfigurationEquiv (thermodynamicPairSiteEquiv N) x ≠
        qubitConfigurationEquiv (thermodynamicPairSiteEquiv N) y :=
      fun h => hxy ((qubitConfigurationEquiv (thermodynamicPairSiteEquiv N)).injective h)
    simp only [Matrix.submatrix_apply]
    change Matrix.diagonal _
      (qubitConfigurationEquiv (thermodynamicPairSiteEquiv N) x)
      (qubitConfigurationEquiv (thermodynamicPairSiteEquiv N) y) =
        Matrix.diagonal _ x y
    rw [Matrix.diagonal_apply_ne _ hmap, Matrix.diagonal_apply_ne _ hxy]

theorem unitaryEvolution_thermodynamicPairTailCenter_diagonal
    (N K : ℕ) (t : ℝ) :
    unitaryEvolution (thermodynamicPairTailCenterHamiltonian N K) t =
      Matrix.diagonal (fun x =>
        Complex.exp (-(Complex.I * (t * thermodynamicPairTailCenterEnergy N K x)))) := by
  rw [thermodynamicPairTailCenterHamiltonian_eq_diagonal]
  exact unitaryEvolution_diagonal _ _

theorem unitaryEvolution_thermodynamicPairMobileReference
    (N K : ℕ) (p : InfinitePathLabel → ℝ) (t : ℝ) :
    unitaryEvolution (thermodynamicPairMobileReference N K p) t =
      unitaryEvolution (thermodynamicPairPrefixHamiltonian N K p) t *
        unitaryEvolution (thermodynamicPairTailCenterHamiltonian N K) t := by
  exact unitaryEvolution_add_of_isSiteSupported_disjoint
    (thermodynamicPairInitial_disjoint_tail N K)
    (thermodynamicPairPrefix_isSiteSupported N K p)
    (thermodynamicPairTailCenter_isSiteSupported N K) t

/-- Early dynamics is an exact unitary complement lift across every late selected first-endpoint
cut. -/
theorem exists_offMatrixLift_thermodynamicPairPrefixEvolution
    {N K : ℕ} (p : InfinitePathLabel → ℝ) (t : ℝ)
    (hKL : 8 * K ≤ N + 2)
    {S : Finset (Fin (N + 2))} (hS : S ⊆ inverseSquareBlock hKL) :
    ∃ B : Matrix (Off (firstEndpointSites S)) (Off (firstEndpointSites S)) ℂ,
      B ∈ Matrix.unitaryGroup (Off (firstEndpointSites S)) ℂ ∧
      unitaryEvolution (thermodynamicPairPrefixHamiltonian N K p) t =
        offMatrixLift (firstEndpointSites S) B := by
  have hsupport := isSiteSupported_unitaryEvolution
    (thermodynamicPairPrefix_isSiteSupported N K p) t
  have hunit : unitaryEvolution (thermodynamicPairPrefixHamiltonian N K p) t ∈
      Matrix.unitaryGroup (Config (PairQubit (N + 2))) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff']
    exact (unitaryEvolution_mem_unitary
      (thermodynamicPairPrefix_isSelfAdjoint N K p) t).1
  exact exists_unitary_offMatrixLift_of_isSiteSupported
    (thermodynamicPairInitial_disjoint_firstEndpointSites hKL hS) hsupport hunit

theorem norm_thermodynamicPair_sub_mobileReference_le
    {N K : ℕ} {p : InfinitePathLabel → ℝ}
    (hK : 8 ≤ K) (hsize : 4 * K ≤ N * 2 + 3)
    (hp : ∀ i, |p i - nestedInfinitePathCenter i| < infinitePathRadius i) :
  ‖thermodynamicPairHamiltonian N p - thermodynamicPairMobileReference N K p‖ ≤
      1 / (((2 * K + 1 : ℕ) : ℝ) ^ 4) +
        12 / (1000000 * (K : ℝ)) := by
  unfold thermodynamicPairHamiltonian thermodynamicPairMobileReference
    thermodynamicPairPrefixHamiltonian thermodynamicPairTailCenterHamiltonian
  simp only [pullThermodynamicPathMatrix]
  rw [← map_add, ← map_sub]
  rw [l2_opNorm_reindexAlgEquiv_eq]
  change ‖pathHamiltonian (infinitePathPrefixShell (N * 2 + 1) p) -
    pathHamiltonianPacketReference (mobileInitialPathSites (N * 2 + 1) K)
      (mobileTailPathSites (N * 2 + 1) K)
      (infinitePathPrefixShell (N * 2 + 1) p)
      (infinitePathPrefixShell (N * 2 + 1) nestedInfinitePathCenter)‖ ≤ _
  exact norm_thermodynamicPath_sub_mobileReference_le hK hsize hp

/-- Pulled physical evolution stays strictly inside the target error of the factorized mobile
reference throughout one shell. -/
theorem norm_unitaryEvolution_thermodynamicPair_sub_mobileReference_lt
    {N K : ℕ} {p : InfinitePathLabel → ℝ} {t ε : ℝ}
    (hK : 8 ≤ K) (hsize : 4 * K ≤ N * 2 + 3)
    (hp : ∀ i, |p i - nestedInfinitePathCenter i| < infinitePathRadius i)
    (hε : 0 < ε) (ht0 : 0 ≤ t)
    (ht : t < 256 * Real.pi * ε * (K + 1)) :
    ‖unitaryEvolution (thermodynamicPairHamiltonian N p) t -
      unitaryEvolution (thermodynamicPairMobileReference N K p) t‖ < ε := by
  have hActual : IsSelfAdjoint (thermodynamicPairHamiltonian N p) :=
    isSelfAdjoint_reindexAlgEquiv _ (isSelfAdjoint_pathHamiltonian _)
  have hReference : IsSelfAdjoint (thermodynamicPairMobileReference N K p) :=
    (isSelfAdjoint_reindexAlgEquiv _ (isSelfAdjoint_pathHamiltonianOnSites _ _)).add
      (isSelfAdjoint_reindexAlgEquiv _ (isSelfAdjoint_pathHamiltonianOnSites _ _))
  have hduhamel :
      ‖unitaryEvolution (thermodynamicPairHamiltonian N p) t -
        unitaryEvolution (thermodynamicPairMobileReference N K p) t‖ ≤
        |t| * ‖thermodynamicPairHamiltonian N p - thermodynamicPairMobileReference N K p‖ := by
    simpa [unitaryEvolution] using selfAdjoint_unitaryEvolution_norm_sub_le
      (thermodynamicPairHamiltonian N p) (thermodynamicPairMobileReference N K p)
      hActual hReference t
  rw [abs_of_nonneg ht0] at hduhamel
  have hnorm := norm_thermodynamicPair_sub_mobileReference_le hK hsize hp
  have hmul := mul_le_mul_of_nonneg_left hnorm ht0
  have hbase := mobileCut_baseDuhamel_lt_half hK hε ht
  have hpert := mobileCut_perturbDuhamel_lt_half hK hε ht0 ht
    (show 12 / (1000000 * (K : ℝ)) ≤ 12 / (1000000 * (K : ℝ)) by rfl)
  nlinarith

end

end GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw
