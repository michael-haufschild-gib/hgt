import GaloisForLFunctions.HTGeometry.FixedEdgeCollectivePauli
import GaloisForLFunctions.HTGeometry.CentralCasimirCommonKernelCorrection

/-!
# Endpoint defects of fixed-orientation edge commutators

Applying a fixed-orientation edge commutator to a sitewise singlet produces an eigenvector of the
collective quadratic Casimir at each endpoint, with the nonzero adjoint eigenvalue.  At a site off
the edge the same vector stays in the Casimir kernel.  Two edges therefore have orthogonal images
as soon as some site separates them.
-/

open Finset Matrix

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

/-- The double contraction of the Pauli structure constants: the adjoint Casimir eigenvalue. -/
theorem pauliStructureCoeff_double_contraction (a m : Fin 3) :
    (∑ c : Fin 3, ∑ k : Fin 3, pauliStructureCoeff c a k * pauliStructureCoeff c k m) =
      if a = m then (8 : ℂ) else 0 := by
  fin_cases a <;> fin_cases m <;>
    simp [pauliStructureCoeff, Fin.sum_univ_three] <;> ring_nf <;> simp [Complex.I_sq]

variable (I R : Type*) [Fintype I] [DecidableEq I] [Fintype R] [DecidableEq R]

/-- The commutator matrix of a fixed-orientation edge operator. -/
def fixedEdgeCommutatorMatrix (i j : I) (a b : Fin 3) :
    Matrix (FiniteAllReplicaOperatorIndex I R) (FiniteAllReplicaOperatorIndex I R) ℂ :=
  matrixCommutatorRepresentation (fixedEdgeCollectivePauli I R i j a b)

/-- The collective quadratic Casimir at a physical site. -/
def siteCollectiveCasimir (v : I) :
    Matrix (FiniteAllReplicaOperatorIndex I R) (FiniteAllReplicaOperatorIndex I R) ℂ :=
  ∑ c : Fin 3, finiteAllReplicaCollectiveCommutatorMatrix I R v c *
    finiteAllReplicaCollectiveCommutatorMatrix I R v c

variable {I R}

theorem toEuclideanLin_mul_apply {X : Type*} [Fintype X] [DecidableEq X]
    (M N : Matrix X X ℂ) (x : EuclideanSpace ℂ X) :
    (M * N).toEuclideanLin x = M.toEuclideanLin (N.toEuclideanLin x) := by
  simp [Matrix.toLpLin_apply, Matrix.toEuclideanLin, Matrix.mulVec_mulVec]

/-- Bracketing the edge commutator matrix with an endpoint's collective commutator matrix rotates
that endpoint's axis. -/
theorem collectiveCommutator_fixedEdgeCommutator_bracket_left {i j : I} (hij : i ≠ j)
    (c a b : Fin 3) :
    finiteAllReplicaCollectiveCommutatorMatrix I R i c * fixedEdgeCommutatorMatrix I R i j a b -
        fixedEdgeCommutatorMatrix I R i j a b *
          finiteAllReplicaCollectiveCommutatorMatrix I R i c =
      ∑ k : Fin 3, pauliStructureCoeff c a k • fixedEdgeCommutatorMatrix I R i j k b := by
  rw [finiteAllReplicaCollectiveCommutatorMatrix, fixedEdgeCommutatorMatrix,
    matrixCommutatorRepresentation_bracket]
  have hbr : finiteReplicatedSiteCollectivePauli I R i c *
      fixedEdgeCollectivePauli I R i j a b -
      fixedEdgeCollectivePauli I R i j a b * finiteReplicatedSiteCollectivePauli I R i c =
      ∑ k : Fin 3, pauliStructureCoeff c a k • fixedEdgeCollectivePauli I R i j k b :=
    collectivePauli_fixedEdge_bracket_left hij c a b
  rw [hbr, map_sum]
  exact Finset.sum_congr rfl fun k _ => map_smul _ _ _

theorem collectiveCommutator_fixedEdgeCommutator_bracket_right {i j : I} (hij : i ≠ j)
    (c a b : Fin 3) :
    finiteAllReplicaCollectiveCommutatorMatrix I R j c * fixedEdgeCommutatorMatrix I R i j a b -
        fixedEdgeCommutatorMatrix I R i j a b *
          finiteAllReplicaCollectiveCommutatorMatrix I R j c =
      ∑ k : Fin 3, pauliStructureCoeff c b k • fixedEdgeCommutatorMatrix I R i j a k := by
  rw [finiteAllReplicaCollectiveCommutatorMatrix, fixedEdgeCommutatorMatrix,
    matrixCommutatorRepresentation_bracket]
  have hbr : finiteReplicatedSiteCollectivePauli I R j c *
      fixedEdgeCollectivePauli I R i j a b -
      fixedEdgeCollectivePauli I R i j a b * finiteReplicatedSiteCollectivePauli I R j c =
      ∑ k : Fin 3, pauliStructureCoeff c b k • fixedEdgeCollectivePauli I R i j a k :=
    collectivePauli_fixedEdge_bracket_right hij c a b
  rw [hbr, map_sum]
  exact Finset.sum_congr rfl fun k _ => map_smul _ _ _

theorem collectiveCommutator_fixedEdgeCommutator_comm_of_notMem {i j v : I} (hvi : v ≠ i)
    (hvj : v ≠ j) (c a b : Fin 3) :
    finiteAllReplicaCollectiveCommutatorMatrix I R v c * fixedEdgeCommutatorMatrix I R i j a b =
      fixedEdgeCommutatorMatrix I R i j a b *
        finiteAllReplicaCollectiveCommutatorMatrix I R v c := by
  have hbr := collectivePauli_fixedEdge_comm_of_notMem (I := I) (R := R) hvi hvj c a b
  rw [ringCommutator, sub_eq_zero] at hbr
  rw [finiteAllReplicaCollectiveCommutatorMatrix, fixedEdgeCommutatorMatrix]
  exact matrixCommutatorRepresentation_comm_of_comm hbr

theorem mem_singlet_iff {x : EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R)} :
    x ∈ finiteAllReplicaCollectiveSingletSubspace I R ↔
      ∀ v : I, ∀ c : Fin 3,
        (finiteAllReplicaCollectiveCommutatorMatrix I R v c).toEuclideanLin x = 0 := by
  rw [finiteAllReplicaCollectiveSingletSubspace, hermitianMatrixFamilyCommonKernel,
    Submodule.mem_iInf]
  constructor
  · intro h v c
    exact h (v, c)
  · rintro h ⟨v, c⟩
    exact h v c


theorem siteCollectiveCasimir_apply
    (v : I) (y : EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R)) :
    (siteCollectiveCasimir I R v).toEuclideanLin y =
      ∑ c : Fin 3, (finiteAllReplicaCollectiveCommutatorMatrix I R v c).toEuclideanLin
        ((finiteAllReplicaCollectiveCommutatorMatrix I R v c).toEuclideanLin y) := by
  rw [siteCollectiveCasimir]
  rw [map_sum, LinearMap.sum_apply]
  exact Finset.sum_congr rfl fun c _ => toEuclideanLin_mul_apply _ _ y

/-- One collective generator at an endpoint rotates the edge image of a singlet. -/
theorem collectiveCommutator_apply_fixedEdge_left {i j : I} (hij : i ≠ j) (c a b : Fin 3)
    {x : EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R)}
    (hx : x ∈ finiteAllReplicaCollectiveSingletSubspace I R) :
    (finiteAllReplicaCollectiveCommutatorMatrix I R i c).toEuclideanLin
        ((fixedEdgeCommutatorMatrix I R i j a b).toEuclideanLin x) =
      ∑ k : Fin 3, pauliStructureCoeff c a k •
        (fixedEdgeCommutatorMatrix I R i j k b).toEuclideanLin x := by
  have hbr := collectiveCommutator_fixedEdgeCommutator_bracket_left (I := I) (R := R) hij c a b
  have happ := congrArg (fun M : Matrix (FiniteAllReplicaOperatorIndex I R)
      (FiniteAllReplicaOperatorIndex I R) ℂ => M.toEuclideanLin x) hbr
  simp only [map_sub, map_sum, map_smul, LinearMap.sub_apply, LinearMap.sum_apply,
    LinearMap.smul_apply] at happ
  rw [toEuclideanLin_mul_apply, toEuclideanLin_mul_apply,
    (mem_singlet_iff.mp hx) i c, map_zero, sub_zero] at happ
  exact happ

theorem collectiveCommutator_apply_fixedEdge_right {i j : I} (hij : i ≠ j) (c a b : Fin 3)
    {x : EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R)}
    (hx : x ∈ finiteAllReplicaCollectiveSingletSubspace I R) :
    (finiteAllReplicaCollectiveCommutatorMatrix I R j c).toEuclideanLin
        ((fixedEdgeCommutatorMatrix I R i j a b).toEuclideanLin x) =
      ∑ k : Fin 3, pauliStructureCoeff c b k •
        (fixedEdgeCommutatorMatrix I R i j a k).toEuclideanLin x := by
  have hbr := collectiveCommutator_fixedEdgeCommutator_bracket_right (I := I) (R := R) hij c a b
  have happ := congrArg (fun M : Matrix (FiniteAllReplicaOperatorIndex I R)
      (FiniteAllReplicaOperatorIndex I R) ℂ => M.toEuclideanLin x) hbr
  simp only [map_sub, map_sum, map_smul, LinearMap.sub_apply, LinearMap.sum_apply,
    LinearMap.smul_apply] at happ
  rw [toEuclideanLin_mul_apply, toEuclideanLin_mul_apply,
    (mem_singlet_iff.mp hx) j c, map_zero, sub_zero] at happ
  exact happ

/-- **The endpoint Casimir acts on the edge image of a singlet by the adjoint eigenvalue.** -/
theorem siteCollectiveCasimir_fixedEdge_left {i j : I} (hij : i ≠ j) (a b : Fin 3)
    {x : EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R)}
    (hx : x ∈ finiteAllReplicaCollectiveSingletSubspace I R) :
    (siteCollectiveCasimir I R i).toEuclideanLin
        ((fixedEdgeCommutatorMatrix I R i j a b).toEuclideanLin x) =
      (8 : ℂ) • (fixedEdgeCommutatorMatrix I R i j a b).toEuclideanLin x := by
  classical
  rw [siteCollectiveCasimir_apply]
  have hstep : ∀ c : Fin 3,
      (finiteAllReplicaCollectiveCommutatorMatrix I R i c).toEuclideanLin
        ((finiteAllReplicaCollectiveCommutatorMatrix I R i c).toEuclideanLin
          ((fixedEdgeCommutatorMatrix I R i j a b).toEuclideanLin x)) =
      ∑ k : Fin 3, ∑ m : Fin 3, (pauliStructureCoeff c a k * pauliStructureCoeff c k m) •
        (fixedEdgeCommutatorMatrix I R i j m b).toEuclideanLin x := by
    intro c
    rw [collectiveCommutator_apply_fixedEdge_left hij c a b hx, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, collectiveCommutator_apply_fixedEdge_left hij c k b hx, Finset.smul_sum]
    exact Finset.sum_congr rfl fun m _ => by rw [smul_smul]
  rw [Finset.sum_congr rfl fun c _ => hstep c]
  have hswap1 : (∑ c : Fin 3, ∑ k : Fin 3, ∑ m : Fin 3,
      (pauliStructureCoeff c a k * pauliStructureCoeff c k m) •
        (fixedEdgeCommutatorMatrix I R i j m b).toEuclideanLin x) =
      ∑ c : Fin 3, ∑ m : Fin 3, ∑ k : Fin 3,
        (pauliStructureCoeff c a k * pauliStructureCoeff c k m) •
          (fixedEdgeCommutatorMatrix I R i j m b).toEuclideanLin x :=
    Finset.sum_congr rfl fun c _ => Finset.sum_comm
  have hswap2 : (∑ c : Fin 3, ∑ m : Fin 3, ∑ k : Fin 3,
      (pauliStructureCoeff c a k * pauliStructureCoeff c k m) •
        (fixedEdgeCommutatorMatrix I R i j m b).toEuclideanLin x) =
      ∑ m : Fin 3, ∑ c : Fin 3, ∑ k : Fin 3,
        (pauliStructureCoeff c a k * pauliStructureCoeff c k m) •
          (fixedEdgeCommutatorMatrix I R i j m b).toEuclideanLin x := Finset.sum_comm
  rw [hswap1, hswap2]
  have hval : ∀ m : Fin 3, (∑ c : Fin 3, ∑ k : Fin 3,
      (pauliStructureCoeff c a k * pauliStructureCoeff c k m) •
        (fixedEdgeCommutatorMatrix I R i j m b).toEuclideanLin x) =
      (if a = m then (8 : ℂ) else 0) •
        (fixedEdgeCommutatorMatrix I R i j m b).toEuclideanLin x := by
    intro m
    rw [← pauliStructureCoeff_double_contraction a m, Finset.sum_smul]
    exact Finset.sum_congr rfl fun c _ => Finset.sum_smul.symm
  rw [Finset.sum_congr rfl fun m _ => hval m,
    Finset.sum_eq_single a (fun m _ hma => by rw [if_neg (fun hc => hma hc.symm), zero_smul])
      (fun hcon => absurd (Finset.mem_univ a) hcon), if_pos rfl]


theorem siteCollectiveCasimir_fixedEdge_right {i j : I} (hij : i ≠ j) (a b : Fin 3)
    {x : EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R)}
    (hx : x ∈ finiteAllReplicaCollectiveSingletSubspace I R) :
    (siteCollectiveCasimir I R j).toEuclideanLin
        ((fixedEdgeCommutatorMatrix I R i j a b).toEuclideanLin x) =
      (8 : ℂ) • (fixedEdgeCommutatorMatrix I R i j a b).toEuclideanLin x := by
  classical
  rw [siteCollectiveCasimir_apply]
  have hstep : ∀ c : Fin 3,
      (finiteAllReplicaCollectiveCommutatorMatrix I R j c).toEuclideanLin
        ((finiteAllReplicaCollectiveCommutatorMatrix I R j c).toEuclideanLin
          ((fixedEdgeCommutatorMatrix I R i j a b).toEuclideanLin x)) =
      ∑ k : Fin 3, ∑ m : Fin 3, (pauliStructureCoeff c b k * pauliStructureCoeff c k m) •
        (fixedEdgeCommutatorMatrix I R i j a m).toEuclideanLin x := by
    intro c
    rw [collectiveCommutator_apply_fixedEdge_right hij c a b hx, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, collectiveCommutator_apply_fixedEdge_right hij c a k hx, Finset.smul_sum]
    exact Finset.sum_congr rfl fun m _ => by rw [smul_smul]
  rw [Finset.sum_congr rfl fun c _ => hstep c]
  have hswap1 : (∑ c : Fin 3, ∑ k : Fin 3, ∑ m : Fin 3,
      (pauliStructureCoeff c b k * pauliStructureCoeff c k m) •
        (fixedEdgeCommutatorMatrix I R i j a m).toEuclideanLin x) =
      ∑ c : Fin 3, ∑ m : Fin 3, ∑ k : Fin 3,
        (pauliStructureCoeff c b k * pauliStructureCoeff c k m) •
          (fixedEdgeCommutatorMatrix I R i j a m).toEuclideanLin x :=
    Finset.sum_congr rfl fun c _ => Finset.sum_comm
  have hswap2 : (∑ c : Fin 3, ∑ m : Fin 3, ∑ k : Fin 3,
      (pauliStructureCoeff c b k * pauliStructureCoeff c k m) •
        (fixedEdgeCommutatorMatrix I R i j a m).toEuclideanLin x) =
      ∑ m : Fin 3, ∑ c : Fin 3, ∑ k : Fin 3,
        (pauliStructureCoeff c b k * pauliStructureCoeff c k m) •
          (fixedEdgeCommutatorMatrix I R i j a m).toEuclideanLin x := Finset.sum_comm
  rw [hswap1, hswap2]
  have hval : ∀ m : Fin 3, (∑ c : Fin 3, ∑ k : Fin 3,
      (pauliStructureCoeff c b k * pauliStructureCoeff c k m) •
        (fixedEdgeCommutatorMatrix I R i j a m).toEuclideanLin x) =
      (if b = m then (8 : ℂ) else 0) •
        (fixedEdgeCommutatorMatrix I R i j a m).toEuclideanLin x := by
    intro m
    rw [← pauliStructureCoeff_double_contraction b m, Finset.sum_smul]
    exact Finset.sum_congr rfl fun c _ => Finset.sum_smul.symm
  rw [Finset.sum_congr rfl fun m _ => hval m,
    Finset.sum_eq_single b (fun m _ hmb => by rw [if_neg (fun hc => hmb hc.symm), zero_smul])
      (fun hcon => absurd (Finset.mem_univ b) hcon), if_pos rfl]

/-- At a site off the edge, the edge image of a singlet stays in the Casimir kernel. -/
theorem siteCollectiveCasimir_fixedEdge_notMem {i j v : I} (hvi : v ≠ i) (hvj : v ≠ j)
    (a b : Fin 3) {x : EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R)}
    (hx : x ∈ finiteAllReplicaCollectiveSingletSubspace I R) :
    (siteCollectiveCasimir I R v).toEuclideanLin
      ((fixedEdgeCommutatorMatrix I R i j a b).toEuclideanLin x) = 0 := by
  classical
  rw [siteCollectiveCasimir_apply]
  refine Finset.sum_eq_zero fun c _ => ?_
  have hzero : (finiteAllReplicaCollectiveCommutatorMatrix I R v c).toEuclideanLin
      ((fixedEdgeCommutatorMatrix I R i j a b).toEuclideanLin x) = 0 := by
    rw [← toEuclideanLin_mul_apply,
      collectiveCommutator_fixedEdgeCommutator_comm_of_notMem hvi hvj c a b,
      toEuclideanLin_mul_apply, (mem_singlet_iff.mp hx) v c, map_zero]
  rw [hzero, map_zero]

theorem siteCollectiveCasimir_conjTranspose (v : I) :
    (siteCollectiveCasimir I R v).conjTranspose = siteCollectiveCasimir I R v := by
  rw [siteCollectiveCasimir, Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Matrix.conjTranspose_mul, finiteAllReplicaCollectiveCommutatorMatrix_conjTranspose]

/-- **Two edges separated by a site have orthogonal images on the singlet sector.** -/
theorem inner_fixedEdge_eq_zero_of_separating {i j k l v : I} (hv : v = i ∨ v = j)
    (hvk : v ≠ k) (hvl : v ≠ l) (hij : i ≠ j) (a b a' b' : Fin 3)
    {x y : EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R)}
    (hx : x ∈ finiteAllReplicaCollectiveSingletSubspace I R)
    (hy : y ∈ finiteAllReplicaCollectiveSingletSubspace I R) :
    @inner ℂ _ _ ((fixedEdgeCommutatorMatrix I R i j a b).toEuclideanLin x)
      ((fixedEdgeCommutatorMatrix I R k l a' b').toEuclideanLin y) = 0 := by
  classical
  have hself : LinearMap.adjoint (siteCollectiveCasimir I R v).toEuclideanLin =
      (siteCollectiveCasimir I R v).toEuclideanLin := by
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, siteCollectiveCasimir_conjTranspose]
  have hleft : (siteCollectiveCasimir I R v).toEuclideanLin
      ((fixedEdgeCommutatorMatrix I R i j a b).toEuclideanLin x) =
      (8 : ℂ) • (fixedEdgeCommutatorMatrix I R i j a b).toEuclideanLin x := by
    rcases hv with rfl | rfl
    · exact siteCollectiveCasimir_fixedEdge_left hij a b hx
    · exact siteCollectiveCasimir_fixedEdge_right hij a b hx
  have hright : (siteCollectiveCasimir I R v).toEuclideanLin
      ((fixedEdgeCommutatorMatrix I R k l a' b').toEuclideanLin y) = 0 :=
    siteCollectiveCasimir_fixedEdge_notMem hvk hvl a' b' hy
  have hmove : @inner ℂ _ _ ((siteCollectiveCasimir I R v).toEuclideanLin
        ((fixedEdgeCommutatorMatrix I R i j a b).toEuclideanLin x))
      ((fixedEdgeCommutatorMatrix I R k l a' b').toEuclideanLin y) =
      @inner ℂ _ _ ((fixedEdgeCommutatorMatrix I R i j a b).toEuclideanLin x)
        ((siteCollectiveCasimir I R v).toEuclideanLin
          ((fixedEdgeCommutatorMatrix I R k l a' b').toEuclideanLin y)) := by
    conv_lhs => rw [← hself]
    exact LinearMap.adjoint_inner_left _ _ _
  rw [hleft, hright, inner_zero_right, inner_smul_left] at hmove
  have h8 : (starRingEnd ℂ) (8 : ℂ) = (8 : ℂ) := Complex.conj_eq_iff_re.mpr rfl
  rw [h8] at hmove
  exact (mul_eq_zero.mp hmove).resolve_left (by norm_num)


/-- A vector annihilated by one structure-constant direction is annihilated by all of them. -/
theorem eq_zero_of_pauliStructure_relations {V : Type*} [AddCommGroup V] [Module ℂ V]
    (w : Fin 3 → V) (a : Fin 3) (hw : w a = 0)
    (hrel : ∀ c : Fin 3, (∑ m : Fin 3, pauliStructureCoeff c a m • w m) = 0) (k : Fin 3) :
    w k = 0 := by
  have h0 := hrel 0
  have h1 := hrel 1
  have h2 := hrel 2
  rw [Fin.sum_univ_three] at h0 h1 h2
  fin_cases a <;> simp only [pauliStructureCoeff] at h0 h1 h2 <;> norm_num at h0 h1 h2 <;>
    fin_cases k <;> simp_all

/-- **One vanishing fixed orientation forces every orientation of that edge to vanish.** -/
theorem fixedEdge_apply_eq_zero_of_axes {i j : I} (hij : i ≠ j) (a b : Fin 3)
    {x : EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R)}
    (hx : x ∈ finiteAllReplicaCollectiveSingletSubspace I R)
    (hzero : (fixedEdgeCommutatorMatrix I R i j a b).toEuclideanLin x = 0) (a' b' : Fin 3) :
    (fixedEdgeCommutatorMatrix I R i j a' b').toEuclideanLin x = 0 := by
  classical
  have hleft : ∀ k : Fin 3, (fixedEdgeCommutatorMatrix I R i j k b).toEuclideanLin x = 0 := by
    refine eq_zero_of_pauliStructure_relations
      (fun k => (fixedEdgeCommutatorMatrix I R i j k b).toEuclideanLin x) a hzero ?_
    intro c
    rw [← collectiveCommutator_apply_fixedEdge_left hij c a b hx, hzero, map_zero]
  refine eq_zero_of_pauliStructure_relations
    (fun k => (fixedEdgeCommutatorMatrix I R i j a' k).toEuclideanLin x) b (hleft a') ?_ b'
  intro c
  rw [← collectiveCommutator_apply_fixedEdge_right hij c a' b hx, hleft a', map_zero]

end GaloisForLFunctions.HTGeometry
