import GaloisForLFunctions.HTGeometry.AllReplicaCollectivePauliCasimir

/-!
# Fixed-orientation edge operators at arbitrary replica order

One Pauli axis is chosen at each endpoint of an edge and the resulting two-site product is summed
over replicas.  Bracketing with the collective generator at an endpoint rotates the axis at that
endpoint and leaves the other endpoint untouched, so the three edge operators obtained by rotating
one endpoint axis carry the adjoint representation of that endpoint's collective `su(2)`.
-/

open Finset Matrix

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

section Helper

variable {S : Type*} [Fintype S] [DecidableEq S] {A : Type*} [Ring A]

/-- A commutator of two sums collapses to its diagonal when the off-diagonal pairs commute. -/
theorem ringCommutator_sum_diagonal (f g : S → A)
    (hcross : ∀ s r, s ≠ r → f s * g r = g r * f s) :
    ringCommutator (∑ s, f s) (∑ r, g r) = ∑ r, ringCommutator (f r) (g r) := by
  classical
  have hfg : (∑ s, f s) * (∑ r, g r) = ∑ s, ∑ r, f s * g r := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun s _ => Finset.mul_sum _ _ _
  have hgf : (∑ r, g r) * (∑ s, f s) = ∑ s, ∑ r, g r * f s := by
    rw [Finset.sum_mul, Finset.sum_comm]
    exact Finset.sum_congr rfl fun s _ => Finset.mul_sum _ _ _
  rw [ringCommutator, hfg, hgf, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← Finset.sum_sub_distrib,
    Finset.sum_eq_single s (fun r _ hrs => by rw [hcross s r (Ne.symm hrs), sub_self])
      (fun hcon => absurd (Finset.mem_univ s) hcon)]
  rfl

end Helper

variable (I R : Type*) [Fintype I] [DecidableEq I] [Fintype R] [DecidableEq R]

/-- The fixed-orientation edge operator: one Pauli axis at each endpoint, synchronized over
replicas. -/
def fixedEdgeCollectivePauli (i j : I) (a b : Fin 3) :
    Matrix (FiniteQubitConfiguration (I × R)) (FiniteQubitConfiguration (I × R)) ℂ :=
  ∑ r : R, finiteSingleSiteMatrix ((i, r) : I × R) (finiteQubitPauli a) *
    finiteSingleSiteMatrix ((j, r) : I × R) (finiteQubitPauli b)

variable {I R}

theorem finiteSingleSiteMatrix_pauli_comm_of_ne {p q : I × R} (hpq : p ≠ q) (a b : Fin 3) :
    finiteSingleSiteMatrix p (finiteQubitPauli a) *
        finiteSingleSiteMatrix q (finiteQubitPauli b) =
      finiteSingleSiteMatrix q (finiteQubitPauli b) *
        finiteSingleSiteMatrix p (finiteQubitPauli a) :=
  finiteSingleSiteMatrix_comm_of_ne hpq _ _

/-- Edge operators are Hermitian. -/
theorem fixedEdgeCollectivePauli_isHermitian {i j : I} (hij : i ≠ j) (a b : Fin 3) :
    (fixedEdgeCollectivePauli I R i j a b).IsHermitian := by
  classical
  rw [Matrix.IsHermitian, fixedEdgeCollectivePauli, Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Matrix.conjTranspose_mul, finiteSingleSiteMatrix_pauli, finiteSingleSiteMatrix_pauli,
    finitePauliMatrix_isHermitian, finitePauliMatrix_isHermitian,
    ← finiteSingleSiteMatrix_pauli, ← finiteSingleSiteMatrix_pauli]
  exact finiteSingleSiteMatrix_pauli_comm_of_ne
    (by intro hc; exact hij (congrArg Prod.fst hc).symm) b a

/-- **Bracketing with an endpoint's collective generator rotates that endpoint's axis.** -/
theorem collectivePauli_fixedEdge_bracket_left {i j : I} (hij : i ≠ j) (c a b : Fin 3) :
    ringCommutator (finiteReplicatedSiteCollectivePauli I R i c)
        (fixedEdgeCollectivePauli I R i j a b) =
      ∑ k : Fin 3, pauliStructureCoeff c a k • fixedEdgeCollectivePauli I R i j k b := by
  classical
  rw [finiteReplicatedSiteCollectivePauli, fixedEdgeCollectivePauli,
    ringCommutator_sum_diagonal]
  · have hdiag : ∀ r : R,
        ringCommutator (finiteSingleSiteMatrix ((i, r) : I × R) (finiteQubitPauli c))
          (finiteSingleSiteMatrix ((i, r) : I × R) (finiteQubitPauli a) *
            finiteSingleSiteMatrix ((j, r) : I × R) (finiteQubitPauli b)) =
        ∑ k : Fin 3, pauliStructureCoeff c a k •
          (finiteSingleSiteMatrix ((i, r) : I × R) (finiteQubitPauli k) *
            finiteSingleSiteMatrix ((j, r) : I × R) (finiteQubitPauli b)) := by
      intro r
      have hcb : finiteSingleSiteMatrix ((i, r) : I × R) (finiteQubitPauli c) *
          finiteSingleSiteMatrix ((j, r) : I × R) (finiteQubitPauli b) =
          finiteSingleSiteMatrix ((j, r) : I × R) (finiteQubitPauli b) *
            finiteSingleSiteMatrix ((i, r) : I × R) (finiteQubitPauli c) :=
        finiteSingleSiteMatrix_pauli_comm_of_ne
          (by intro hc; exact hij (congrArg Prod.fst hc)) c b
      rw [ringCommutator, ← mul_assoc, mul_assoc _ _
        (finiteSingleSiteMatrix ((i, r) : I × R) (finiteQubitPauli c)), ← hcb, ← mul_assoc,
        ← sub_mul, finiteSingleSitePauli_bracket, Finset.sum_mul]
      exact Finset.sum_congr rfl fun k _ => (smul_mul_assoc _ _ _)
    rw [Finset.sum_congr rfl fun r _ => hdiag r, Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.smul_sum, fixedEdgeCollectivePauli]
  · intro s r hsr
    have h1 : finiteSingleSiteMatrix ((i, s) : I × R) (finiteQubitPauli c) *
        finiteSingleSiteMatrix ((i, r) : I × R) (finiteQubitPauli a) =
        finiteSingleSiteMatrix ((i, r) : I × R) (finiteQubitPauli a) *
          finiteSingleSiteMatrix ((i, s) : I × R) (finiteQubitPauli c) :=
      finiteSingleSiteMatrix_pauli_comm_of_ne
        (by intro hc; exact hsr (congrArg Prod.snd hc)) c a
    have h2 : finiteSingleSiteMatrix ((i, s) : I × R) (finiteQubitPauli c) *
        finiteSingleSiteMatrix ((j, r) : I × R) (finiteQubitPauli b) =
        finiteSingleSiteMatrix ((j, r) : I × R) (finiteQubitPauli b) *
          finiteSingleSiteMatrix ((i, s) : I × R) (finiteQubitPauli c) :=
      finiteSingleSiteMatrix_pauli_comm_of_ne
        (by intro hc; exact hij (congrArg Prod.fst hc)) c b
    rw [← mul_assoc, h1, mul_assoc, h2, ← mul_assoc]

/-- The same rotation law at the other endpoint. -/
theorem collectivePauli_fixedEdge_bracket_right {i j : I} (hij : i ≠ j) (c a b : Fin 3) :
    ringCommutator (finiteReplicatedSiteCollectivePauli I R j c)
        (fixedEdgeCollectivePauli I R i j a b) =
      ∑ k : Fin 3, pauliStructureCoeff c b k • fixedEdgeCollectivePauli I R i j a k := by
  classical
  rw [finiteReplicatedSiteCollectivePauli, fixedEdgeCollectivePauli,
    ringCommutator_sum_diagonal]
  · have hdiag : ∀ r : R,
        ringCommutator (finiteSingleSiteMatrix ((j, r) : I × R) (finiteQubitPauli c))
          (finiteSingleSiteMatrix ((i, r) : I × R) (finiteQubitPauli a) *
            finiteSingleSiteMatrix ((j, r) : I × R) (finiteQubitPauli b)) =
        ∑ k : Fin 3, pauliStructureCoeff c b k •
          (finiteSingleSiteMatrix ((i, r) : I × R) (finiteQubitPauli a) *
            finiteSingleSiteMatrix ((j, r) : I × R) (finiteQubitPauli k)) := by
      intro r
      have hca : finiteSingleSiteMatrix ((j, r) : I × R) (finiteQubitPauli c) *
          finiteSingleSiteMatrix ((i, r) : I × R) (finiteQubitPauli a) =
          finiteSingleSiteMatrix ((i, r) : I × R) (finiteQubitPauli a) *
            finiteSingleSiteMatrix ((j, r) : I × R) (finiteQubitPauli c) :=
        finiteSingleSiteMatrix_pauli_comm_of_ne
          (by intro hc; exact hij (congrArg Prod.fst hc).symm) c a
      rw [ringCommutator, ← mul_assoc, hca, mul_assoc, mul_assoc, ← mul_sub,
        finiteSingleSitePauli_bracket, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => (mul_smul_comm _ _ _)
    rw [Finset.sum_congr rfl fun r _ => hdiag r, Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.smul_sum, fixedEdgeCollectivePauli]
  · intro s r hsr
    have h1 : finiteSingleSiteMatrix ((j, s) : I × R) (finiteQubitPauli c) *
        finiteSingleSiteMatrix ((i, r) : I × R) (finiteQubitPauli a) =
        finiteSingleSiteMatrix ((i, r) : I × R) (finiteQubitPauli a) *
          finiteSingleSiteMatrix ((j, s) : I × R) (finiteQubitPauli c) :=
      finiteSingleSiteMatrix_pauli_comm_of_ne
        (by intro hc; exact hij (congrArg Prod.fst hc).symm) c a
    have h2 : finiteSingleSiteMatrix ((j, s) : I × R) (finiteQubitPauli c) *
        finiteSingleSiteMatrix ((j, r) : I × R) (finiteQubitPauli b) =
        finiteSingleSiteMatrix ((j, r) : I × R) (finiteQubitPauli b) *
          finiteSingleSiteMatrix ((j, s) : I × R) (finiteQubitPauli c) :=
      finiteSingleSiteMatrix_pauli_comm_of_ne
        (by intro hc; exact hsr (congrArg Prod.snd hc)) c b
    rw [← mul_assoc, h1, mul_assoc, h2, ← mul_assoc]

/-- Edge operators at a site not on the edge commute with that site's collective generator. -/
theorem collectivePauli_fixedEdge_comm_of_notMem {i j v : I} (hvi : v ≠ i) (hvj : v ≠ j)
    (c a b : Fin 3) :
    ringCommutator (finiteReplicatedSiteCollectivePauli I R v c)
      (fixedEdgeCollectivePauli I R i j a b) = 0 := by
  classical
  rw [finiteReplicatedSiteCollectivePauli, fixedEdgeCollectivePauli, ringCommutator,
    Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero fun s _ => ?_
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero fun r _ => ?_
  have h1 : finiteSingleSiteMatrix ((v, s) : I × R) (finiteQubitPauli c) *
      finiteSingleSiteMatrix ((i, r) : I × R) (finiteQubitPauli a) =
      finiteSingleSiteMatrix ((i, r) : I × R) (finiteQubitPauli a) *
        finiteSingleSiteMatrix ((v, s) : I × R) (finiteQubitPauli c) :=
    finiteSingleSiteMatrix_pauli_comm_of_ne
      (by intro hc; exact hvi (congrArg Prod.fst hc)) c a
  have h2 : finiteSingleSiteMatrix ((v, s) : I × R) (finiteQubitPauli c) *
      finiteSingleSiteMatrix ((j, r) : I × R) (finiteQubitPauli b) =
      finiteSingleSiteMatrix ((j, r) : I × R) (finiteQubitPauli b) *
        finiteSingleSiteMatrix ((v, s) : I × R) (finiteQubitPauli c) :=
    finiteSingleSiteMatrix_pauli_comm_of_ne
      (by intro hc; exact hvj (congrArg Prod.fst hc)) c b
  rw [← mul_assoc, h1, mul_assoc, h2, ← mul_assoc, sub_self]

end GaloisForLFunctions.HTGeometry
