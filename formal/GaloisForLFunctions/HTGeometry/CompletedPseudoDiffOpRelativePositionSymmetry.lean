import GaloisForLFunctions.HTGeometry.CompletedPseudoDiffOpProjectiveRelativePosition

/-!
# Symmetry of completed pseudodifferential Cartan position

Reversing an ordered pair of completed valuation lattices negates its Cartan coweight and reverses
the Weyl-chamber order.  This file proves that statement on the actual lattice carrier, descends it
to projective vertices, and records invariance of the Euclidean norm.  These are prerequisites for
the Euclidean affine-building metric; no abstract building or metric hypothesis is introduced.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

namespace DiffOp

variable {K : Type*} [Field K] [Differential K]
variable {ι : Type*}

/-- Ambient diagonal right multiplication realizes diagonal scaling of a completed lattice. -/
theorem mapCompletedPseudoDiffOpLatticeLinear_diagonalRightMul
    (a : ι → (CompletedPseudoDiffOp K)ˣ)
    (L : CompletedPseudoDiffOpLattice K ι) :
    mapCompletedPseudoDiffOpLatticeLinear
        (diagonalRightMulCompletedPseudoVecLinearEquiv a) L =
      diagonalScaleCompletedPseudoDiffOpLattice a L := by
  apply CompletedPseudoDiffOpLattice.ext
  ext y
  rw [mem_mapCompletedPseudoDiffOpLatticeLinear_iff,
    mem_diagonalScaleCompletedPseudoDiffOpLattice_iff]
  rfl

/-- Diagonal right multiplication adds its coweight to a standard-apartment lattice. -/
theorem mapCompletedPseudoDiffOpLatticeLinear_diagonalCoweight
    [Fintype ι] (m n : ι → ℤ) :
    mapCompletedPseudoDiffOpLatticeLinear
        (diagonalRightMulCompletedPseudoVecLinearEquiv
          (completedPseudoDiffOpUniformizerCoweight n))
        (standardCompletedPseudoDiffOpLatticeAtCoweight (K := K) m) =
      standardCompletedPseudoDiffOpLatticeAtCoweight (K := K) (m + n) := by
  rw [mapCompletedPseudoDiffOpLatticeLinear_diagonalRightMul,
    standardCompletedPseudoDiffOpLatticeAtCoweight,
    diagonalScaleCompletedPseudoDiffOpLattice_mul,
    ← completedPseudoDiffOpUniformizerCoweight_add]
  rfl

/-- Reversal permutation of a finite coordinate frame. -/
def completedPseudoDiffOpFinRevPerm (r : ℕ) : Equiv.Perm (Fin r) :=
  { toFun := Fin.rev
    invFun := Fin.rev
    left_inv := Fin.rev_rev
    right_inv := Fin.rev_rev }

/-- Weyl-chamber reversal: negate a coweight and reverse its coordinates. -/
def completedPseudoDiffOpReverseNegCoweight {r : ℕ} (m : Fin r → ℤ) : Fin r → ℤ :=
  fun i => -m i.rev

/-- Negated coordinate reversal preserves dominance. -/
theorem completedPseudoDiffOpReverseNegCoweight_antitone
    {r : ℕ} {m : Fin r → ℤ} (hm : Antitone m) :
    Antitone (completedPseudoDiffOpReverseNegCoweight m) := by
  intro i j hij
  have hrev : j.rev ≤ i.rev := Fin.rev_le_rev.mpr hij
  exact neg_le_neg (hm hrev)

/-- **Reversal law for canonical dominant Cartan position.** -/
theorem completedPseudoDiffOpDominantRelativePosition_reverse
    {r : ℕ} (L M : CompletedPseudoDiffOpLattice K (Fin r)) :
    completedPseudoDiffOpDominantRelativePosition M L =
      completedPseudoDiffOpReverseNegCoweight
        (completedPseudoDiffOpDominantRelativePosition L M) := by
  let d := completedPseudoDiffOpDominantCartanData L M
  let q := diagonalRightMulCompletedPseudoVecLinearEquiv (K := K)
    (completedPseudoDiffOpUniformizerCoweight (K := K) (-d.coweight))
  let p := completedPseudoDiffOpCoordinatePermutationLinearEquiv
    (K := K) (completedPseudoDiffOpFinRevPerm r)
  let e := d.frame.trans q
  let g := e.trans p
  have heM : mapCompletedPseudoDiffOpLatticeLinear e M =
      standardCompletedPseudoDiffOpLattice (K := K) (ι := Fin r) := by
    rw [← mapCompletedPseudoDiffOpLatticeLinear_trans, d.map_right]
    simp only [q]
    rw [mapCompletedPseudoDiffOpLatticeLinear_diagonalCoweight]
    rw [show d.coweight + -d.coweight = (fun _ => 0) by
      funext i
      simp]
    exact standardCompletedPseudoDiffOpLatticeAtCoweight_zero (K := K) (r := r)
  have heL : mapCompletedPseudoDiffOpLatticeLinear e L =
      standardCompletedPseudoDiffOpLatticeAtCoweight (K := K) (-d.coweight) := by
    rw [← mapCompletedPseudoDiffOpLatticeLinear_trans, d.map_left]
    simp only [q]
    rw [mapCompletedPseudoDiffOpLatticeLinear_diagonalRightMul]
    rfl
  have hgM : mapCompletedPseudoDiffOpLatticeLinear g M =
      standardCompletedPseudoDiffOpLattice (K := K) (ι := Fin r) := by
    rw [← mapCompletedPseudoDiffOpLatticeLinear_trans, heM]
    exact map_completedPseudoDiffOpCoordinatePermutation_standard
      (K := K) (completedPseudoDiffOpFinRevPerm r)
  have hgL : mapCompletedPseudoDiffOpLatticeLinear g L =
      standardCompletedPseudoDiffOpLatticeAtCoweight (K := K)
        (completedPseudoDiffOpReverseNegCoweight d.coweight) := by
    rw [← mapCompletedPseudoDiffOpLatticeLinear_trans, heL,
      map_completedPseudoDiffOpCoordinatePermutation_coweight]
    rfl
  have hdom : Antitone (completedPseudoDiffOpReverseNegCoweight d.coweight) :=
    completedPseudoDiffOpReverseNegCoweight_antitone d.dominant
  have hcanonical := completedPseudoDiffOpDominantRelativePosition_eq
    M L g (completedPseudoDiffOpReverseNegCoweight d.coweight) hgM hgL hdom
  rw [← hcanonical]
  rfl

/-- The canonical dominant relative position of a lattice with itself is zero. -/
theorem completedPseudoDiffOpDominantRelativePosition_self
    {r : ℕ} (L : CompletedPseudoDiffOpLattice K (Fin r)) :
    completedPseudoDiffOpDominantRelativePosition L L = fun _ => 0 := by
  let d := completedPseudoDiffOpDominantCartanData L L
  have hright : mapCompletedPseudoDiffOpLatticeLinear d.frame L =
      standardCompletedPseudoDiffOpLatticeAtCoweight (K := K) (fun _ => 0) := by
    rw [standardCompletedPseudoDiffOpLatticeAtCoweight_zero]
    exact d.map_left
  have hdom : Antitone (fun _ : Fin r => (0 : ℤ)) := antitone_const
  exact (completedPseudoDiffOpDominantRelativePosition_eq L L d.frame
    (fun _ => 0) d.map_left hright hdom).symm

/-- Centering intertwines coweight reversal with Euclidean coordinate reversal and negation. -/
theorem centeredCoweight_reverseNeg {r : ℕ} (m : Fin r → ℤ) :
    centeredCoweight (completedPseudoDiffOpReverseNegCoweight m) =
      fun i => -centeredCoweight m i.rev := by
  classical
  have hperm : (∑ j : Fin r, (m j.rev : ℝ)) = ∑ j : Fin r, (m j : ℝ) := by
    simpa [completedPseudoDiffOpFinRevPerm] using
      (Equiv.sum_comp (completedPseudoDiffOpFinRevPerm r)
        (fun j : Fin r => (m j : ℝ)))
  funext i
  simp only [centeredCoweight, completedPseudoDiffOpReverseNegCoweight, Int.cast_neg,
    Finset.sum_neg_distrib, hperm]
  ring

/-- Reversal law for the centered Euclidean relative-position vector of actual lattices. -/
theorem completedPseudoDiffOpEuclideanRelativePosition_reverse
    {r : ℕ} (L M : CompletedPseudoDiffOpLattice K (Fin r)) :
    completedPseudoDiffOpEuclideanRelativePosition M L =
      fun i => -completedPseudoDiffOpEuclideanRelativePosition L M i.rev := by
  rw [completedPseudoDiffOpEuclideanRelativePosition,
    completedPseudoDiffOpDominantRelativePosition_reverse,
    centeredCoweight_reverseNeg]
  rfl

/-- Euclidean relative position vanishes on the diagonal. -/
theorem completedPseudoDiffOpEuclideanRelativePosition_self
    {r : ℕ} (L : CompletedPseudoDiffOpLattice K (Fin r)) :
    completedPseudoDiffOpEuclideanRelativePosition L L = 0 := by
  rw [completedPseudoDiffOpEuclideanRelativePosition,
    completedPseudoDiffOpDominantRelativePosition_self]
  funext i
  simp [centeredCoweight]

/-- Reversing the lattice pair preserves the Euclidean norm of its relative-position point. -/
theorem completedPseudoDiffOpEuclideanRelativePositionPoint_norm_reverse
    {r : ℕ} (L M : CompletedPseudoDiffOpLattice K (Fin r)) :
    ‖(completedPseudoDiffOpEuclideanRelativePositionPoint M L).1‖ =
      ‖(completedPseudoDiffOpEuclideanRelativePositionPoint L M).1‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  calc
    ∑ i : Fin r,
        ‖(completedPseudoDiffOpEuclideanRelativePositionPoint M L).1.ofLp i‖ ^ 2 =
      ∑ i : Fin r,
        ‖(completedPseudoDiffOpEuclideanRelativePositionPoint L M).1.ofLp i.rev‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro i _
          rw [show (completedPseudoDiffOpEuclideanRelativePositionPoint M L).1.ofLp i =
              -(completedPseudoDiffOpEuclideanRelativePositionPoint L M).1.ofLp i.rev by
            exact congrFun (completedPseudoDiffOpEuclideanRelativePosition_reverse L M) i]
          simp
    _ = ∑ i : Fin r,
        ‖(completedPseudoDiffOpEuclideanRelativePositionPoint L M).1.ofLp i‖ ^ 2 := by
          simpa [completedPseudoDiffOpFinRevPerm] using
            (Equiv.sum_comp (completedPseudoDiffOpFinRevPerm r)
              (fun i : Fin r =>
                (completedPseudoDiffOpEuclideanRelativePositionPoint L M).1.ofLp i ^ 2))

/-- Projective Euclidean position reverses coordinatewise, with Weyl order reversal. -/
theorem differentialVariationalProjectiveEuclideanRelativePosition_reverse_apply
    {r : ℕ}
    (x y : DifferentialVariationalProjectiveBuildingCarrier K (Fin r)) (i : Fin r) :
    (differentialVariationalProjectiveEuclideanRelativePosition y x : Fin r → ℝ) i =
      -(differentialVariationalProjectiveEuclideanRelativePosition x y : Fin r → ℝ) i.rev := by
  refine Quotient.inductionOn₂ x y ?_
  intro L M
  change completedPseudoDiffOpEuclideanRelativePosition M L i =
    -completedPseudoDiffOpEuclideanRelativePosition L M i.rev
  rw [completedPseudoDiffOpEuclideanRelativePosition_reverse]

/-- The norm of projective Euclidean relative position is symmetric. -/
theorem differentialVariationalProjectiveEuclideanRelativePosition_norm_comm
    {r : ℕ}
    (x y : DifferentialVariationalProjectiveBuildingCarrier K (Fin r)) :
    ‖(differentialVariationalProjectiveEuclideanRelativePosition y x).1‖ =
      ‖(differentialVariationalProjectiveEuclideanRelativePosition x y).1‖ := by
  refine Quotient.inductionOn₂ x y ?_
  intro L M
  exact completedPseudoDiffOpEuclideanRelativePositionPoint_norm_reverse L M

/-- Projective Euclidean relative position vanishes coordinatewise on the diagonal. -/
theorem differentialVariationalProjectiveEuclideanRelativePosition_self_apply
    {r : ℕ}
    (x : DifferentialVariationalProjectiveBuildingCarrier K (Fin r)) (i : Fin r) :
    (differentialVariationalProjectiveEuclideanRelativePosition x x : Fin r → ℝ) i = 0 := by
  refine Quotient.inductionOn x ?_
  intro L
  change completedPseudoDiffOpEuclideanRelativePosition L L i = 0
  rw [completedPseudoDiffOpEuclideanRelativePosition_self]
  rfl

/-- Euclidean norm of the centered Cartan vector between two projective lattice vertices. -/
def differentialVariationalProjectiveEuclideanVertexDistance
    {r : ℕ}
    (x y : DifferentialVariationalProjectiveBuildingCarrier K (Fin r)) : ℝ :=
  ‖(differentialVariationalProjectiveEuclideanRelativePosition x y).1‖

theorem differentialVariationalProjectiveEuclideanVertexDistance_self
    {r : ℕ}
    (x : DifferentialVariationalProjectiveBuildingCarrier K (Fin r)) :
    differentialVariationalProjectiveEuclideanVertexDistance x x = 0 := by
  rw [differentialVariationalProjectiveEuclideanVertexDistance, norm_eq_zero]
  apply PiLp.ext
  intro i
  exact differentialVariationalProjectiveEuclideanRelativePosition_self_apply x i

theorem differentialVariationalProjectiveEuclideanVertexDistance_comm
    {r : ℕ}
    (x y : DifferentialVariationalProjectiveBuildingCarrier K (Fin r)) :
    differentialVariationalProjectiveEuclideanVertexDistance x y =
      differentialVariationalProjectiveEuclideanVertexDistance y x := by
  exact (differentialVariationalProjectiveEuclideanRelativePosition_norm_comm x y).symm

theorem differentialVariationalProjectiveEuclideanVertexDistance_nonneg
    {r : ℕ}
    (x y : DifferentialVariationalProjectiveBuildingCarrier K (Fin r)) :
    0 ≤ differentialVariationalProjectiveEuclideanVertexDistance x y := norm_nonneg _

end DiffOp

end

end GaloisForLFunctions.HTGeometry
