import GaloisForLFunctions.HTGeometry.FreeAffinePencilInnerRank
import GaloisForLFunctions.HTGeometry.AllReplicaStaticCentralizerPlanarSeparation

/-!
# Full inner rank for the all-replica graph-local affine pencil

This instantiates free-pencil fullness for the exact weighted completed matrix family used by the
all-replica planar-separation card.  Zero energy is covered separately by the existing Hall
zero-atom theorem; this module supplies algebraic fullness at every nonzero real energy.
-/

namespace GaloisForLFunctions.HTGeometry

variable {I R : Type*} [Fintype I] [DecidableEq I]
  [Fintype R] [DecidableEq R]

/-- Every nonzero-energy affine free pencil of the literal weighted graph-local family is full. -/
theorem graphLocalWeightedCompletedFreePencil_hasFullInnerRank
    (G : SimpleGraph I) (v : GraphLocalPositiveVariance G)
    {a : ℝ} (ha : a ≠ 0) :
    Matrix.HasFullInnerRank
      (FreeAffinePencil.matrix
        (graphLocalWeightedCompletedMatrix (R := R) G v) (a : ℂ)) :=
  FreeAffinePencil.complex_hasFullInnerRank_of_ne_zero _ ha

/-- At every real energy, the literal graph-local pencil is covered unconditionally: Hall excludes
the atom at zero, while the shifted affine free pencil has full inner rank away from zero. -/
theorem graphLocalWeightedCompletedMatrix_zeroAtom_or_freePencil_full
    (G : SimpleGraph I) (v : GraphLocalPositiveVariance G) (a : ℝ) :
    (a = 0 ∧
      freeFockMatrixAtomMass
        (graphLocalWeightedCompletedMatrix (R := R) G v)
        (graphLocalWeightedCompletedMatrix_conjTranspose G v)
        (graphLocalWeightedCompletedMatrix_hasTrivialCommonKernel G v) a = 0) ∨
      Matrix.HasFullInnerRank
        (FreeAffinePencil.matrix
          (graphLocalWeightedCompletedMatrix (R := R) G v) (a : ℂ)) := by
  by_cases ha : a = 0
  · left
    refine ⟨ha, ?_⟩
    subst a
    exact graphLocalWeightedCompletedMatrix_zeroAtomMass_eq_zero G v
  · right
    exact graphLocalWeightedCompletedFreePencil_hasFullInnerRank G v ha

end GaloisForLFunctions.HTGeometry
