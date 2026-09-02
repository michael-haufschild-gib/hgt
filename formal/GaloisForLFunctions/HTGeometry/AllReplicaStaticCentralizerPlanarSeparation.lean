import GaloisForLFunctions.HTGeometry.QuenchedCentralizerPropagatorSplit
import GaloisForLFunctions.HTGeometry.HistogramCentralizerDimension
import GaloisForLFunctions.HTGeometry.PauliChainReplicaSpectralPropagation
import GaloisForLFunctions.HTGeometry.AveragedCentralizerProjectionFloor
import GaloisForLFunctions.HTGeometry.PlanarStaticSeparation
import GaloisForLFunctions.HTGeometry.CentralizerCenteredTransfer
import GaloisForLFunctions.HTGeometry.GraphLocalHallSaturation
import GaloisForLFunctions.HTGeometry.CentralCasimirComplementHallExpansion
import GaloisForLFunctions.HTGeometry.FreeFockMatrixZeroAtomExclusion
import GaloisForLFunctions.HTGeometry.FreeFockMatrixFullFourierDecay

/-!
# All-replica static-centralizer / planar-separation infrastructure

The quenched split, histogram centralizer count, concrete annealed dephasing, averaged-centralizer
floor, and abstract separation inequality are imported above.  This module constructs the literal
non-diagonal all-replica matrix pencil required by the planar side: the complete one-site and
graph-edge collective-Pauli commutator family, completed by its simultaneous-kernel projector and
weighted by arbitrary strictly positive variances.

The Euclidean-space Hall theorem is transported exactly to matrix `mulVec` coordinates.  Thus the
completed coefficient family is Hermitian, has trivial common kernel, is Hall rank-nondecreasing,
has no zero-energy matrix atom, and satisfies the full matrix atom/covariance annihilation law at
every energy.  No subsingleton-column or diagonal-Dyson reduction is used.
-/

open Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Simultaneous conjugation of a family through a linear equivalence. -/
def conjugateLinearFamily
    {𝕜 X Y J : Type*} [DivisionRing 𝕜]
    [AddCommGroup X] [Module 𝕜 X] [AddCommGroup Y] [Module 𝕜 Y]
    (e : X ≃ₗ[𝕜] Y) (A : J → X →ₗ[𝕜] X) : J → Y →ₗ[𝕜] Y :=
  fun j => e.toLinearMap.comp ((A j).comp e.symm.toLinearMap)

/-- Hall rank-nondecrease is invariant under simultaneous input/output coordinate transport. -/
theorem linearFamilyHall_conjugate
    {𝕜 X Y J : Type*} [DivisionRing 𝕜]
    [AddCommGroup X] [Module 𝕜 X] [AddCommGroup Y] [Module 𝕜 Y]
    [FiniteDimensional 𝕜 X] [FiniteDimensional 𝕜 Y]
    (e : X ≃ₗ[𝕜] Y) (A : J → X →ₗ[𝕜] X)
    (hA : LinearFamilyHall A) :
    LinearFamilyHall (conjugateLinearFamily e A) := by
  intro V
  let U : Submodule 𝕜 X := V.map e.symm.toLinearMap
  have hshadow : linearFamilyShadow A U ≤
      (linearFamilyShadow (conjugateLinearFamily e A) V).map e.symm.toLinearMap := by
    rw [linearFamilyShadow]
    apply iSup_le
    intro j
    rintro y ⟨x, hx, rfl⟩
    obtain ⟨v, hv, rfl⟩ := hx
    refine ⟨conjugateLinearFamily e A j v, ?_, ?_⟩
    · rw [linearFamilyShadow]
      exact (le_iSup (fun k => V.map (conjugateLinearFamily e A k)) j) ⟨v, hv, rfl⟩
    · simp [conjugateLinearFamily]
  calc
    Module.finrank 𝕜 V = Module.finrank 𝕜 U :=
      (e.symm.finrank_map_eq V).symm
    _ ≤ Module.finrank 𝕜 (linearFamilyShadow A U) := hA U
    _ ≤ Module.finrank 𝕜
        ((linearFamilyShadow (conjugateLinearFamily e A) V).map e.symm.toLinearMap) :=
      Submodule.finrank_mono hshadow
    _ = Module.finrank 𝕜
        (linearFamilyShadow (conjugateLinearFamily e A) V) :=
      e.symm.finrank_map_eq _

/-- Multiplying a linear map by a nonzero scalar does not change the image of a subspace. -/
theorem submodule_map_smul_linearMap_eq
    {𝕜 X Y : Type*} [Field 𝕜]
    [AddCommGroup X] [Module 𝕜 X] [AddCommGroup Y] [Module 𝕜 Y]
    (U : Submodule 𝕜 X) (f : X →ₗ[𝕜] Y) (c : 𝕜) (hc : c ≠ 0) :
    U.map (c • f) = U.map f := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    refine ⟨c • x, U.smul_mem c hx, ?_⟩
    simp
  · rintro _ ⟨x, hx, rfl⟩
    refine ⟨c⁻¹ • x, U.smul_mem c⁻¹ hx, ?_⟩
    simp [hc]

/-- Independent nonzero rescaling of family members preserves Hall rank-nondecrease. -/
theorem linearFamilyHall_smul
    {𝕜 X J : Type*} [Field 𝕜]
    [AddCommGroup X] [Module 𝕜 X] [FiniteDimensional 𝕜 X]
    (A : J → X →ₗ[𝕜] X) (c : J → 𝕜)
    (hc : ∀ j, c j ≠ 0) (hA : LinearFamilyHall A) :
    LinearFamilyHall (fun j => c j • A j) := by
  intro U
  have hshadow : linearFamilyShadow (fun j => c j • A j) U =
      linearFamilyShadow A U := by
    unfold linearFamilyShadow
    apply le_antisymm
    · apply iSup_le
      intro j
      rw [submodule_map_smul_linearMap_eq U (A j) (c j) (hc j)]
      exact le_iSup (fun k => U.map (A k)) j
    · apply iSup_le
      intro j
      rw [← submodule_map_smul_linearMap_eq U (A j) (c j) (hc j)]
      exact le_iSup (fun k => U.map (c k • A k)) j
  rw [hshadow]
  exact hA U

variable {I R : Type*} [Fintype I] [DecidableEq I]
  [Fintype R] [DecidableEq R]

/-- Literal matrix of one complete graph-local collective-Pauli commutator generator. -/
def graphLocalCommutatorMatrix (G : SimpleGraph I) (j : GraphLocalIndex I G) :
    Matrix (FiniteAllReplicaOperatorIndex I R)
      (FiniteAllReplicaOperatorIndex I R) ℂ :=
  matrixCommutatorRepresentation
    (collectivePauliString I R (graphLocalLabel G j))

theorem graphLocalCommutatorMatrix_conjTranspose
    (G : SimpleGraph I) (j : GraphLocalIndex I G) :
    (graphLocalCommutatorMatrix (R := R) G j)ᴴ =
      graphLocalCommutatorMatrix (R := R) G j := by
  exact matrixCommutatorRepresentation_conjTranspose
    (collectivePauliString_isHermitian (R := R) _)

/-- Matrix and Euclidean formulations of the graph-local generator agree exactly. -/
theorem graphLocalCommutatorMatrix_toEuclideanLin
    (G : SimpleGraph I) (j : GraphLocalIndex I G) :
    (graphLocalCommutatorMatrix (R := R) G j).toEuclideanLin =
      graphLocalGenerator I R G j := rfl

/-- Matrix family obtained by adjoining the simultaneous-kernel projector. -/
def graphLocalCompletedMatrix (G : SimpleGraph I) :
    Option (GraphLocalIndex I G) →
      Matrix (FiniteAllReplicaOperatorIndex I R)
        (FiniteAllReplicaOperatorIndex I R) ℂ :=
  completedHermitianFamily (graphLocalCommutatorMatrix (R := R) G)

/-- Strictly positive variances on every member of the completed graph-local family. -/
def GraphLocalPositiveVariance (G : SimpleGraph I) :=
  {v : Option (GraphLocalIndex I G) → ℝ // ∀ j, 0 < v j}

/-- The completed all-replica graph-local coefficient pencil with arbitrary positive weights. -/
def graphLocalWeightedCompletedMatrix (G : SimpleGraph I)
    (v : GraphLocalPositiveVariance G) :
    Option (GraphLocalIndex I G) →
      Matrix (FiniteAllReplicaOperatorIndex I R)
        (FiniteAllReplicaOperatorIndex I R) ℂ :=
  fun j => ((Real.sqrt (v.1 j) : ℝ) : ℂ) •
    graphLocalCompletedMatrix (R := R) G j

theorem graphLocalMatrix_commonKernel_eq (G : SimpleGraph I) :
    hermitianMatrixFamilyCommonKernel
        (graphLocalCommutatorMatrix (R := R) G) =
      graphLocalCommonKernel I R G := by
  rfl

/-- The completed matrix family is literally the completed Euclidean family used by Hall. -/
theorem graphLocalCompletedMatrix_toEuclideanLin
    (G : SimpleGraph I) (j : Option (GraphLocalIndex I G)) :
    (graphLocalCompletedMatrix (R := R) G j).toEuclideanLin =
      graphLocalCompleted I R G j := by
  cases j with
  | none =>
      apply LinearMap.ext
      intro x
      change
        (hermitianMatrixFamilyCommonKernelProjection
            (graphLocalCommutatorMatrix (R := R) G)).toEuclideanLin x =
          (graphLocalCommonKernel I R G).starProjection x
      rw [hermitianMatrixFamilyCommonKernelProjection_apply,
        graphLocalMatrix_commonKernel_eq]
  | some j =>
      exact graphLocalCommutatorMatrix_toEuclideanLin G j

theorem graphLocalCompletedMatrix_conjTranspose
    (G : SimpleGraph I) (j : Option (GraphLocalIndex I G)) :
    (graphLocalCompletedMatrix (R := R) G j)ᴴ =
      graphLocalCompletedMatrix (R := R) G j := by
  exact completedHermitianFamily_conjTranspose _
    (graphLocalCommutatorMatrix_conjTranspose G) j

/-- Kernel completion makes the matrix coefficient family jointly injective. -/
theorem graphLocalCompletedMatrix_hasTrivialCommonKernel
    (G : SimpleGraph I) :
    HasTrivialCommonKernel (graphLocalCompletedMatrix (R := R) G) := by
  intro x hx
  have hxE : ∀ j,
      (graphLocalCompletedMatrix (R := R) G j).toEuclideanLin
        (WithLp.toLp 2 x) = 0 := by
    intro j
    rw [Matrix.toLpLin_toLp]
    apply congrArg (WithLp.toLp 2)
    funext i
    exact hx j i
  have hzero := completedHermitianFamily_commonKernel_eq_bot
    (graphLocalCommutatorMatrix (R := R) G) (WithLp.toLp 2 x) hxE
  exact (WithLp.linearEquiv 2 ℂ _).symm.injective hzero

/-- Exact all-subspace Hall law for the completed matrix pencil in `mulVec` coordinates. -/
theorem graphLocalCompletedMatrix_hall (G : SimpleGraph I) :
    LinearFamilyHall
      (fun j => (graphLocalCompletedMatrix (R := R) G j).mulVecLin) := by
  let e : EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R) ≃ₗ[ℂ]
      (FiniteAllReplicaOperatorIndex I R → ℂ) :=
    WithLp.linearEquiv 2 ℂ _
  have hE : LinearFamilyHall
      (fun j => (graphLocalCompletedMatrix (R := R) G j).toEuclideanLin) := by
    simpa only [graphLocalCompletedMatrix_toEuclideanLin] using
      (graphLocalCompleted_hall (I := I) (R := R) G)
  have h := linearFamilyHall_conjugate e
    (fun j => (graphLocalCompletedMatrix (R := R) G j).toEuclideanLin) hE
  have hfamily : conjugateLinearFamily e
      (fun j => (graphLocalCompletedMatrix (R := R) G j).toEuclideanLin) =
      fun j => (graphLocalCompletedMatrix (R := R) G j).mulVecLin := by
    funext j
    apply LinearMap.ext
    intro x
    funext i
    simp [conjugateLinearFamily, e, Matrix.toLpLin_toLp,
      Matrix.mulVecLin, Matrix.mulVec]
  rwa [hfamily] at h

/-- Hall fullness excludes the zero-energy atom of the unweighted completed pencil. -/
theorem graphLocalCompletedMatrix_zeroAtomMass_eq_zero
    (G : SimpleGraph I) :
    freeFockMatrixAtomMass
      (graphLocalCompletedMatrix (R := R) G)
      (graphLocalCompletedMatrix_conjTranspose G)
      (graphLocalCompletedMatrix_hasTrivialCommonKernel G) 0 = 0 := by
  exact freeFockMatrixAtomMass_zero_eq_zero_of_hall
    (graphLocalCompletedMatrix (R := R) G)
    (graphLocalCompletedMatrix_conjTranspose G)
    (graphLocalCompletedMatrix_hasTrivialCommonKernel G)
    (graphLocalCompletedMatrix_hall G)

theorem graphLocalWeightedCompletedMatrix_conjTranspose
    (G : SimpleGraph I) (v : GraphLocalPositiveVariance G)
    (j : Option (GraphLocalIndex I G)) :
    (graphLocalWeightedCompletedMatrix (R := R) G v j)ᴴ =
      graphLocalWeightedCompletedMatrix (R := R) G v j := by
  rw [graphLocalWeightedCompletedMatrix, Matrix.conjTranspose_smul,
    graphLocalCompletedMatrix_conjTranspose]
  simp

/-- Positive variance rescaling preserves joint injectivity of the completed pencil. -/
theorem graphLocalWeightedCompletedMatrix_hasTrivialCommonKernel
    (G : SimpleGraph I) (v : GraphLocalPositiveVariance G) :
    HasTrivialCommonKernel (graphLocalWeightedCompletedMatrix (R := R) G v) := by
  intro x hx
  apply graphLocalCompletedMatrix_hasTrivialCommonKernel G x
  intro j i
  have hj := hx j i
  have hc : (((Real.sqrt (v.1 j) : ℝ) : ℂ)) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (v.2 j)))
  apply (mul_eq_zero.mp ?_).resolve_left hc
  simpa only [graphLocalWeightedCompletedMatrix, Matrix.smul_apply, smul_eq_mul,
    Finset.mul_sum, mul_assoc] using hj

/-- Positive variance rescaling preserves exact Hall rank-nondecrease. -/
theorem graphLocalWeightedCompletedMatrix_hall
    (G : SimpleGraph I) (v : GraphLocalPositiveVariance G) :
    LinearFamilyHall
      (fun j => (graphLocalWeightedCompletedMatrix (R := R) G v j).mulVecLin) := by
  have hc : ∀ j : Option (GraphLocalIndex I G),
      (((Real.sqrt (v.1 j) : ℝ) : ℂ)) ≠ 0 := fun j =>
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (v.2 j)))
  have h := linearFamilyHall_smul
    (fun j => (graphLocalCompletedMatrix (R := R) G j).mulVecLin)
    (fun j => ((Real.sqrt (v.1 j) : ℝ) : ℂ)) hc
    (graphLocalCompletedMatrix_hall G)
  have hfamily :
      (fun j => (graphLocalWeightedCompletedMatrix (R := R) G v j).mulVecLin) =
      (fun j => (((Real.sqrt (v.1 j) : ℝ) : ℂ)) •
        (graphLocalCompletedMatrix (R := R) G j).mulVecLin) := by
    funext j
    apply LinearMap.ext
    intro x
    funext i
    simp [graphLocalWeightedCompletedMatrix, Matrix.mulVecLin, Matrix.mulVec]
  rw [hfamily]
  exact h

/-- The positive-variance all-replica completed pencil has no zero-energy matrix atom. -/
theorem graphLocalWeightedCompletedMatrix_zeroAtomMass_eq_zero
    (G : SimpleGraph I) (v : GraphLocalPositiveVariance G) :
    freeFockMatrixAtomMass
      (graphLocalWeightedCompletedMatrix (R := R) G v)
      (graphLocalWeightedCompletedMatrix_conjTranspose G v)
      (graphLocalWeightedCompletedMatrix_hasTrivialCommonKernel G v) 0 = 0 := by
  exact freeFockMatrixAtomMass_zero_eq_zero_of_hall
    (graphLocalWeightedCompletedMatrix (R := R) G v)
    (graphLocalWeightedCompletedMatrix_conjTranspose G v)
    (graphLocalWeightedCompletedMatrix_hasTrivialCommonKernel G v)
    (graphLocalWeightedCompletedMatrix_hall G v)

/-- At every real energy, the covariance image of the exact replicated pencil's atom annihilates
that atom.  This is the full non-diagonal Dyson boundary equation. -/
theorem graphLocalWeightedCompletedMatrix_atomCovariance_mul_eq_zero
    (G : SimpleGraph I) (v : GraphLocalPositiveVariance G) (a : ℝ) :
    matrixSemicircleCovariance
        (graphLocalWeightedCompletedMatrix (R := R) G v)
        (freeFockMatrixAtomMass
          (graphLocalWeightedCompletedMatrix (R := R) G v)
          (graphLocalWeightedCompletedMatrix_conjTranspose G v)
          (graphLocalWeightedCompletedMatrix_hasTrivialCommonKernel G v) a) *
      freeFockMatrixAtomMass
        (graphLocalWeightedCompletedMatrix (R := R) G v)
        (graphLocalWeightedCompletedMatrix_conjTranspose G v)
        (graphLocalWeightedCompletedMatrix_hasTrivialCommonKernel G v) a = 0 := by
  exact matrixSemicircleCovariance_freeFockMatrixAtomMass_mul_eq_zero
    (graphLocalWeightedCompletedMatrix (R := R) G v)
    (graphLocalWeightedCompletedMatrix_conjTranspose G v)
    (graphLocalWeightedCompletedMatrix_hasTrivialCommonKernel G v) a

end

end GaloisForLFunctions.HTGeometry
