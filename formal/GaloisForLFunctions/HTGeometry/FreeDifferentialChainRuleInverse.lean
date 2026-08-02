import GaloisForLFunctions.HTGeometry.FreeDifferentialFrechetIndependence
import GaloisForLFunctions.HTGeometry.OperatorConductorLength

/-!
# Inverting the chain rule

The chain rule expresses the ambient Fréchet row of a substituted element as the product of the
transported intrinsic row with the Fréchet matrix of the embedding.  Since the rows of that matrix
are left independent, the matrix has a right inverse over the skew field of rational
pseudodifferential operators, and the intrinsic row is recovered from the ambient one:

`B = A · P` and `A = B · Q`.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

namespace JetField

noncomputable section

universe w

variable {C : Type u} {ι : Type v} {ι' : Type w} [Field C]

section Embedding

variable [Algebra (JetField C ι') (JetField C ι)]
  [IsScalarTower C (JetField C ι') (JetField C ι)]

variable (hδ : ∀ u : JetField C ι', algebraMap (JetField C ι') (JetField C ι) (u′)
  = (algebraMap (JetField C ι') (JetField C ι) u)′)

include hδ

/-- **The inverse chain rule.**  There is one matrix over the skew field of rational
pseudodifferential operators which recovers the intrinsic Fréchet row of every element from its
ambient Fréchet row. -/
theorem exists_skewVecMul_frechet_eq [CharZero C] [Fintype ι] [Fintype ι'] [DecidableEq ι]
    [DecidableEq ι'] :
    ∃ Q : ι → ι' → DiffOp.PseudoDiffOp (JetField C ι),
      ∀ u : JetField C ι',
        DiffOp.skewVecMul Q
            (DiffOp.integralVec ι fun j =>
              frechet (algebraMap (JetField C ι') (JetField C ι) u) j)
          = DiffOp.integralVec ι' fun i =>
              DiffOp.map (algebraMap (JetField C ι') (JetField C ι)) (frechet u i) := by
  obtain ⟨Q, hQ, -⟩ := DiffOp.exists_pseudo_inverse (frechetMatrix (C := C) (ι' := ι') (ι := ι))
    (rowIndep_frechetMatrix hδ)
  refine ⟨Q, fun u => ?_⟩
  have hchain : (fun j => frechet (algebraMap (JetField C ι') (JetField C ι) u) j)
      = DiffOp.vecMul
          (fun i => DiffOp.map (algebraMap (JetField C ι') (JetField C ι)) (frechet u i))
          frechetMatrix :=
    funext fun j => frechet_algebraMap_eq_vecMul hδ u j
  rw [hchain, ← DiffOp.pseudoVecMul_integralVec]
  exact hQ _

end Embedding

end

end JetField

end GaloisForLFunctions.HTGeometry
