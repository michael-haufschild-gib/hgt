import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.LocalTangents.Multiplicity.ResponseForm
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.LocalTangents.Multiplicity.MatchedSlopes

/-! # Matching the full first variation on the maximal singular space -/

open Matrix Module Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.LocalTangents.Multiplicity
open AccuracyScales.TenthPlateau
noncomputable section
private abbrev Bits (N : ℕ) := Fin N → Bool
private abbrev Reg (N : ℕ) := Matrix (Bits N) (Bits N) ℂ

/-- Complex span of the unit input states attaining the operator norm. -/
def activeSpan {N : ℕ} (X : Reg N) : Submodule ℂ (Bits N → ℂ) :=
  Submodule.span ℂ (WithLp.ofLp '' maxRightSingularSphere X)

/-- Complex dimension of the span of all maximizing input states. -/
def activeRank {N : ℕ} (X : Reg N) : ℕ := finrank ℂ (activeSpan X)

private theorem active_columns {N : ℕ} (X : Reg N) :
    ∃ E : Matrix (Bits N) (Fin (activeRank X)) ℂ, ∀ ψ∈maxRightSingularSphere X,
      ∃ c, E *ᵥ c=ψ.ofLp := by
  let b : Basis (Fin (activeRank X)) ℂ (activeSpan X) := Module.finBasis ℂ (activeSpan X)
  let E : Matrix (Bits N) (Fin (activeRank X)) ℂ := fun j i => (b i).val j
  refine ⟨E,fun ψ hψ => ?_⟩
  let z : activeSpan X := ⟨ψ.ofLp,Submodule.subset_span ⟨ψ,hψ,rfl⟩⟩
  refine ⟨fun i => b.repr z i,?_⟩
  funext j
  have h := congrArg (fun w : activeSpan X => w.val j) (b.sum_repr z)
  change (∑ i : Fin (activeRank X), (b i).val j * b.repr z i)=z.val j
  rw [Finset.sum_congr rfl (fun i _ => mul_comm ((b i).val j) (b.repr z i))]
  simp only [Submodule.coe_sum,Finset.sum_apply,SetLike.val_smul,Pi.smul_apply,smul_eq_mul] at h
  exact h

/-- The number of Pauli rotations needed to match all norming-state
variations is controlled by the active space of the actual residual. -/
theorem sparse_active_readings {N : ℕ} (X Q : Reg N) (B : selfAdjoint (Reg N)) :
    ∃ d ≤ (activeRank X)^2, ∃ (w : Fin d → Fin N → Option (Fin 3)) (a : Fin d → ℝ),
      let C := ∑ i, a i • finitePauliSelfAdjoint (w i)
      ∀ ψ∈maxRightSingularSphere X,
        (inner ℂ (matAct X ψ) (matAct ((Complex.I • C.val)*Q) ψ)).re=
        (inner ℂ (matAct X ψ) (matAct ((Complex.I • B.val)*Q) ψ)).re := by
  obtain ⟨E,hE⟩ := active_columns X
  obtain ⟨d,hd,w,a,hread⟩ := sparse_cross_readings (X*E) (Q*E) B
  refine ⟨d,by simpa only [Fintype.card_fin] using hd,w,a,?_⟩
  intro C ψ hψ
  obtain ⟨c,hc⟩ := hE ψ hψ
  have hh := hread c
  simp only [←mulVec_mulVec,hc] at hh
  rw [EuclideanSpace.inner_eq_star_dotProduct,EuclideanSpace.inner_eq_star_dotProduct]
  change (((Complex.I • C.val)*Q)*ᵥψ.ofLp ⬝ᵥ star (X *ᵥ ψ.ofLp)).re=
    (((Complex.I • B.val)*Q)*ᵥψ.ofLp ⬝ᵥ star (X *ᵥ ψ.ofLp)).re
  simpa only [←mulVec_mulVec,dotProduct_comm] using hh

#print axioms sparse_active_readings
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.LocalTangents.Multiplicity
