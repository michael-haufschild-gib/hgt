import GaloisForLFunctions.HTGeometry.MvPowerSeriesRootFamily
import GaloisForLFunctions.HTGeometry.ParametricSpectralBranch

/-! # Simple spectra distinguished by one physical field -/
open Matrix Filter Topology
namespace GaloisForLFunctions.HTGeometry.FirstGate.Boundary
noncomputable section
variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
private abbrev Mat (I : Type) := Matrix I I ℂ

/-- Every energy and its slope in the specified field can be read separately. -/
def Resolved (H Z : Mat I) : Prop :=
  ∃ f : I → ℂ → ℂ,
    (∀ j, AnalyticAt ℂ (f j) 0 ∧ ∀ᶠ s in 𝓝 0, matrixCharpolyRelation (H+s • Z,f j s)=0) ∧
    Function.Injective (fun j => f j 0) ∧ Function.Injective (fun j => deriv (f j) 0)

theorem separable_of_branches (H Z : Mat I) (f : I→ℂ→ℂ)
    (hf : ∀ j, ∀ᶠ s in 𝓝 0, matrixCharpolyRelation (H+s • Z,f j s)=0)
    (hi : Function.Injective (fun j => f j 0)) : H.charpoly.Separable := by
  have hz (j : I) : H.charpoly.IsRoot (f j 0) := by
    simpa only [Polynomial.IsRoot,Matrix.eval_charpoly,matrixCharpolyRelation,zero_smul,add_zero] using
      (hf j).self_of_nhds
  rw [eq_prod_X_sub_C_of_monic_of_injective_family H.charpoly_monic H.charpoly_natDegree_eq_dim hi hz]
  exact Polynomial.separable_prod_X_sub_C_iff.mpr hi

theorem Resolved.reindex {H Z : Mat I} (hr : Resolved H Z) (e : I ≃ J) :
    Resolved (Matrix.reindex e e H) (Matrix.reindex e e Z) := by
  obtain ⟨f,hf,hi,hd⟩ := hr
  refine ⟨fun j => f (e.symm j),fun j => ⟨(hf _).1,?_⟩,hi.comp e.symm.injective,hd.comp e.symm.injective⟩
  filter_upwards [(hf (e.symm j)).2] with s hs
  have hm : Matrix.reindex e e H+s • Matrix.reindex e e Z=Matrix.reindex e e (H+s • Z) := rfl
  simpa only [matrixCharpolyRelation,←Matrix.eval_charpoly,hm,Matrix.charpoly_reindex] using hs

end
end GaloisForLFunctions.HTGeometry.FirstGate.Boundary
