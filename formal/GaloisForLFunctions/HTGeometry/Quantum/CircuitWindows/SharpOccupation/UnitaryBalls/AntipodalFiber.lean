import GaloisForLFunctions.HTGeometry.SelfAdjointPropagator
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # An antipodal eigenvector on every coordinate phase circle -/
open Matrix Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SharpOccupation.UnitaryBalls
noncomputable section

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The unitary with the given diagonal phases in the chosen basis. -/
def packet (x : UnitAddTorus I) : Matrix I I ℂ := diagonal fun j => ((x j).toCircle:ℂ)

private theorem unitary_norm_sum {C : Matrix I I ℂ} (hC : C∈unitary (Matrix I I ℂ)) (v : I→ℂ) :
    ∑ j, ‖(C *ᵥ v) j‖^2 = ∑ j, ‖v j‖^2 := by
  let Φ := Matrix.toEuclideanCLM (n:=I) (𝕜:=ℂ)
  have h := congrArg (fun a : ℝ => a^2) (norm_apply_of_mem_unitary (Unitary.map_mem Φ hC) (WithLp.toLp 2 v))
  simpa only [Φ,Matrix.toEuclideanCLM_toLp,EuclideanSpace.norm_sq_eq] using h

/-- All but one row of C v = -diag(z) v leave a nonzero solution.
Unitarity equates the two remaining coordinate norms, so varying the
last phase solves that row as well. -/
theorem antipodal_fiber {C : Matrix I I ℂ} (hC : C∈unitary (Matrix I I ℂ))
    (i : I) (x : UnitAddTorus I) :
    ∃ u : UnitAddCircle, ∃ v : I→ℂ, v≠0 ∧ (C+packet (x+Pi.single i u)) *ᵥ v=0 := by
  classical
  let L := ((C+packet x).submatrix ((↑) : {j : I // j≠i} → I) id).mulVecLin
  have hd : Module.finrank ℂ ({j : I // j≠i} → ℂ) < Module.finrank ℂ (I→ℂ) := by
    simpa only [Module.finrank_fintype_fun_eq_card] using
      Fintype.card_subtype_lt (x:=i) (p:=fun j : I => j≠i) (not_not.mpr rfl)
  obtain ⟨v,hv,hv₀⟩ := L.ker.ne_bot_iff.mp (LinearMap.ker_ne_bot_of_finrank_lt hd)
  have ho (j : I) (hj : j≠i) : (C *ᵥ v) j = -(((x j).toCircle:ℂ)*v j) := by
    have hh := congrFun (LinearMap.mem_ker.mp hv) ⟨j,hj⟩
    change ((C+packet x) *ᵥ v) j = 0 at hh
    rw [add_mulVec,Pi.add_apply,packet,mulVec_diagonal] at hh
    exact eq_neg_of_add_eq_zero_left hh
  have hn (j : I) (hj : j≠i) : ‖(C *ᵥ v) j‖=‖v j‖ := by
    rw [ho j hj,norm_neg,norm_mul,Circle.norm_coe,one_mul]
  have hsum := unitary_norm_sum hC v
  rw [←Finset.sum_erase_add _ _ (Finset.mem_univ i),←Finset.sum_erase_add _ (fun j => ‖v j‖^2) (Finset.mem_univ i)] at hsum
  have hoff : ∑ j ∈ Finset.univ.erase i, ‖(C *ᵥ v) j‖^2 = ∑ j ∈ Finset.univ.erase i, ‖v j‖^2 :=
    Finset.sum_congr rfl fun j hj => congrArg (fun q : ℝ => q^2) (hn j (Finset.mem_erase.mp hj).1)
  have hm : ‖(C *ᵥ v) i‖=‖v i‖ := by
    rw [hoff] at hsum
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (add_left_cancel hsum)
  have hp : ∃ a : UnitAddCircle, (C *ᵥ v) i + (a.toCircle:ℂ)*v i=0 := by
    by_cases hz : v i=0
    · have hu : (C *ᵥ v) i=0 := norm_eq_zero.mp (by simpa only [hz,norm_zero] using hm)
      exact ⟨0,by rw [hz,hu,mul_zero,add_zero]⟩
    · let c := -(C *ᵥ v) i/v i
      have hc : ‖c‖=1 := by
        change ‖-(C *ᵥ v) i/v i‖=1
        rw [norm_div,norm_neg,hm,div_self (norm_ne_zero_iff.mpr hz)]
      let z : Circle := ⟨c,mem_sphere_zero_iff_norm.mpr hc⟩
      let e := AddCircle.homeomorphCircle (T:=1) one_ne_zero
      obtain ⟨a,ha⟩ := e.surjective z
      change AddCircle.homeomorphCircle _ a=z at ha
      rw [AddCircle.homeomorphCircle_apply] at ha
      refine ⟨a,?_⟩
      rw [ha]
      change (C *ᵥ v) i + (-(C *ᵥ v) i/v i)*v i=0
      rw [div_mul_cancel₀ _ hz,add_neg_cancel]
  obtain ⟨a,ha⟩ := hp
  refine ⟨a-x i,v,hv₀,?_⟩
  funext j
  rw [add_mulVec,Pi.add_apply,packet,mulVec_diagonal,Pi.add_apply]
  by_cases hj : j=i
  · subst j
    simpa only [Pi.single_eq_same,add_sub_cancel,Pi.zero_apply] using ha
  · simp only [Pi.single_eq_of_ne hj,add_zero,ho j hj,neg_add_cancel,Pi.zero_apply]

#print axioms antipodal_fiber
end
end GaloisForLFunctions.HTGeometry.SharpOccupation.UnitaryBalls
