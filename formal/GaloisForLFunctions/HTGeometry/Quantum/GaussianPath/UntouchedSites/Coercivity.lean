import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # Stability of a scalar joint commutant in operator norm -/
open Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.UntouchedSites
noncomputable section

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
private abbrev Mat (I : Type*) := Matrix I I ℂ

/-- Commuting with K is a linear test on the unknown matrix. -/
def bracket (K : Mat I) : Mat I →ₗ[ℂ] Mat I :=
  LinearMap.mulLeft ℂ K - LinearMap.mulRight ℂ K

private def tests (r : I) (H : Mat I) (P : J → Mat I) :
    Mat I →ₗ[ℂ] ℂ × Mat I × (J → Mat I) :=
  LinearMap.prod (Matrix.entryLinearMap ℂ ℂ r r)
    ((bracket H).prod (LinearMap.pi fun j => bracket (P j)))

/-- A joint commutant consists of scalars exactly when the commutator
defects control distance to a scalar linearly, uniformly over all matrices. -/
theorem scalar_commutant_iff_estimate (r : I) (H : Mat I) (P : J → Mat I) :
    (∀ X : Mat I, H*X = X*H → (∀ j, P j*X = X*P j) → X = X r r • (1 : Mat I)) ↔
    ∃ K : ℝ, 0 < K ∧ ∀ X : Mat I, ‖X-X r r • (1 : Mat I)‖ ≤
      K*max ‖H*X-X*H‖ ‖fun j => P j*X-X*P j‖ := by
  constructor
  · intro hs
    let F := tests r H P
    have hk : LinearMap.ker F = ⊥ := by
      rw [LinearMap.ker_eq_bot']
      intro X hX
      have h0 : X r r = 0 := congrArg Prod.fst hX
      have hH : H*X-X*H = 0 := congrArg (fun z : ℂ × Mat I × (J → Mat I) => z.2.1) hX
      have hP (j : J) : P j*X-X*P j = 0 := congrArg (fun z : ℂ × Mat I × (J → Mat I) => z.2.2 j) hX
      rw [hs X (sub_eq_zero.mp hH) (fun j => sub_eq_zero.mp (hP j)),h0,zero_smul]
    obtain ⟨K,hK,hbound⟩ := F.exists_antilipschitzWith hk
    refine ⟨K,by exact_mod_cast hK,?_⟩
    intro X
    let Y := X-X r r • (1 : Mat I)
    have htest : F Y = (0,H*X-X*H,fun j => P j*X-X*P j) := by
      have he (M : Mat I) : bracket M Y = M*X-X*M := by
        change M*(X-X r r • 1)-(X-X r r • 1)*M = _
        rw [mul_sub,sub_mul,Matrix.smul_mul,Matrix.mul_smul,one_mul,mul_one]
        abel
      refine Prod.ext ?_ (Prod.ext (he H) (funext fun j => he (P j)))
      simp [F,tests,Y]
    have hh := hbound.le_mul_dist Y 0
    rw [map_zero,dist_zero_right,dist_zero_right,htest] at hh
    simpa only [Prod.norm_def,norm_zero,max_eq_right (le_max_of_le_left (norm_nonneg _))] using hh
  · rintro ⟨K,_,h⟩ X hH hP
    have hz : (fun j => P j*X-X*P j) = 0 := funext fun j => sub_eq_zero.mpr (hP j)
    have hh := h X
    rw [hz,hH,sub_self,norm_zero,norm_zero,max_self,mul_zero,norm_le_zero_iff] at hh
    exact sub_eq_zero.mp hh

#print axioms scalar_commutant_iff_estimate
end
end GaloisForLFunctions.HTGeometry.UntouchedSites
