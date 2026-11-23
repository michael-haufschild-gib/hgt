import GaloisForLFunctions.HTGeometry.KroneckerIdentityIsometry
import GaloisForLFunctions.HTGeometry.TensorConcatenation
import Mathlib.LinearAlgebra.Matrix.Rank

/-! # Spectator dimension as a lower bound on approximation rank -/
open Matrix
open scoped Matrix.Norms.L2Operator Kronecker
namespace GaloisForLFunctions.HTGeometry.SpectralApproximation
noncomputable section

private def tensorRight {d n : Type*} (x : d → ℂ) : (n → ℂ) →ₗ[ℂ] (d × n → ℂ) where
  toFun y p := x p.1 * y p.2
  map_add' y z := funext fun p => mul_add (x p.1) (y p.2) (z p.2)
  map_smul' a y := funext fun p => mul_left_comm (x p.1) a (y p.2)

private theorem tensorRight_norm {d n : Type*} [Fintype d] [Fintype n]
    (x : EuclideanSpace ℂ d) (y : EuclideanSpace ℂ n) :
    ‖WithLp.toLp 2 (tensorRight x.ofLp y.ofLp)‖ = ‖x‖ * ‖y‖ := norm_tensorVec x y

/-- All spectator copies of one nearly maximizing input have the same
expansion. Any approximant closer than the active operator norm must be
injective on their span, whose dimension is the number of spectators. -/
theorem spectator_rank {d n : Type*} [Fintype d] [Fintype n] [DecidableEq d] [DecidableEq n]
    (A : Matrix d d ℂ) (B : Matrix (d × n) (d × n) ℂ)
    (h : ‖A ⊗ₖ (1 : Matrix n n ℂ) - B‖ < ‖A‖) : Fintype.card n ≤ B.rank := by
  let K := A ⊗ₖ (1 : Matrix n n ℂ)
  let T := Matrix.toEuclideanCLM (𝕜 := ℂ) A
  obtain ⟨x,hx⟩ : ∃ x : EuclideanSpace ℂ d, ‖K-B‖ * ‖x‖ < ‖T x‖ := by
    by_contra! hall
    exact h.not_ge ((Matrix.l2_opNorm_toEuclideanCLM A).symm.le.trans (T.opNorm_le_bound (norm_nonneg _) hall))
  let F := B.mulVecLin.comp (tensorRight x.ofLp)
  have hinj : Function.Injective F := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro y hy
    by_contra hne
    let v : EuclideanSpace ℂ n := WithLp.toLp 2 y
    let w : EuclideanSpace ℂ (d × n) := WithLp.toLp 2 (tensorRight x.ofLp y)
    have hv : 0 < ‖v‖ := norm_pos_iff.mpr fun hv => hne (congrArg WithLp.ofLp hv)
    have hB : B *ᵥ w.ofLp = 0 := hy
    have hK : K *ᵥ w.ofLp = tensorRight (T x).ofLp y := by
      funext ⟨i,j⟩
      rw [kronecker_one_mulVec]
      change (∑ a, A i a * (x a * y j)) = (∑ a, A i a * x a) * y j
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun _ _ => (mul_assoc ..).symm
    have he : Matrix.toEuclideanCLM (𝕜 := ℂ) (K-B) w =
        WithLp.toLp 2 (tensorRight (T x).ofLp y) := by
      apply (EuclideanSpace.equiv _ ℂ).injective
      change (K-B) *ᵥ w.ofLp = tensorRight (T x).ofLp y
      rw [Matrix.sub_mulVec,hB,sub_zero,hK]
    have hb := (Matrix.toEuclideanCLM (𝕜 := ℂ) (K-B)).le_opNorm w
    rw [he,Matrix.l2_opNorm_toEuclideanCLM] at hb
    change ‖WithLp.toLp 2 (tensorRight (T x).ofLp v.ofLp)‖ ≤
      ‖K-B‖ * ‖WithLp.toLp 2 (tensorRight x.ofLp v.ofLp)‖ at hb
    rw [tensorRight_norm,tensorRight_norm,←mul_assoc] at hb
    exact (mul_lt_mul_of_pos_right hx hv).not_ge hb
  have hdim := Submodule.finrank_mono (LinearMap.range_comp_le_range (tensorRight x.ofLp) B.mulVecLin)
  change Module.finrank ℂ (LinearMap.range F) ≤ B.rank at hdim
  simpa only [LinearMap.finrank_range_of_inj hinj,Module.finrank_fintype_fun_eq_card] using hdim

#print axioms spectator_rank
end
end GaloisForLFunctions.HTGeometry.SpectralApproximation
