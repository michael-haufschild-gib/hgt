import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Calculus.DSlope

/-!
# Exact transport of approximate eigenvectors through functional calculus

A real symbol continuous on a bounded self-adjoint operator's spectrum and
differentiable at the target coordinate has a continuous removable divided
difference. Functional calculus factors the transformed residual exactly through
the original residual. The resulting norm bound transports vanishing residuals
without assuming spectral membership, a spectral gap, or a bound on vector norms.
-/

open Filter Topology
namespace GaloisForLFunctions.HTGeometry
noncomputable section

private theorem continuousOn_dslope_of_differentiableAt {g : ℝ → ℝ} {S : Set ℝ} {x : ℝ}
    (hg : ContinuousOn g S) (hd : DifferentiableAt ℝ g x) :
    ContinuousOn (dslope g x) S := by
  intro y hy
  by_cases hxy : y = x
  · subst y
    exact (continuousAt_dslope_same.mpr hd).continuousWithinAt
  · exact (continuousWithinAt_dslope_of_ne hxy).mpr (hg y hy)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- An exact divided-difference factorization of the functional-calculus residual. -/
theorem cfc_residual_eq_dslope_apply
    (B : H →L[ℂ] H) (hB : IsSelfAdjoint B) (g : ℝ → ℝ) (x : ℝ)
    (hg : ContinuousOn g (spectrum ℝ B)) (hd : DifferentiableAt ℝ g x) (v : H) :
    cfc g B v - (g x : ℂ) • v =
      cfc (dslope g x) B (B v - (x : ℂ) • v) := by
  have hs := continuousOn_dslope_of_differentiableAt hg hd
  have hparam : cfc (fun y : ℝ => y - x) B = B - algebraMap ℝ (H →L[ℂ] H) x := by
    rw [cfc_sub (fun y : ℝ => y) (fun _ => x) B continuousOn_id continuousOn_const,
      cfc_id' ℝ B hB, cfc_const x B hB]
  have hop : cfc g B - algebraMap ℝ (H →L[ℂ] H) (g x) =
      cfc (dslope g x) B * (B - algebraMap ℝ (H →L[ℂ] H) x) := by
    rw [← cfc_const (g x) B hB, ← cfc_sub g (fun _ => g x) B hg continuousOn_const,
      ← hparam,
      ← cfc_mul (dslope g x) (fun y => y - x) B hs
        (continuousOn_id.sub continuousOn_const)]
    apply cfc_congr
    intro y _
    simpa only [smul_eq_mul, mul_comm] using (sub_smul_dslope g x y).symm
  have h := congrArg (fun T : H →L[ℂ] H => T v) hop
  simpa [Algebra.algebraMap_eq_smul_one, mul_apply_eq_comp] using h

/-- One fixed bounded divided-difference operator controls every transformed residual. -/
theorem norm_cfc_residual_le
    (B : H →L[ℂ] H) (hB : IsSelfAdjoint B) (g : ℝ → ℝ) (x : ℝ)
    (hg : ContinuousOn g (spectrum ℝ B)) (hd : DifferentiableAt ℝ g x) (v : H) :
    ‖cfc g B v - (g x : ℂ) • v‖ ≤
      ‖cfc (dslope g x) B‖ * ‖B v - (x : ℂ) • v‖ := by
  rw [cfc_residual_eq_dslope_apply B hB g x hg hd]
  exact (cfc (dslope g x) B).le_opNorm _

/-- Vanishing residual transports to the actual functional calculus without a spectral premise. -/
theorem cfc_residual_tendsto_zero
    {ι : Type*} {l : Filter ι}
    (B : H →L[ℂ] H) (hB : IsSelfAdjoint B) (g : ℝ → ℝ) (x : ℝ)
    (hg : ContinuousOn g (spectrum ℝ B)) (hd : DifferentiableAt ℝ g x)
    (v : ι → H) (hv : Tendsto (fun i => ‖B (v i) - (x : ℂ) • v i‖) l (𝓝 0)) :
    Tendsto (fun i => ‖cfc g B (v i) - (g x : ℂ) • v i‖) l (𝓝 0) :=
  squeeze_zero (fun _ => norm_nonneg _)
    (fun i => norm_cfc_residual_le B hB g x hg hd (v i))
    (by simpa using hv.const_mul ‖cfc (dslope g x) B‖)

end
end GaloisForLFunctions.HTGeometry
