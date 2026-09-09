import GaloisForLFunctions.HTGeometry.ConservativeDissipativeAdaptive
import GaloisForLFunctions.HTGeometry.ConservativeDissipativeConstraints

set_option autoImplicit false

/-!
# Adaptive midpoint enforcement of linear constraints

The Schaffer–Exl energy split (arXiv:2609.04530), applied to the existing
constraint-defect operator, gives an exact discrete energy budget. For steps
`1 + u n ^ 2`, midpoint constraint energy and defect norm tend to zero under
arbitrary time- and state-dependent conservative mixing. Completeness and
orthogonal projections follow from finite dimension. These are midpoint
consistency statements and do not assert convergence of the trajectory.
-/
open scoped InnerProductSpace NNReal BigOperators
namespace GaloisForLFunctions.HTGeometry.SchafferExl
noncomputable section
variable {𝕜 E ι : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] [Fintype ι]

local instance : CompleteSpace E := FiniteDimensional.complete 𝕜 E

/-- Positive adaptive step sizes with a constructed uniform lower bound. -/
def constraintStepSize (u : ℕ → ℝ) (n : ℕ) : ℝ≥0 := ⟨1 + u n ^ 2, by positivity⟩

/-- Constraint-driven discrete trajectory with arbitrary changing conservative mixing. -/
def constraintCayleyOrbit (U : ι → Submodule 𝕜 E) (A : ℕ → E → E →L[𝕜] E)
    (u : ℕ → ℝ) (x : E) : ℕ → E :=
  adaptiveCayleyOrbit A (fun _ _ => constraintDefect U) (constraintStepSize u) x

/-- The implicit midpoint on which the physical constraint damping acts. -/
def constraintCayleyMidpoint (U : ι → Submodule 𝕜 E) (A : ℕ → E → E →L[𝕜] E)
    (u : ℕ → ℝ) (x : E) (n : ℕ) : E :=
  let y := constraintCayleyOrbit U A u x n
  implicitStep (A n y) (constraintDefect U) (constraintStepSize u n) y

/-- Physical step loss is exactly the existing constraint energy at its midpoint. -/
theorem constraintCayley_loss_eq (U : ι → Submodule 𝕜 E) (A : ℕ → E → E →L[𝕜] E)
    (u : ℕ → ℝ) (x : E) (n : ℕ) :
    adaptiveCayleyLoss A (fun _ _ => constraintDefect U) (constraintStepSize u) x n =
      4 * (1 + u n ^ 2) * constraintEnergy U (constraintCayleyMidpoint U A u x n) := by
  change 4 * (1 + u n ^ 2) * ‖constraintDefect U (constraintCayleyMidpoint U A u x n)‖ ^ 2 = _
  rw [norm_sq_constraintDefect]

/-- Total weighted constraint error is accounted for by the exact finite energy drop. -/
theorem constraintCayley_energy_balance (U : ι → Submodule 𝕜 E) (A : ℕ → E → E →L[𝕜] E)
    (u : ℕ → ℝ) (x : E) (n : ℕ) :
    ‖constraintCayleyOrbit U A u x n‖ ^ 2 +
      ∑ k ∈ Finset.range n, 4 * (1 + u k ^ 2) * constraintEnergy U (constraintCayleyMidpoint U A u x k) =
        ‖x‖ ^ 2 := by
  simpa only [constraintCayley_loss_eq, constraintCayleyOrbit] using
    adaptiveCayley_energy_balance A (fun _ _ => constraintDefect U) (constraintStepSize u) x n

/-- Uniformly positive steps force the midpoint constraint energy to vanish asymptotically. -/
theorem constraintCayleyMidpoint_energy_tendsto_zero (U : ι → Submodule 𝕜 E)
    (A : ℕ → E → E →L[𝕜] E) (u : ℕ → ℝ) (x : E) :
    Filter.Tendsto (fun n => constraintEnergy U (constraintCayleyMidpoint U A u x n))
      Filter.atTop (nhds 0) := by
  have h := adaptiveCayleyLoss_tendsto_zero A (fun _ _ => constraintDefect U) (constraintStepSize u) x
  apply squeeze_zero (fun n => constraintEnergy_nonneg U _)
    (fun n => show constraintEnergy U (constraintCayleyMidpoint U A u x n) ≤
      adaptiveCayleyLoss A (fun _ _ => constraintDefect U) (constraintStepSize u) x n from by
      rw [constraintCayley_loss_eq]
      have hn := constraintEnergy_nonneg U (constraintCayleyMidpoint U A u x n)
      nlinarith [sq_nonneg (u n)]) h

/-- The combined constraint-defect norm vanishes at the actual discrete midpoints. -/
theorem constraintCayleyMidpoint_defect_tendsto_zero (U : ι → Submodule 𝕜 E)
    (A : ℕ → E → E →L[𝕜] E) (u : ℕ → ℝ) (x : E) :
    Filter.Tendsto (fun n => ‖constraintDefect U (constraintCayleyMidpoint U A u x n)‖)
      Filter.atTop (nhds 0) := by
  have h := (constraintCayleyMidpoint_energy_tendsto_zero U A u x).sqrt
  simpa only [← norm_sq_constraintDefect, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _),
    Real.sqrt_zero] using h

end
end GaloisForLFunctions.HTGeometry.SchafferExl
