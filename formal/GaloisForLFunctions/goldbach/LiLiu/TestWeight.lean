import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Smooth weights on the central third

The symmetric test weight is a choice of test function. Its squared mass is
strictly positive by continuity and nonvanishing.
-/

namespace GaloisForLFunctions.Goldbach.LiLiu
open MeasureTheory Set
open scoped ContDiff
noncomputable section

structure TestWeight where
  toFun : ℝ → ℝ
  smooth : ContDiff ℝ ∞ toFun
  values : ∀ x, toFun x ∈ Icc (0 : ℝ) 1
  supported : Function.support toFun ⊆ Icc (1 / 3 : ℝ) (2 / 3)
  symmetric : ∀ x, toFun (1 - x) = toFun x
  nonzero : ∃ x, toFun x ≠ 0

instance : CoeFun TestWeight (fun _ => ℝ → ℝ) := ⟨TestWeight.toFun⟩

/-- Integrating over all of ℝ gives the same mass as restricting to the unit interval. -/
def TestWeight.mass (φ : TestWeight) : ℝ := ∫ u : ℝ, φ u ^ 2

theorem TestWeight.mass_eq_integral_unit (φ : TestWeight) :
    φ.mass = ∫ u in Icc (0 : ℝ) 1, φ u ^ 2 := by
  unfold TestWeight.mass
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro u hu
  have hz : φ u = 0 := Function.notMem_support.mp fun h => hu
    ⟨by linarith only [(φ.supported h).1], by linarith only [(φ.supported h).2]⟩
  simp [hz]

theorem TestWeight.mass_pos (φ : TestWeight) : 0 < φ.mass := by
  unfold TestWeight.mass
  obtain ⟨x, hx⟩ := φ.nonzero
  apply (φ.smooth.continuous.pow 2).integral_pos_of_hasCompactSupport_nonneg_nonzero
    (x := x) _ (fun u => sq_nonneg _) (pow_ne_zero _ hx)
  apply HasCompactSupport.intro (K := Icc (1 / 3 : ℝ) (2 / 3)) isCompact_Icc
  intro u hu
  have hz : φ u = 0 := Function.notMem_support.mp fun h => hu (φ.supported h)
  simp [hz]

/-- A concrete admissible bump, centered at one half with outer radius one sixth. -/
def centralBump : TestWeight := by
  let b : ContDiffBump (1 / 2 : ℝ) := ⟨1 / 12, 1 / 6, by norm_num, by norm_num⟩
  refine ⟨b, b.contDiff, fun _ => ⟨b.nonneg, b.le_one⟩, ?_, ?_, ?_⟩
  · rw [b.support_eq]
    intro u hu
    change dist u (1 / 2) < 1 / 6 at hu
    rw [Real.dist_eq, abs_lt] at hu
    exact ⟨by linarith only [hu.1], by linarith only [hu.2]⟩
  · intro u
    have h := b.sub (u - 1 / 2)
    rwa [show 1 / 2 - (u - 1 / 2) = 1 - u by ring,
      show 1 / 2 + (u - 1 / 2) = u by ring] at h
  · exact ⟨1 / 2, (b.pos_of_mem_ball (Metric.mem_ball_self b.rOut_pos)).ne'⟩

#print axioms TestWeight.mass_pos
#print axioms centralBump

end
end GaloisForLFunctions.Goldbach.LiLiu
