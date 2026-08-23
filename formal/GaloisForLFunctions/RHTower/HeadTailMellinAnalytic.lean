import GaloisForLFunctions.RHTower.MellinHeadHardyEquiv
import GaloisForLFunctions.RHTower.MellinHardyBridge

/-!
# Analyticity of `headTailMellin`, and filling a single puncture

`headTailMellin a c g` is the sum of the explicit head `c·a^{1-s}/(1-s)` and the tail Laplace
transform of `MellinHardyBridge`; both are holomorphic on `Re s > 1/2` away from `s = 1`.  Together
with the elementary "two continuous functions agreeing off one point agree at it" this is what lets
a description valid off a removable singularity be extended across it.

## Main results

* `differentiableAt_headTailMellin`
* `eq_of_eventuallyEq_punctured`
-/

namespace RHTower

open MeasureTheory Set Complex Filter Topology

open GaloisForLFunctions.HTGeometry

noncomputable section

theorem continuous_const_cpow_ofReal {a : ℝ} (ha : 0 < a) :
    Continuous fun w : ℂ => ((a : ℝ) : ℂ) ^ w := by
  have hac : ((a : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ha
  have h : (fun w : ℂ => ((a : ℝ) : ℂ) ^ w)
      = fun w : ℂ => Complex.exp (Complex.log ((a : ℝ) : ℂ) * w) := by
    funext w
    rw [Complex.cpow_def_of_ne_zero hac]
  rw [h]
  fun_prop

theorem differentiable_const_cpow_ofReal {a : ℝ} (ha : 0 < a) (u : ℂ → ℂ)
    (hu : Differentiable ℂ u) : Differentiable ℂ fun w : ℂ => ((a : ℝ) : ℂ) ^ (u w) := by
  have hac : ((a : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ha
  have h : (fun w : ℂ => ((a : ℝ) : ℂ) ^ (u w))
      = fun w : ℂ => Complex.exp (Complex.log ((a : ℝ) : ℂ) * u w) := by
    funext w
    rw [Complex.cpow_def_of_ne_zero hac]
  rw [h]
  exact Complex.differentiable_exp.comp ((differentiable_const _).mul hu)

/-- **`headTailMellin` is holomorphic on `Re s > 1/2` away from `s = 1`.** -/
theorem differentiableAt_headTailMellin {a : ℝ} (ha : 0 < a) (c : ℂ) {g : ℝ → ℂ}
    (hg : MemLp g 2 (volume.restrict (Ioi a))) {s : ℂ} (hs : 1 / 2 < s.re) (hs1 : s ≠ 1) :
    DifferentiableAt ℂ (headTailMellin a c g) s := by
  have hφ : MemLp (logChart a g) 2 (volume.restrict (Ioi (0 : ℝ))) := memLp_two_logChart ha hg
  have hopen : IsOpen {z : ℂ | 1 / 2 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hmem : s ∈ {z : ℂ | 1 / 2 < z.re} := hs
  -- the model function
  set M : ℂ → ℂ := fun z : ℂ =>
    c * ((a : ℝ) : ℂ) ^ ((1 : ℂ) - z) / (1 - z)
      + ((a : ℝ) : ℂ) ^ ((1 : ℂ) / 2 - z) * laplaceRay (logChart a g) (z - 1 / 2) with hM
  have hMeq : headTailMellin a c g =ᶠ[𝓝 s] M := by
    filter_upwards [hopen.mem_nhds hmem] with z hz
    rw [hM]
    simp only
    rw [headTailMellin, mellinTail_eq_laplaceRay ha g z]
  refine DifferentiableAt.congr_of_eventuallyEq ?_ hMeq
  refine DifferentiableAt.add ?_ ?_
  · have hnum : DifferentiableAt ℂ (fun z : ℂ => c * ((a : ℝ) : ℂ) ^ ((1 : ℂ) - z)) s :=
      (differentiable_const c).mul
        (differentiable_const_cpow_ofReal ha (fun z : ℂ => (1 : ℂ) - z)
          ((differentiable_const _).sub differentiable_id)) s
    have hden : DifferentiableAt ℂ (fun z : ℂ => (1 : ℂ) - z) s :=
      ((differentiable_const _).sub differentiable_id) s
    have hne : (1 : ℂ) - s ≠ 0 := sub_ne_zero.2 (Ne.symm hs1)
    exact hnum.div hden hne
  · have h1 : DifferentiableAt ℂ (fun z : ℂ => ((a : ℝ) : ℂ) ^ ((1 : ℂ) / 2 - z)) s :=
      (differentiable_const_cpow_ofReal ha (fun z : ℂ => (1 : ℂ) / 2 - z)
        ((differentiable_const _).sub differentiable_id)) s
    have hhalf : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
    have hlap : DifferentiableAt ℂ (laplaceRay (logChart a g)) (s - 1 / 2) := by
      have hd := (differentiableOn_laplaceRay hφ)
      have hmem' : (s - 1 / 2) ∈ {w : ℂ | 0 < w.re} := by
        simp only [Set.mem_setOf_eq, Complex.sub_re]
        have h2 : ((1 : ℂ) / 2).re = 1 / 2 := by norm_num
        rw [h2]
        linarith
      exact (hd.differentiableAt (hhalf.mem_nhds hmem'))
    have hshift : DifferentiableAt ℂ (fun z : ℂ => z - (1 : ℂ) / 2) s :=
      (differentiable_id.sub (differentiable_const _)) s
    have hcomp : DifferentiableAt ℂ
        (fun z : ℂ => laplaceRay (logChart a g) (z - (1 : ℂ) / 2)) s := by
      have hc := DifferentiableAt.comp (𝕜 := ℂ)
        (g := laplaceRay (logChart a g)) (f := fun z : ℂ => z - (1 : ℂ) / 2) s hlap hshift
      exact hc
    exact h1.mul hcomp

/-- Two functions continuous at a point and agreeing off it agree at it. -/
theorem eq_of_eventuallyEq_punctured {F H : ℂ → ℂ} {ρ : ℂ}
    (hF : ContinuousAt F ρ) (hH : ContinuousAt H ρ)
    (h : ∀ᶠ z in 𝓝[≠] ρ, F z = H z) : F ρ = H ρ := by
  have h1 : Tendsto F (𝓝[≠] ρ) (𝓝 (F ρ)) := hF.continuousWithinAt.tendsto
  have h2 : Tendsto H (𝓝[≠] ρ) (𝓝 (H ρ)) := hH.continuousWithinAt.tendsto
  have h3 : Tendsto F (𝓝[≠] ρ) (𝓝 (H ρ)) := h2.congr' (Filter.EventuallyEq.symm h)
  exact tendsto_nhds_unique h1 h3

end

end RHTower
