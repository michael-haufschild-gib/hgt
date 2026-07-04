/-
# Böttcher tower — Weyl's lemma (distributional-harmonic ⟹ harmonic)

Discharges `WeylOnBall (greenFunctionDyn c)` (Brolin/RieszSupport), the elliptic-
regularity input of the GAP-A support theorem: a continuous function that is weakly
harmonic on a ball (annihilates `∫ G·Δφ` for every `C²` bump supported in the ball)
is `HarmonicOnNhd` there.

Route: mollify `G_δ = G ⋆ η_δ`; `Δ G_δ = G ⋆ Δη_δ` and the reflection identity turn
`Δ G_δ(x)` into `∫ G · Δ(η_δ(x−·))`, which vanishes by weak-harmonicity, so `G_δ`
is harmonic; `G_δ → G` (approximate identity) and Poisson reproduction pass
harmonicity to `G`.

## Convolution–Laplacian core

`laplacian_convolution`: `Δ (G ⋆ ρ) = G ⋆ (Δρ)` for `ρ ∈ C³` compact support, `G`
locally integrable — obtained by moving each directional second derivative onto the
smooth factor (`hasFDerivAt_convolution_right`, twice) and summing.
-/
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import GaloisForLFunctions.Bottcher.Brolin.RieszSupport
import GaloisForLFunctions.Bottcher.PoissonHarmonic
import GaloisForLFunctions.Bottcher.PoissonBoundary

open MeasureTheory Complex Metric Laplacian InnerProductSpace
open scoped Laplacian Real Topology

namespace Bottcher

noncomputable section
noncomputable def dderiv (f : ℂ → ℝ) (u x : ℂ) : ℝ := fderiv ℝ (fun y => fderiv ℝ f y u) x u

theorem laplacian_eq_dderiv (f : ℂ → ℝ) (hf : ContDiff ℝ 2 f) (x : ℂ) :
    Δ f x = dderiv f 1 x + dderiv f I x := by
  have key : ∀ u : ℂ, iteratedFDeriv ℝ 2 f x ![u, u] = dderiv f u x := by
    intro u
    rw [iteratedFDeriv_two_apply]
    show (fderiv ℝ (fderiv ℝ f) x u) u = fderiv ℝ (fun y => fderiv ℝ f y u) x u
    have hdiff : DifferentiableAt ℝ (fderiv ℝ f) x :=
      (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) |>.differentiableAt
    have hcomp : fderiv ℝ (fun y => (fderiv ℝ f y) u) x
        = (ContinuousLinearMap.apply ℝ ℝ u).comp (fderiv ℝ (fderiv ℝ f) x) := by
      rw [show (fun y => (fderiv ℝ f y) u) = (ContinuousLinearMap.apply ℝ ℝ u) ∘ (fderiv ℝ f) from rfl]
      rw [fderiv_comp x (ContinuousLinearMap.apply ℝ ℝ u).differentiableAt hdiff,
        ContinuousLinearMap.fderiv]
    rw [hcomp]; rfl
  rw [laplacian_eq_iteratedFDeriv_complexPlane f]
  show iteratedFDeriv ℝ 2 f x ![1,1] + iteratedFDeriv ℝ 2 f x ![I,I] = dderiv f 1 x + dderiv f I x
  rw [key 1, key I]

theorem hasCompactSupport_fderiv_apply {ρ : ℂ → ℝ} (hρc : HasCompactSupport ρ)
    (u : ℂ) : HasCompactSupport (fun z => fderiv ℝ ρ z u) := by
  apply HasCompactSupport.of_support_subset_isCompact (hρc.fderiv ℝ)
  intro z hz
  rw [Function.mem_support] at hz
  refine subset_tsupport (fderiv ℝ ρ) ?_
  rw [Function.mem_support]
  intro hzero
  exact hz (by rw [hzero]; rfl)

theorem conv_fderiv_apply (G : ℂ → ℝ) (hG : LocallyIntegrable G)
    (ρ : ℂ → ℝ) (hρc : HasCompactSupport ρ) (hρ : ContDiff ℝ 2 ρ) (u x : ℂ) :
    fderiv ℝ (convolution G ρ (ContinuousLinearMap.lsmul ℝ ℝ) volume) x u
      = convolution G (fun y => fderiv ℝ ρ y u) (ContinuousLinearMap.lsmul ℝ ℝ) volume x := by
  have hfd := (hρc.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ) hG
    (hρ.of_le (by norm_num)) x).fderiv
  rw [hfd]
  have hcont : Continuous (fun y => fderiv ℝ ρ y) := hρ.continuous_fderiv (by norm_num)
  have hcs : HasCompactSupport (fun y => fderiv ℝ ρ y) := hρc.fderiv ℝ
  rw [convolution_precompR_apply (ContinuousLinearMap.lsmul ℝ ℝ) hG hcs hcont]

theorem contDiff_fderiv_apply (ρ : ℂ → ℝ) (hρ : ContDiff ℝ 3 ρ) (u : ℂ) :
    ContDiff ℝ 2 (fun y => fderiv ℝ ρ y u) := by
  have h1 : ContDiff ℝ 2 (fun y => fderiv ℝ ρ y) := hρ.fderiv_right (m := 2) (by norm_num)
  exact (ContinuousLinearMap.apply ℝ ℝ u).contDiff.comp h1

theorem dderiv_convolution (G : ℂ → ℝ) (hG : LocallyIntegrable G)
    (ρ : ℂ → ℝ) (hρc : HasCompactSupport ρ) (hρ : ContDiff ℝ 3 ρ) (u x : ℂ) :
    dderiv (convolution G ρ (ContinuousLinearMap.lsmul ℝ ℝ) volume) u x
      = convolution G (fun y => dderiv ρ u y) (ContinuousLinearMap.lsmul ℝ ℝ) volume x := by
  have hfun : (fun y => fderiv ℝ (convolution G ρ (ContinuousLinearMap.lsmul ℝ ℝ) volume) y u)
      = convolution G (fun z => fderiv ℝ ρ z u) (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
    funext y; exact conv_fderiv_apply G hG ρ hρc (hρ.of_le (by norm_num)) u y
  rw [dderiv, hfun,
    conv_fderiv_apply G hG (fun z => fderiv ℝ ρ z u)
      (hasCompactSupport_fderiv_apply hρc u) (contDiff_fderiv_apply ρ hρ u) u x]
  rfl

theorem continuous_dderiv (ρ : ℂ → ℝ) (hρ : ContDiff ℝ 3 ρ) (u : ℂ) :
    Continuous (dderiv ρ u) := by
  have h2 : ContDiff ℝ 2 (fun z => fderiv ℝ ρ z u) := contDiff_fderiv_apply ρ hρ u
  have hc : Continuous (fun x => fderiv ℝ (fun z => fderiv ℝ ρ z u) x) := h2.continuous_fderiv (by norm_num)
  exact (ContinuousLinearMap.apply ℝ ℝ u).continuous.comp hc

theorem hasCompactSupport_dderiv (ρ : ℂ → ℝ) (hρc : HasCompactSupport ρ) (u : ℂ) :
    HasCompactSupport (dderiv ρ u) :=
  hasCompactSupport_fderiv_apply (hasCompactSupport_fderiv_apply hρc u) u

theorem laplacian_convolution (G : ℂ → ℝ) (hG : LocallyIntegrable G)
    (ρ : ℂ → ℝ) (hρc : HasCompactSupport ρ) (hρ : ContDiff ℝ 3 ρ) (x : ℂ) :
    Δ (convolution G ρ (ContinuousLinearMap.lsmul ℝ ℝ) volume) x
      = convolution G (Δ ρ) (ContinuousLinearMap.lsmul ℝ ℝ) volume x := by
  have hC2 : ContDiff ℝ 2 (convolution G ρ (ContinuousLinearMap.lsmul ℝ ℝ) volume) :=
    hρc.contDiff_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ) hG (hρ.of_le (by norm_num))
  rw [laplacian_eq_dderiv _ hC2 x,
      dderiv_convolution G hG ρ hρc hρ 1 x,
      dderiv_convolution G hG ρ hρc hρ I x]
  have hΔ : (Δ ρ) = fun y => dderiv ρ 1 y + dderiv ρ I y := by
    funext y; exact laplacian_eq_dderiv ρ (hρ.of_le (by norm_num)) y
  rw [hΔ]
  have hint1 := HasCompactSupport.convolutionExists_right (ContinuousLinearMap.lsmul ℝ ℝ)
    (hasCompactSupport_dderiv ρ hρc 1) hG (continuous_dderiv ρ hρ 1) x
  have hint2 := HasCompactSupport.convolutionExists_right (ContinuousLinearMap.lsmul ℝ ℝ)
    (hasCompactSupport_dderiv ρ hρc I) hG (continuous_dderiv ρ hρ I) x
  rw [convolution_def, convolution_def, convolution_def, ← integral_add hint1 hint2]
  congr 1; funext t; rw [← ContinuousLinearMap.map_add]

end

end Bottcher
