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

/-- **Reflection invariance of the Laplacian.** `Δ (f ∘ (-·)) = (Δ f) ∘ (-·)`. -/
theorem laplacian_comp_neg (f : ℂ → ℝ) (hf : ContDiff ℝ 2 f) :
    Δ (fun w => f (-w)) = fun w => (Δ f) (-w) := by
  set g : ℂ →L[ℝ] ℂ := -ContinuousLinearMap.id ℝ ℂ with hg
  have hcomp : (fun w : ℂ => f (-w)) = f ∘ (⇑g) := by funext z; simp [hg]
  funext w
  have key : ∀ u : ℂ, iteratedFDeriv ℝ 2 (fun w => f (-w)) w ![u, u]
      = iteratedFDeriv ℝ 2 f (-w) ![u, u] := by
    intro u
    rw [hcomp, ContinuousLinearMap.iteratedFDeriv_comp_right g hf w (le_refl 2)]
    have hgw : g w = -w := by simp [hg]
    rw [hgw, ContinuousMultilinearMap.compContinuousLinearMap_apply]
    have hval : (fun i => g (![u,u] i)) = fun i => (-1 : ℝ) • (![u,u] i) := by
      funext i; fin_cases i <;> simp [hg]
    rw [hval, ContinuousMultilinearMap.map_smul_univ]; simp
  rw [laplacian_eq_iteratedFDeriv_complexPlane (fun w => f (-w))]
  show iteratedFDeriv ℝ 2 (fun w => f (-w)) w ![1,1] + iteratedFDeriv ℝ 2 (fun w => f (-w)) w ![I,I]
    = (Δ f) (-w)
  rw [key 1, key I, laplacian_eq_iteratedFDeriv_complexPlane f]

/-- **Laplacian of the reflected-translated bump** `Δ (fun y => ρ(x−y)) = (Δρ)(x−·)`.
This is what turns the convolution Laplacian into a test-function pairing. -/
theorem laplacian_translate_reflect (ρ : ℂ → ℝ) (hρ : ContDiff ℝ 2 ρ) (x : ℂ) :
    Δ (fun y => ρ (x - y)) = fun y => (Δ ρ) (x - y) := by
  have hσ : ContDiff ℝ 2 (fun w => ρ (w + x)) := hρ.comp (contDiff_id.add contDiff_const)
  have h1 : (fun y => ρ (x - y)) = fun y => (fun w => ρ (w + x)) (-y) := by
    funext y; simp [sub_eq_neg_add]
  rw [h1, laplacian_comp_neg _ hσ]
  funext y
  rw [laplacian_comp_add_right ρ x]
  simp [sub_eq_neg_add]

/-- **`Δ G_δ = 0` on the interior.** The mollification `G ⋆ η` of a weakly-harmonic
`G` has vanishing Laplacian wherever the reflected bump `η(x−·)` is supported inside
the weak-harmonicity ball.  `Δ(G⋆η)(x) = ∫ G · (Δη)(x−·) = ∫ G · Δ(η(x−·)) = 0`. -/
theorem laplacian_mollified_eq_zero (G : ℂ → ℝ) (hG : LocallyIntegrable G)
    (η : ℂ → ℝ) (hηc : HasCompactSupport η) (hη : ContDiff ℝ 3 η)
    {p : ℂ} {ε rOut : ℝ}
    (hηsupp : tsupport η ⊆ Metric.closedBall 0 rOut)
    (hweak : ∀ φ : ℂ → ℝ, ContDiff ℝ 2 φ → HasCompactSupport φ → tsupport φ ⊆ Metric.ball p ε →
      ∫ z, G z * Δ φ z = 0)
    {x : ℂ} (hx : x ∈ Metric.ball p (ε - rOut)) :
    Δ (convolution G η (ContinuousLinearMap.lsmul ℝ ℝ) volume) x = 0 := by
  set φ := fun y => η (x - y) with hφdef
  have hΔφ : Δ φ = fun y => (Δ η) (x - y) :=
    laplacian_translate_reflect η (hη.of_le (by norm_num)) x
  have hφC2 : ContDiff ℝ 2 φ := (hη.of_le (by norm_num)).comp (contDiff_const.sub contDiff_id)
  have hsuppsub : Function.support φ ⊆ Metric.closedBall x rOut := by
    intro y hy
    rw [Function.mem_support] at hy
    have : x - y ∈ tsupport η := subset_tsupport η (by rw [Function.mem_support]; exact hy)
    have h2 : x - y ∈ Metric.closedBall 0 rOut := hηsupp this
    rw [Metric.mem_closedBall, dist_zero_right] at h2
    rw [Metric.mem_closedBall, Complex.dist_eq, norm_sub_rev]; exact h2
  have hφcs : HasCompactSupport φ :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall x rOut) hsuppsub
  have hφsupp : tsupport φ ⊆ Metric.ball p ε := by
    have hsub : Metric.closedBall x rOut ⊆ Metric.ball p ε := by
      intro z hz
      rw [Metric.mem_closedBall] at hz
      rw [Metric.mem_ball] at hx ⊢
      calc dist z p ≤ dist z x + dist x p := dist_triangle z x p
        _ < rOut + (ε - rOut) := by
              apply add_lt_add_of_le_of_lt hz hx
        _ = ε := by ring
    exact (closure_minimal hsuppsub (isClosed_closedBall)).trans hsub
  rw [laplacian_convolution G hG η hηc hη x, convolution_def]
  calc ∫ t, (ContinuousLinearMap.lsmul ℝ ℝ) (G t) ((Δ η) (x - t))
      = ∫ z, G z * Δ φ z := by
        apply integral_congr_ae; filter_upwards with t
        rw [ContinuousLinearMap.lsmul_apply, smul_eq_mul, hΔφ]
    _ = 0 := hweak φ hφC2 hφcs hφsupp

/-- **The mollification is harmonic.** `G ⋆ η` is `HarmonicOnNhd` on the interior
`ball p (ε − rOut)`: smooth (compact-support convolution) with vanishing Laplacian. -/
theorem harmonicOnNhd_mollified (G : ℂ → ℝ) (hG : LocallyIntegrable G)
    (η : ℂ → ℝ) (hηc : HasCompactSupport η) (hη : ContDiff ℝ 3 η)
    {p : ℂ} {ε rOut : ℝ}
    (hηsupp : tsupport η ⊆ Metric.closedBall 0 rOut)
    (hweak : ∀ φ : ℂ → ℝ, ContDiff ℝ 2 φ → HasCompactSupport φ → tsupport φ ⊆ Metric.ball p ε →
      ∫ z, G z * Δ φ z = 0) :
    HarmonicOnNhd (convolution G η (ContinuousLinearMap.lsmul ℝ ℝ) volume)
      (Metric.ball p (ε - rOut)) := by
  have hC2 : ContDiff ℝ 2 (convolution G η (ContinuousLinearMap.lsmul ℝ ℝ) volume) :=
    hηc.contDiff_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ) hG (hη.of_le (by norm_num))
  intro x hx
  refine ⟨hC2.contDiffAt, ?_⟩
  filter_upwards [(isOpen_ball).mem_nhds hx] with y hy
  exact laplacian_mollified_eq_zero G hG η hηc hη hηsupp hweak hy

end

end Bottcher
