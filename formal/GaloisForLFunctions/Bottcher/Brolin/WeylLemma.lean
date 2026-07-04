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

open MeasureTheory Complex Metric Laplacian InnerProductSpace Filter Set
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

noncomputable def poissonInt (g : ℂ → ℝ) (c : ℂ) (R : ℝ) (w : ℂ) : ℝ :=
  Real.circleAverage (poissonKernel c w • g) c R

/-- Interior Dirichlet maximum principle: a function harmonic on `ball c R`, continuous on
`closedBall c R`, vanishing on the sphere, is `≤ 0` inside. -/
theorem harmonic_le_zero_of_sphere_zero {v : ℂ → ℝ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hvh : HarmonicOnNhd v (Metric.ball c R)) (hvc : ContinuousOn v (Metric.closedBall c R))
    (hvs : ∀ z ∈ Metric.sphere c R, v z = 0) : ∀ y ∈ Metric.ball c R, v y ≤ 0 := by
  intro y hy
  obtain ⟨z₀, hz₀mem, hz₀max⟩ := (isCompact_closedBall c R).exists_isMaxOn
    ⟨c, Metric.mem_closedBall_self hR.le⟩ hvc
  by_contra hcon
  push_neg at hcon
  have hz₀pos : 0 < v z₀ := lt_of_lt_of_le hcon (hz₀max (Metric.ball_subset_closedBall hy))
  have hz₀ball : z₀ ∈ Metric.ball c R := by
    rcases (Metric.mem_closedBall.mp hz₀mem).lt_or_eq with hlt | heq
    · exact Metric.mem_ball.mpr hlt
    · exact absurd (hvs z₀ (Metric.mem_sphere.mpr heq)) (ne_of_gt hz₀pos)
  have hmaxball : IsMaxOn v (Metric.ball c R) z₀ :=
    fun x hx => hz₀max (Metric.ball_subset_closedBall hx)
  have heqc := harmonic_eqOn_const_of_isMaxOn (convex_ball c R).isPreconnected
    isOpen_ball hvh hz₀ball hmaxball
  obtain ⟨z₁, hz₁⟩ := (NormedSpace.sphere_nonempty (x := c) (r := R)).mpr hR.le
  have hz₁cl : z₁ ∈ closure (Metric.ball c R) := by
    rw [closure_ball c hR.ne']; exact Metric.sphere_subset_closedBall hz₁
  haveI : (𝓝[Metric.ball c R] z₁).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hz₁cl
  have t1 : Tendsto v (𝓝[Metric.ball c R] z₁) (𝓝 (v z₁)) :=
    ((hvc.continuousWithinAt (Metric.sphere_subset_closedBall hz₁)).mono
      Metric.ball_subset_closedBall).tendsto
  have t2 : Tendsto v (𝓝[Metric.ball c R] z₁) (𝓝 (v z₀)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx using (heqc hx).symm
  have hz10 : v z₁ = v z₀ := tendsto_nhds_unique t1 t2
  rw [hvs z₁ hz₁] at hz10
  exact absurd hz10.symm (ne_of_gt hz₀pos)

theorem harmonic_reproduction {h : ℂ → ℝ} {c : ℂ} {R R' : ℝ} (hR : 0 < R) (hRR' : R < R')
    (hh : HarmonicOnNhd h (Metric.ball c R')) {w : ℂ} (hw : w ∈ Metric.ball c R) :
    h w = poissonInt h c R w := by
  have hball_sub : Metric.ball c R ⊆ Metric.ball c R' := Metric.ball_subset_ball hRR'.le
  have hclosed_sub : Metric.closedBall c R ⊆ Metric.ball c R' := Metric.closedBall_subset_ball hRR'
  have hhball : HarmonicOnNhd h (Metric.ball c R) := hh.mono hball_sub
  have hhsphere : ContinuousOn h (Metric.sphere c R) :=
    (hh.continuousOn).mono (Metric.sphere_subset_closedBall.trans hclosed_sub)
  have hPharm : HarmonicOnNhd (poissonInt h c R) (Metric.ball c R) :=
    poissonInt_harmonicOnNhd hR hhsphere
  set u : ℂ → ℝ := (Metric.ball c R).indicator (h - poissonInt h c R) with hu
  have huEq : Set.EqOn u (h - poissonInt h c R) (Metric.ball c R) :=
    fun z hz => Set.indicator_of_mem hz _
  have huball : HarmonicOnNhd u (Metric.ball c R) := by
    intro z hz
    refine (harmonicAt_congr_nhds (Filter.eventuallyEq_of_mem
      ((isOpen_ball).mem_nhds hz) (fun y hy => huEq hy))).mpr ((hhball.sub hPharm) z hz)
  have huzero : ∀ z, z ∉ Metric.ball c R → u z = 0 := fun z hz => Set.indicator_of_notMem hz _
  have husphere0 : ∀ z ∈ Metric.sphere c R, u z = 0 := fun z hz =>
    huzero z (by rw [Metric.mem_sphere] at hz; rw [Metric.mem_ball, hz]; exact lt_irrefl _)
  have hucont : ContinuousOn u (Metric.closedBall c R) := by
    intro z hz
    by_cases hzb : z ∈ Metric.ball c R
    · have hnb : Metric.ball c R ∈ 𝓝 z := (isOpen_ball).mem_nhds hzb
      have hdc : ContinuousAt (h - poissonInt h c R) z :=
        ((hhball.continuousOn).continuousAt hnb).sub ((hPharm.continuousOn).continuousAt hnb)
      exact (hdc.congr (Filter.eventuallyEq_of_mem hnb (fun y hy => huEq hy)).symm).continuousWithinAt
    · have hzs : z ∈ Metric.sphere c R := by
        rw [Metric.mem_sphere]
        rcases (Metric.mem_closedBall.mp hz).lt_or_eq with hlt | heq
        · exact absurd (Metric.mem_ball.mpr hlt) hzb
        · exact heq
      rw [ContinuousWithinAt, huzero z hzb, ← Metric.ball_union_sphere, nhdsWithin_union, tendsto_sup]
      refine ⟨?_, ?_⟩
      · have hcAt : ContinuousAt h z := (hh.continuousOn).continuousAt
          ((isOpen_ball).mem_nhds (hclosed_sub hz))
        have hd0 : Tendsto (h - poissonInt h c R) (𝓝[Metric.ball c R] z) (𝓝 0) := by
          have := (hcAt.continuousWithinAt.tendsto).sub (poissonInt_tendsto_boundary hR hhsphere hzs)
          simpa using this
        refine hd0.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with x hx using (huEq hx).symm
      · refine tendsto_const_nhds.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with x hx
        exact (huzero x (fun hxb => by
          rw [Metric.mem_sphere] at hx; exact absurd (Metric.mem_ball.mp hxb) (by rw [hx]; exact lt_irrefl _))).symm
  have hle := harmonic_le_zero_of_sphere_zero hR huball hucont husphere0 w hw
  have hge := harmonic_le_zero_of_sphere_zero hR huball.neg hucont.neg
    (fun z hz => by rw [Pi.neg_apply, husphere0 z hz, neg_zero]) w hw
  rw [Pi.neg_apply] at hge
  have huw : u w = 0 := le_antisymm hle (by linarith)
  have := huEq hw
  rw [huw] at this
  simpa [sub_eq_zero] using this.symm

/-! ## Mollifier sequence and approximate identity -/

noncomputable def bumpN (n : ℕ) : ContDiffBump (0:ℂ) where
  rIn := 1/(n+2)
  rOut := 1/(n+1)
  rIn_pos := by positivity
  rIn_lt_rOut := by apply one_div_lt_one_div_of_lt <;> [positivity; · push_cast; linarith]

noncomputable def mollN (n : ℕ) : ℂ → ℝ := (bumpN n).normed volume

theorem mollN_contDiff (n : ℕ) : ContDiff ℝ 3 (mollN n) := (bumpN n).contDiff_normed

theorem mollN_hasCompactSupport (n : ℕ) : HasCompactSupport (mollN n) :=
  (bumpN n).hasCompactSupport_normed

theorem mollN_tsupport (n : ℕ) : tsupport (mollN n) ⊆ Metric.closedBall 0 (1/(n+1)) := by
  show closure (Function.support (mollN n)) ⊆ Metric.closedBall 0 (1/(n+1))
  refine closure_minimal ?_ isClosed_closedBall
  rw [show mollN n = (bumpN n).normed volume from rfl, (bumpN n).support_normed_eq]
  exact ball_subset_closedBall

theorem tendsto_mollified (G : ℂ → ℝ) (hG : Continuous G) (w : ℂ) :
    Tendsto (fun n => convolution G (mollN n) (ContinuousLinearMap.lsmul ℝ ℝ) volume w)
      atTop (𝓝 (G w)) := by
  have hflip : (ContinuousLinearMap.lsmul ℝ ℝ).flip = ContinuousLinearMap.lsmul ℝ ℝ := by
    ext a b; simp [mul_comm]
  have happrox : Tendsto
      (fun n => convolution ((bumpN n).normed volume) G (ContinuousLinearMap.lsmul ℝ ℝ) volume w)
      atTop (𝓝 (G w)) := by
    refine ContDiffBump.convolution_tendsto_right (φ := bumpN) (g := fun _ => G)
      (k := fun _ => w) (x₀ := w) (z₀ := G w) ?_ ?_ ?_ ?_
    · simp only [bumpN]; exact tendsto_one_div_add_atTop_nhds_zero_nat
    · exact Filter.Eventually.of_forall (fun n => hG.aestronglyMeasurable)
    · exact (hG.tendsto w).comp tendsto_snd
    · exact tendsto_const_nhds
  refine happrox.congr (fun n => ?_)
  show convolution ((bumpN n).normed volume) G (ContinuousLinearMap.lsmul ℝ ℝ) volume w
     = convolution G (mollN n) (ContinuousLinearMap.lsmul ℝ ℝ) volume w
  rw [show mollN n = (bumpN n).normed volume from rfl, ← convolution_flip, hflip]

/-! ## Uniform bound on the mollification -/

theorem mollN_continuous (n : ℕ) : Continuous (mollN n) := (mollN_contDiff n).continuous
theorem mollN_nonneg (n : ℕ) (t : ℂ) : 0 ≤ mollN n t := (bumpN n).nonneg_normed t

theorem integrable_mollN_comp (n : ℕ) (z : ℂ) : Integrable (fun t => mollN n (z - t)) := by
  have hcs : HasCompactSupport (fun t => mollN n (z - t)) := by
    have : HasCompactSupport ((mollN n) ∘ (fun t => z - t)) :=
      (mollN_hasCompactSupport n).comp_homeomorph (Homeomorph.subLeft z)
    simpa [Function.comp] using this
  exact ((mollN_continuous n).comp (continuous_const.sub continuous_id)).integrable_of_hasCompactSupport hcs

theorem integral_mollN_comp (n : ℕ) (z : ℂ) : ∫ t, mollN n (z - t) = 1 := by
  rw [integral_sub_left_eq_self (mollN n) volume z]
  exact (bumpN n).integral_normed

theorem convolution_mollN_le {G : ℂ → ℝ} {M : ℝ} {z : ℂ} {r : ℝ} (n : ℕ)
    (hrOut : 1/((n:ℝ)+1) ≤ r)
    (hM : ∀ t, ‖z - t‖ ≤ r → |G t| ≤ M) :
    |convolution G (mollN n) (ContinuousLinearMap.lsmul ℝ ℝ) volume z| ≤ M := by
  rw [convolution_def]
  have hpt : ∀ t, |(ContinuousLinearMap.lsmul ℝ ℝ) (G t) (mollN n (z - t))|
      ≤ M * mollN n (z - t) := by
    intro t
    rw [ContinuousLinearMap.lsmul_apply, smul_eq_mul, abs_mul, abs_of_nonneg (mollN_nonneg n _)]
    by_cases ht : mollN n (z - t) = 0
    · rw [ht]; simp
    · have hball : ‖z - t‖ ≤ r := by
        have hmem := mollN_tsupport n (subset_tsupport _ (by rw [Function.mem_support]; exact ht))
        rw [Metric.mem_closedBall, dist_zero_right] at hmem
        exact le_trans hmem hrOut
      exact mul_le_mul_of_nonneg_right (hM t hball) (mollN_nonneg n _)
  have hMint : Integrable (fun t => M * mollN n (z - t)) := (integrable_mollN_comp n z).const_mul M
  calc |∫ t, (ContinuousLinearMap.lsmul ℝ ℝ) (G t) (mollN n (z - t))|
      ≤ ∫ t, M * mollN n (z - t) := by
        rw [← Real.norm_eq_abs]
        refine (norm_integral_le_integral_norm _).trans ?_
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall (fun t => norm_nonneg _))
          hMint (Filter.Eventually.of_forall (fun t => ?_))
        simp only [Real.norm_eq_abs]; exact hpt t
    _ = M := by rw [integral_const_mul, integral_mollN_comp, mul_one]

end

end Bottcher
