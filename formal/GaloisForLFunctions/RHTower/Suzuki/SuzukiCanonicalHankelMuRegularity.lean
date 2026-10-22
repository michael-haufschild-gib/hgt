import GaloisForLFunctions.RHTower.Suzuki.SuzukiCanonicalHankelDifferentialSystemCoupled

/-!
# Regularity of Suzuki's coupling coefficient

This module formalizes the paragraph immediately following Suzuki (2012), equation (411): the
boundary-trace sum `μ` is continuous for `a > 1`, tends to zero as `a → 1⁺`, and is `C¹` away
from the square-root arithmetic locus.  The definitions below totalize the printed functions only
to make topological statements at the endpoint; on `a > 1` they are definitionally the literal
Fredholm boundary traces already used in equations (410)--(413).
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped ENNReal
noncomputable section
namespace RHTower

attribute [local instance] Measure.Subtype.measureSpace
attribute [local instance 2000] NormedAddCommGroup.toAddCommGroup

/-- Total real-parameter version of the signed diagonal trace `a φ_a^ε(a)`. -/
def suzukiHankelBoundaryTraceReal
    (epsilon : SuzukiHankelSign) (omega : ℝ) (homega : 1 < omega) : ℝ → ℂ :=
  fun a => if ha : 1 < a then
    (a : ℂ) * suzukiHankelPhiGlobal epsilon omega a homega ha a
  else 0

/-- Total real-parameter version of Suzuki's coefficient `μ`; it is set to zero at and below the
left endpoint, matching the literal right limit proved below. -/
def suzukiHankelMuReal (omega : ℝ) (homega : 1 < omega) : ℝ → ℂ :=
  fun a =>
    suzukiHankelBoundaryTraceReal SuzukiHankelSign.positive omega homega a +
      suzukiHankelBoundaryTraceReal SuzukiHankelSign.negative omega homega a

@[simp] theorem suzukiHankelBoundaryTraceReal_of_one_lt
    (epsilon : SuzukiHankelSign) {omega a : ℝ}
    (homega : 1 < omega) (ha : 1 < a) :
    suzukiHankelBoundaryTraceReal epsilon omega homega a =
      (a : ℂ) * suzukiHankelPhiGlobal epsilon omega a homega ha a := by
  rw [suzukiHankelBoundaryTraceReal, dif_pos ha]

@[simp] theorem suzukiHankelMuReal_of_one_lt
    {omega a : ℝ} (homega : 1 < omega) (ha : 1 < a) :
    suzukiHankelMuReal omega homega a =
      suzukiHankelMu omega a homega ha := by
  simp only [suzukiHankelMuReal,
    suzukiHankelBoundaryTraceReal_of_one_lt _ homega ha, suzukiHankelMu]

/-- On a subcritical diagonal `0 < b ≤ 1`, the literal fixed-window Fredholm point is zero.  Both
the source `h_ω(b²)` and every kernel row surviving the aperture cutoff lie in the support gap. -/
theorem suzukiFixedWindowPhiPoint_diagonal_eq_zero
    (epsilon : SuzukiHankelSign) {omega B b : ℝ}
    (homega : 1 < omega) (hB : 1 < B)
    (hb0 : 0 < b) (hb1 : b ≤ 1) (hbB : b ≤ B) :
    suzukiFixedWindowPhiPoint epsilon omega B homega hB b
        (⟨b, ⟨hb0.le, hbB⟩⟩ : ClosedInterval 0 B) = 0 := by
  let x : ClosedInterval 0 B := ⟨b, ⟨hb0.le, hbB⟩⟩
  let f := suzukiFixedWindowPhi epsilon omega B (by linarith : 1 / 2 < omega) hB b
  have hsource : suzukiSourceHFinite omega (b * (x : ℝ)) = 0 := by
    rw [suzukiSourceHFinite, if_neg]
    exact not_lt_of_ge (by
      change b * b ≤ 1
      calc
        b * b ≤ 1 * 1 := mul_le_mul hb1 hb1 hb0.le zero_le_one
        _ = 1 := one_mul 1)
  have hcut := suzukiApertureCutoff_ae b B f
  have hout : suzukiCompressedHankelContinuousOutput omega B (by linarith) hB
      (suzukiApertureCutoff b B f) x = 0 := by
    rw [suzukiCompressedHankelContinuousOutput_eq_integral (by linarith) hB]
    apply integral_eq_zero_of_ae
    filter_upwards [hcut] with y hy
    rw [hy]
    by_cases hya : y ∈ suzukiApertureSet b B
    · rw [Set.indicator_of_mem hya]
      have hxy : (x : ℝ) * (y : ℝ) ≤ 1 := by
        calc
          (x : ℝ) * (y : ℝ) ≤ b * b :=
            mul_le_mul_of_nonneg_left hya (by simpa only [x] using hb0.le)
          _ ≤ 1 := by
            calc
              b * b ≤ 1 * 1 := mul_le_mul hb1 hb1 hb0.le zero_le_one
              _ = 1 := one_mul 1
      rw [suzukiSourceHFinite, if_neg (not_lt_of_ge hxy), zero_mul]
      simp
    · rw [Set.indicator_of_notMem hya, mul_zero]
      simp
  rw [suzukiFixedWindowPhiPoint, hsource, hout, mul_zero, sub_zero]

/-- Each signed diagonal trace is continuous at every supercritical aperture. -/
theorem continuousAt_suzukiHankelBoundaryTraceReal_of_one_lt
    (epsilon : SuzukiHankelSign) {omega a : ℝ}
    (homega : 1 < omega) (ha : 1 < a) :
    ContinuousAt (suzukiHankelBoundaryTraceReal epsilon omega homega) a := by
  let B := a + 1
  have haB : a < B := by dsimp only [B]; linarith
  have hB : 1 < B := ha.trans haB
  let hB0 : 0 ≤ B := by linarith
  let q : ℝ → ClosedInterval 0 B := fun b => Set.projIcc 0 B hB0 b
  let F : ℝ → ℂ := fun b =>
    (b : ℂ) * suzukiFixedWindowPhiContinuousCurve
      epsilon omega B homega hB b (q b)
  have hcurve := continuousAt_suzukiFixedWindowPhiContinuousCurve
    epsilon homega hB (lt_trans zero_lt_one ha) haB
  have hq : ContinuousAt q a := continuous_projIcc.continuousAt
  have heval : ContinuousAt (fun b =>
      suzukiFixedWindowPhiContinuousCurve epsilon omega B homega hB b (q b)) a :=
    continuous_eval.continuousAt.comp (hcurve.prodMk hq)
  have hF : ContinuousAt F a := Complex.continuous_ofReal.continuousAt.mul heval
  have hev : suzukiHankelBoundaryTraceReal epsilon omega homega =ᶠ[𝓝 a] F := by
    filter_upwards [Ioo_mem_nhds ha haB] with b hb
    have hbMem : b ∈ Icc (0 : ℝ) B :=
      ⟨(lt_trans zero_lt_one hb.1).le, hb.2.le⟩
    rw [suzukiHankelBoundaryTraceReal, dif_pos hb.1]
    change (b : ℂ) * _ = (b : ℂ) * _
    congr 1
    rw [show q b = (⟨b, hbMem⟩ : ClosedInterval 0 B) by
      exact Set.projIcc_of_mem hB0 hbMem]
    rw [suzukiFixedWindowPhiContinuousCurve_eq epsilon homega hB
      (lt_trans zero_lt_one hb.1) hb.2.le,
      suzukiFixedWindowPhiContinuous_apply]
    exact (suzukiFixedWindowPhiPoint_eq_global epsilon homega hb.1 hB hb.2.le
      ⟨b, hbMem⟩ (lt_trans zero_lt_one hb.1)).symm
  exact hF.congr_of_eventuallyEq hev

/-- The totalized signed trace is continuous at the endpoint `a = 1`; this proves rather than
postulates Suzuki's boundary limit. -/
theorem continuousAt_suzukiHankelBoundaryTraceReal_one
    (epsilon : SuzukiHankelSign) {omega : ℝ} (homega : 1 < omega) :
    ContinuousAt (suzukiHankelBoundaryTraceReal epsilon omega homega) 1 := by
  let B : ℝ := 2
  have hB : 1 < B := by norm_num [B]
  let hB0 : 0 ≤ B := by norm_num [B]
  let q : ℝ → ClosedInterval 0 B := fun b => Set.projIcc 0 B hB0 b
  let F : ℝ → ℂ := fun b =>
    (b : ℂ) * suzukiFixedWindowPhiContinuousCurve
      epsilon omega B homega hB b (q b)
  have hcurve := continuousAt_suzukiFixedWindowPhiContinuousCurve
    (a := (1 : ℝ)) epsilon homega hB
      (by norm_num : (0 : ℝ) < 1) (by norm_num [B] : (1 : ℝ) < B)
  have hq : ContinuousAt q 1 := continuous_projIcc.continuousAt
  have heval : ContinuousAt (fun b =>
      suzukiFixedWindowPhiContinuousCurve epsilon omega B homega hB b (q b)) 1 :=
    continuous_eval.continuousAt.comp (hcurve.prodMk hq)
  have hF : ContinuousAt F 1 := Complex.continuous_ofReal.continuousAt.mul heval
  have hev : suzukiHankelBoundaryTraceReal epsilon omega homega =ᶠ[𝓝 1] F := by
    filter_upwards [Ioo_mem_nhds (by norm_num : (0 : ℝ) < 1)
      (by norm_num [B] : (1 : ℝ) < B)] with b hb
    have hbMem : b ∈ Icc (0 : ℝ) B := ⟨hb.1.le, hb.2.le⟩
    have hqEq : q b = (⟨b, hbMem⟩ : ClosedInterval 0 B) :=
      Set.projIcc_of_mem hB0 hbMem
    by_cases hb1 : 1 < b
    · rw [suzukiHankelBoundaryTraceReal, dif_pos hb1]
      change (b : ℂ) * _ = (b : ℂ) * _
      congr 1
      rw [hqEq, suzukiFixedWindowPhiContinuousCurve_eq epsilon homega hB
        (lt_trans zero_lt_one hb1) hb.2.le,
        suzukiFixedWindowPhiContinuous_apply]
      exact (suzukiFixedWindowPhiPoint_eq_global epsilon homega hb1 hB hb.2.le
        ⟨b, hbMem⟩ (lt_trans zero_lt_one hb1)).symm
    · have hble : b ≤ 1 := le_of_not_gt hb1
      rw [suzukiHankelBoundaryTraceReal, dif_neg hb1]
      change 0 = (b : ℂ) * _
      rw [hqEq, suzukiFixedWindowPhiContinuousCurve_eq epsilon homega hB hb.1 hb.2.le,
        suzukiFixedWindowPhiContinuous_apply,
        suzukiFixedWindowPhiPoint_diagonal_eq_zero epsilon homega hB hb.1 hble hb.2.le,
        mul_zero]
  exact hF.congr_of_eventuallyEq hev

/-- Suzuki's coefficient is continuous on the full printed domain `(1,∞)`. -/
theorem continuousOn_suzukiHankelMuReal
    {omega : ℝ} (homega : 1 < omega) :
    ContinuousOn (suzukiHankelMuReal omega homega) (Ioi 1) := by
  intro a ha
  exact ((continuousAt_suzukiHankelBoundaryTraceReal_of_one_lt
    SuzukiHankelSign.positive homega ha).add
      (continuousAt_suzukiHankelBoundaryTraceReal_of_one_lt
        SuzukiHankelSign.negative homega ha)).continuousWithinAt

/-- Suzuki (2012), equation (404) consequence used after (411): `μ(a) → 0` as `a → 1⁺`. -/
theorem tendsto_suzukiHankelMuReal_one_right
    {omega : ℝ} (homega : 1 < omega) :
    Tendsto (suzukiHankelMuReal omega homega) (𝓝[Ioi 1] 1) (𝓝 0) := by
  have hc : ContinuousAt (suzukiHankelMuReal omega homega) 1 :=
    (continuousAt_suzukiHankelBoundaryTraceReal_one
      SuzukiHankelSign.positive homega).add
      (continuousAt_suzukiHankelBoundaryTraceReal_one
        SuzukiHankelSign.negative homega)
  have hzero : suzukiHankelMuReal omega homega 1 = 0 := by
    simp [suzukiHankelMuReal, suzukiHankelBoundaryTraceReal]
  rw [← hzero]
  exact hc.mono_left nhdsWithin_le_nhds

/-! ## A diagonal `C¹` principle -/

/-- A bivariate scalar function is `C¹` along the diagonal when both partial derivatives exist on
an open neighborhood and their coefficient fields are continuous there.  This packages the joint
regularity step suppressed in Suzuki's passage from Lemmas `ad1`, `ad2` to diagonal traces. -/
theorem contDiffAt_one_diagonal_of_continuous_partials
    {f d₁ d₂ : ℝ → ℝ → ℂ} {W : Set (ℝ × ℝ)} {a : ℝ}
    (hWopen : IsOpen W) (haa : (a, a) ∈ W)
    (h₁ : ∀ p ∈ W, HasDerivAt (fun b : ℝ => f b p.2) (d₁ p.1 p.2) p.1)
    (h₂ : ∀ p ∈ W, HasDerivAt (f p.1) (d₂ p.1 p.2) p.2)
    (hc₁ : ContinuousOn (Function.uncurry d₁) W)
    (hc₂ : ContinuousOn (Function.uncurry d₂) W) :
    ContDiffAt ℝ 1 (fun b : ℝ => f b b) a := by
  let diagonal : ℝ → ℝ × ℝ := fun b => (b, b)
  let U : Set ℝ := diagonal ⁻¹' W
  let d : ℝ → ℂ := fun b => d₁ b b + d₂ b b
  let d' : ℝ → ℝ →L[ℝ] ℂ := fun b => ContinuousLinearMap.toSpanSingleton ℝ (d b)
  have hdiag : Continuous diagonal := continuous_id.prodMk continuous_id
  have hUopen : IsOpen U := hWopen.preimage hdiag
  have haU : a ∈ U := haa
  rw [contDiffAt_one_iff]
  refine ⟨d', U, hUopen.mem_nhds haU, ?_, ?_⟩
  · have hd₁ : ContinuousOn (fun b : ℝ => d₁ b b) U :=
      hc₁.comp hdiag.continuousOn (fun b hb => hb)
    have hd₂ : ContinuousOn (fun b : ℝ => d₂ b b) U :=
      hc₂.comp hdiag.continuousOn (fun b hb => hb)
    exact (ContinuousLinearMap.toSpanSingletonCLE
      (𝕜 := ℝ) (E := ℂ)).continuous.comp_continuousOn (hd₁.add hd₂)
  · intro b hb
    let p : ℝ × ℝ := (b, b)
    let f₁ : ℝ → ℝ → ℝ →L[ℝ] ℂ := fun c x =>
      ContinuousLinearMap.toSpanSingleton ℝ (d₁ c x)
    let f₂ : ℝ → ℝ → ℝ →L[ℝ] ℂ := fun c x =>
      ContinuousLinearMap.toSpanSingleton ℝ (d₂ c x)
    have hpW : p ∈ W := hb
    have hWnhds : W ∈ 𝓝 p := hWopen.mem_nhds hpW
    have hpart₁ : ∀ᶠ q : ℝ × ℝ in 𝓝 p,
        HasFDerivAt (f · q.2) (f₁ q.1 q.2) q.1 := by
      filter_upwards [hWnhds] with q hq
      exact (h₁ q hq).hasFDerivAt
    have hpart₂ : ∀ᶠ q : ℝ × ℝ in 𝓝 p,
        HasFDerivAt (f q.1) (f₂ q.1 q.2) q.2 := by
      filter_upwards [hWnhds] with q hq
      exact (h₂ q hq).hasFDerivAt
    have hc₁p : ContinuousAt (Function.uncurry d₁) p :=
      hc₁.continuousAt hWnhds
    have hc₂p : ContinuousAt (Function.uncurry d₂) p :=
      hc₂.continuousAt hWnhds
    have hcf₁ : ContinuousAt (Function.uncurry f₁) p :=
      (ContinuousLinearMap.toSpanSingletonCLE
        (𝕜 := ℝ) (E := ℂ)).continuous.continuousAt.comp hc₁p
    have hcf₂ : ContinuousAt (Function.uncurry f₂) p :=
      (ContinuousLinearMap.toSpanSingletonCLE
        (𝕜 := ℝ) (E := ℂ)).continuous.continuousAt.comp hc₂p
    have hjoint := hasStrictFDerivAt_uncurry_coprod
      (u := p) (f := f) (f₁ := f₁) (f₂ := f₂)
      hpart₁ hpart₂ hcf₁ hcf₂
    have hdiagDeriv : HasFDerivAt diagonal
        ((1 : ℝ →L[ℝ] ℝ).prod (1 : ℝ →L[ℝ] ℝ)) b :=
      (hasFDerivAt_id b).prodMk (hasFDerivAt_id b)
    have hmap :
        ((↿f₁ p).coprod (↿f₂ p)).comp
            ((1 : ℝ →L[ℝ] ℝ).prod (1 : ℝ →L[ℝ] ℝ)) = d' b := by
      refine ContinuousLinearMap.ext fun t => ?_
      simp only [f₁, f₂, p, d', d,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
        one_apply_eq_self, ContinuousLinearMap.coprod_apply,
        ContinuousLinearMap.toSpanSingleton_apply]
      exact (smul_add t (d₁ b b) (d₂ b b)).symm
    have hcomp := HasFDerivAt.comp (f := diagonal) b
      hjoint.hasFDerivAt hdiagDeriv
    rw [hmap] at hcomp
    have hfun : (↿f ∘ diagonal) = fun c : ℝ => f c c := by
      funext c
      rfl
    rw [hfun] at hcomp
    exact hcomp

/-! ## Joint Fredholm fields -/

/-- Fixed-window Fredholm solution evaluated at a clamped real spatial coordinate.  Clamping only
totalizes the field; on the open box used below it is the literal point solution. -/
def suzukiFixedWindowPhiJointPoint
    (epsilon : SuzukiHankelSign) (omega B : ℝ)
    (homega : 1 < omega) (hB : 1 < B) (b x : ℝ) : ℂ :=
  suzukiFixedWindowPhiContinuousCurve epsilon omega B homega hB b
    (Set.projIcc 0 B (by linarith) x)

/-- Jointly defined coefficient of aperture differentiation.  It is written using the common
smooth-extension derivative curve, so its dependence on both aperture and spatial coordinate is
visible rather than hidden inside a pointwise `deriv`. -/
def suzukiFixedWindowPhiJointApertureDerivative
    (epsilon : SuzukiHankelSign) (omega B R : ℝ)
    (homega : 1 < omega) (hB : 1 < B) (b x : ℝ) : ℂ :=
  (x : ℂ) * deriv (suzukiSourceHFinite omega) (b * x) -
    epsilon.coeff *
      suzukiFixedWindowSmoothedPhiDerivativeCurvePoint
        epsilon omega B R homega hB b (Set.projIcc 0 B (by linarith) x)

theorem continuousAt_suzukiFixedWindowPhiJointPoint
    (epsilon : SuzukiHankelSign) {omega B b x : ℝ}
    (homega : 1 < omega) (hB : 1 < B)
    (hb0 : 0 < b) (hbB : b < B) :
    ContinuousAt (Function.uncurry
      (suzukiFixedWindowPhiJointPoint epsilon omega B homega hB)) (b, x) := by
  let hB0 : 0 ≤ B := by linarith
  let curve := suzukiFixedWindowPhiContinuousCurve epsilon omega B homega hB
  let q : ℝ → ClosedInterval 0 B := fun y => Set.projIcc 0 B hB0 y
  change ContinuousAt (fun p : ℝ × ℝ => curve p.1 (q p.2)) (b, x)
  have hcurve : ContinuousAt curve b := continuousAt_suzukiFixedWindowPhiContinuousCurve
    epsilon homega hB hb0 hbB
  have hcurve' : ContinuousAt (curve ∘ Prod.fst) (b, x) :=
    hcurve.comp continuousAt_fst
  have hq : ContinuousAt (q ∘ Prod.snd) (b, x) :=
    continuous_projIcc.continuousAt.comp continuousAt_snd
  exact continuous_eval.continuousAt.comp (hcurve'.prodMk hq)

/-- The explicit aperture coefficient is jointly continuous at every positive noninteger product
inside a fixed window. -/
theorem continuousAt_suzukiFixedWindowPhiJointApertureDerivative
    (epsilon : SuzukiHankelSign) {omega B R b x : ℝ}
    (homega : 1 < omega) (hB : 1 < B)
    (hb0 : 0 < b) (hbB : b < B) (hx0 : 0 < x)
    (hregular : ∀ n : ℕ, b * x ≠ (n : ℝ)) :
    ContinuousAt (Function.uncurry
      (suzukiFixedWindowPhiJointApertureDerivative
        epsilon omega B R homega hB)) (b, x) := by
  let H := suzukiSourceHFinite omega
  let hB0 : 0 ≤ B := by linarith
  let q : ℝ → ClosedInterval 0 B := fun y => Set.projIcc 0 B hB0 y
  have harg : ContinuousAt (fun p : ℝ × ℝ => p.1 * p.2) (b, x) :=
    continuousAt_fst.mul continuousAt_snd
  have hH : ContDiffAt ℝ 1 H (b * x) :=
    contDiffAt_one_suzukiSourceHFinite_of_not_nat homega (mul_pos hb0 hx0) hregular
  have hdH : ContinuousAt (deriv H ∘ fun p : ℝ × ℝ => p.1 * p.2) (b, x) :=
    ContinuousAt.comp (f := fun p : ℝ × ℝ => p.1 * p.2) (g := deriv H)
      (continuousAt_deriv_of_contDiffAt_one hH) harg
  change ContinuousAt (fun p : ℝ × ℝ => deriv H (p.1 * p.2)) (b, x) at hdH
  have hsource : ContinuousAt (fun p : ℝ × ℝ =>
      (p.2 : ℂ) * deriv H (p.1 * p.2)) (b, x) :=
    (Complex.continuous_ofReal.continuousAt.comp continuousAt_snd).mul hdH
  let dcurve := suzukiFixedWindowPhiDerivativeCurveL1 epsilon omega B R homega hB
  let cut : ℝ → IntervalL1 0 B := fun c => suzukiApertureCutoffL1 c B (dcurve c)
  have hdCurve : ContinuousAt dcurve b := continuousAt_suzukiFixedWindowPhiDerivativeCurveL1
    (R := R) epsilon homega hB hb0 hbB
  have hcut0 : ContinuousAt cut b :=
    continuousAt_suzukiApertureCutoffL1_apply₂ B b hdCurve
  have hcut : ContinuousAt (cut ∘ Prod.fst) (b, x) := hcut0.comp continuousAt_fst
  have hfunctional : ContinuousAt (fun p : ℝ × ℝ =>
      suzukiHankelL1FunctionalContinuous omega B homega (q p.2)) (b, x) :=
    (suzukiHankelL1FunctionalContinuous omega B homega).continuous.continuousAt.comp
      (continuous_projIcc.continuousAt.comp continuousAt_snd)
  have hfirst : ContinuousAt (fun p : ℝ × ℝ =>
      suzukiHankelL1FunctionalContinuous omega B homega (q p.2)
        (cut p.1)) (b, x) :=
    hfunctional.clm_apply hcut
  have hcurve := continuousAt_suzukiFixedWindowPhiContinuousCurve
    epsilon homega hB hb0 hbB
  have hprojB : ContinuousAt (fun c : ℝ => Set.projIcc 0 B hB0 c) b :=
    continuous_projIcc.continuousAt
  let endpoint : ℝ → ℂ := fun c =>
    suzukiFixedWindowPhiContinuousCurve epsilon omega B homega hB c
      (Set.projIcc 0 B hB0 c)
  have hendpoint0 : ContinuousAt endpoint b :=
    continuous_eval.continuousAt.comp (hcurve.prodMk hprojB)
  have hendpoint : ContinuousAt (fun p : ℝ × ℝ =>
      suzukiFixedWindowPhiContinuousCurve epsilon omega B homega hB p.1
        (Set.projIcc 0 B hB0 p.1)) (b, x) := by
    have hcomp : ContinuousAt (endpoint ∘ Prod.fst) (b, x) :=
      ContinuousAt.comp (f := Prod.fst) (g := endpoint) hendpoint0 continuousAt_fst
    exact hcomp
  have hrow : ContinuousAt (fun p : ℝ × ℝ =>
      suzukiHankelKernelContinuousRowOnReal omega B homega hB0 p.1 (q p.2))
      (b, x) := by
    have hr : ContinuousAt (fun p : ℝ × ℝ =>
        suzukiHankelKernelContinuousRowOnReal omega B homega hB0 p.1) (b, x) :=
      (continuous_suzukiHankelKernelContinuousRowOnReal
        omega B homega hB0).continuousAt.comp continuousAt_fst
    have hqx : ContinuousAt (fun p : ℝ × ℝ => q p.2) (b, x) :=
      continuous_projIcc.continuousAt.comp continuousAt_snd
    exact continuous_eval.continuousAt.comp (hr.prodMk hqx)
  have hsmooth : ContinuousAt (fun p : ℝ × ℝ =>
      suzukiFixedWindowSmoothedPhiDerivativeCurvePoint
        epsilon omega B R homega hB p.1 (q p.2)) (b, x) := by
    change ContinuousAt (fun p : ℝ × ℝ =>
      suzukiHankelL1FunctionalContinuous omega B homega (q p.2)
          (suzukiApertureCutoffL1 p.1 B
            (suzukiFixedWindowPhiDerivativeCurveL1
              epsilon omega B R homega hB p.1)) +
        suzukiFixedWindowPhiContinuousCurve epsilon omega B homega hB p.1
            (Set.projIcc 0 B (by linarith) p.1) *
          suzukiHankelKernelContinuousRowOnReal omega B homega
            (by linarith) p.1 (q p.2)) (b, x)
    convert hfirst.add (hendpoint.mul hrow) using 1
    funext p
    rfl
  change ContinuousAt (fun p : ℝ × ℝ =>
    (p.2 : ℂ) * deriv H (p.1 * p.2) - epsilon.coeff *
      suzukiFixedWindowSmoothedPhiDerivativeCurvePoint
        epsilon omega B R homega hB p.1 (q p.2)) (b, x)
  exact hsource.sub (continuousAt_const.mul hsmooth)

/-- Exact chain-rule formula for the aperture derivative of Suzuki's arithmetic source. -/
theorem deriv_suzukiSourceHFinite_aperture
    {omega b x : ℝ} (homega : 1 < omega) (hb0 : 0 < b) (hx0 : 0 < x)
    (hregular : ∀ n : ℕ, b * x ≠ (n : ℝ)) :
    deriv (fun c : ℝ => suzukiSourceHFinite omega (c * x)) b =
      (x : ℂ) * deriv (suzukiSourceHFinite omega) (b * x) := by
  let H := suzukiSourceHFinite omega
  have hbase : HasDerivAt H (deriv H (b * x)) (b * x) :=
    ((contDiffAt_one_suzukiSourceHFinite_of_not_nat homega
      (mul_pos hb0 hx0) hregular).differentiableAt (by norm_num)).hasDerivAt
  have hlinear : HasDerivAt (fun c : ℝ => c * x) x b := by
    simpa using (hasDerivAt_id b).mul_const x
  have hcomp := hbase.scomp b hlinear
  have hcomp' : HasDerivAt
      (fun c : ℝ => suzukiSourceHFinite omega (c * x))
      (x • deriv H (b * x)) b :=
    hcomp.congr_of_eventuallyEq (Eventually.of_forall fun _ => rfl)
  simpa only [H, Complex.real_smul] using hcomp'.deriv

/-- The pointwise aperture coefficient from Lemma `ad2` is exactly the jointly continuous
coefficient above; no derivative is redefined. -/
theorem suzukiFixedWindowPhiPointApertureDerivative_eq_joint
    (epsilon : SuzukiHankelSign) {omega B R b x : ℝ}
    (homega : 1 < omega) (hB : 1 < B) (hR : 0 ≤ R)
    (hb0 : 0 < b) (hbB : b < B) (hx0 : 0 < x) (hxB : x ≤ B)
    (hbR : Real.log b + Real.log B < R)
    (hregular : ∀ n : ℕ, b * x ≠ (n : ℝ)) :
    suzukiFixedWindowPhiPointApertureDerivative epsilon omega B homega hB
        b hb0 hbB (⟨x, ⟨hx0.le, hxB⟩⟩ : ClosedInterval 0 B) =
      suzukiFixedWindowPhiJointApertureDerivative
        epsilon omega B R homega hB b x := by
  let xB : ClosedInterval 0 B := ⟨x, ⟨hx0.le, hxB⟩⟩
  have hsource := deriv_suzukiSourceHFinite_aperture homega hb0 hx0 hregular
  have hdEq := suzukiFixedWindowPhiDerivativeL1_eq_curve
    epsilon homega hB hR hb0 hbB hbR
  have hfEq := suzukiFixedWindowPhiContinuousCurve_eq
    epsilon homega hB hb0 hbB.le
  have hsmooth :
      suzukiFixedWindowSmoothedPhiDerivativePoint
          epsilon omega B homega hB b hb0 hbB xB =
        suzukiFixedWindowSmoothedPhiDerivativeCurvePoint
          epsilon omega B R homega hB b xB := by
    change
      suzukiHankelL1FunctionalContinuous omega B homega xB
          (suzukiApertureCutoffL1 b B
            (suzukiFixedWindowPhiDerivativeL1
              epsilon omega B homega hB b hb0 hbB)) +
        suzukiSmoothedApertureProfileIntegrand omega B homega (by linarith)
          (suzukiFixedWindowPhiContinuous
            epsilon omega B homega hB b hb0 hbB.le) b xB = _
    simp [suzukiFixedWindowSmoothedPhiDerivativeCurvePoint, hdEq, ← hfEq,
      suzukiSmoothedApertureProfileIntegrand,
      suzukiHankelKernelContinuousRowOnReal] 
  rw [suzukiFixedWindowPhiPointApertureDerivative,
    suzukiFixedWindowPhiJointApertureDerivative, hsource, hsmooth]
  rw [Set.projIcc_of_mem (by linarith : 0 ≤ B) ⟨hx0.le, hxB⟩]

/-- Aperture partial derivative of the jointly totalized fixed-window point field. -/
theorem hasDerivAt_suzukiFixedWindowPhiJointPoint_aperture
    (epsilon : SuzukiHankelSign) {omega B R b x : ℝ}
    (homega : 1 < omega) (hB : 1 < B) (hR : 0 ≤ R)
    (hb0 : 0 < b) (hbB : b < B) (hx0 : 0 < x) (hxB : x < B)
    (hbR : Real.log b + Real.log B < R)
    (hregular : ∀ n : ℕ, b * x ≠ (n : ℝ)) :
    HasDerivAt (fun c : ℝ =>
      suzukiFixedWindowPhiJointPoint epsilon omega B homega hB c x)
      (suzukiFixedWindowPhiJointApertureDerivative
        epsilon omega B R homega hB b x) b := by
  let hB0 : 0 ≤ B := by linarith
  let xB : ClosedInterval 0 B := ⟨x, ⟨hx0.le, hxB.le⟩⟩
  have hbase := hasDerivAt_suzukiFixedWindowPhiPoint
    epsilon homega hB hb0 hbB xB hx0 hregular
  have hev : (fun c : ℝ =>
      suzukiFixedWindowPhiJointPoint epsilon omega B homega hB c x) =ᶠ[𝓝 b]
      fun c : ℝ => suzukiFixedWindowPhiPoint epsilon omega B homega hB c xB := by
    filter_upwards [Ioo_mem_nhds hb0 hbB] with c hc
    rw [suzukiFixedWindowPhiJointPoint]
    rw [Set.projIcc_of_mem hB0 ⟨hx0.le, hxB.le⟩]
    rw [suzukiFixedWindowPhiContinuousCurve_eq epsilon homega hB hc.1 hc.2.le,
      suzukiFixedWindowPhiContinuous_apply]
  have hderiv := hbase.congr_of_eventuallyEq hev
  rw [suzukiFixedWindowPhiPointApertureDerivative_eq_joint
    epsilon homega hB hR hb0 hbB hx0 hxB.le hbR hregular] at hderiv
  exact hderiv

/-- On the interior box, the jointly totalized point is the literal global Fredholm solution. -/
theorem suzukiFixedWindowPhiJointPoint_eq_global
    (epsilon : SuzukiHankelSign) {omega B b x : ℝ}
    (homega : 1 < omega) (hB : 1 < B) (hb1 : 1 < b) (hbB : b < B)
    (hx0 : 0 < x) (hxB : x ≤ B) :
    suzukiFixedWindowPhiJointPoint epsilon omega B homega hB b x =
      suzukiHankelPhiGlobal epsilon omega b homega hb1 x := by
  rw [suzukiFixedWindowPhiJointPoint]
  rw [Set.projIcc_of_mem (by linarith : 0 ≤ B) ⟨hx0.le, hxB⟩]
  rw [suzukiFixedWindowPhiContinuousCurve_eq epsilon homega hB
    (lt_trans zero_lt_one hb1) hbB.le,
    suzukiFixedWindowPhiContinuous_apply]
  exact suzukiFixedWindowPhiPoint_eq_global epsilon homega hb1 hB hbB.le
    ⟨x, ⟨hx0.le, hxB⟩⟩ hx0

/-- Spatial partial coefficient recovered from the exact coupled equation (413). -/
def suzukiFixedWindowPhiJointSpatialDerivative
    (epsilon : SuzukiHankelSign) (omega B R : ℝ)
    (homega : 1 < omega) (hB : 1 < B) (b x : ℝ) : ℂ :=
  (x : ℂ)⁻¹ *
    ((b : ℂ) * suzukiFixedWindowPhiJointApertureDerivative
        epsilon.opposite omega B R homega hB b x +
      ((1 / 2 : ℂ) + epsilon.opposite.coeff * suzukiHankelMuReal omega homega b) *
        suzukiFixedWindowPhiJointPoint epsilon.opposite omega B homega hB b x -
      (1 / 2 : ℂ) *
        suzukiFixedWindowPhiJointPoint epsilon omega B homega hB b x)

/-- Equation (413) turns joint aperture regularity into joint spatial regularity. -/
theorem continuousAt_suzukiFixedWindowPhiJointSpatialDerivative
    (epsilon : SuzukiHankelSign) {omega B R b x : ℝ}
    (homega : 1 < omega) (hB : 1 < B)
    (hb1 : 1 < b) (hbB : b < B) (hx0 : 0 < x)
    (hregular : ∀ n : ℕ, b * x ≠ (n : ℝ)) :
    ContinuousAt (Function.uncurry
      (suzukiFixedWindowPhiJointSpatialDerivative
        epsilon omega B R homega hB)) (b, x) := by
  have hd := continuousAt_suzukiFixedWindowPhiJointApertureDerivative
    (R := R) epsilon.opposite homega hB (lt_trans zero_lt_one hb1) hbB hx0 hregular
  have hP := continuousAt_suzukiFixedWindowPhiJointPoint
    (x := x) epsilon homega hB (lt_trans zero_lt_one hb1) hbB
  have hPop := continuousAt_suzukiFixedWindowPhiJointPoint
    (x := x) epsilon.opposite homega hB (lt_trans zero_lt_one hb1) hbB
  have hmu0 : ContinuousAt (suzukiHankelMuReal omega homega) b :=
    (continuousAt_suzukiHankelBoundaryTraceReal_of_one_lt
      SuzukiHankelSign.positive homega hb1).add
      (continuousAt_suzukiHankelBoundaryTraceReal_of_one_lt
        SuzukiHankelSign.negative homega hb1)
  have hmu : ContinuousAt (fun p : ℝ × ℝ => suzukiHankelMuReal omega homega p.1)
      (b, x) := by
    have hc : ContinuousAt (suzukiHankelMuReal omega homega ∘ Prod.fst) (b, x) :=
      ContinuousAt.comp (f := Prod.fst) (g := suzukiHankelMuReal omega homega)
        hmu0 continuousAt_fst
    exact hc
  have hbCast : ContinuousAt (fun p : ℝ × ℝ => (p.1 : ℂ)) (b, x) :=
    Complex.continuous_ofReal.continuousAt.comp continuousAt_fst
  have hxCast : ContinuousAt (fun p : ℝ × ℝ => (p.2 : ℂ)) (b, x) :=
    Complex.continuous_ofReal.continuousAt.comp continuousAt_snd
  have hinner : ContinuousAt (fun p : ℝ × ℝ =>
      (p.1 : ℂ) * suzukiFixedWindowPhiJointApertureDerivative
          epsilon.opposite omega B R homega hB p.1 p.2 +
        ((1 / 2 : ℂ) + epsilon.opposite.coeff * suzukiHankelMuReal omega homega p.1) *
          suzukiFixedWindowPhiJointPoint epsilon.opposite omega B homega hB p.1 p.2 -
        (1 / 2 : ℂ) *
          suzukiFixedWindowPhiJointPoint epsilon omega B homega hB p.1 p.2) (b, x) :=
    (hbCast.mul hd).add
      ((continuousAt_const.add (continuousAt_const.mul hmu)).mul hPop) |>.sub
        (continuousAt_const.mul hP)
  change ContinuousAt (fun p : ℝ × ℝ => (p.2 : ℂ)⁻¹ *
    ((p.1 : ℂ) * suzukiFixedWindowPhiJointApertureDerivative
        epsilon.opposite omega B R homega hB p.1 p.2 +
      ((1 / 2 : ℂ) + epsilon.opposite.coeff * suzukiHankelMuReal omega homega p.1) *
        suzukiFixedWindowPhiJointPoint epsilon.opposite omega B homega hB p.1 p.2 -
      (1 / 2 : ℂ) *
        suzukiFixedWindowPhiJointPoint epsilon omega B homega hB p.1 p.2)) (b, x)
  exact (hxCast.inv₀ (by exact_mod_cast hx0.ne')).mul hinner

/-- Spatial partial derivative of the joint point field, proved from the independently established
spatial derivative and exact pointwise equation (413). -/
theorem hasDerivAt_suzukiFixedWindowPhiJointPoint_spatial
    (epsilon : SuzukiHankelSign) {omega B R b x : ℝ}
    (homega : 1 < omega) (hB : 1 < B) (hR : 0 ≤ R)
    (hb1 : 1 < b) (hbB : b < B) (hx0 : 0 < x) (hxB : x < B)
    (hbR : Real.log b + Real.log B < R)
    (hregular : ∀ n : ℕ, b * x ≠ (n : ℝ)) :
    HasDerivAt
      (suzukiFixedWindowPhiJointPoint epsilon omega B homega hB b)
      (suzukiFixedWindowPhiJointSpatialDerivative
        epsilon omega B R homega hB b x) x := by
  have hxRegular : x ∈ SuzukiHankelRegularX b := by
    refine ⟨hx0, ?_⟩
    intro n hxn
    apply hregular n
    apply (eq_div_iff (ne_of_gt (lt_trans zero_lt_one hb1))).1 at hxn
    simpa only [mul_comm] using hxn
  have hglobal :=
    ((contDiffAt_one_suzukiHankelPhiGlobal_of_regular
      epsilon homega hb1 hxRegular).differentiableAt (by norm_num)).hasDerivAt
  have hev : (fun z : ℝ =>
      suzukiFixedWindowPhiJointPoint epsilon omega B homega hB b z) =ᶠ[𝓝 x]
      suzukiHankelPhiGlobal epsilon omega b homega hb1 := by
    filter_upwards [Ioo_mem_nhds hx0 hxB] with z hz
    exact suzukiFixedWindowPhiJointPoint_eq_global
      epsilon homega hB hb1 hbB hz.1 hz.2.le
  have hlocal := hglobal.congr_of_eventuallyEq hev
  let xB : ClosedInterval 0 B := ⟨x, ⟨hx0.le, hxB.le⟩⟩
  have h413 := suzuki_equation_413_fixedWindow
    epsilon.opposite homega hB hb1 hbB xB hxRegular
  have hdEq := suzukiFixedWindowPhiPointApertureDerivative_eq_joint
    epsilon.opposite homega hB hR (lt_trans zero_lt_one hb1) hbB hx0 hxB.le hbR hregular
  have hPEq := suzukiFixedWindowPhiJointPoint_eq_global
    epsilon homega hB hb1 hbB hx0 hxB.le
  have hPopEq := suzukiFixedWindowPhiJointPoint_eq_global
    epsilon.opposite homega hB hb1 hbB hx0 hxB.le
  have hmuEq := suzukiHankelMuReal_of_one_lt homega hb1
  have h413' : (b : ℂ) *
        suzukiFixedWindowPhiPointApertureDerivative epsilon.opposite omega B homega hB
          b (by linarith) hbB xB +
        ((1 / 2 : ℂ) + epsilon.opposite.coeff * suzukiHankelMu omega b homega hb1) *
          suzukiHankelPhiGlobal epsilon.opposite omega b homega hb1 x =
        (x : ℂ) * deriv (suzukiHankelPhiGlobal epsilon omega b homega hb1) x +
          (1 / 2 : ℂ) * suzukiHankelPhiGlobal epsilon omega b homega hb1 x := by
    simpa only [SuzukiHankelSign.opposite_opposite, suzukiHankelEulerPhi, xB] using h413
  have h413Joint : (b : ℂ) *
        suzukiFixedWindowPhiJointApertureDerivative
          epsilon.opposite omega B R homega hB b x +
      ((1 / 2 : ℂ) + epsilon.opposite.coeff * suzukiHankelMu omega b homega hb1) *
        suzukiFixedWindowPhiJointPoint epsilon.opposite omega B homega hB b x =
      (x : ℂ) * deriv (suzukiHankelPhiGlobal epsilon omega b homega hb1) x +
        (1 / 2 : ℂ) *
          suzukiFixedWindowPhiJointPoint epsilon omega B homega hB b x := by
    rw [← hdEq, hPopEq, hPEq]
    simpa only [xB] using h413'
  have hcoeff : suzukiFixedWindowPhiJointSpatialDerivative
      epsilon omega B R homega hB b x =
      deriv (suzukiHankelPhiGlobal epsilon omega b homega hb1) x := by
    rw [suzukiFixedWindowPhiJointSpatialDerivative, hmuEq]
    have hxne : (x : ℂ) ≠ 0 := by exact_mod_cast hx0.ne'
    rw [inv_mul_eq_iff_eq_mul₀ hxne]
    linear_combination h413Joint
  rw [hcoeff]
  exact hlocal

/-! ## Diagonal assembly -/

/-- Natural numbers form a closed subset of the real line.  This explicit bridge is used to make
Suzuki's arithmetic regular locus an open set suitable for joint differentiation. -/
theorem isClosed_range_natCast_real :
    IsClosed (Set.range fun n : ℕ => (n : ℝ)) := by
  have heq : (Set.range fun n : ℕ => (n : ℝ)) =
      Set.range (Int.cast : ℤ → ℝ) ∩ Ici 0 := by
    ext y
    constructor
    · rintro ⟨n, rfl⟩
      exact ⟨⟨(n : ℤ), by simp⟩, by
        simpa only [mem_Ici] using Nat.cast_nonneg n⟩
    · rintro ⟨⟨z, rfl⟩, hz⟩
      have hzReal : (0 : ℝ) ≤ (z : ℝ) := by simpa only [mem_Ici] using hz
      have hzInt : 0 ≤ z := by exact_mod_cast hzReal
      refine ⟨z.toNat, ?_⟩
      change (z.toNat : ℝ) = (z : ℝ)
      exact_mod_cast Int.toNat_of_nonneg hzInt
  rw [heq]
  exact Real.isClosed_range_intCast.inter isClosed_Ici

/-- Open joint regularity box: physical apertures, positive spatial points, and no arithmetic
product cusp. -/
def suzukiFixedWindowJointRegularSet (B : ℝ) : Set (ℝ × ℝ) :=
  (Ioo 1 B ×ˢ Ioo 0 B) ∩
    (fun p : ℝ × ℝ => p.1 * p.2) ⁻¹'
      (Set.range fun n : ℕ => (n : ℝ))ᶜ

theorem isOpen_suzukiFixedWindowJointRegularSet (B : ℝ) :
    IsOpen (suzukiFixedWindowJointRegularSet B) := by
  exact (isOpen_Ioo.prod isOpen_Ioo).inter
    (isClosed_range_natCast_real.isOpen_compl.preimage
      (continuous_fst.mul continuous_snd))

/-- Each signed fixed-window boundary trace is `C¹` along the diagonal away from precisely the
square-root arithmetic locus printed by Suzuki. -/
theorem contDiffAt_one_suzukiFixedWindowPhiJointPoint_diagonal
    (epsilon : SuzukiHankelSign) {omega a : ℝ}
    (homega : 1 < omega) (ha1 : 1 < a)
    (hsquare : ∀ n : ℕ, a ≠ Real.sqrt n) :
    ContDiffAt ℝ 1 (fun b : ℝ =>
      suzukiFixedWindowPhiJointPoint epsilon omega (a + 1) homega
        (by linarith) b b) a := by
  let B := a + 1
  have haB : a < B := by dsimp only [B]; linarith
  have hB : 1 < B := ha1.trans haB
  let R := suzukiSourceLogExtensionHorizon B (Real.log B)
  have hR : 0 ≤ R := suzukiSourceLogExtensionHorizon_nonneg B (Real.log B)
  have hBR : Real.log B + Real.log B < R :=
    lt_suzukiSourceLogExtensionHorizon B (Real.log B)
  let W := suzukiFixedWindowJointRegularSet B
  let f := suzukiFixedWindowPhiJointPoint epsilon omega B homega hB
  let d₁ := suzukiFixedWindowPhiJointApertureDerivative epsilon omega B R homega hB
  let d₂ := suzukiFixedWindowPhiJointSpatialDerivative epsilon omega B R homega hB
  have hWopen : IsOpen W := isOpen_suzukiFixedWindowJointRegularSet B
  have haa : (a, a) ∈ W := by
    refine ⟨⟨⟨ha1, haB⟩, ⟨lt_trans zero_lt_one ha1, haB⟩⟩, ?_⟩
    intro hmem
    rcases hmem with ⟨n, hn⟩
    apply hsquare n
    have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hsqrt := Real.sq_sqrt hn0
    have hsqrt0 := Real.sqrt_nonneg (n : ℝ)
    norm_num only [Prod.fst, Prod.snd] at hn
    nlinarith
  have hlogR : ∀ {b : ℝ}, 0 < b → b < B → Real.log b + Real.log B < R := by
    intro b hb0 hbB
    have hlog : Real.log b < Real.log B :=
      Real.strictMonoOn_log hb0 (by linarith : 0 < B) hbB
    linarith
  have hparts₁ : ∀ p ∈ W,
      HasDerivAt (fun b : ℝ => f b p.2) (d₁ p.1 p.2) p.1 := by
    intro p hp
    rcases hp with ⟨⟨hpB, hpX⟩, hpReg⟩
    have hreg : ∀ n : ℕ, p.1 * p.2 ≠ (n : ℝ) := by
      intro n hn
      exact hpReg ⟨n, hn.symm⟩
    exact hasDerivAt_suzukiFixedWindowPhiJointPoint_aperture
      epsilon homega hB hR (lt_trans zero_lt_one hpB.1) hpB.2 hpX.1 hpX.2
        (hlogR (lt_trans zero_lt_one hpB.1) hpB.2) hreg
  have hparts₂ : ∀ p ∈ W,
      HasDerivAt (f p.1) (d₂ p.1 p.2) p.2 := by
    intro p hp
    rcases hp with ⟨⟨hpB, hpX⟩, hpReg⟩
    have hreg : ∀ n : ℕ, p.1 * p.2 ≠ (n : ℝ) := by
      intro n hn
      exact hpReg ⟨n, hn.symm⟩
    exact hasDerivAt_suzukiFixedWindowPhiJointPoint_spatial
      epsilon homega hB hR hpB.1 hpB.2 hpX.1 hpX.2
        (hlogR (lt_trans zero_lt_one hpB.1) hpB.2) hreg
  have hcont₁ : ContinuousOn (Function.uncurry d₁) W := by
    intro p hp
    rcases hp with ⟨⟨hpB, hpX⟩, hpReg⟩
    have hreg : ∀ n : ℕ, p.1 * p.2 ≠ (n : ℝ) := by
      intro n hn
      exact hpReg ⟨n, hn.symm⟩
    exact (continuousAt_suzukiFixedWindowPhiJointApertureDerivative
      epsilon homega hB (lt_trans zero_lt_one hpB.1) hpB.2 hpX.1 hreg).continuousWithinAt
  have hcont₂ : ContinuousOn (Function.uncurry d₂) W := by
    intro p hp
    rcases hp with ⟨⟨hpB, hpX⟩, hpReg⟩
    have hreg : ∀ n : ℕ, p.1 * p.2 ≠ (n : ℝ) := by
      intro n hn
      exact hpReg ⟨n, hn.symm⟩
    exact (continuousAt_suzukiFixedWindowPhiJointSpatialDerivative
      epsilon homega hB hpB.1 hpB.2 hpX.1 hreg).continuousWithinAt
  exact contDiffAt_one_diagonal_of_continuous_partials
    hWopen haa hparts₁ hparts₂ hcont₁ hcont₂

/-- Each literal signed boundary trace `a φ_a^ε(a)` is `C¹` at every point away from Suzuki's
square-root cusp locus. -/
theorem contDiffAt_one_suzukiHankelBoundaryTraceReal_of_regular
    (epsilon : SuzukiHankelSign) {omega a : ℝ}
    (homega : 1 < omega) (ha1 : 1 < a)
    (hsquare : ∀ n : ℕ, a ≠ Real.sqrt n) :
    ContDiffAt ℝ 1 (suzukiHankelBoundaryTraceReal epsilon omega homega) a := by
  let B := a + 1
  have haB : a < B := by dsimp only [B]; linarith
  have hB : 1 < B := ha1.trans haB
  have hdiag : ContDiffAt ℝ 1 (fun b : ℝ =>
      suzukiFixedWindowPhiJointPoint epsilon omega B homega hB b b) a := by
    simpa only [B, hB] using
      (contDiffAt_one_suzukiFixedWindowPhiJointPoint_diagonal
        epsilon homega ha1 hsquare)
  have hcast : ContDiffAt ℝ 1 (fun b : ℝ => (b : ℂ)) a :=
    (Complex.ofRealCLM.contDiff (n := 1)).contDiffAt
  have hmodel : ContDiffAt ℝ 1 (fun b : ℝ =>
      (b : ℂ) * suzukiFixedWindowPhiJointPoint epsilon omega B homega hB b b) a :=
    hcast.mul hdiag
  have hev : suzukiHankelBoundaryTraceReal epsilon omega homega =ᶠ[𝓝 a]
      fun b : ℝ => (b : ℂ) *
        suzukiFixedWindowPhiJointPoint epsilon omega B homega hB b b := by
    filter_upwards [Ioo_mem_nhds ha1 haB] with b hb
    rw [suzukiHankelBoundaryTraceReal_of_one_lt epsilon homega hb.1]
    rw [suzukiFixedWindowPhiJointPoint_eq_global
      epsilon homega hB hb.1 hb.2 (lt_trans zero_lt_one hb.1) hb.2.le]
  exact hmodel.congr_of_eventuallyEq hev

/-- Exact open locus on which Suzuki claims continuous differentiability of `μ`. -/
def SuzukiHankelMuRegularLocus : Set ℝ :=
  {a | 1 < a ∧ ∀ n : ℕ, a ≠ Real.sqrt n}

/-- Suzuki's coupling coefficient is `C¹` on the full printed regular locus, with no auxiliary
analytic hypotheses. -/
theorem contDiffOn_one_suzukiHankelMuReal
    {omega : ℝ} (homega : 1 < omega) :
    ContDiffOn ℝ 1 (suzukiHankelMuReal omega homega) SuzukiHankelMuRegularLocus := by
  intro a ha
  have hpos := contDiffAt_one_suzukiHankelBoundaryTraceReal_of_regular
    SuzukiHankelSign.positive homega ha.1 ha.2
  have hneg := contDiffAt_one_suzukiHankelBoundaryTraceReal_of_regular
    SuzukiHankelSign.negative homega ha.1 ha.2
  exact (hpos.add hneg).contDiffWithinAt

/-- Closed Lean formulation of the full regularity paragraph following Suzuki (2012), equation
(411): continuity on `(1,∞)`, right limit zero at `1`, and `C¹` regularity off `√ℕ`. -/
theorem suzuki_2012_mu_regularity
    {omega : ℝ} (homega : 1 < omega) :
    ContinuousOn (suzukiHankelMuReal omega homega) (Ioi 1) ∧
      Tendsto (suzukiHankelMuReal omega homega) (𝓝[Ioi 1] 1) (𝓝 0) ∧
      ContDiffOn ℝ 1 (suzukiHankelMuReal omega homega) SuzukiHankelMuRegularLocus := by
  exact ⟨continuousOn_suzukiHankelMuReal homega,
    tendsto_suzukiHankelMuReal_one_right homega,
    contDiffOn_one_suzukiHankelMuReal homega⟩

end RHTower
