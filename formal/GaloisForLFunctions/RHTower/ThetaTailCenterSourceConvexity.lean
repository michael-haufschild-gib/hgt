import GaloisForLFunctions.RHTower.ThetaTailSchurAxisExtension
import Mathlib.Analysis.Convex.Deriv

/-! Strict local convexity of the actual normalized center source deficit. -/

noncomputable section
open MeasureTheory Filter Topology Set
namespace RHTower.ThetaJoint
open ThetaConfluent ThetaCoordinate

local notation "k" => thetaCuspFullSource
local notation "k₁" => deriv thetaCuspFullSource
local notation "k₂" => deriv (deriv thetaCuspFullSource)
local notation "H" => thetaTailFirstMomentKernel
local notation "J" => thetaTailFirstMomentKernel 0 0
local notation "q" => thetaCuspLogCurvature 0

/-- The positive-node tail comparison survives at the center without losing its curvature. -/
theorem center_curvature_mass_le : q*J ≤ k 0^2 := by
  have hp0 : thetaCuspLogDecaySlope 0 = 0 := by
    simp only [thetaCuspLogDecaySlope,
      iteratedDeriv_thetaCuspLogSource_zero_of_odd (m := 1) ⟨0,rfl⟩, neg_zero]
  have hp : Tendsto (fun x => thetaCuspLogDecaySlope x/x) (𝓝[>] 0) (𝓝 q) := by
    simpa only [zero_add, hp0, sub_zero, smul_eq_mul, inv_mul_eq_div] using
      (hasDerivAt_thetaCuspLogDecaySlope 0).tendsto_slope_zero_right
  have hJ : Tendsto (fun x => H x x) (𝓝[>] 0) (𝓝 J) :=
    (source_kernel_continuous.comp (continuous_id.prodMk continuous_id)).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  have hk : Tendsto (fun x => k x^2) (𝓝[>] 0) (𝓝 (k 0^2)) :=
    (thetaCuspSchwartzReal.continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).pow 2
  apply le_of_tendsto_of_tendsto (hp.mul hJ) hk
  filter_upwards [self_mem_nhdsWithin] with x hx
  have h := ThetaTailTwoPoint.diagonal_tail_lt_source_square hx
  simpa only [ThetaTailTwoPoint.kernel_diag_eq_cut] using h.le

theorem center_source_gap_pos : 0 < 2*derivativeMass-q*J := by
  have h := centerEntry_pos
  unfold centerEntry at h
  linarith only [center_curvature_mass_le, h]

private theorem k_hasDerivAt (x : ℝ) : HasDerivAt k (k₁ x) x :=
  thetaCuspSchwartzReal.hasDerivAt x
private theorem k₁_hasDerivAt (x : ℝ) : HasDerivAt k₁ (k₂ x) x :=
  (SchwartzMap.derivCLM ℝ ℝ thetaCuspSchwartzReal).hasDerivAt x
private theorem k₁_zero : k₁ 0 = 0 := by
  simpa only [iteratedDeriv_one] using
    iteratedDeriv_thetaCuspFullSource_zero_of_odd (m := 1) ⟨0,rfl⟩
private theorem k_cont : Continuous k := thetaCuspSchwartzReal.continuous
private theorem k₁_cont : Continuous k₁ :=
  (SchwartzMap.derivCLM ℝ ℝ thetaCuspSchwartzReal).continuous
private theorem k₂_cont : Continuous k₂ :=
  (SchwartzMap.derivCLM ℝ ℝ (SchwartzMap.derivCLM ℝ ℝ thetaCuspSchwartzReal)).continuous

def sourceDeficit (y : ℝ) : ℝ := 1-k 0/J*(H 0 y/k y)
def sourceDeficitFirst (y : ℝ) : ℝ :=
  -k 0/J*((firstLeft y 0*k y-H 0 y*k₁ y)/k y^2)
def sourceDeficitSecond (y : ℝ) : ℝ :=
  -k 0/J*((secondLeft y 0*k y^2-2*firstLeft y 0*k y*k₁ y-
    H 0 y*k y*k₂ y+2*H 0 y*k₁ y^2)/k y^3)

theorem sourceDeficit_continuous : Continuous sourceDeficit :=
  continuous_const.sub
    (((source_kernel_continuous.comp (continuous_const.prodMk continuous_id)).div k_cont
      (fun y => (thetaCuspFullSource_pos_all y).ne')).const_mul (k 0/J))

theorem sourceDeficit_hasDerivAt (y : ℝ) :
    HasDerivAt sourceDeficit (sourceDeficitFirst y) y := by
  convert! (((source_hasDerivAt_right 0 y).div (k_hasDerivAt y)
    (thetaCuspFullSource_pos_all y).ne').const_mul (k 0/J)).const_sub 1 using 1
  simp only [sourceDeficitFirst]
  ring

theorem sourceDeficitFirst_hasDerivAt (y : ℝ) :
    HasDerivAt sourceDeficitFirst (sourceDeficitSecond y) y := by
  have hnum : HasDerivAt (fun y => firstLeft y 0*k y-H 0 y*k₁ y)
      (secondLeft y 0*k y-H 0 y*k₂ y) y := by
    convert! ((firstLeft_hasDerivAt_left y 0).mul (k_hasDerivAt y)).sub
      ((source_hasDerivAt_right 0 y).mul (k₁_hasDerivAt y)) using 1
    ring
  convert! (hnum.div ((k_hasDerivAt y).pow 2)
    (pow_ne_zero 2 (thetaCuspFullSource_pos_all y).ne')).const_mul (-k 0/J) using 1
  dsimp only [sourceDeficitSecond, Pi.pow_apply]
  field_simp [(thetaCuspFullSource_pos_all y).ne', centerMass_pos.ne']
  ring

theorem sourceDeficitFirst_continuous : Continuous sourceDeficitFirst :=
  continuous_iff_continuousAt.mpr fun y => (sourceDeficitFirst_hasDerivAt y).continuousAt

theorem sourceDeficitSecond_continuous : Continuous sourceDeficitSecond := by
  have hh : Continuous (H 0) := source_kernel_continuous.comp (continuous_const.prodMk continuous_id)
  have h₁ : Continuous fun y => firstLeft y 0 :=
    firstLeft_continuous.comp (continuous_id.prodMk continuous_const)
  have h₂ : Continuous fun y => secondLeft y 0 :=
    secondLeft_continuous.comp (continuous_id.prodMk continuous_const)
  exact (((((h₂.mul (k_cont.pow 2)).sub (((h₁.const_mul 2).mul k_cont).mul k₁_cont)).sub
    ((hh.mul k_cont).mul k₂_cont)).add ((hh.const_mul 2).mul (k₁_cont.pow 2))).div
      (k_cont.pow 3) (fun y => pow_ne_zero 3 (thetaCuspFullSource_pos_all y).ne')).const_mul (-k 0/J)

theorem sourceDeficit_zero : sourceDeficit 0 = 0 := by
  unfold sourceDeficit
  field_simp [(thetaCuspFullSource_pos_all 0).ne', centerMass_pos.ne']
  ring

theorem sourceDeficitFirst_zero : sourceDeficitFirst 0 = 0 := by
  simp [sourceDeficitFirst, firstLeft_origin, k₁_zero]

theorem sourceDeficitSecond_zero : sourceDeficitSecond 0 = (2*derivativeMass-q*J)/J := by
  simp only [sourceDeficitSecond, secondLeft_origin, firstLeft_origin, k₁_zero, source_second_center]
  field_simp [(thetaCuspFullSource_pos_all 0).ne', centerMass_pos.ne']
  ring

theorem sourceDeficitSecond_zero_pos : 0 < sourceDeficitSecond 0 := by
  rw [sourceDeficitSecond_zero]
  exact div_pos center_source_gap_pos centerMass_pos

private theorem local_convex_chord {f g h : ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g) (hh : Continuous h)
    (df : ∀ x, HasDerivAt f (g x) x) (dg : ∀ x, HasDerivAt g (h x) x)
    (hf0 : f 0 = 0) (hg0 : g 0 = 0) (hh0 : 0 < h 0) :
    ∃ e > 0, ∀ x y : ℝ, 0 < x → x < y → y < e → 0 < f x ∧ y*f x ≤ x*f y := by
  have ht : Tendsto h (𝓝 0) (𝓝 (h 0)) := hh.continuousAt
  obtain ⟨e,he,hs⟩ := Metric.eventually_nhds_iff.mp ((tendsto_order.1 ht).1 0 hh0)
  have hp (t : ℝ) (ht0 : 0 ≤ t) (hte : t < e) : 0 < h t := by
    apply hs
    simpa only [Real.dist_eq, sub_zero, abs_of_nonneg ht0] using hte
  have hgm : StrictMonoOn g (Icc 0 e) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 e) hg.continuousOn
    intro t ht
    have ht' : 0 < t ∧ t < e := by simpa only [interior_Icc, mem_Ioo] using ht
    rw [(dg t).deriv]
    exact hp t ht'.1.le ht'.2
  have hgp (t : ℝ) (ht0 : 0 < t) (hte : t < e) : 0 < g t := by
    simpa only [hg0] using hgm ⟨le_rfl,he.le⟩ ⟨ht0.le,hte.le⟩ ht0
  have hfm : StrictMonoOn f (Icc 0 e) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 e) hf.continuousOn
    intro t ht
    have ht' : 0 < t ∧ t < e := by simpa only [interior_Icc, mem_Ioo] using ht
    rw [(df t).deriv]
    exact hgp t ht'.1 ht'.2
  have hc : ConvexOn ℝ (Icc 0 e) f := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (f' := g) (f'' := h)
      (convex_Icc 0 e) hf.continuousOn
      (fun t _ => (df t).hasDerivWithinAt) (fun t _ => (dg t).hasDerivWithinAt)
    intro t ht
    have ht' : 0 < t ∧ t < e := by simpa only [interior_Icc, mem_Ioo] using ht
    exact (hp t ht'.1.le ht'.2).le
  refine ⟨e,he,?_⟩
  intro x y hx hxy hye
  have hy : 0 < y := hx.trans hxy
  have hab : 0 ≤ 1-x/y := sub_nonneg.mpr ((div_le_one hy).mpr hxy.le)
  have h := hc.2 ⟨le_rfl,he.le⟩ ⟨hy.le,hye.le⟩ hab (div_nonneg hx.le hy.le)
    (by ring : 1-x/y+x/y=1)
  have heq : (x/y)*y=x := by field_simp
  simp only [smul_eq_mul, hf0, mul_zero, zero_add, heq] at h
  have hle := mul_le_mul_of_nonneg_left h hy.le
  constructor
  · simpa only [hf0] using hfm ⟨le_rfl,he.le⟩ ⟨hx.le,(hxy.trans hye).le⟩ hx
  · calc y*f x ≤ y*(x/y*f y) := hle
         _ = x*f y := by field_simp

/-- A single center neighborhood has a positive source deficit and its convex chord inequality. -/
theorem exists_sourceDeficit_chord :
    ∃ e > 0, ∀ z y : ℝ, 0 < z → z < y → y < e →
      0 < sourceDeficit z ∧ y*sourceDeficit z ≤ z*sourceDeficit y :=
  local_convex_chord sourceDeficit_continuous sourceDeficitFirst_continuous
    sourceDeficitSecond_continuous sourceDeficit_hasDerivAt sourceDeficitFirst_hasDerivAt
    sourceDeficit_zero sourceDeficitFirst_zero sourceDeficitSecond_zero_pos

end RHTower.ThetaJoint
