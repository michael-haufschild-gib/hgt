import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheDepthCenteredCameraPaysItsExteriorMass
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# The persistent exterior mass is exactly the boundary-depth mass

At a fixed centre and width, increasing lag damps every submaximal-depth
zero. The multiplicity-weighted Lorentzian majorant is summable, so no
uniform depth gap is needed. Only maximal-depth exterior zeros survive.
-/

noncomputable section

open Complex Set MeasureTheory Filter Topology
open RHTower Zeta23

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

open SquareRootThreshold (zetaZeroWidth)

/-- Complete exterior norm mass, including every zero multiplicity. -/
def widthCenteredExteriorMass (v : ℝ → ℝ) (δ t : ℝ)
    (s : Finset zetaZeroConfig.carrier) (y : ℝ) : ℝ := by
  classical
  exact ∑' q : zetaZeroConfig.carrier, if q ∈ s then 0 else
    (zetaZeroConfig.mult q : ℝ) *
      ‖paperFT (depthCenteredCamera v zetaZeroWidth δ y) (gammaOf q - t)‖

/-- The part of exterior mass supported on the maximal-depth line. -/
def widthBoundaryExteriorMass (v : ℝ → ℝ) (δ t : ℝ)
    (s : Finset zetaZeroConfig.carrier) : ℝ := by
  classical
  exact ∑' q : zetaZeroConfig.carrier, if q ∈ s then 0 else
    if (q : ℂ).re - 1 / 2 = zetaZeroWidth then
      (zetaZeroConfig.mult q : ℝ) *
        ‖paperFT (depthCenteredCamera v zetaZeroWidth δ δ) (gammaOf q - t)‖
    else 0

/-- Translation changes each centered Fourier norm by its relative-depth exponential. -/
theorem norm_depthCenteredCamera_add_lag
    {v : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ) (b t u : ℝ) (q : ℂ) :
    ‖paperFT (depthCenteredCamera v b δ (δ + u)) (gammaOf q - t)‖ =
      Real.exp ((q.re - 1 / 2 - b) * u) *
        ‖paperFT (depthCenteredCamera v b δ δ) (gammaOf q - t)‖ := by
  have hz : (gammaOf (q - (b : ℂ)) - (t : ℂ)).im = b - (q.re - 1 / 2) := by
    simp [ZeroConfigurationGeometry.gammaOf_eq, ZeroConfigurationGeometry.depth]
    ring
  simp only [paperFT_depthCenteredCamera, paperFT_cameraTest hδ,
    norm_mul, norm_cexp_I_mul, hz]
  rw [show -((b - (q.re - 1 / 2)) * (δ + u)) =
    (q.re - 1 / 2 - b) * u + -((b - (q.re - 1 / 2)) * δ) by ring, Real.exp_add]
  ring

/-- The exterior's full norm mass converges to its boundary-depth projection.
There is no isolation or common depth-gap premise. -/
theorem tendsto_widthCenteredExteriorMass
    {v : ℝ → ℝ} (hv : ContDiff ℝ 2 v) (hsupp : ∀ u, v u ≠ 0 → |u| ≤ 1)
    {δ : ℝ} (hδ : 1 ≤ δ) (t : ℝ) (s : Finset zetaZeroConfig.carrier) :
    Tendsto (widthCenteredExteriorMass v δ t s) atTop
      (𝓝 (widthBoundaryExteriorMass v δ t s)) := by
  classical
  let term := fun (u : ℝ) (q : zetaZeroConfig.carrier) =>
    if q ∈ s then 0 else (zetaZeroConfig.mult q : ℝ) *
      ‖paperFT (depthCenteredCamera v zetaZeroWidth δ (δ + u)) (gammaOf q - t)‖
  let boundary := fun q : zetaZeroConfig.carrier =>
    if q ∈ s then 0 else if (q : ℂ).re - 1 / 2 = zetaZeroWidth then
      (zetaZeroConfig.mult q : ℝ) *
        ‖paperFT (depthCenteredCamera v zetaZeroWidth δ δ) (gammaOf q - t)‖ else 0
  have hδ0 : 0 < δ := one_pos.trans_le hδ
  have hwidth (q : zetaZeroConfig.carrier) : (q : ℂ).re - 1 / 2 ≤ zetaZeroWidth :=
    (le_abs_self _).trans (SquareRootThreshold.abs_re_sub_half_le_zetaZeroWidth q.2)
  have hs := (summable_mult_lorentzKernel hδ t).mul_left (profileMass v)
  have hpt (q : zetaZeroConfig.carrier) :
      Tendsto (fun u : ℝ => term u q) atTop (𝓝 (boundary q)) := by
    by_cases hq : q ∈ s
    · simpa only [term, boundary, hq, if_true] using
        (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) atTop (𝓝 0))
    by_cases he : (q : ℂ).re - 1 / 2 = zetaZeroWidth
    · simpa only [term, boundary, hq, if_false, he, if_true,
        norm_depthCenteredCamera_add_lag hδ0, sub_self, zero_mul,
        Real.exp_zero, one_mul] using
        (tendsto_const_nhds : Tendsto (fun _ : ℝ => (zetaZeroConfig.mult q : ℝ) *
          ‖paperFT (depthCenteredCamera v zetaZeroWidth δ δ) (gammaOf q - t)‖)
          atTop (𝓝 _))
    · have hp : 0 < zetaZeroWidth - ((q : ℂ).re - 1 / 2) :=
        sub_pos.mpr (lt_of_le_of_ne (hwidth q) he)
      have hl := Real.tendsto_exp_atBot.comp
        (tendsto_neg_atTop_atBot.comp (Tendsto.const_mul_atTop hp tendsto_id))
      have hlim : Tendsto (fun u : ℝ =>
          Real.exp (((q : ℂ).re - 1 / 2 - zetaZeroWidth) * u)) atTop (𝓝 0) := by
        apply hl.congr
        intro u
        change Real.exp (-((zetaZeroWidth - ((q : ℂ).re - 1 / 2)) * u)) = _
        congr 1
        ring
      have hm := (hlim.mul_const
        ‖paperFT (depthCenteredCamera v zetaZeroWidth δ δ) (gammaOf q - t)‖).const_mul
          (zetaZeroConfig.mult q : ℝ)
      simpa only [term, boundary, hq, he, if_false,
        norm_depthCenteredCamera_add_lag hδ0, mul_zero, zero_mul] using hm
  have hdom : ∀ᶠ u : ℝ in atTop, ∀ q : zetaZeroConfig.carrier,
      ‖term u q‖ ≤ profileMass v *
        ((zetaZeroConfig.mult q : ℝ) * lorentzKernel δ ((q : ℂ).im - t)) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with u hu q
    by_cases hq : q ∈ s
    · simp only [term, hq, if_true, norm_zero]
      exact mul_nonneg (profileMass_nonneg v)
        (mul_nonneg (Nat.cast_nonneg _) (lorentzKernel_nonneg _ _))
    · simp only [term, hq, if_false, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _))]
      have hb := mul_le_mul_of_nonneg_left
        (norm_paperFT_widthCenteredCamera_le hv hsupp hδ0
          (by linarith only [hu] : δ ≤ δ + u) q (t := t))
        (Nat.cast_nonneg (zetaZeroConfig.mult q))
      simpa only [mul_assoc, mul_left_comm, mul_comm] using hb
  have hlim : Tendsto (fun u : ℝ => widthCenteredExteriorMass v δ t s (δ + u))
      atTop (𝓝 (widthBoundaryExteriorMass v δ t s)) :=
    tendsto_tsum_of_dominated_convergence hs hpt hdom
  have hsub : Tendsto (fun y : ℝ => y - δ) atTop atTop := by
    apply tendsto_atTop.mpr
    intro B
    filter_upwards [eventually_ge_atTop (B + δ)] with y hy
    linarith only [hy]
  apply (hlim.comp hsub).congr
  intro y
  change widthCenteredExteriorMass v δ t s (δ + (y - δ)) =
    widthCenteredExteriorMass v δ t s y
  rw [show δ + (y - δ) = y by ring]

/-- Every tolerance above the persistent boundary mass eventually bounds
all finite exterior sums at once. -/
theorem eventually_sum_widthCenteredCamera_exterior_lt_of_boundary_lt
    {v : ℝ → ℝ} (hv : ContDiff ℝ 2 v) (hsupp : ∀ u, v u ≠ 0 → |u| ≤ 1)
    {δ : ℝ} (hδ : 1 ≤ δ) (t : ℝ) (s : Finset zetaZeroConfig.carrier)
    {ε : ℝ} (hε : widthBoundaryExteriorMass v δ t s < ε) :
    ∀ᶠ y : ℝ in atTop, ∀ F : Finset zetaZeroConfig.carrier, Disjoint F s →
      (∑ q ∈ F, (zetaZeroConfig.mult q : ℝ) *
        ‖paperFT (depthCenteredCamera v zetaZeroWidth δ y) (gammaOf q - t)‖) < ε := by
  classical
  have hlim := tendsto_widthCenteredExteriorMass hv hsupp hδ t s
  filter_upwards [hlim.eventually (gt_mem_nhds hε), eventually_ge_atTop δ]
    with y hy hyδ F hF
  let w := fun q : zetaZeroConfig.carrier => (zetaZeroConfig.mult q : ℝ) *
    ‖paperFT (depthCenteredCamera v zetaZeroWidth δ y) (gammaOf q - t)‖
  let f := fun q : zetaZeroConfig.carrier => if q ∈ s then 0 else w q
  have hw0 (q : zetaZeroConfig.carrier) : 0 ≤ w q :=
    mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)
  have hw : Summable w := by
    simpa only [w, norm_mul, Complex.norm_natCast] using
      (summable_widthCenteredCamera hv hsupp hδ hyδ (t := t)).norm
  have hf0 (q : zetaZeroConfig.carrier) : 0 ≤ f q := by
    dsimp only [f]
    split_ifs
    · exact le_refl 0
    · exact hw0 q
  have hf : Summable f := hw.of_nonneg_of_le hf0 fun q => by
    dsimp only [f]
    split_ifs
    · exact hw0 q
    · exact le_refl _
  calc
    _ = ∑ q ∈ F, f q := by
      apply Finset.sum_congr rfl
      intro q hq
      exact (if_neg (fun hqs => Finset.disjoint_left.mp hF hq hqs)).symm
    _ ≤ ∑' q, f q := hf.sum_le_tsum F (fun q _ => hf0 q)
    _ < ε := hy

/-- Vanishing exterior mass is equivalent to vanishing boundary exterior mass. -/
theorem tendsto_widthCenteredExteriorMass_zero_iff
    {v : ℝ → ℝ} (hv : ContDiff ℝ 2 v) (hsupp : ∀ u, v u ≠ 0 → |u| ≤ 1)
    {δ : ℝ} (hδ : 1 ≤ δ) (t : ℝ) (s : Finset zetaZeroConfig.carrier) :
    Tendsto (widthCenteredExteriorMass v δ t s) atTop (𝓝 0) ↔
      widthBoundaryExteriorMass v δ t s = 0 := by
  have hlim := tendsto_widthCenteredExteriorMass hv hsupp hδ t s
  constructor
  · intro hz
    exact tendsto_nhds_unique hlim hz
  · intro hz
    simpa only [hz] using hlim

/-- Capturing the entire maximal-depth line pays all exterior mass at
large lag, even when lower depths have no uniform separation from it. -/
theorem tendsto_widthCenteredExteriorMass_zero_of_boundary_subset
    {v : ℝ → ℝ} (hv : ContDiff ℝ 2 v) (hsupp : ∀ u, v u ≠ 0 → |u| ≤ 1)
    {δ : ℝ} (hδ : 1 ≤ δ) (t : ℝ) (s : Finset zetaZeroConfig.carrier)
    (hcore : ∀ q : zetaZeroConfig.carrier,
      (q : ℂ).re - 1 / 2 = zetaZeroWidth → q ∈ s) :
    Tendsto (widthCenteredExteriorMass v δ t s) atTop (𝓝 0) := by
  classical
  apply (tendsto_widthCenteredExteriorMass_zero_iff hv hsupp hδ t s).mpr
  unfold widthBoundaryExteriorMass
  calc
    _ = ∑' _q : zetaZeroConfig.carrier, (0 : ℝ) := by
      apply tsum_congr
      intro q
      by_cases hq : q ∈ s
      · simp only [hq, if_true]
      · simp only [hq, if_false, show (q : ℂ).re - 1 / 2 ≠ zetaZeroWidth from
          fun he => hq (hcore q he)]
    _ = 0 := tsum_zero

end GaloisForLFunctions.MultiscaleMollifiedZetaField
