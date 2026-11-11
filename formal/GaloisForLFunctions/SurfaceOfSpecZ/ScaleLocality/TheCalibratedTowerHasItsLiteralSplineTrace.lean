import GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality.TheCalibratedTowerHasLogarithmicLocalCounts

/-!
# Literal spline trace of the calibrated tower

The squared transform of `boxSpline 1 3` is `sinc⁸`. Reindexing its
absolutely convergent zero sum by levels therefore gives exactly the
calibrated reflected blocks, with the coefficient masses used in the
sparse tower construction.
-/

open Complex Filter Set Topology

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality
open ArithmeticOrientationGeometry ArithmeticCastelnuovoSeveri SquareRootThreshold Zeta23
namespace CalibratedWindowTower.Tower

variable {γmin C Θ : ℝ} {R : ℝ → ℝ} (W : Tower γmin C Θ R)

def exponent (j : ℕ) : Fin ((W.block j).k + 1) × Bool → ℂ :=
  calibratedReflectedExponent (calibratedDepthCenter Θ j) (W.block j).z

def weight (j : ℕ) : ℝ := splineBlockWeight (W.exponent j)

def blockTrace (j : ℕ) (u : ℝ) : ℝ := 2 * (splineExponentialBlock (W.exponent j) u).re

def right (j : ℕ) : ℝ := (W.block j).T + R (W.block j).T

theorem weight_nonneg (j : ℕ) : 0 ≤ W.weight j := splineBlockWeight_nonneg _

/-- The actual spline mass satisfies the bound used when selecting the blocks. -/
theorem weight_le_bound (hΘ : 0 < Θ) (hΘ2 : Θ ≤ 1 / 2) (j : ℕ) :
    W.weight j ≤ 524288 * Real.exp 4 * ((W.block j).k : ℝ) / (W.block j).Γ ^ 2 := by
  have hΓ : 0 < (W.block j).Γ := by linarith only [(W.block j).four_le]
  have hΓ1 : 1 ≤ (W.block j).Γ := by linarith only [(W.block j).four_le]
  have hη := (calibratedDepth_bounds hΘ j).1
  have hd := (calibratedDepth_bounds hΘ j).2.1
  have hu := (calibratedDepth_bounds hΘ j).2.2.1
  have hgeom := calibratedReflectedExponent_geometry (W.block j).z hη.le
    (by linarith only [hd]) hu.le (fun i => ((W.block j).geometry i).1)
  have hw : ∀ p, |(W.exponent j p).re| ≤ 1 / 2 := fun p =>
    (W.exponent_abs_re_le hΘ j p).trans ((calibratedDepth_bounds hΘ j).2.2.2.le.trans hΘ2)
  have him : ∀ p, (W.block j).Γ / 2 ≤ (W.exponent j p).im := by
    intro p
    rw [(hgeom p).1]
    exact ((W.block j).geometry p.1).2.1
  have hh := splineBlockWeight_le hΓ (W.exponent j) hw him
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool] at hh
  push_cast at hh
  have hk1 : (1 : ℝ) ≤ (W.block j).k := by exact_mod_cast (W.block j).degree_pos
  have hnum : 131072 * Real.exp 4 * (((W.block j).k + 1 : ℝ) * 2) ≤
      524288 * Real.exp 4 * ((W.block j).k : ℝ) := by
    have he := Real.exp_pos (4 : ℝ)
    nlinarith only [mul_nonneg he.le (sub_nonneg.mpr hk1)]
  have hpow : (W.block j).Γ ^ 2 ≤ (W.block j).Γ ^ 8 := by
    calc
      _ = (W.block j).Γ ^ 2 * 1 := by ring
      _ ≤ (W.block j).Γ ^ 2 * (W.block j).Γ ^ 6 :=
        mul_le_mul_of_nonneg_left (one_le_pow₀ hΓ1) (sq_nonneg _)
      _ = _ := by ring
  exact hh.trans ((div_le_div_of_nonneg_right hnum (by positivity)).trans
    (div_le_div_of_nonneg_left (by positivity) (by positivity) hpow))

theorem weight_zero_le (hΘ : 0 < Θ) (hΘ2 : Θ ≤ 1 / 2) : W.weight 0 ≤ 1 :=
  (W.weight_le_bound hΘ hΘ2 0).trans W.weight_zero

theorem weight_succ_le (hΘ : 0 < Θ) (hΘ2 : Θ ≤ 1 / 2) (j : ℕ) :
    W.weight (j + 1) ≤ (1 / 2 : ℝ) ^ (j + 1) * Real.exp (-(Θ * W.right j)) :=
  (W.weight_le_bound hΘ hΘ2 (j + 1)).trans (W.weight_succ j)

theorem right_nonneg (hR0 : ∀ T, 0 ≤ R T) (j : ℕ) : 0 ≤ W.right j := by
  have hh := (W.block j).left_le
  have hr := hR0 (W.block j).T
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  dsimp only [right]
  linarith only [hh, hr, hj]

theorem monotone_right (hR0 : ∀ T, 0 ≤ R T) : Monotone W.right := by
  apply monotone_nat_of_le_succ
  intro j
  have hh := W.window_gap j
  have hr := hR0 (W.block (j + 1)).T
  dsimp only [right]
  linarith only [hh, hr]

/-- The complete configuration trace is the sum of its literal finite spline blocks. -/
theorem two_re_lagStructure_config (hΘ : 0 < Θ) (hΘ2 : Θ ≤ 1 / 2) (u : ℝ) :
    2 * (lagStructure (W.config hΘ hΘ2) (boxSpline 1 3) u).re = ∑' j, W.blockTrace j u := by
  classical
  let Z := W.config hΘ hΘ2
  have hs := summable_lagStructure Z (W.temperedConfig_config hΘ hΘ2)
    (SplineTower.contDiff_two_boxSpline (o := 3) le_rfl) (boxSpline_support (r := 1) one_pos 3) u
  let e := Equiv.ofInjective W.pt (W.pt_injective hΘ)
  let F : W.Idx → ℂ := fun p =>
    paperFT (EF.weilTest (boxSpline 1 3) (boxSpline 1 3)) (gammaOf (W.pt p)) *
      Complex.exp (I * gammaOf (W.pt p) * u)
  have hcomp : ∀ p, ((Z.mult (e p) : ℂ) *
      paperFT (EF.weilTest (boxSpline 1 3) (boxSpline 1 3)) (gammaOf (e p)) *
      Complex.exp (I * gammaOf (e p) * u)) = F p := by
    intro p
    simp [Z, config, e, F]
  have hS : HasSum F (lagStructure Z (boxSpline 1 3) u) := by
    have hh := (e.hasSum_iff).mpr hs.hasSum
    simpa only [Function.comp_def, hcomp] using hh
  have hI (w : ℂ) : I * (-I * w) = w := by
    rw [← mul_assoc, mul_neg, I_mul_I]
    ring
  have hfib : ∀ j, HasSum (fun p : Fin ((W.block j).k + 1) × Bool => F ⟨j, p⟩)
      (splineExponentialBlock (W.exponent j) u) := by
    intro j
    have hh := hasSum_fintype (fun p : Fin ((W.block j).k + 1) × Bool => F ⟨j, p⟩)
    simpa only [F, W.gammaOf_pt, SplineTower.paperFT_weilTest_spline (o := 3) le_rfl,
      show 2 * (3 + 1) = 8 by rfl, hI, exponent, splineExponentialBlock] using hh
  have hG := hS.sigma hfib
  have hre := (Complex.reCLM.hasSum hG).mul_left 2
  simpa only [Complex.reCLM_apply, blockTrace] using hre.tsum_eq.symm

end CalibratedWindowTower.Tower
end GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality
