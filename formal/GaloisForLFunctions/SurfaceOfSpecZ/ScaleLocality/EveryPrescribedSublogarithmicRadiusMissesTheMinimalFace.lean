import GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality.TheCalibratedTowerHasItsLiteralSplineTrace

/-!
# Every prescribed sublogarithmic radius misses the minimal face

Self-consistent interpolation blocks produce positive windows for any
prescribed nonnegative `R(T)=o(log T)`. The sparse reflected tower is a
simple tempered configuration in the required logarithmic density class,
with an unattained positive top and window floors tending to infinity.
-/

open Complex Filter Set Topology

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality
open ArithmeticOrientationGeometry ArithmeticCastelnuovoSeveri SquareRootThreshold Zeta23
namespace CalibratedWindowTower.Tower

variable {γmin C Θ : ℝ} {R : ℝ → ℝ} (W : Tower γmin C Θ R)

private theorem weight_le_one (hΘ : 0 < Θ) (hΘ2 : Θ ≤ 1 / 2)
    (hR0 : ∀ T, 0 ≤ R T) (j : ℕ) : W.weight j ≤ 1 := by
  cases j with
  | zero => exact W.weight_zero_le hΘ hΘ2
  | succ j =>
    have hp : (1 / 2 : ℝ) ^ (j + 1) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have he : Real.exp (-(Θ * W.right j)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hΘ.le (W.right_nonneg hR0 j)))
    exact (W.weight_succ_le hΘ hΘ2 j).trans (by
      simpa only [one_mul] using mul_le_mul hp he (Real.exp_pos _).le zero_le_one)

/-- The selected block dominates the previous upper depth throughout its prescribed window. -/
private theorem normalized_block_dominates (hΘ : 0 < Θ) (hΘ2 : Θ ≤ 1 / 2)
    (hR0 : ∀ T, 0 ≤ R T) (j : ℕ) {u : ℝ}
    (hu : |u - (W.block (j + 1)).T| ≤ R (W.block (j + 1)).T) :
    (j : ℝ) + 10 ≤ Real.exp
      ((calibratedDepthUpper Θ (j + 1) - calibratedDepthUpper Θ j) * u) *
        (Real.exp (-(calibratedDepthUpper Θ (j + 1) * u)) * W.blockTrace (j + 1) u) := by
  have hul : (W.block (j + 1)).T - R (W.block (j + 1)).T ≤ u := by
    linarith only [(abs_le.mp hu).1]
  have hu0 : 0 ≤ u := by
    have hh := (W.block (j + 1)).left_le
    have hj : (0 : ℝ) ≤ j + 1 := by positivity
    linarith only [hul, hh, hj]
  obtain ⟨hη, hlo, _, _⟩ := calibratedDepth_bounds hΘ (j + 1)
  have htvu : (W.block (j + 1)).T + (u - (W.block (j + 1)).T) = u := by ring
  have hfinite := two_re_reflected_calibrated_block_ge (W.block (j + 1)).z hη.le
    (by linarith only [hlo]) (fun i => ((W.block (j + 1)).geometry i).1
    (T := (W.block (j + 1)).T) (v := u - (W.block (j + 1)).T)
    (by simpa only [htvu] using hu0) hu (W.block (j + 1)).positive
  have hfinite' : (3 / 2 : ℝ) * Real.exp (calibratedDepthCenter Θ (j + 1) * (u - 8)) -
      W.weight (j + 1) ≤ W.blockTrace (j + 1) u := by
    simpa only [htvu, weight, blockTrace, exponent] using hfinite
  let b := calibratedDepthUpper Θ j
  let x := calibratedDepthCenter Θ (j + 1)
  have hb0 : 0 ≤ b := SplineTower.depth_nonneg hΘ _
  have hgap : 0 < x - b := sub_pos.mpr (calibratedDepthUpper_lt_next_center hΘ j)
  have hexp : Real.exp (-(b * u)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hb0 hu0))
  have hw : Real.exp (-(b * u)) * W.weight (j + 1) ≤ 1 := by
    simpa only [one_mul] using mul_le_mul hexp (W.weight_le_one hΘ hΘ2 hR0 (j + 1))
      (W.weight_nonneg (j + 1)) zero_le_one
  have hgain : (j : ℝ) + 12 ≤ (3 / 2 : ℝ) * Real.exp ((x - b) * u - 8 * x) :=
    (W.gain j).trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (sub_le_sub_right (mul_le_mul_of_nonneg_left hul hgap.le) _))
      (by norm_num))
  have hm := mul_le_mul_of_nonneg_left hfinite' (Real.exp_pos (-(b * u))).le
  have hp : Real.exp (-(b * u)) * Real.exp (x * (u - 8)) =
      Real.exp ((x - b) * u - 8 * x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hm' : (3 / 2 : ℝ) * Real.exp ((x - b) * u - 8 * x) -
      Real.exp (-(b * u)) * W.weight (j + 1) ≤
        Real.exp (-(b * u)) * W.blockTrace (j + 1) u := by
    convert hm using 1
    rw [mul_sub]
    rw [show Real.exp (-(b * u)) * ((3 / 2 : ℝ) * Real.exp (x * (u - 8))) =
      (3 / 2 : ℝ) * (Real.exp (-(b * u)) * Real.exp (x * (u - 8))) by ring, hp]
  have he : Real.exp ((calibratedDepthUpper Θ (j + 1) - calibratedDepthUpper Θ j) * u) *
      (Real.exp (-(calibratedDepthUpper Θ (j + 1) * u)) * W.blockTrace (j + 1) u) =
        Real.exp (-(b * u)) * W.blockTrace (j + 1) u := by
    rw [← mul_assoc, ← Real.exp_add]
    congr 2
    dsimp only [b]
    ring
  rw [he]
  linarith only [hm', hgain, hw]

/-- The whole trace exceeds the level index throughout the selected window. -/
theorem window_floor (hΘ : 0 < Θ) (hΘ2 : Θ ≤ 1 / 2)
    (hR0 : ∀ T, 0 ≤ R T) (j : ℕ) {u : ℝ}
    (hu : |u - (W.block (j + 1)).T| ≤ R (W.block (j + 1)).T) :
    (j : ℝ) + 1 ≤ 2 * (lagStructure (W.config hΘ hΘ2) (boxSpline 1 3) u).re := by
  let a : ℕ → ℝ := fun k => Real.exp (-(calibratedDepthUpper Θ k * u)) * W.blockTrace k u
  have hul : (W.block (j + 1)).T - R (W.block (j + 1)).T ≤ u := by
    linarith only [(abs_le.mp hu).1]
  have hu0 : 0 ≤ u := by
    have hh := (W.block (j + 1)).left_le
    have hj : (0 : ℝ) ≤ j + 1 := by positivity
    linarith only [hul, hh, hj]
  have hur : u ≤ W.right (j + 1) := by
    dsimp only [right]
    linarith only [(abs_le.mp hu).2]
  have ha : ∀ k, |a k| ≤ W.weight k := by
    intro k
    apply abs_normalized_spline_block_le (W.exponent k) hu0
    intro p
    exact (le_abs_self _).trans (W.exponent_abs_re_le hΘ k p)
  have hdom := W.normalized_block_dominates hΘ hΘ2 hR0 j hu
  have hg := tsum_ge_of_top_window hΘ
    (x := calibratedDepthUpper Θ) (w := W.weight) (U := W.right) (a := a) (b := fun _ => 0)
    (fun k => SplineTower.depth_nonneg hΘ _)
    (fun k => (calibratedDepth_bounds hΘ k).2.2.2.le)
    (strictMono_calibratedDepthUpper hΘ).monotone W.weight_nonneg
    (W.weight_zero_le hΘ hΘ2) (W.weight_succ_le hΘ hΘ2)
    (W.monotone_right hR0) (W.right_nonneg hR0 0) ha
    (fun k => by simpa only [abs_zero] using W.weight_nonneg k)
    hu0 (M := (j : ℝ) + 1) (by positivity) hur (by simpa only [a, add_assoc, show (1 : ℝ) + 9 = 10 by norm_num] using hdom)
  have he (k : ℕ) : Real.exp (calibratedDepthUpper Θ k * u) * a k +
      Real.exp (-(calibratedDepthUpper Θ k * u)) * 0 = W.blockTrace k u := by
    dsimp only [a]
    rw [mul_zero, add_zero, ← mul_assoc, ← Real.exp_add]
    simp only [add_neg_cancel, Real.exp_zero, one_mul]
  rw [W.two_re_lagStructure_config hΘ hΘ2]
  simpa only [he] using hg

end CalibratedWindowTower.Tower

/-- Every prescribed nonnegative sublogarithmic radius admits one simple configuration in class `𝒵`
with an unattained positive top and arbitrarily late windows exceeding every fixed floor. -/
theorem exists_classZ_prescribed_sublogarithmic_windows_bddBelow_beyond_every_bound
    {γmin C Θ : ℝ} (hγ : 0 < γmin) (hC : 0 < C) (hΘ : 0 < Θ) (hΘ2 : Θ ≤ 1 / 2)
    (R : ℝ → ℝ) (hR0 : ∀ T, 0 ≤ R T)
    (hR : Tendsto (fun T => R T / Real.log T) atTop (𝓝 0)) :
    ∃ Z : ZeroConfig,
      InClassZ γmin C Z ∧
      (∀ ρ ∈ Z.carrier, Z.mult ρ = 1) ∧
      (∀ ρ ∈ Z.carrier, ρ.re < 1 / 2 + Θ) ∧
      (∀ ε : ℝ, 0 < ε → ∃ ρ ∈ Z.carrier, 1 / 2 + Θ - ε < ρ.re) ∧
      ∀ K U : ℝ, ∃ T : ℝ, U ≤ T ∧
        ∀ u : ℝ, |u - T| ≤ R T → K ≤ 2 * (lagStructure Z (boxSpline 1 3) u).re := by
  obtain ⟨W⟩ := CalibratedWindowTower.exists_tower (γmin := γmin) hC hΘ hR0 hR
  refine ⟨W.config hΘ hΘ2, W.inClassZ_config hγ hC hΘ hΘ2, fun _ _ => rfl,
    fun _ hρ => W.re_lt_half_add hΘ hΘ2 hρ,
    fun ε hε => W.exists_re_gt_half_add_sub hΘ hΘ2 hε, ?_⟩
  intro K U
  let j := max ⌈max K 0⌉₊ ⌈max U 0⌉₊
  have hK : K ≤ (j : ℝ) := by
    exact ((le_max_left K 0).trans (Nat.le_ceil _)).trans
      (by exact_mod_cast le_max_left ⌈max K 0⌉₊ ⌈max U 0⌉₊)
  have hU : U ≤ (j : ℝ) := by
    exact ((le_max_left U 0).trans (Nat.le_ceil _)).trans
      (by exact_mod_cast le_max_right ⌈max K 0⌉₊ ⌈max U 0⌉₊)
  refine ⟨(W.block (j + 1)).T, ?_, fun u hu => ?_⟩
  · have hh := (W.block (j + 1)).left_le
    have hr := hR0 (W.block (j + 1)).T
    push_cast at hh
    linarith only [hh, hr, hU]
  · have hh := W.window_floor hΘ hΘ2 hR0 j hu
    linarith only [hh, hK]

end GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality
