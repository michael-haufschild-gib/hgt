import GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality.TheSublogarithmicWindowsLeaveRoomForSparseBlocks

/-!
# A sparse tower of calibrated windows

Successive blocks have disjoint ordinate bands, summable normalized mass,
and spline weights small enough for all earlier windows. Their common
depths give the exponential gain needed to dominate the preceding levels.
-/

open Complex Filter Set Topology

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality
namespace CalibratedWindowTower

/-- One finite calibrated block, with its static strip, density and tempering bounds. -/
structure Block (γmin C Θ : ℝ) (R : ℝ → ℝ) (j : ℕ) where
  T : ℝ
  Γ : ℝ
  k : ℕ
  z : Fin (k + 1) → ℂ
  four_le : 4 ≤ Γ
  lowest : γmin ≤ Γ / 2
  index_le : (j : ℝ) + 1 ≤ Γ / 2
  left_le : (j : ℝ) + 1 ≤ T - R T
  degree_pos : 0 < k
  geometry : ∀ i, |(z i).re| ≤ calibratedDepthTolerance Θ j ∧
    Γ / 2 ≤ (z i).im ∧ (z i).im ≤ 4 * Γ ∧ ‖z i‖ ≤ 4 * Γ
  separation : ∀ i l, |((i : ℕ) : ℝ) - ((l : ℕ) : ℝ)| * (Γ / k) ≤ |(z i).im - (z l).im|
  positive : ∀ v : ℝ, |v| ≤ R T + 8 →
    (3 / 4 : ℝ) ≤ (∑ i, Complex.exp (((T + v : ℝ) : ℂ) * z i)).re
  local_count : 4 * (1 + (k : ℝ) / Γ) ≤ C * Real.log Γ
  tempered_mass : 16 * (k : ℝ) / Γ ^ 2 ≤ (1 / 2 : ℝ) ^ j

/-- A block can satisfy arbitrary additional separation, weight and depth-gap bounds. -/
theorem exists_block {γmin C Θ : ℝ} {R : ℝ → ℝ}
    (hC : 0 < C) (hΘ : 0 < Θ) (hR0 : ∀ T, 0 ≤ R T)
    (hR : Tendsto (fun T => R T / Real.log T) atTop (𝓝 0))
    (j : ℕ) {ε d : ℝ} (hε : 0 < ε) (hd : 0 < d) (H P M : ℝ) :
    ∃ B : Block γmin C Θ R j,
      H ≤ B.Γ ∧ P ≤ B.T - R B.T ∧
      524288 * Real.exp 4 * (B.k : ℝ) / B.Γ ^ 2 ≤ ε ∧
      M ≤ (3 / 2 : ℝ) * Real.exp
        (d * (B.T - R B.T) - 8 * calibratedDepthCenter Θ j) := by
  let e : ℝ := min ε ((1 / 2 : ℝ) ^ j)
  have he : 0 < e := lt_min hε (by positivity)
  let H' : ℝ := max H (max (2 * γmin) (2 * ((j : ℝ) + 1)))
  let P' : ℝ := max P ((j : ℝ) + 1)
  obtain ⟨T, hH, hP, hΓ4, hk, hcount, hmass, hweight, hgain, z, hz, hsep, hpos⟩ :=
    exists_sparse_calibrated_block hR0 hR hC he (calibratedDepth_bounds hΘ j).1 hd
      H' P' M (calibratedDepthCenter Θ j)
  let Γ := calibratedGridFrequency T
  let k := calibratedGridDegree Γ (R T)
  have hlow : γmin ≤ Γ / 2 := by
    have hh := (le_max_left (2 * γmin) (2 * ((j : ℝ) + 1))).trans (le_max_right H _)
    linarith only [hh, hH]
  have hidx : (j : ℝ) + 1 ≤ Γ / 2 := by
    have hh := (le_max_right (2 * γmin) (2 * ((j : ℝ) + 1))).trans (le_max_right H _)
    linarith only [hh, hH]
  have hleft : (j : ℝ) + 1 ≤ T - R T := (le_max_right P _).trans hP
  let B : Block γmin C Θ R j :=
    { T := T, Γ := Γ, k := k, z := z, four_le := hΓ4, lowest := hlow,
      index_le := hidx, left_le := hleft, degree_pos := hk, geometry := hz,
      separation := hsep, positive := hpos, local_count := hcount,
      tempered_mass := hmass.trans (min_le_right _ _) }
  exact ⟨B, (le_max_left _ _).trans hH, (le_max_left _ _).trans hP,
    hweight.trans (min_le_left _ _), hgain⟩

/-- The separation and tail conditions linking the calibrated levels. -/
structure Tower (γmin C Θ : ℝ) (R : ℝ → ℝ) where
  block : ∀ j, Block γmin C Θ R j
  weight_zero : 524288 * Real.exp 4 * ((block 0).k : ℝ) / (block 0).Γ ^ 2 ≤ 1
  frequency_gap : ∀ j, 8 * (block j).Γ + 4 ≤ (block (j + 1)).Γ
  window_gap : ∀ j, (block j).T + R (block j).T + 1 ≤
    (block (j + 1)).T - R (block (j + 1)).T
  weight_succ : ∀ j, 524288 * Real.exp 4 * ((block (j + 1)).k : ℝ) /
      (block (j + 1)).Γ ^ 2 ≤
    (1 / 2 : ℝ) ^ (j + 1) * Real.exp (-(Θ * ((block j).T + R (block j).T)))
  gain : ∀ j, (j : ℝ) + 12 ≤ (3 / 2 : ℝ) * Real.exp
    ((calibratedDepthCenter Θ (j + 1) - calibratedDepthUpper Θ j) *
      ((block (j + 1)).T - R (block (j + 1)).T) - 8 * calibratedDepthCenter Θ (j + 1))

variable {γmin C Θ : ℝ} {R : ℝ → ℝ}

/-- Every prescribed nonnegative sublogarithmic radius admits such a sparse tower. -/
theorem exists_tower (hC : 0 < C) (hΘ : 0 < Θ) (hR0 : ∀ T, 0 ≤ R T)
    (hR : Tendsto (fun T => R T / Real.log T) atTop (𝓝 0)) :
    Nonempty (Tower γmin C Θ R) := by
  classical
  obtain ⟨B₀, _, _, hw₀, _⟩ := exists_block (γmin := γmin) hC hΘ hR0 hR 0
    (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) < 1) 0 0 0
  have hnext (j : ℕ) (B : Block γmin C Θ R j) :
      ∃ B' : Block γmin C Θ R (j + 1),
        8 * B.Γ + 4 ≤ B'.Γ ∧ B.T + R B.T + 1 ≤ B'.T - R B'.T ∧
        524288 * Real.exp 4 * (B'.k : ℝ) / B'.Γ ^ 2 ≤
          (1 / 2 : ℝ) ^ (j + 1) * Real.exp (-(Θ * (B.T + R B.T))) ∧
        (j : ℝ) + 12 ≤ (3 / 2 : ℝ) * Real.exp
          ((calibratedDepthCenter Θ (j + 1) - calibratedDepthUpper Θ j) *
            (B'.T - R B'.T) - 8 * calibratedDepthCenter Θ (j + 1)) :=
    exists_block hC hΘ hR0 hR (j + 1) (by positivity)
      (sub_pos.mpr (calibratedDepthUpper_lt_next_center hΘ j))
      (8 * B.Γ + 4) (B.T + R B.T + 1) ((j : ℝ) + 12)
  choose next hnext_spec using hnext
  let B : ∀ j, Block γmin C Θ R j := fun j => Nat.rec B₀ (fun j Bj => next j Bj) j
  have hzero : B 0 = B₀ := rfl
  have hsucc (j : ℕ) : B (j + 1) = next j (B j) := rfl
  refine ⟨{ block := B, weight_zero := ?_, frequency_gap := ?_, window_gap := ?_,
    weight_succ := ?_, gain := ?_ }⟩
  · simpa only [hzero] using hw₀
  · intro j
    rw [hsucc]
    exact (hnext_spec j (B j)).1
  · intro j
    rw [hsucc]
    exact (hnext_spec j (B j)).2.1
  · intro j
    rw [hsucc]
    exact (hnext_spec j (B j)).2.2.1
  · intro j
    rw [hsucc]
    exact (hnext_spec j (B j)).2.2.2

end CalibratedWindowTower
end GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality
