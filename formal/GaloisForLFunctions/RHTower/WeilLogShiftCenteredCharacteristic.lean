import GaloisForLFunctions.RHTower.WeilLogShiftEdgeCharacteristic
import GaloisForLFunctions.RHTower.WeilLogShiftMeanBiasBound

/-! Actual edge centering changes the normalized characteristic function by a vanishing amount. -/

open scoped BigOperators
open Filter Topology

noncomputable section
namespace RHTower

def finiteWeilCanonicalCenteredCharacteristic (r k : ℕ) (u : ℝ) : ℂ :=
  ∑ i : Fin (r + 1), (finiteWeilCanonicalEdgeMass r k i : ℂ) *
    finiteWeilPhase (u * (((i : ℕ) : ℝ) - finiteWeilCanonicalEdgeIndexMean r k))

theorem finiteWeilCanonicalCenteredCharacteristic_center_bound (r k : ℕ) (u : ℝ) :
    ‖finiteWeilCanonicalCenteredCharacteristic r k u - finiteWeilCanonicalEdgeCharacteristic r k u‖ ≤
      |u| * |finiteWeilCanonicalEdgeIndexMean r k - (r : ℝ) / 2| := by
  let f := fun i : Fin (r + 1) => u * (((i : ℕ) : ℝ) - (r : ℝ) / 2)
  let c := u * ((r : ℝ) / 2 - finiteWeilCanonicalEdgeIndexMean r k)
  have heq : finiteWeilCanonicalCenteredCharacteristic r k u =
      ∑ i, (finiteWeilCanonicalEdgeMass r k i : ℂ) * finiteWeilPhase (f i + c) := by
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    congr 1
    dsimp [f, c]
    ring
  rw [heq]
  calc
    _ ≤ |c| := finiteWeilCanonicalEdge_phase_shift_bound r k f c
    _ = _ := by dsimp [c]; rw [abs_mul, abs_sub_comm]

theorem finiteWeilCanonicalCenteredCharacteristic_quadratic_bound (r t : ℕ) (u : ℝ) :
    ‖finiteWeilCanonicalCenteredCharacteristic r (2 * (r + 1) ^ 2 + t) u -
      finiteWeilCanonicalEdgeCharacteristic r (2 * (r + 1) ^ 2 + t) u‖ ≤ 2 * |u| := by
  calc
    _ ≤ |u| * |finiteWeilCanonicalEdgeIndexMean r (2 * (r + 1) ^ 2 + t) - (r : ℝ) / 2| :=
      finiteWeilCanonicalCenteredCharacteristic_center_bound r _ u
    _ ≤ |u| * 2 := mul_le_mul_of_nonneg_left
      (finiteWeilCanonicalEdgeIndexMean_quadratic_bias_bound r t) (abs_nonneg _)
    _ = _ := by ring

theorem tendsto_finiteWeilCanonicalCenteredCharacteristic_gaussian (t : ℕ → ℕ) (α : ℝ) :
    Tendsto (fun r : ℕ => finiteWeilCanonicalCenteredCharacteristic r (2 * (r + 1) ^ 2 + t r)
      (α / Real.sqrt ((r + 1 : ℕ) : ℝ))) atTop (𝓝 ((Real.exp (-(α ^ 2 / 8)) : ℝ) : ℂ)) := by
  apply (tendsto_finiteWeilCanonicalEdgeCharacteristic_gaussian t α).congr_dist
  apply squeeze_zero (g := fun r : ℕ => (2 * |α|) * (Real.sqrt ((r + 1 : ℕ) : ℝ))⁻¹)
    (fun r => dist_nonneg)
  · intro r
    rw [dist_eq_norm, norm_sub_rev]
    calc
      _ ≤ 2 * |α / Real.sqrt ((r + 1 : ℕ) : ℝ)| :=
        finiteWeilCanonicalCenteredCharacteristic_quadratic_bound r (t r) _
      _ = _ := by
        rw [abs_div, abs_of_pos (show 0 < Real.sqrt ((r + 1 : ℕ) : ℝ) by positivity)]
        ring
  · simpa only [mul_zero] using tendsto_finiteWeil_inverse_sqrt_succ.const_mul (2 * |α|)

end RHTower
