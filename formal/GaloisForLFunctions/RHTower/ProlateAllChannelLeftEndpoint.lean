import GaloisForLFunctions.RHTower.ProlateUnconditionalChannelBound
import GaloisForLFunctions.HTGeometry.InverseSquareTailSum
import GaloisForLFunctions.HTGeometry.VerticalShiftTailEstimate

/-!
# All dilation channels from a common left endpoint

Pushing the left endpoint of the radial primitive out to `L ≥ 2` makes the exact-channel estimate
uniform: every channel, including the first, is then in the oscillatory regime, and the channel
majorant is the inverse square of the dilation.  Summing gives a bound with no endpoint term.
-/

noncomputable section

open MeasureTheory

namespace RHTower

variable {s c : ℝ} {R DR DDR : ℝ → ℝ}

theorem abs_integral_radialProlate_dilate_left_le
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 1 ≤ c)
    (hR : ∀ t : ℝ, HasDerivAt R (DR t) t) (hDR : ∀ t : ℝ, HasDerivAt DR (DDR t) t)
    (hode : ∀ t : ℝ, (t ^ 2 - 1) * DDR t + 2 * t * DR t
      - (s * c ^ 2 - c ^ 2 * t ^ 2) * R t = 0)
    {L X : ℝ} (hL : 2 ≤ L) (hLX : L ≤ X) (n : ℕ) :
    |∫ t in L..X, R (((n : ℝ) + 1) * t)|
      ≤ 4500 * GaloisForLFunctions.RHTower.exactEnergyBudget s c R DR 2 /
          (Real.sqrt c * (c * ((n : ℝ) + 1) ^ 2) * L) := by
  have hk : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hL1 : (1 : ℝ) ≤ L := by linarith
  have hkL : (2 : ℝ) ≤ ((n : ℝ) + 1) * L := by nlinarith
  have h := GaloisForLFunctions.RHTower.norm_integral_radialProlate_dilate_left_le
    (DDR := DDR) (k := (n : ℝ) + 1) (L := L) hs0 hs1 hc hk hL1 hkL hLX hR hDR hode
  have hcast : (∫ t in L..X, ((R (((n : ℝ) + 1) * t) : ℝ) : ℂ))
      = ((∫ t in L..X, R (((n : ℝ) + 1) * t) : ℝ) : ℂ) := intervalIntegral.integral_ofReal
  rw [hcast, Complex.norm_real, Real.norm_eq_abs] at h
  exact h

/-- **All channels from a common left endpoint.** -/
theorem tsum_abs_integral_radialProlate_left_le
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 1 ≤ c)
    (hR : ∀ t : ℝ, HasDerivAt R (DR t) t) (hDR : ∀ t : ℝ, HasDerivAt DR (DDR t) t)
    (hode : ∀ t : ℝ, (t ^ 2 - 1) * DDR t + 2 * t * DR t
      - (s * c ^ 2 - c ^ 2 * t ^ 2) * R t = 0)
    {L X : ℝ} (hL : 2 ≤ L) (hLX : L ≤ X) :
    Summable (fun n : ℕ => |∫ t in L..X, R (((n : ℝ) + 1) * t)|) ∧
      ∑' n : ℕ, |∫ t in L..X, R (((n : ℝ) + 1) * t)|
        ≤ 2 * (4500 * GaloisForLFunctions.RHTower.exactEnergyBudget s c R DR 2 /
            (Real.sqrt c * c * L)) := by
  have hc0 : (0 : ℝ) < c := lt_of_lt_of_le zero_lt_one hc
  have hsc : (0 : ℝ) < Real.sqrt c := Real.sqrt_pos.mpr hc0
  have hL0 : (0 : ℝ) < L := by linarith
  set M : ℝ := GaloisForLFunctions.RHTower.exactEnergyBudget s c R DR 2 with hMdef
  have hM : (0 : ℝ) ≤ M := Real.sqrt_nonneg _
  set B : ℝ := 4500 * M / (Real.sqrt c * c * L) with hBdef
  have hB : (0 : ℝ) ≤ B := by rw [hBdef]; positivity
  have hterm : ∀ n : ℕ, |∫ t in L..X, R (((n : ℝ) + 1) * t)|
      ≤ B * (1 / (1 + (n : ℝ)) ^ 2) := by
    intro n
    have h := abs_integral_radialProlate_dilate_left_le hs0 hs1 hc hR hDR hode hL hLX n
    refine le_trans h (le_of_eq ?_)
    rw [hBdef, ← hMdef]
    have hne : ((n : ℝ) + 1) ≠ 0 := by positivity
    have hcomm : (1 + (n : ℝ)) = ((n : ℝ) + 1) := by ring
    rw [hcomm]
    field_simp
  have hnn : ∀ n : ℕ, (0 : ℝ) ≤ |∫ t in L..X, R (((n : ℝ) + 1) * t)| := fun n => abs_nonneg _
  have hmaj : Summable fun n : ℕ => B * (1 / (1 + (n : ℝ)) ^ 2) :=
    (GaloisForLFunctions.HTGeometry.summable_inv_sq_shift (σ := 1) (by norm_num)).mul_left B
  have hsummable : Summable fun n : ℕ => |∫ t in L..X, R (((n : ℝ) + 1) * t)| :=
    hmaj.of_nonneg_of_le hnn hterm
  refine ⟨hsummable, ?_⟩
  calc ∑' n : ℕ, |∫ t in L..X, R (((n : ℝ) + 1) * t)|
      ≤ ∑' n : ℕ, B * (1 / (1 + (n : ℝ)) ^ 2) := hsummable.tsum_le_tsum hterm hmaj
    _ = B * ∑' n : ℕ, 1 / (1 + (n : ℝ)) ^ 2 := tsum_mul_left
    _ ≤ B * 2 := mul_le_mul_of_nonneg_left
        GaloisForLFunctions.HTGeometry.tsum_inv_sq_shift_one_le_two hB
    _ = 2 * B := by ring

end RHTower
