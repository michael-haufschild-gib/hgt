import GaloisForLFunctions.HTGeometry.SmoothWeightSharpMellin

/-!
# Sharp-cutoff Mellin mass from an actual weighted vertical integral

The half-integer cutoff has a fractional Mellin majorant with cost
`(N+1)^(c+q)`. Integrating this majorant against an admitted weighted norm
profile keeps the actual vertical line; no mean-over-twists step is used.
-/

open Complex MeasureTheory Set
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower.WeilSingularArithmetic

/-- A single fractional weight controls the sharp half-integer Mellin kernel,
including its central interval. -/
theorem exists_mellin_halfWidth_weighted_bound {c q : ℝ}
    (hc : 0 < c) (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ N : ℕ, 0 < N → ∀ y : ℝ,
      ‖mellin (fun x : ℝ => ((smoothWeight N (1 / 2) x : ℝ) : ℂ))
        ((c : ℂ) + (y : ℂ) * I)‖ ≤
          D * ((N : ℝ) + 1) ^ (c + q) * (2 + |y|) ^ (-1 - q) := by
  obtain ⟨C₀, C₁, hC₀, hC₁, hfrac⟩ := exists_mellin_smoothWeight_fractional_scale_bounds
  let P : ℝ := C₀ ^ (1 - q) * C₁ ^ q
  let D : ℝ := 3 ^ (1 + q) * (1 / c + P * 2 ^ q)
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hDc : 3 ^ (1 + q) / c ≤ D := by
    calc
      _ ≤ 3 ^ (1 + q) / c + 3 ^ (1 + q) * P * 2 ^ q :=
        le_add_of_nonneg_right (by positivity)
      _ = D := by dsimp [D]; ring
  have hDt : 3 ^ (1 + q) * P * 2 ^ q ≤ D := by
    calc
      _ ≤ 3 ^ (1 + q) * P * 2 ^ q + 3 ^ (1 + q) / c :=
        le_add_of_nonneg_right (by positivity)
      _ = D := by dsimp [D]; ring
  refine ⟨D, hD, fun N hN y => ?_⟩
  have hN0 : 0 < (N : ℝ) := by exact_mod_cast hN
  have hN1 : 1 ≤ (N : ℝ) + 1 := by linarith
  have hp : 0 ≤ 1 + q := by linarith
  have hX : ((N : ℝ) + 1 / 2) ^ c ≤ ((N : ℝ) + 1) ^ (c + q) :=
    (Real.rpow_le_rpow (by positivity) (by linarith) hc.le).trans
      (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith))
  have hRX : (((N : ℝ) + 1 / 2) / (1 / 2)) ^ q * ((N : ℝ) + 1 / 2) ^ c ≤
      2 ^ q * ((N : ℝ) + 1) ^ (c + q) := by
    calc
      _ ≤ (2 * ((N : ℝ) + 1)) ^ q * ((N : ℝ) + 1) ^ c :=
        mul_le_mul (Real.rpow_le_rpow (by positivity) (by linarith) hq)
          (Real.rpow_le_rpow (by positivity) (by linarith) hc.le)
          (by positivity) (by positivity)
      _ = _ := by
        rw [Real.mul_rpow (by norm_num) (by positivity), mul_assoc,
          ← Real.rpow_add (by positivity), add_comm q c]
  let W : ℝ := ‖mellin (fun x : ℝ => ((smoothWeight N (1 / 2) x : ℝ) : ℂ))
    ((c : ℂ) + (y : ℂ) * I)‖
  have hW0 : 0 ≤ W := norm_nonneg _
  have hscaled : W * (2 + |y|) ^ (1 + q) ≤ D * ((N : ℝ) + 1) ^ (c + q) := by
    rcases le_or_gt 1 |y| with hy | hy
    · have hfrac' := hfrac N (1 / 2) hN0 (by norm_num)
        ((c : ℂ) + (y : ℂ) * I) (by simpa using hc) q hq hq1 (by simpa using hy)
      have hkernel : W * |y| ^ (1 + q) ≤
          P * (((N : ℝ) + 1 / 2) / (1 / 2)) ^ q * ((N : ℝ) + 1 / 2) ^ c := by
        simpa [W, P, mul_comm, mul_left_comm, mul_assoc] using hfrac'
      have hweight : (2 + |y|) ^ (1 + q) ≤ 3 ^ (1 + q) * |y| ^ (1 + q) := by
        calc
          _ ≤ (3 * |y|) ^ (1 + q) :=
            Real.rpow_le_rpow (by positivity) (by linarith) hp
          _ = _ := Real.mul_rpow (by norm_num) (abs_nonneg y)
      calc
        _ ≤ W * (3 ^ (1 + q) * |y| ^ (1 + q)) :=
          mul_le_mul_of_nonneg_left hweight hW0
        _ = 3 ^ (1 + q) * (W * |y| ^ (1 + q)) := by ring
        _ ≤ 3 ^ (1 + q) *
            (P * (((N : ℝ) + 1 / 2) / (1 / 2)) ^ q * ((N : ℝ) + 1 / 2) ^ c) :=
          mul_le_mul_of_nonneg_left hkernel (by positivity)
        _ = (3 ^ (1 + q) * P) *
            ((((N : ℝ) + 1 / 2) / (1 / 2)) ^ q * ((N : ℝ) + 1 / 2) ^ c) := by ring
        _ ≤ (3 ^ (1 + q) * P) * (2 ^ q * ((N : ℝ) + 1) ^ (c + q)) :=
          mul_le_mul_of_nonneg_left hRX (by positivity)
        _ ≤ _ := by
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_right hDt (by positivity)
    · have hsmall := norm_mellin_smoothWeight_le_pow (N := N) (H := 1 / 2)
        hN0.le (by norm_num) (s := (c : ℂ) + (y : ℂ) * I) (by simpa using hc)
      have hsmall' : W ≤ ((N : ℝ) + 1 / 2) ^ c / c := by simpa [W] using hsmall
      have hkernel : W ≤ ((N : ℝ) + 1) ^ (c + q) / c :=
        hsmall'.trans (div_le_div_of_nonneg_right hX hc.le)
      have hweight : (2 + |y|) ^ (1 + q) ≤ 3 ^ (1 + q) :=
        Real.rpow_le_rpow (by positivity) (by linarith) hp
      calc
        _ ≤ (((N : ℝ) + 1) ^ (c + q) / c) * 3 ^ (1 + q) :=
          mul_le_mul hkernel hweight (by positivity) (by positivity)
        _ = (3 ^ (1 + q) / c) * ((N : ℝ) + 1) ^ (c + q) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hDc (by positivity)
  change W ≤ _
  rw [show -1 - q = -(1 + q) by ring, Real.rpow_neg (by positivity),
    ← div_eq_mul_inv, le_div_iff₀ (Real.rpow_pos_of_pos (by positivity) _)]
  exact hscaled

/-- An actual fractionally weighted vertical norm integral pays the sharp
Mellin mass. Contour admission remains explicit and separate from the bound. -/
theorem exists_mellin_halfWidth_mass_le {F : ℂ → ℂ} {c q : ℝ}
    (hc : 0 < c) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (hweight : Integrable (fun y : ℝ =>
      ‖F ((c : ℂ) + (y : ℂ) * I)‖ * (2 + |y|) ^ (-1 - q)))
    (hprod : ∀ N : ℕ, 0 < N → Integrable (fun y : ℝ =>
      F ((c : ℂ) + (y : ℂ) * I) *
        mellin (fun x : ℝ => ((smoothWeight N (1 / 2) x : ℝ) : ℂ))
          ((c : ℂ) + (y : ℂ) * I))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 0 < N →
      (∫ y : ℝ, ‖F ((c : ℂ) + (y : ℂ) * I) *
        mellin (fun x : ℝ => ((smoothWeight N (1 / 2) x : ℝ) : ℂ))
          ((c : ℂ) + (y : ℂ) * I)‖) ≤ C * ((N : ℝ) + 1) ^ (c + q) := by
  obtain ⟨D, hD, hkernel⟩ := exists_mellin_halfWidth_weighted_bound hc hq hq1
  let J : ℝ := ∫ y : ℝ, ‖F ((c : ℂ) + (y : ℂ) * I)‖ * (2 + |y|) ^ (-1 - q)
  have hJ : 0 ≤ J := integral_nonneg fun _ => by positivity
  refine ⟨D * J, mul_nonneg hD hJ, fun N hN => ?_⟩
  calc
    _ ≤ ∫ y : ℝ, (D * ((N : ℝ) + 1) ^ (c + q)) *
        (‖F ((c : ℂ) + (y : ℂ) * I)‖ * (2 + |y|) ^ (-1 - q)) := by
      apply integral_mono (hprod N hN).norm (hweight.const_mul _)
      intro y
      dsimp only
      rw [norm_mul]
      convert mul_le_mul_of_nonneg_left (hkernel N hN y) (norm_nonneg _) using 1
      ring
    _ = (D * J) * ((N : ℝ) + 1) ^ (c + q) := by
      rw [integral_const_mul]
      dsimp [J]
      ring

end RHTower.WeilSingularArithmetic
