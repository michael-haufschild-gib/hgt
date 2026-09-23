import GaloisForLFunctions.RHTower.QuarterGramEntry
import GaloisForLFunctions.RHTower.BaezDuarteHalfBound

/-!
# The full `{2,4}` Gram matrix in closed form

`QuarterGramEntry` evaluated the diagonal entry at `m = 4` and `BaezDuarteHalfBound` the one at `m = 2`.  The
same residue-class decomposition gives the off-diagonal entry, because

`(n mod 2)·(n mod 4) = [n ≡ 1 mod 4] + 3·[n ≡ 3 mod 4]`

(check the four residues: `0·0`, `1·1`, `0·2`, `1·3`).  Summing with the constants `T₁`, `T₃`:

**`bdGram_half_quarter` — `bdGram (1/2) (1/4) = (5 log 2)/16 − π/32`.**

So the whole Gram matrix of the two-generator system `{1/2, 1/4}` is explicit:

| | `1/2` | `1/4` |
|---|---|---|
| `1/2` | `(log 2)/4` | `(5log 2)/16 − π/32` |
| `1/4` | `(5log 2)/16 − π/32` | `(3log 2)/8 − π/32` |

with pairing vector `((log 2)/2, (log 2)/2)` — the two pairings coincide, since `−θ log θ = (log m)/m` is the
same at `m = 2` and `m = 4`.  Feeding any coefficient pair into `bdDist_sq_le_quadratic` now yields a bound in
closed form; the optimal pair is `G⁻¹v`, and `bdGram_half_quarter_posDef` records that `G` is invertible so
that solution exists.
-/

open Finset

noncomputable section

namespace RHTower

/-- **The off-diagonal entry of the `{2,4}` Gram matrix.** -/
theorem bdGram_half_quarter :
    bdGram (1 / (2 : ℝ)) (1 / (4 : ℝ)) = 5 * Real.log 2 / 16 - Real.pi / 32 := by
  have hT1 := hasSum_indicator_quarter (j := 1) (by norm_num) (by norm_num) _
    (hasSum_quarter_recip_real 1 _ hasSum_quarter_recip_one)
  have hT3 := hasSum_indicator_quarter (j := 3) (by norm_num) (by norm_num) _
    (hasSum_quarter_recip_real 3 _ hasSum_quarter_recip_three)
  have hcomb := ((hT1.add (hT3.mul_left 3))).mul_left (1 / 8 : ℝ)
  have hgram := hasSum_bdGram_discrete (m₁ := 2) (m₂ := 4) (by norm_num) (by norm_num)
  have hterm : ∀ n : ℕ,
      (1 / 8 : ℝ) * ((if (n + 1) % 4 = 1 then 1 / (((n : ℝ) + 1) * ((n : ℝ) + 2)) else 0)
        + 3 * (if (n + 1) % 4 = 3 then 1 / (((n : ℝ) + 1) * ((n : ℝ) + 2)) else 0))
      = (((n + 1) % 2 : ℕ) : ℝ) * (((n + 1) % 4 : ℕ) : ℝ)
          / (((2 : ℕ) : ℝ) * ((4 : ℕ) : ℝ) * ((n : ℝ) + 1) * ((n : ℝ) + 2)) := by
    intro n
    have h1 : ((n : ℝ) + 1) ≠ 0 := by positivity
    have h2 : ((n : ℝ) + 2) ≠ 0 := by positivity
    have hr : (n + 1) % 4 = 0 ∨ (n + 1) % 4 = 1 ∨ (n + 1) % 4 = 2 ∨ (n + 1) % 4 = 3 := by omega
    have hmod2 : (n + 1) % 2 = ((n + 1) % 4) % 2 := (Nat.mod_mod_of_dvd _ (by norm_num)).symm
    rcases hr with h | h | h | h <;> rw [hmod2, h] <;> norm_num <;> field_simp
  rw [(funext hterm : (fun n : ℕ => (1 / 8 : ℝ) * _) = _)] at hcomb
  have hval := hgram.unique hcomb
  push_cast at hval
  rw [hval]
  ring

/-- The `{2,4}` Gram matrix is invertible: its determinant is positive. -/
theorem bdGram_half_quarter_det_pos :
    0 < bdGram (1 / (2 : ℝ)) (1 / (2 : ℝ)) * bdGram (1 / (4 : ℝ)) (1 / (4 : ℝ))
      - bdGram (1 / (2 : ℝ)) (1 / (4 : ℝ)) ^ (2 : ℕ) := by
  rw [bdGram_half, bdGram_quarter, bdGram_half_quarter]
  have h2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have h2' : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have h3 : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
  have h4 : Real.pi < 3.15 := Real.pi_lt_d2
  nlinarith [h2, h2', h3, h4]

end RHTower

end
