import GaloisForLFunctions.RHTower.DigammaThreeQuarter
import GaloisForLFunctions.RHTower.BaezDuarteGramDiscrete
import GaloisForLFunctions.RHTower.BaezDuartePairingSeries

/-!
# The `q = 4` Báez-Duarte Gram entry

`DigammaThreeQuarter` proved the three progression constants
`T₁ = (log 2 + π/2)/4`, `T₂ = (π/2 − log 2)/4`, `T₃ = (3log 2 − π/2)/4`.  This file performs the assembly they
were built for.

Since `(n mod 4)² = (n mod 4) + 2·[n ≡ 2] + 6·[n ≡ 3]`, the Gram series of `hasSum_bdGram_discrete` splits into
the pairing series (`hasSum_mod_div_mul_succ` at `m = 4`, value `log 4`) and two indicator series, each a
reindexing of a progression sum along `k ↦ 4k + (j−1)`:

**`bdGram_quarter` — `bdGram (1/4) (1/4) = (3 log 2)/8 − π/32`.**

Combined with the pairing `−θ log θ = (log 4)/4 = (log 2)/2` and the quadratic form, this gives a strictly
better single-generator bound than `BaezDuarteHalfBound`:

**`bdDist_sq_le_quarter_bound` — `d² ≤ 1 − (log 2)²/(4·((3log 2)/8 − π/32))` for the family `{1/4}`.**
-/

open Finset

noncomputable section

namespace RHTower

/-! ## Real forms of the progression sums -/

theorem hasSum_quarter_recip_real (j : ℕ) (v : ℝ)
    (h : HasSum (fun k : ℕ => 1 / ((((4 * k + j : ℕ)) : ℂ) * (((4 * k + j + 1 : ℕ)) : ℂ)))
      ((v : ℝ) : ℂ)) :
    HasSum (fun k : ℕ => 1 / ((((4 * k + j : ℕ)) : ℝ) * (((4 * k + j + 1 : ℕ)) : ℝ))) v := by
  refine Complex.hasSum_ofReal.mp ?_
  refine h.congr_fun ?_
  intro k
  push_cast
  ring

/-! ## Indicator series -/

/-- The indicator of a residue class, reindexed onto the progression. -/
theorem hasSum_indicator_quarter {j : ℕ} (hj1 : 1 ≤ j) (hj4 : j ≤ 3) (v : ℝ)
    (h : HasSum (fun k : ℕ => 1 / ((((4 * k + j : ℕ)) : ℝ) * (((4 * k + j + 1 : ℕ)) : ℝ))) v) :
    HasSum (fun n : ℕ => if (n + 1) % 4 = j then
      1 / (((n : ℝ) + 1) * ((n : ℝ) + 2)) else 0) v := by
  have hinj : Function.Injective (fun k : ℕ => 4 * k + (j - 1)) := by
    intro a b hab
    simp only at hab
    omega
  have hzero : ∀ n ∉ Set.range (fun k : ℕ => 4 * k + (j - 1)),
      (if (n + 1) % 4 = j then 1 / (((n : ℝ) + 1) * ((n : ℝ) + 2)) else 0) = 0 := by
    intro n hn
    by_cases hmod : (n + 1) % 4 = j
    · exfalso
      refine hn ⟨(n + 1) / 4, ?_⟩
      simp only
      omega
    · rw [if_neg hmod]
  refine (hinj.hasSum_iff hzero).mp ?_
  refine h.congr_fun ?_
  intro k
  have hmod : (4 * k + (j - 1) + 1) % 4 = j := by omega
  simp only [Function.comp_apply, hmod]
  have hc1 : ((4 * k + (j - 1) : ℕ) : ℝ) + 1 = ((4 * k + j : ℕ) : ℝ) := by
    push_cast [Nat.cast_sub hj1]
    ring
  have hc2 : ((4 * k + (j - 1) : ℕ) : ℝ) + 2 = ((4 * k + j + 1 : ℕ) : ℝ) := by
    push_cast [Nat.cast_sub hj1]
    ring
  rw [hc1, hc2]
  simp

/-! ## The entry -/

/-- **The `q = 4` Gram entry in closed form.** -/
theorem bdGram_quarter :
    bdGram (1 / (4 : ℝ)) (1 / (4 : ℝ)) = 3 * Real.log 2 / 8 - Real.pi / 32 := by
  have hT2 := hasSum_indicator_quarter (j := 2) (by norm_num) (by norm_num) _
    (hasSum_quarter_recip_real 2 _ hasSum_quarter_recip_two)
  have hT3 := hasSum_indicator_quarter (j := 3) (by norm_num) (by norm_num) _
    (hasSum_quarter_recip_real 3 _ hasSum_quarter_recip_three)
  have hpair := hasSum_mod_div_mul_succ (m := 4) (by norm_num)
  have hcomb := ((hpair.add (hT2.mul_left 2)).add (hT3.mul_left 6)).mul_left (1 / 16 : ℝ)
  have hgram := hasSum_bdGram_discrete (m₁ := 4) (m₂ := 4) (by norm_num) (by norm_num)
  have hterm : ∀ n : ℕ,
      (1 / 16 : ℝ) * ((((((n + 1) % 4 : ℕ) : ℝ) / (((n : ℝ) + 1) * ((n : ℝ) + 2))
        + 2 * (if (n + 1) % 4 = 2 then 1 / (((n : ℝ) + 1) * ((n : ℝ) + 2)) else 0))
        + 6 * (if (n + 1) % 4 = 3 then 1 / (((n : ℝ) + 1) * ((n : ℝ) + 2)) else 0)))
      = (((n + 1) % 4 : ℕ) : ℝ) * (((n + 1) % 4 : ℕ) : ℝ)
          / (((4 : ℕ) : ℝ) * ((4 : ℕ) : ℝ) * ((n : ℝ) + 1) * ((n : ℝ) + 2)) := by
    intro n
    have h1 : ((n : ℝ) + 1) ≠ 0 := by positivity
    have h2 : ((n : ℝ) + 2) ≠ 0 := by positivity
    have hr : (n + 1) % 4 = 0 ∨ (n + 1) % 4 = 1 ∨ (n + 1) % 4 = 2 ∨ (n + 1) % 4 = 3 := by omega
    rcases hr with h | h | h | h <;> rw [h] <;> norm_num <;> field_simp <;> ring
  rw [(funext hterm : (fun n : ℕ => (1 / 16 : ℝ) * _) = _)] at hcomb
  have hval := hgram.unique hcomb
  push_cast at hval
  rw [hval]
  have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) from by norm_num, Real.log_pow]
    push_cast
    ring
  rw [hlog4]
  ring

/-- **A better single-generator bound.**  The `m = 4` generator beats `m = 2`. -/
theorem bdDist_sq_le_quarter_bound :
    bdDist (fun _ : Fin 1 => 1 / (4 : ℝ)) ^ (2 : ℕ)
      ≤ 1 - Real.log 2 ^ (2 : ℕ) / (4 * (3 * Real.log 2 / 8 - Real.pi / 32)) := by
  have hgram := bdGram_quarter
  have hpos : 0 < 3 * Real.log 2 / 8 - Real.pi / 32 := by
    have h2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
    have h4 : Real.pi < 3.15 := Real.pi_lt_d2
    nlinarith
  have hθ : ∀ _i : Fin 1, 0 < (1 / (4 : ℝ)) ∧ (1 / (4 : ℝ)) ≤ 1 := by
    intro _
    norm_num
  have h := bdDist_sq_le_quadratic (fun _ : Fin 1 => 1 / (4 : ℝ)) hθ
    (fun _ : Fin 1 => Real.log 2 / (2 * (3 * Real.log 2 / 8 - Real.pi / 32)))
  have hlog : Real.log (1 / (4 : ℝ)) = -(2 * Real.log 2) := by
    rw [one_div, Real.log_inv, show (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) from by norm_num, Real.log_pow]
    push_cast
    ring
  refine le_trans h ?_
  simp only [Fin.sum_univ_one]
  rw [hlog, hgram]
  have hgne : (3 * Real.log 2 / 8 - Real.pi / 32) ≠ 0 := ne_of_gt hpos
  field_simp
  ring_nf
  exact le_rfl

end RHTower

end
