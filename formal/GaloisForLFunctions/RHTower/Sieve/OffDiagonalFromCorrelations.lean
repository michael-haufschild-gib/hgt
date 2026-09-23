import GaloisForLFunctions.RHTower.Sieve.OffDiagonalShiftBound

/-!
# The off-diagonal vanishes, given averaged correlations

The explicit bound

```text
| off-diagonal |  ≤  (9h+3)·∑_{k ≤ h} B k  +  2h·(3√x + 1)
```

is `o(h²√x)` as soon as the shift-averaged partial correlation sums are `o(h√x)`: the first term is
then `o(h²√x)` and the second is `O(h√x)`, a whole factor `h` below the normalisation.  So the fibre
mean square — hence `MRBilinear`, hence both Route E sign-density theorems — follows from the
averaged form of Chowla's conjecture in its maximal-partial-sum form.
-/

noncomputable section

namespace RHTower.Sieve

open Finset Filter Topology

/-- Partial correlation sums of `f`, averaged over the shifts `k ≤ h`, are `o(h√x)`. -/
def AveragedCorrelationSmall (f : ℕ → ℝ) (hh : ℝ → ℝ) : Prop :=
  ∀ ε > 0, ∀ᶠ x : ℝ in atTop,
    ∃ B : ℕ → ℝ, (∀ k, 0 ≤ B k)
      ∧ CorrelationPartialBound (fun i => f (i + 1)) ⌊hh x⌋₊ B
      ∧ ∑ k ∈ Finset.Icc 1 ⌊hh x⌋₊, B k ≤ ε * (hh x * Real.sqrt x)

theorem four_le_sqrt {x : ℝ} (hx : 16 ≤ x) : (4 : ℝ) ≤ Real.sqrt x := by
  have h16 : Real.sqrt 16 = 4 := by
    rw [show (16 : ℝ) = 4 ^ (2 : ℕ) by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 4)]
  rw [← h16]
  exact Real.sqrt_le_sqrt hx

/-- **The off-diagonal vanishes, given averaged correlations.** -/
theorem offDiagonalVanishes_of_correlations {f : ℕ → ℝ} (hf : ∀ n, |f n| ≤ 1) {hh : ℝ → ℝ}
    (hgrow : Tendsto hh atTop atTop) (hcap : ∀ᶠ x in atTop, hh x ≤ Real.sqrt x)
    (hcorr : AveragedCorrelationSmall f hh) :
    OffDiagonalVanishes f hh := by
  rw [OffDiagonalVanishes, NormedAddGroup.tendsto_nhds_zero]
  intro ε hε
  filter_upwards [hcorr (ε / 48) (by linarith), hcap,
    hgrow.eventually_ge_atTop (max 1 (64 / ε)), Filter.eventually_ge_atTop (16 : ℝ)]
    with x hBx hcapx hhbig hx16
  obtain ⟨B, hB0, hB, hBsum⟩ := hBx
  set h := hh x with hhdef
  have hh1 : (1 : ℝ) ≤ h := le_trans (le_max_left _ _) hhbig
  have hh64 : 64 / ε ≤ h := le_trans (le_max_right _ _) hhbig
  have hεh : (64 : ℝ) ≤ h * ε := by
    rw [div_le_iff₀ hε] at hh64
    linarith
  have hs4 : (4 : ℝ) ≤ Real.sqrt x := four_le_sqrt hx16
  have hden : (0 : ℝ) < h ^ (2 : ℕ) * Real.sqrt x := by nlinarith [hh1, hs4]
  have hbase := abs_offDiagonal_le hf hx16 hh1 hcapx hB0 hB
  have hsumB0 : (0 : ℝ) ≤ ∑ k ∈ Finset.Icc 1 ⌊h⌋₊, B k := Finset.sum_nonneg fun k _ => hB0 k
  have h9 : (0 : ℝ) ≤ 9 * h + 3 := by linarith
  have step1 : (9 * h + 3) * (∑ k ∈ Finset.Icc 1 ⌊h⌋₊, B k)
      ≤ (9 * h + 3) * ((ε / 48) * (h * Real.sqrt x)) :=
    mul_le_mul_of_nonneg_left hBsum h9
  have step2 : (9 * h + 3) * ((ε / 48) * (h * Real.sqrt x))
      ≤ (ε / 4) * (h ^ (2 : ℕ) * Real.sqrt x) := by
    nlinarith [hh1, hs4, hε.le, mul_nonneg (mul_nonneg hε.le (by linarith : (0:ℝ) ≤ h - 1))
      (mul_nonneg (by linarith : (0:ℝ) ≤ h) (by linarith : (0:ℝ) ≤ Real.sqrt x))]
  have step3 : 2 * h * (3 * Real.sqrt x + 1) ≤ (ε / 8) * (h ^ (2 : ℕ) * Real.sqrt x) := by
    have hhs : (0 : ℝ) ≤ h * Real.sqrt x := by nlinarith [hh1, hs4]
    nlinarith [hεh, hhs, hh1, hs4]
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hden, div_lt_iff₀ hden, abs_mul]
  have habs : |(2 : ℝ)| = 2 := by norm_num
  rw [habs]
  nlinarith [hbase, step1, step2, step3, hden, hε]

end RHTower.Sieve

end
