import GaloisForLFunctions.RHTower.Sieve.Section4ExceptionalCofactor
import GaloisForLFunctions.RHTower.Sieve.Section4RelativeThreshold
import GaloisForLFunctions.RHTower.Sieve.StepMassCard
import GaloisForLFunctions.RHTower.Sieve.MoebiusTwoRangeWindow

/-!
# The measure of the exceptional half of the annulus

The large half of the annulus is the set where some block of the designated range exceeds its
threshold, and its measure is what Halász–Montgomery spends.  The moment method of exposé §4
supplies it: for one block `B` of a ladder whose top is `NA`, at a threshold `V`,

```text
   |{ |w| ≤ W : ‖∑_{p∈B} μ(p)p^{iw}‖ ≥ V }|
      ≤ (2π)⁻¹·2·( 2πW + 4·NA^k(1 + log NA^k) )·( k·#B / V² )^k .
```

The Gallagher and Dirichlet variables differ by the scaling `w ↦ 2πw`, under which Lebesgue measure
picks up `(2π)⁻¹`; everything else is `Sieve/Section4ExceptionalMeasure` verbatim.

**The threshold is a maximum, and that is what makes the bound unconditional.**  A purely relative
threshold `V = θ·#B` needs a *lower* bound for `#B` — a short-interval prime count — before the
ratio `k·#B/V² = k/(#B·θ²)` is small.  With

```text
   V = max( θ·#B , B₀ )
```

the ratio is at most `k/(θ·B₀)` **whichever branch the maximum takes**: if `θ#B ≥ B₀` then
`V² ≥ θ#B·B₀`, and if `θ#B < B₀` then `#B < B₀/θ` and `V² = B₀²`.  So no block ever has to be shown
to contain many primes; blocks that happen to be thin are simply never thresholded, and the price is
the term `B₀²` in the mean-value ladder group.

**The moment order is not a constant.**  The second term of the bound grows like `exp(k·log NA)`
while the saving is `exp(−k·log(θB₀/k))`, so a bounded `k` cannot make the product small: `k` must
grow, and the useful pairing is per block, `log(θB₀/k) − log NA_j`.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

/-- A ladder step lies in the initial segment ending at its right endpoint. -/
theorem geomBlock_subset_Icc_one {P : Finset ℕ} {Q η : ℝ} (hQ : 0 < Q) (hη : 0 ≤ η) (j : ℕ) :
    geomBlock P Q (1 + η) j ⊆ Finset.Icc 1 ⌊Q * (1 + η) ^ (j + 1)⌋₊ := by
  intro p hp
  have hIoc := geomBlock_subset_Ioc (P := P) hQ hη j hp
  rw [Finset.mem_Ioc] at hIoc
  rw [Finset.mem_Icc]
  exact ⟨by omega, hIoc.2⟩

/-- **Lemma 2.5 in the Gallagher variable, at a free threshold.** -/
theorem measureReal_shortExceptional_le {B : Finset ℕ} {NA k : ℕ}
    (hBprime : ∀ p ∈ B, p.Prime) (hB : B ⊆ Finset.Icc 1 NA) (hk : 1 ≤ k)
    {W V : ℝ} (hW : 0 ≤ W) (hV : 0 < V) :
    volume.real (shortExceptional B W V)
      ≤ (2 * Real.pi)⁻¹
        * (2 * ((2 * Real.pi * W + 4 * ((NA ^ k : ℕ) : ℝ) * (1 + Real.log ((NA ^ k : ℕ) : ℝ)))
            * ((k : ℝ) ^ k * (B.card : ℝ) ^ k)) / V ^ (2 * k)) := by
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  rw [shortExceptional_eq_preimage hB W V, volume_real_preimage_mul_left hpi]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact volume_blockExceptional_le hBprime hk (by positivity) hV

/-- **Lemma 2.5 in the Gallagher variable, at a relative threshold.** -/
theorem measureReal_shortExceptional_le_relative {B : Finset ℕ} {NA k : ℕ}
    (hBprime : ∀ p ∈ B, p.Prime) (hB : B ⊆ Finset.Icc 1 NA) (hk : 1 ≤ k)
    {W θ : ℝ} (hW : 0 ≤ W) (hθ : 0 < θ) (hcard : 0 < (B.card : ℝ)) :
    volume.real (shortExceptional B W ((B.card : ℝ) * θ))
      ≤ (2 * Real.pi)⁻¹
        * (2 * (2 * Real.pi * W + 4 * ((NA ^ k : ℕ) : ℝ) * (1 + Real.log ((NA ^ k : ℕ) : ℝ)))
          * ((k : ℝ) / ((B.card : ℝ) * θ ^ 2)) ^ k) := by
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  rw [shortExceptional_eq_preimage hB W ((B.card : ℝ) * θ), volume_real_preimage_mul_left hpi]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact volume_blockExceptional_le_relative hBprime hk (by positivity) hθ hcard

/-- **The moment ratio at a maximum threshold, with no lower bound on the block.** -/
theorem moment_ratio_max_le {Bc θ B₀ kk : ℝ} (hBc : 0 ≤ Bc) (hθ : 0 < θ) (hB₀ : 0 < B₀)
    (hk : 0 ≤ kk) :
    kk * Bc / max (θ * Bc) B₀ ^ 2 ≤ kk / (θ * B₀) := by
  have hV0 : (0 : ℝ) < max (θ * Bc) B₀ := lt_of_lt_of_le hB₀ (le_max_right _ _)
  rcases eq_or_lt_of_le hBc with hzero | hpos
  · rw [← hzero]
    simp only [mul_zero, zero_div]
    positivity
  · have h1 : θ * Bc ≤ max (θ * Bc) B₀ := le_max_left _ _
    have h2 : B₀ ≤ max (θ * Bc) B₀ := le_max_right _ _
    have hsq : θ * Bc * B₀ ≤ max (θ * Bc) B₀ ^ 2 := by nlinarith [hB₀, h1, h2, hθ, hpos]
    have hnum : (0 : ℝ) ≤ kk * Bc := mul_nonneg hk hBc
    have hden : (0 : ℝ) < θ * Bc * B₀ := by positivity
    refine (div_le_div_of_nonneg_left hnum hden hsq).trans (le_of_eq ?_)
    field_simp

/-- **One block's exceptional measure at a maximum threshold.**  Unconditional in the block: the
ratio `k/(θ·B₀)` does not see `#B` at all. -/
theorem measureReal_shortExceptional_max_le {B : Finset ℕ} {NA k : ℕ}
    (hBprime : ∀ p ∈ B, p.Prime) (hB : B ⊆ Finset.Icc 1 NA) (hk : 1 ≤ k)
    {W θ B₀ : ℝ} (hW : 0 ≤ W) (hθ : 0 < θ) (hB₀ : 0 < B₀) :
    volume.real (shortExceptional B W (max (θ * (B.card : ℝ)) B₀))
      ≤ (2 * Real.pi)⁻¹
        * (2 * (2 * Real.pi * W + 4 * ((NA ^ k : ℕ) : ℝ) * (1 + Real.log ((NA ^ k : ℕ) : ℝ)))
          * ((k : ℝ) / (θ * B₀)) ^ k) := by
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hV0 : (0 : ℝ) < max (θ * (B.card : ℝ)) B₀ := lt_of_lt_of_le hB₀ (le_max_right _ _)
  refine (measureReal_shortExceptional_le hBprime hB hk hW hV0).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hpow : ((k : ℝ) ^ k * (B.card : ℝ) ^ k) / max (θ * (B.card : ℝ)) B₀ ^ (2 * k)
      = ((k : ℝ) * (B.card : ℝ) / max (θ * (B.card : ℝ)) B₀ ^ 2) ^ k := by
    rw [div_pow, mul_pow, pow_mul]
  have hratio := moment_ratio_max_le (Bc := (B.card : ℝ)) (θ := θ) (B₀ := B₀) (kk := (k : ℝ))
    (Nat.cast_nonneg _) hθ hB₀ (Nat.cast_nonneg _)
  have hr0 : (0 : ℝ) ≤ (k : ℝ) * (B.card : ℝ) / max (θ * (B.card : ℝ)) B₀ ^ 2 := by positivity
  have hstep : ((k : ℝ) * (B.card : ℝ) / max (θ * (B.card : ℝ)) B₀ ^ 2) ^ k
      ≤ ((k : ℝ) / (θ * B₀)) ^ k := pow_le_pow_left₀ hr0 hratio k
  have hX0 : (0 : ℝ) ≤ 2 * Real.pi * W
      + 4 * ((NA ^ k : ℕ) : ℝ) * (1 + Real.log ((NA ^ k : ℕ) : ℝ)) := by
    have hNA1 : (1 : ℝ) ≤ ((NA ^ k : ℕ) : ℝ) ∨ ((NA ^ k : ℕ) : ℝ) = 0 := by
      rcases Nat.eq_zero_or_pos (NA ^ k) with h0 | hp
      · right; rw [h0]; norm_num
      · left; exact_mod_cast hp
    rcases hNA1 with h1 | h0
    · have hlog : (0 : ℝ) ≤ Real.log ((NA ^ k : ℕ) : ℝ) := Real.log_nonneg h1
      have : (0 : ℝ) ≤ 4 * ((NA ^ k : ℕ) : ℝ) * (1 + Real.log ((NA ^ k : ℕ) : ℝ)) := by
        have h4 : (0 : ℝ) ≤ 4 * ((NA ^ k : ℕ) : ℝ) := by positivity
        nlinarith [h4, hlog]
      positivity
    · rw [h0]
      simp only [mul_zero, zero_mul, add_zero]
      positivity
  calc 2 * ((2 * Real.pi * W + 4 * ((NA ^ k : ℕ) : ℝ) * (1 + Real.log ((NA ^ k : ℕ) : ℝ)))
          * ((k : ℝ) ^ k * (B.card : ℝ) ^ k)) / max (θ * (B.card : ℝ)) B₀ ^ (2 * k)
      = 2 * (2 * Real.pi * W + 4 * ((NA ^ k : ℕ) : ℝ) * (1 + Real.log ((NA ^ k : ℕ) : ℝ)))
          * (((k : ℝ) ^ k * (B.card : ℝ) ^ k) / max (θ * (B.card : ℝ)) B₀ ^ (2 * k)) := by
        ring
    _ = 2 * (2 * Real.pi * W + 4 * ((NA ^ k : ℕ) : ℝ) * (1 + Real.log ((NA ^ k : ℕ) : ℝ)))
          * (((k : ℝ) * (B.card : ℝ) / max (θ * (B.card : ℝ)) B₀ ^ 2) ^ k) := by rw [hpow]
    _ ≤ 2 * (2 * Real.pi * W + 4 * ((NA ^ k : ℕ) : ℝ) * (1 + Real.log ((NA ^ k : ℕ) : ℝ)))
          * ((k : ℝ) / (θ * B₀)) ^ k :=
        mul_le_mul_of_nonneg_left hstep (by linarith)

/-- **The exceptional half of the annulus, block by block, at the maximum threshold.** -/
theorem measureReal_annulusLarge_le_moment {P : Finset ℕ} {R η θ B₀ W w₀ : ℝ} {L k : ℕ}
    (hR : 0 < R) (hη : 0 ≤ η) (hk : 1 ≤ k) (hW : 0 ≤ W) (hθ : 0 < θ) (hB₀ : 0 < B₀)
    (hPprime : ∀ p ∈ P, p.Prime) :
    volume.real (annulusLarge
        (allBlocksSmall P R η L
          (fun j => max (θ * ((geomBlock P R (1 + η) j).card : ℝ)) B₀) W) W w₀)
      ≤ ∑ j ∈ Finset.range L,
          (2 * Real.pi)⁻¹
            * (2 * (2 * Real.pi * W
                  + 4 * ((⌊R * (1 + η) ^ (j + 1)⌋₊ ^ k : ℕ) : ℝ)
                    * (1 + Real.log ((⌊R * (1 + η) ^ (j + 1)⌋₊ ^ k : ℕ) : ℝ)))
              * ((k : ℝ) / (θ * B₀)) ^ k) := by
  refine (measureReal_annulusLarge_le P R η L
    (fun j => max (θ * ((geomBlock P R (1 + η) j).card : ℝ)) B₀) W w₀).trans ?_
  refine Finset.sum_le_sum fun j _ => ?_
  refine measureReal_shortExceptional_max_le ?_ (geomBlock_subset_Icc_one hR hη j) hk hW hθ hB₀
  intro p hp
  exact hPprime p (geomBlock_subset P R (1 + η) j hp)

end

end RHTower.Sieve
