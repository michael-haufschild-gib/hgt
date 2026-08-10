import GaloisForLFunctions.RHTower.Sieve.AveragedFromOffDiagonal

/-!
# The trivial size, for benchmarking

The corpus's `card_innerFibre_le` gives `#(innerFibre x h a) ≤ h√x/a + 1`; on the dyadic block
`a ≥ √x`, so

```text
#(innerFibre x h a) ≤ h + 1 ,      |∑_{b ∈ innerFibre a} f(b)| ≤ h + 1 ,
```

and the whole mean square is at most `(2√x + 1)(h + 1)²`.  Normalised by `h²√x` that is `≍ 2`: the
target `AveragedMeanSquare` asks for `o(1)`, i.e. any saving at all over the trivial bound.

Recording the benchmark is not decoration.  Two routes were abandoned today precisely because their
output, measured against it, *was* the trivial size — the absolute-value band bound of
`DyadicBandBound`, and the height exponent `4` in `ghsHeight`.  Both were correct theorems whose
conclusions said nothing, and that is only visible once the trivial size is written down.
-/

noncomputable section

namespace RHTower.Sieve

open Finset

/-- **On the dyadic block a fibre has at most `h + 1` elements.** -/
theorem card_innerFibre_le_block {x h : ℝ} (hx : 0 ≤ x) (hh : 0 ≤ h) {a : ℕ}
    (ha : a ∈ outerBlock x h) :
    ((innerFibre x h a).card : ℝ) ≤ h + 1 := by
  have hs0 : (0 : ℝ) ≤ Real.sqrt x := Real.sqrt_nonneg x
  rw [mem_outerBlock] at ha
  obtain ⟨⟨ha1, -⟩, hal, -⟩ := ha
  have ha0 : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha1
  refine le_trans (card_innerFibre_le hx hh ha1) ?_
  have hdiv : h * Real.sqrt x / (a : ℝ) ≤ h := by
    rw [div_le_iff₀ ha0]
    nlinarith [hal, hh, hs0]
  linarith

/-- **The fibre sum is at most `h + 1` in absolute value.** -/
theorem abs_fibre_sum_le {f : ℕ → ℝ} (hf : ∀ n, |f n| ≤ 1) {x h : ℝ} (hx : 0 ≤ x) (hh : 0 ≤ h)
    {a : ℕ} (ha : a ∈ outerBlock x h) :
    |∑ b ∈ innerFibre x h a, f b| ≤ h + 1 := by
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_card_nsmul _ _ 1 fun b _ => hf b) ?_
  rw [nsmul_eq_mul, mul_one]
  exact card_innerFibre_le_block hx hh ha

/-- **The trivial size of the fibre mean square.** -/
theorem sum_fibreSq_trivial_le {f : ℕ → ℝ} (hf : ∀ n, |f n| ≤ 1) {x h : ℝ}
    (hx : 0 ≤ x) (hh : 0 ≤ h) :
    ∑ a ∈ outerBlock x h, (∑ b ∈ innerFibre x h a, f b) ^ 2
      ≤ ((outerBlock x h).card : ℝ) * (h + 1) ^ 2 := by
  refine le_trans (Finset.sum_le_card_nsmul _ _ ((h + 1) ^ 2) fun a ha => ?_) ?_
  · have habs := abs_fibre_sum_le hf hx hh ha
    have h0 : (0 : ℝ) ≤ h + 1 := by linarith
    calc (∑ b ∈ innerFibre x h a, f b) ^ 2
        = |∑ b ∈ innerFibre x h a, f b| ^ 2 := (sq_abs _).symm
      _ ≤ (h + 1) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) habs 2
  · rw [nsmul_eq_mul]

end RHTower.Sieve

end
