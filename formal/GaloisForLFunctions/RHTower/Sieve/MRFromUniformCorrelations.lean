import GaloisForLFunctions.RHTower.Sieve.OffDiagonalUniformBound
import GaloisForLFunctions.RHTower.Sieve.MRFromCorrelations

/-!
# The bilinear all-interval theorem from shift-uniform averaged correlations

The reduction, on the weakest interface it can run on.  The input is

```text
∀ ε > 0, ∀ᶠ x, ∀ J,  ∑_{k ≤ h} | ∑_{i < J} f(i+1)·f(i+1+k) |  ≤  ε·h·√x ,
```

one bound valid for every initial segment `J` — not a bound on the maximum over `J` at each shift.
For `f = μ` this is the averaged form of Chowla's conjecture, a theorem of Matomäki, Radziwiłł and
Tao for `h → ∞`: for `J ≥ ε'·x` it is their estimate, and for shorter segments the trivial bound
`|∑_{i<J}| ≤ J` already gives it.

Given it, `MRBilinear μ hh` holds for every window law with `hh → ∞` and `hh x ≤ √x`, and with it
both Route E sign-density theorems.
-/

noncomputable section

namespace RHTower.Sieve

open Finset Filter Topology
open scoped ArithmeticFunction.Moebius

/-- Partial correlation sums, summed over the shifts `k ≤ h` and bounded uniformly in the length of
the initial segment, are `o(h√x)`. -/
def UniformCorrelationSmall (f : ℕ → ℝ) (hh : ℝ → ℝ) : Prop :=
  ∀ ε > 0, ∀ᶠ x : ℝ in atTop,
    CorrelationUniformBound (fun i => f (i + 1)) ⌊hh x⌋₊ (ε * (hh x * Real.sqrt x))

/-- **The off-diagonal vanishes, given shift-uniform averaged correlations.** -/
theorem offDiagonalVanishes_of_uniformCorrelations {f : ℕ → ℝ} (hf : ∀ n, |f n| ≤ 1)
    {hh : ℝ → ℝ} (hgrow : Tendsto hh atTop atTop)
    (hcap : ∀ᶠ x in atTop, hh x ≤ Real.sqrt x)
    (hcorr : UniformCorrelationSmall f hh) :
    OffDiagonalVanishes f hh := by
  rw [OffDiagonalVanishes, NormedAddGroup.tendsto_nhds_zero]
  intro ε hε
  filter_upwards [hcorr (ε / 824) (by linarith), hcap,
    hgrow.eventually_ge_atTop (max 1 (64 / ε)), Filter.eventually_ge_atTop (64 : ℝ)]
    with x hPx hcapx hhbig hx64
  set h := hh x with hhdef
  have hh1 : (1 : ℝ) ≤ h := le_trans (le_max_left _ _) hhbig
  have hh64 : 64 / ε ≤ h := le_trans (le_max_right _ _) hhbig
  have hεh : (64 : ℝ) ≤ h * ε := by
    rw [div_le_iff₀ hε] at hh64
    linarith
  have hs8 : (8 : ℝ) ≤ Real.sqrt x := eight_le_sqrt hx64
  have hden : (0 : ℝ) < h ^ 2 * Real.sqrt x := by nlinarith [hh1, hs8]
  have hbase := abs_offDiagonal_uniform_le hf hx64 hh1 hcapx hPx
  have hP0 : (0 : ℝ) ≤ ε / 824 * (h * Real.sqrt x) := by positivity
  have step2 : (88 * h + 15) * (ε / 824 * (h * Real.sqrt x))
      ≤ (ε / 8) * (h ^ 2 * Real.sqrt x) := by
    nlinarith [hh1, hs8, hε.le,
      mul_nonneg (mul_nonneg hε.le (by linarith : (0:ℝ) ≤ h - 1))
        (mul_nonneg (by linarith : (0:ℝ) ≤ h) (by linarith : (0:ℝ) ≤ Real.sqrt x))]
  have step3 : 2 * h * (3 * Real.sqrt x + 1) ≤ (ε / 8) * (h ^ 2 * Real.sqrt x) := by
    have hhs : (0 : ℝ) ≤ h * Real.sqrt x := by nlinarith [hh1, hs8]
    nlinarith [hεh, hhs, hh1, hs8]
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hden, div_lt_iff₀ hden, abs_mul]
  have habs : |(2 : ℝ)| = 2 := by norm_num
  rw [habs]
  nlinarith [hbase, step2, step3, hden, hε]

/-- **The fibre mean square, from shift-uniform averaged correlations.** -/
theorem averagedMeanSquare_of_uniformCorrelations {f : ℕ → ℝ} (hf : ∀ n, |f n| ≤ 1)
    {hh : ℝ → ℝ} (hgrow : Tendsto hh atTop atTop)
    (hcap : ∀ᶠ x in atTop, hh x ≤ Real.sqrt x)
    (hcorr : UniformCorrelationSmall f hh) :
    AveragedMeanSquare f hh :=
  averagedMeanSquare_of_offDiagonal hf hgrow
    (offDiagonalVanishes_of_uniformCorrelations hf hgrow hcap hcorr)

/-- **The bilinear all-interval theorem at `μ`, from shift-uniform averaged correlations.** -/
theorem MRBilinear_moebius_of_uniformCorrelations {hh : ℝ → ℝ} (hgrow : Tendsto hh atTop atTop)
    (hcap : ∀ᶠ x in atTop, hh x ≤ Real.sqrt x)
    (hcorr : UniformCorrelationSmall (fun n : ℕ => ((μ n : ℤ) : ℝ)) hh) :
    MRBilinear (fun n : ℕ => ((μ n : ℤ) : ℝ)) hh :=
  MRBilinear_moebius_of_averaged
    (averagedShortInterval_of_meanSquare hgrow
      (averagedMeanSquare_of_uniformCorrelations abs_moebius_real_le_one hgrow hcap hcorr))
    (eventually_pos_window_normalisation hgrow)

end RHTower.Sieve

end
