import GaloisForLFunctions.RHTower.Sieve.PairFibre

/-!
# The bilinear theorem reduced to an averaged short-interval bound

The fibre decomposition turns the balanced pair sum into an outer sum of short Möbius sums, one for
each starting point `x/a` with `a` in the dyadic block.  Discarding the outer weight — legitimate,
since `|μ| ≤ 1` — leaves

    |pairSum μ x h|  ≤  ∑_{a ∈ block} |∑_{b ∈ fibre(a)} μ(b)|,

so the bilinear all-interval theorem at `μ` follows from cancellation in the *average* over the
`√x` starting points, not from cancellation in any single short interval.  That is the correct shape
of the hypothesis: no pointwise short-interval statement is true at window lengths as short as the
card allows, whereas the averaged one is exactly Matomäki–Radziwiłł's theorem.

The reduction is recorded as a named `Prop` so that the analytic work has a single target.
-/

namespace RHTower.Sieve

open Finset Filter Topology
open scoped ArithmeticFunction.Moebius

/-- **The averaged short-interval property.**  The mean over the dyadic block of starting points of
the absolute short sum is `o` of the trivial size. -/
def AveragedShortInterval (f : ℕ → ℝ) (hh : ℝ → ℝ) : Prop :=
  Tendsto (fun x => (∑ a ∈ outerBlock x (hh x), |∑ b ∈ innerFibre x (hh x) a, f b|)
      / (hh x * Real.sqrt x * Real.log 2)) atTop (𝓝 0)

/-- The pair sum vanishes on the trivial scale once the average does. -/
theorem tendsto_pairSum_of_averaged {f : ℕ → ℝ} {hh : ℝ → ℝ} (hf : ∀ n, |f n| ≤ 1)
    (havg : AveragedShortInterval f hh)
    (hpos : ∀ᶠ x in atTop, 0 < hh x * Real.sqrt x * Real.log 2) :
    Tendsto (fun x => pairSum f x (hh x) / (hh x * Real.sqrt x * Real.log 2)) atTop (𝓝 0) := by
  refine squeeze_zero_norm' ?_ havg
  filter_upwards [hpos] with x hx
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hx]
  have hnum := abs_pairSum_le_sum_abs_fibre hf x (hh x)
  exact div_le_div_of_nonneg_right hnum hx.le

/-- **The reduction.**  For a unit-bounded weight whose block mean vanishes, the bilinear
all-interval theorem is exactly the averaged short-interval property. -/
theorem MRBilinear_of_averaged {f : ℕ → ℝ} {hh : ℝ → ℝ} (hf : ∀ n, |f n| ≤ 1)
    (hmean : Tendsto (blockMean f) atTop (𝓝 0))
    (havg : AveragedShortInterval f hh)
    (hpos : ∀ᶠ x in atTop, 0 < hh x * Real.sqrt x * Real.log 2) :
    MRBilinear f hh := by
  have hpair := tendsto_pairSum_of_averaged hf havg hpos
  have hsq : Tendsto (fun x => (blockMean f x) ^ (2 : ℕ)) atTop (𝓝 0) := by
    have := hmean.pow 2
    simpa using this
  have := hpair.sub hsq
  rw [sub_zero] at this
  exact this

theorem abs_moebius_real_le_one (n : ℕ) : |((μ n : ℤ) : ℝ)| ≤ 1 := by
  rcases eq_or_ne (μ n) 0 with h | h
  · rw [h]
    norm_num
  · rcases ArithmeticFunction.moebius_ne_zero_iff_eq_or.mp h with h1 | h1 <;> rw [h1] <;> norm_num

/-- **The bilinear all-interval theorem at `μ`, reduced.**  Its whole content is that the short
Möbius sums over the `√x` starting points `x/a` cancel on average. -/
theorem MRBilinear_moebius_of_averaged {hh : ℝ → ℝ}
    (havg : AveragedShortInterval (fun n : ℕ => ((μ n : ℤ) : ℝ)) hh)
    (hpos : ∀ᶠ x in atTop, 0 < hh x * Real.sqrt x * Real.log 2) :
    MRBilinear (fun n : ℕ => ((μ n : ℤ) : ℝ)) hh :=
  MRBilinear_of_averaged abs_moebius_real_le_one tendsto_blockMean_moebius havg hpos

end RHTower.Sieve
