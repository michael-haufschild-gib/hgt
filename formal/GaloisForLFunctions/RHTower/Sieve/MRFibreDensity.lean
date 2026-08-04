import GaloisForLFunctions.RHTower.Sieve.MRFibreReduction
import GaloisForLFunctions.RHTower.Sieve.PairFibreTrivial
import GaloisForLFunctions.RHTower.Sieve.SquarefreeLogSum

/-!
# The bilinear theorem at `μ²`, reduced

At `μ` the block mean vanishes and the bilinear all-interval theorem is exactly an averaged
cancellation statement.  At `μ²` the block mean is the squarefree density `D`, so the fibre sums are
expected to equal their length times `D` rather than to cancel, and the reduction reads

    ∑_{a ∈ block} | (∑_{b ∈ fibre(a)} μ²(b)) − D·h√x/a |  =  o(h√x)   ⟹   MRBilinear μ² hh.

The main term is then `D·h√x·∑_{a ∈ block} μ²(a)/a`, and the *logarithmic* block mean
`∑_{√x < a ≤ 2√x} μ²(a)/a → D log 2` turns it into `D²` after the normalisation — exactly the square
of the block mean that the theorem asserts.

So both instances the card needs are averaged short-interval statements about one arithmetic
function each, with the constant `D²` produced by the logarithmic mean rather than assumed.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction Filter Topology
open scoped ArithmeticFunction.Moebius

/-- **The averaged short-interval property with a density.**  The fibre sums agree with their
lengths times `c`, on average over the block. -/
def AveragedShortIntervalDensity (f : ℕ → ℝ) (c : ℝ) (hh : ℝ → ℝ) : Prop :=
  Tendsto (fun x => (∑ a ∈ outerBlock x (hh x),
      |(∑ b ∈ innerFibre x (hh x) a, f b) - c * (hh x * Real.sqrt x / (a : ℝ))|)
      / (hh x * Real.sqrt x * Real.log 2)) atTop (𝓝 0)

/-- The pair sum against its density main term. -/
theorem abs_pairSum_sub_main_le {f : ℕ → ℝ} (hf : ∀ n, |f n| ≤ 1) (c x h : ℝ) :
    |pairSum f x h - c * (h * Real.sqrt x) * (∑ a ∈ outerBlock x h, f a / (a : ℝ))|
      ≤ ∑ a ∈ outerBlock x h,
          |(∑ b ∈ innerFibre x h a, f b) - c * (h * Real.sqrt x / (a : ℝ))| := by
  rw [pairSum_eq_sum_fibre]
  have hmain : c * (h * Real.sqrt x) * (∑ a ∈ outerBlock x h, f a / (a : ℝ))
      = ∑ a ∈ outerBlock x h, f a * (c * (h * Real.sqrt x / (a : ℝ))) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro a _
    ring
  rw [hmain, ← Finset.sum_sub_distrib]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine Finset.sum_le_sum ?_
  intro a _
  have hfac : f a * (∑ b ∈ innerFibre x h a, f b) - f a * (c * (h * Real.sqrt x / (a : ℝ)))
      = f a * ((∑ b ∈ innerFibre x h a, f b) - c * (h * Real.sqrt x / (a : ℝ))) := by ring
  rw [hfac, abs_mul]
  exact mul_le_of_le_one_left (abs_nonneg _) (hf a)

theorem abs_moebius_sq_real_le_one (n : ℕ) : |((μ n : ℤ) : ℝ) ^ 2| ≤ 1 := by
  have h := abs_moebius_real_le_one n
  have h0 : (0 : ℝ) ≤ ((μ n : ℤ) : ℝ) ^ 2 := sq_nonneg _
  rw [abs_of_nonneg h0]
  nlinarith [abs_nonneg (((μ n : ℤ) : ℝ)), sq_abs (((μ n : ℤ) : ℝ))]

/-- The logarithmic block mean of `μ²`, in the variable of the pair sum. -/
theorem tendsto_block_moebius_sq_log_mean :
    Tendsto (fun x : ℝ => ∑ a ∈ Finset.Icc ⌈Real.sqrt x⌉₊ ⌊2 * Real.sqrt x⌋₊,
        ((μ a : ℤ) : ℝ) ^ 2 / (a : ℝ))
      atTop (𝓝 (squarefreeDensity * Real.log 2)) :=
  tendsto_squarefree_block_log_mean.comp Real.tendsto_sqrt_atTop

/-- **The bilinear all-interval theorem at `μ²`, reduced.** -/
theorem MRBilinear_moebius_sq_of_averaged {hh : ℝ → ℝ}
    (havg : AveragedShortIntervalDensity (fun n : ℕ => ((μ n : ℤ) : ℝ) ^ 2)
      squarefreeDensity hh)
    (hgrow : Tendsto hh atTop atTop) :
    MRBilinear (fun n : ℕ => ((μ n : ℤ) : ℝ) ^ 2) hh := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hpos : ∀ᶠ x in atTop, 0 < hh x * Real.sqrt x * Real.log 2 := by
    filter_upwards [eventually_gt_atTop (4 : ℝ), hgrow.eventually_gt_atTop 0] with x hx hhx
    have hs : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 (by linarith)
    positivity
  have hblock : ∀ᶠ x in atTop,
      outerBlock x (hh x) = Finset.Icc ⌈Real.sqrt x⌉₊ ⌊2 * Real.sqrt x⌋₊ := by
    filter_upwards [eventually_ge_atTop (4 : ℝ), hgrow.eventually_ge_atTop 0] with x hx hhx
    exact outerBlock_eq hx hhx
  -- the main term
  have hmainlim : Tendsto (fun x : ℝ =>
      squarefreeDensity
        * (∑ a ∈ Finset.Icc ⌈Real.sqrt x⌉₊ ⌊2 * Real.sqrt x⌋₊, ((μ a : ℤ) : ℝ) ^ 2 / (a : ℝ))
        / Real.log 2) atTop (𝓝 (squarefreeDensity ^ 2)) := by
    have hbase := (tendsto_block_moebius_sq_log_mean.const_mul squarefreeDensity).div_const
      (Real.log 2)
    have hval : squarefreeDensity * (squarefreeDensity * Real.log 2) / Real.log 2
        = squarefreeDensity ^ 2 := by
      field_simp
    rwa [hval] at hbase
  -- the deviation is controlled by the averaged hypothesis
  have hdiff : Tendsto (fun x : ℝ =>
      pairSum (fun n : ℕ => ((μ n : ℤ) : ℝ) ^ 2) x (hh x)
          / (hh x * Real.sqrt x * Real.log 2)
        - squarefreeDensity
            * (∑ a ∈ Finset.Icc ⌈Real.sqrt x⌉₊ ⌊2 * Real.sqrt x⌋₊,
                ((μ a : ℤ) : ℝ) ^ 2 / (a : ℝ)) / Real.log 2) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ havg
    filter_upwards [hpos, hblock, eventually_gt_atTop (4 : ℝ),
      hgrow.eventually_gt_atTop 0] with x hx hbx hx4 hhx
    have hs : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 (by linarith)
    have hprod : (0 : ℝ) < hh x * Real.sqrt x := by positivity
    have hbase := abs_pairSum_sub_main_le abs_moebius_sq_real_le_one squarefreeDensity x (hh x)
    rw [hbx] at hbase
    have hval : pairSum (fun n : ℕ => ((μ n : ℤ) : ℝ) ^ 2) x (hh x)
          / (hh x * Real.sqrt x * Real.log 2)
        - squarefreeDensity
            * (∑ a ∈ Finset.Icc ⌈Real.sqrt x⌉₊ ⌊2 * Real.sqrt x⌋₊,
                ((μ a : ℤ) : ℝ) ^ 2 / (a : ℝ)) / Real.log 2
        = (pairSum (fun n : ℕ => ((μ n : ℤ) : ℝ) ^ 2) x (hh x)
            - squarefreeDensity * (hh x * Real.sqrt x)
              * (∑ a ∈ Finset.Icc ⌈Real.sqrt x⌉₊ ⌊2 * Real.sqrt x⌋₊,
                  ((μ a : ℤ) : ℝ) ^ 2 / (a : ℝ)))
          / (hh x * Real.sqrt x * Real.log 2) := by
      field_simp
    rw [Real.norm_eq_abs, hval, abs_div, abs_of_pos hx, hbx]
    exact div_le_div_of_nonneg_right hbase hx.le
  have hpair := hdiff.add hmainlim
  rw [zero_add] at hpair
  have hpair' : Tendsto (fun x : ℝ =>
      pairSum (fun n : ℕ => ((μ n : ℤ) : ℝ) ^ 2) x (hh x)
        / (hh x * Real.sqrt x * Real.log 2)) atTop (𝓝 (squarefreeDensity ^ 2)) := by
    refine hpair.congr fun x => ?_
    ring
  have hmean : Tendsto
      (fun x => (blockMean (fun n : ℕ => ((μ n : ℤ) : ℝ) ^ 2) x) ^ 2)
      atTop (𝓝 (squarefreeDensity ^ 2)) := tendsto_blockMean_moebius_sq.pow 2
  have := hpair'.sub hmean
  rw [sub_self] at this
  exact this

end RHTower.Sieve
