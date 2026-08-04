import GaloisForLFunctions.RHTower.Sieve.CoprimeLogSum
import GaloisForLFunctions.RHTower.Sieve.SharedSectorLimit

/-!
# The bilinear theorem at a moving pair of parameters, reduced

The card's third input is the bilinear all-interval theorem at the rescaled pair `(x/p², h/p)` for
the weight `μ²·1_{p∤·}`.  The fibre decomposition does not care which pair of parameters is used, so
the reduction is the same one, stated for a moving scale:

    ∑_{a ∈ block(X)} | (∑_{b ∈ fibre(a)} f(b)) − c·h√X/a |  =  o(h√X)   ⟹   MRBilinearAt f X hh,

for any unit-bounded weight whose partial sums are `mc + O(√m)` and whose block mean tends to `c`.
The constant `c²` in the conclusion is produced by the logarithmic block mean, exactly as in the
unrescaled case.
-/

namespace RHTower.Sieve

open Finset Filter Topology
open scoped ArithmeticFunction.Moebius

/-- **The averaged short-interval property at a moving pair of parameters.** -/
def AveragedShortIntervalDensityAt (f : ℕ → ℝ) (c : ℝ) (X hh : ℝ → ℝ) : Prop :=
  Tendsto (fun x => (∑ a ∈ outerBlock (X x) (hh x),
      |(∑ b ∈ innerFibre (X x) (hh x) a, f b) - c * (hh x * Real.sqrt (X x) / (a : ℝ))|)
      / (hh x * Real.sqrt (X x) * Real.log 2)) atTop (𝓝 0)

/-- **The reduction at a moving pair of parameters.** -/
theorem MRBilinearAt_of_averaged {f : ℕ → ℝ} {c C : ℝ} {X hh : ℝ → ℝ}
    (hf : ∀ n, |f n| ≤ 1) (hc : 0 ≤ c) (hC : 0 ≤ C)
    (hcount : ∀ m : ℕ, |weightErr f c m| ≤ C * Real.sqrt m + C)
    (hmean : Tendsto (fun x => blockMean f (X x)) atTop (𝓝 c))
    (hXtop : Tendsto X atTop atTop) (hhtop : Tendsto hh atTop atTop)
    (havg : AveragedShortIntervalDensityAt f c X hh) :
    MRBilinearAt f X hh := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hXsqrt : Tendsto (fun x => Real.sqrt (X x)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hXtop
  have hpos : ∀ᶠ x in atTop, 0 < hh x * Real.sqrt (X x) * Real.log 2 := by
    filter_upwards [hXsqrt.eventually_gt_atTop 0, hhtop.eventually_gt_atTop 0] with x hs hhx
    positivity
  have hblock : ∀ᶠ x in atTop,
      outerBlock (X x) (hh x) = Finset.Icc ⌈Real.sqrt (X x)⌉₊ ⌊2 * Real.sqrt (X x)⌋₊ := by
    filter_upwards [hXtop.eventually_ge_atTop 4, hhtop.eventually_ge_atTop 0] with x hx hhx
    exact outerBlock_eq hx hhx
  have hlogmean : Tendsto (fun x : ℝ =>
      ∑ a ∈ Finset.Icc ⌈Real.sqrt (X x)⌉₊ ⌊2 * Real.sqrt (X x)⌋₊, f a / (a : ℝ))
      atTop (𝓝 (c * Real.log 2)) :=
    (tendsto_block_log_mean_of_count hc hC hcount).comp hXsqrt
  have hmainlim : Tendsto (fun x : ℝ =>
      c * (∑ a ∈ Finset.Icc ⌈Real.sqrt (X x)⌉₊ ⌊2 * Real.sqrt (X x)⌋₊, f a / (a : ℝ))
        / Real.log 2) atTop (𝓝 (c ^ 2)) := by
    have hbase := (hlogmean.const_mul c).div_const (Real.log 2)
    have hval : c * (c * Real.log 2) / Real.log 2 = c ^ 2 := by
      field_simp
    rwa [hval] at hbase
  have hdiff : Tendsto (fun x : ℝ =>
      pairSum f (X x) (hh x) / (hh x * Real.sqrt (X x) * Real.log 2)
        - c * (∑ a ∈ Finset.Icc ⌈Real.sqrt (X x)⌉₊ ⌊2 * Real.sqrt (X x)⌋₊, f a / (a : ℝ))
            / Real.log 2) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ havg
    filter_upwards [hpos, hblock, hXsqrt.eventually_gt_atTop 0,
      hhtop.eventually_gt_atTop 0] with x hx hbx hs hhx
    have hprod : (0 : ℝ) < hh x * Real.sqrt (X x) := by positivity
    have hbase := abs_pairSum_sub_main_le hf c (X x) (hh x)
    rw [hbx] at hbase
    have hval : pairSum f (X x) (hh x) / (hh x * Real.sqrt (X x) * Real.log 2)
        - c * (∑ a ∈ Finset.Icc ⌈Real.sqrt (X x)⌉₊ ⌊2 * Real.sqrt (X x)⌋₊, f a / (a : ℝ))
            / Real.log 2
        = (pairSum f (X x) (hh x)
            - c * (hh x * Real.sqrt (X x))
              * (∑ a ∈ Finset.Icc ⌈Real.sqrt (X x)⌉₊ ⌊2 * Real.sqrt (X x)⌋₊, f a / (a : ℝ)))
          / (hh x * Real.sqrt (X x) * Real.log 2) := by
      field_simp
    rw [Real.norm_eq_abs, hval, abs_div, abs_of_pos hx, hbx]
    exact div_le_div_of_nonneg_right hbase hx.le
  have hpair := hdiff.add hmainlim
  rw [zero_add] at hpair
  have hpair' : Tendsto (fun x : ℝ =>
      pairSum f (X x) (hh x) / (hh x * Real.sqrt (X x) * Real.log 2))
      atTop (𝓝 (c ^ 2)) := by
    refine hpair.congr fun x => ?_
    ring
  have hsq : Tendsto (fun x : ℝ => (blockMean f (X x)) ^ 2) atTop (𝓝 (c ^ 2)) := hmean.pow 2
  have := hpair'.sub hsq
  rw [sub_self] at this
  exact this

/-- **The card's third input, reduced.**  The shared-prime sector needs only the averaged
short-interval estimate for `μ²·1_{p∤·}` at the rescaled pair of parameters. -/
theorem MRBilinearAt_coprime_of_averaged {p : ℕ} (hp : p.Prime) {hh : ℝ → ℝ}
    (hgrow : Tendsto hh atTop atTop)
    (havg : AveragedShortIntervalDensityAt (coprimeSquarefreeWeight p)
      (squarefreeDensity * (p : ℝ) / ((p : ℝ) + 1))
      (fun x => x / (p : ℝ) ^ 2) (fun x => hh x / (p : ℝ))) :
    MRBilinearAt (coprimeSquarefreeWeight p) (fun x => x / (p : ℝ) ^ 2)
      (fun x => hh x / (p : ℝ)) := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hpsq : (0 : ℝ) < (p : ℝ) ^ 2 := by positivity
  have hXtop : Tendsto (fun x : ℝ => x / (p : ℝ) ^ 2) atTop atTop :=
    tendsto_id.atTop_div_const hpsq
  have hhtop : Tendsto (fun x : ℝ => hh x / (p : ℝ)) atTop atTop :=
    hgrow.atTop_div_const hp0
  exact MRBilinearAt_of_averaged (abs_coprimeSquarefreeWeight_le_one p)
    (coprime_block_density_nonneg hp) (by norm_num) (abs_weightErr_coprime_le hp)
    (tendsto_blockMean_coprime hp) hXtop hhtop havg

end RHTower.Sieve
