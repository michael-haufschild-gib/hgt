import GaloisForLFunctions.RHTower.Sieve.ChernoffTails
import GaloisForLFunctions.RHTower.MobiusWoldBreadthTwoSidedDeviationRate

/-!
# The tilt optimum is the two-sided entropy rate

Both Chernoff tails carry a factor `(log z)^{w-1} / w^m` in which `w` is a free tilt and `m` the
threshold.  At the natural calibration `m = w · log log z` this factor collapses to

`(log z)^{-I(w)}`,  `I(w) = 1 - w + w log w`,

which is exactly the two-sided deviation rate of `MobiusWoldBreadthTwoSidedDeviationRate.lean`.
The same identity serves both tails: the lower one has `w = t ≤ 1` and the exponent `-(1-t)`, the
upper one has `w = u ≥ 1` and the exponent `u-1`, and these are the same expression `w - 1`.

Since that rate is strictly positive on both sides of `w = 1`, each tail is a genuine negative
power of `log z`.
-/

namespace RHTower.Sieve

open Finset Nat

/-- **Tilt optimum.**  At the calibration `m = w · log log z` the Chernoff factor is the negative
power of `log z` given by the entropy rate. -/
theorem pow_div_pow_eq_rate {z : ℕ} (hz : 2 ≤ z) {w : ℝ} (hw : 0 < w) {m : ℕ}
    (hm : (m : ℝ) = w * logLog z) :
    (Real.log z) ^ (w - 1) / w ^ m = (Real.log z) ^ (-woldBreadthDeviationRate w) := by
  have hzR : (2 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
  have hlogz : 0 < Real.log z := Real.log_pos (by linarith)
  have hwm : (0 : ℝ) < w ^ m := pow_pos hw m
  have hnum : (Real.log z) ^ (w - 1) = Real.exp (Real.log (Real.log z) * (w - 1)) :=
    Real.rpow_def_of_pos hlogz _
  have hden : w ^ m = Real.exp ((m : ℝ) * Real.log w) := by
    rw [← Real.log_pow, Real.exp_log hwm]
  have hrhs : (Real.log z) ^ (-woldBreadthDeviationRate w)
      = Real.exp (Real.log (Real.log z) * (-woldBreadthDeviationRate w)) :=
    Real.rpow_def_of_pos hlogz _
  rw [hnum, hden, hrhs, ← Real.exp_sub]
  congr 1
  rw [hm]
  unfold logLog woldBreadthDeviationRate
  ring

/-- **Lower tail at the tilt optimum.**  The entropy rate appears explicitly. -/
theorem card_omega_le_le_rate (a b z k r : ℕ) (hab : a ≤ b) (hz : 2 ≤ z) (hr : Even r)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) (hk : (k : ℝ) = t * logLog z)
    {lam : ℝ} (hlam : 1 ≤ lam) :
    ((#{n ∈ Finset.Ioc a b | n.primeFactors.card ≤ k} : ℕ) : ℝ)
      ≤ ((b : ℝ) - a) * (Real.exp ((1 - t) * mertensSecondLowerConst)
              * (Real.log z) ^ (-woldBreadthDeviationRate t)
            + Real.exp (lam * mertensSecondUpperConst) * (Real.log z) ^ lam / (lam ^ r * t ^ k))
        + ((truncDivisors (primorial z) r).card : ℝ) / t ^ k := by
  have htk : (0 : ℝ) < t ^ k := pow_pos ht0 k
  have hlen : (0 : ℝ) ≤ (b : ℝ) - a := by
    have : (a : ℝ) ≤ b := by exact_mod_cast hab
    linarith
  have hbase := card_omega_le_le_chernoff a b z k r hab hz hr ht0 ht1 hlam
  rw [← le_div_iff₀ htk] at hbase
  refine le_trans hbase (le_of_eq ?_)
  have hrate : (Real.log z) ^ (-(1 - t)) / t ^ k
      = (Real.log z) ^ (-woldBreadthDeviationRate t) := by
    have hneg : -(1 - t) = t - 1 := by ring
    rw [hneg]
    exact pow_div_pow_eq_rate hz ht0 hk
  have hrate' : (Real.log z) ^ (-(1 - t))
      = (Real.log z) ^ (-woldBreadthDeviationRate t) * t ^ k := by
    rw [← hrate]
    field_simp
  rw [hrate']
  field_simp

/-- **Upper tail at the tilt optimum.**  The same entropy rate governs the other side. -/
theorem card_omega_ge_le_rate (a b z k k' J c D : ℕ) (hab : a ≤ b) (hz : 2 ≤ z) (hzb : z ≤ b)
    (hJ : 1 ≤ J) (hc : 1 ≤ c) (hD : b < (D + 1) ^ c) (hk : k' + c * J ≤ k + 1)
    {u : ℝ} (hu1 : 1 ≤ u) (hu2 : u ≤ 2) (hku : (k' : ℝ) = u * logLog z)
    {v : ℝ} (hv : 1 ≤ v) :
    ((#{n ∈ Finset.Ioc a b | k ≤ n.primeFactors.card} : ℕ) : ℝ)
      ≤ ((b : ℝ) - a) * (Real.exp ((u - 1) * mertensSecondUpperConst)
              * (Real.log z) ^ (-woldBreadthDeviationRate u))
          + ((truncDivisors (primorial z) k').card : ℝ) / u ^ k'
        + (((b : ℝ) - a) * (Real.exp (v * (mertensS b - mertensS z)) / v ^ J) + (D : ℝ)) := by
  have hu0 : (0 : ℝ) < u := lt_of_lt_of_le zero_lt_one hu1
  have huk : (0 : ℝ) < u ^ k' := pow_pos hu0 k'
  have hbase := card_omega_ge_le_chernoff a b z k k' J c D hab hz hzb hJ hc hD hk hu1 hu2 hv
  refine le_trans hbase (le_of_eq ?_)
  have hrate := pow_div_pow_eq_rate hz hu0 hku
  have hsplit : (((b : ℝ) - a) * (Real.exp ((u - 1) * mertensSecondUpperConst)
        * (Real.log z) ^ (u - 1)) + ((truncDivisors (primorial z) k').card : ℝ)) / u ^ k'
      = ((b : ℝ) - a) * (Real.exp ((u - 1) * mertensSecondUpperConst)
            * ((Real.log z) ^ (u - 1) / u ^ k'))
        + ((truncDivisors (primorial z) k').card : ℝ) / u ^ k' := by
    field_simp
  rw [hsplit, hrate]

end RHTower.Sieve
