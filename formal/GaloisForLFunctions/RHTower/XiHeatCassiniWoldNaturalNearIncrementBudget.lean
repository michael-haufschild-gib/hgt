import GaloisForLFunctions.RHTower.XiHeatCassiniWoldHolonomyExpRate
import GaloisForLFunctions.RHTower.EulerFisherCurvature

/-!
# Absolute near-pair budget for natural Wold increments

For the actual residual increment `d_n = R_(n+2) - R_(n+1)`, the literal
prime coefficient and integer logarithmic mesh give
`|d_n| ≤ (log(n+1)+2)/(n+1)`. This majorant decreases with the cutoff.
Hence the weighted absolute interaction of `d_n` with the next
`floor((n+1)^eta)` increments is summable whenever `2*t+eta<1`.

At square-root width this estimate covers `t<1/4`. The signed interactions
outside the displayed window remain to be controlled in a full drift estimate.
-/

open scoped BigOperators
namespace RHTower
noncomputable section

/-- Consecutive natural residual increment, starting at cutoff one. -/
def xiHeatCassiniWoldNatIncrement (n : ℕ) : ℝ :=
  xiHeatCassiniWoldNatResidualLogDiscrepancy (n + 2) -
    xiHeatCassiniWoldNatResidualLogDiscrepancy (n + 1)

/-- The residual increment is the literal prime weight minus its logarithmic cell. -/
theorem xiHeatCassiniWoldNatIncrement_eq (n : ℕ) :
    xiHeatCassiniWoldNatIncrement n =
      xiHeatCassiniWoldNatWeight (n + 2) -
        (Real.log (n + 2) - Real.log (n + 1)) := by
  have hsum : xiHeatCassiniWoldNatWeightSum (n + 2) =
      xiHeatCassiniWoldNatWeightSum (n + 1) + xiHeatCassiniWoldNatWeight (n + 2) := by
    rw [xiHeatCassiniWoldNatWeightSum, xiHeatCassiniWoldNatWeightSum,
      Sieve.Icc_zero_eq_range, Sieve.Icc_zero_eq_range]
    simpa [Nat.add_assoc] using
      Finset.sum_range_succ xiHeatCassiniWoldNatWeight (n + 2)
  simp only [xiHeatCassiniWoldNatIncrement, xiHeatCassiniWoldNatResidualLogDiscrepancy]
  rw [hsum]
  push_cast
  ring

private theorem nearWeight_bounds {m : ℕ} (hm : 1 ≤ m) :
    0 ≤ xiHeatCassiniWoldNatWeight m ∧
      xiHeatCassiniWoldNatWeight m ≤ Real.log m / m := by
  unfold xiHeatCassiniWoldNatWeight
  split_ifs with hp
  · exact ⟨woldCoeff_nonneg 1 ⟨m, hp⟩,
      (woldCoeff_one_le_harmonic_le_eight_mul_woldCoeff_one ⟨m, hp⟩).1⟩
  · exact ⟨le_rfl, div_nonneg (Real.log_nonneg (by exact_mod_cast hm))
      (Nat.cast_nonneg m)⟩

/-- A decreasing logarithmic envelope for the actual arithmetic increment. -/
theorem xiHeatCassiniWoldNatIncrement_abs_le (n : ℕ) :
    |xiHeatCassiniWoldNatIncrement n| ≤ (Real.log (n + 1) + 2) / (n + 1) := by
  have hn : (0 : ℝ) < n + 1 := by positivity
  have hlog : 0 ≤ Real.log (n + 2) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hw := nearWeight_bounds (m := n + 2) (by omega)
  push_cast at hw
  have hg0 : 0 ≤ Real.log (n + 2) - Real.log (n + 1) :=
    sub_nonneg.mpr (Real.log_le_log hn (by linarith))
  have hg : Real.log (n + 2) - Real.log (n + 1) ≤ 1 / (n + 1) := by
    simpa only [Nat.cast_add, Nat.cast_one, show (n : ℝ) + 1 + 1 = n + 2 by ring]
      using log_succ_sub_log_le (j := n + 1) (by omega)
  have hi : 1 / ((n : ℝ) + 1) ≤ 1 :=
    (div_le_one hn).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hw' : xiHeatCassiniWoldNatWeight (n + 2) ≤
      Real.log (n + 2) / (n + 1) := hw.2.trans
        (div_le_div_of_nonneg_left hlog hn (by linarith))
  calc
    |xiHeatCassiniWoldNatIncrement n| ≤ xiHeatCassiniWoldNatWeight (n + 2) +
        (Real.log (n + 2) - Real.log (n + 1)) := by
      rw [xiHeatCassiniWoldNatIncrement_eq]
      exact abs_le.mpr ⟨by linarith [hw.1], by linarith⟩
    _ ≤ Real.log (n + 2) / (n + 1) + 1 / (n + 1) := add_le_add hw' hg
    _ ≤ (Real.log (n + 1) + 1) / (n + 1) + 1 / (n + 1) := by
      gcongr
      linarith
    _ = (Real.log (n + 1) + 2) / (n + 1) := by ring

private theorem nearEnvelope_antitone {x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) :
    (Real.log y + 2) / y ≤ (Real.log x + 2) / x := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hy0 : 0 < y := hx0.trans_le hxy
  have hlog := Real.log_le_sub_one_of_pos (x := y / x) (by positivity)
  rw [Real.log_div hy0.ne' hx0.ne'] at hlog
  have hdiv : Real.log y - Real.log x ≤ (y - x) / x := by
    calc
      _ ≤ y / x - 1 := hlog
      _ = (y - x) / x := by field_simp
  have hmul := (le_div_iff₀ hx0).mp hdiv
  have hnon : 0 ≤ Real.log x + 1 := by linarith [Real.log_nonneg hx]
  have hcomp := mul_le_mul_of_nonneg_right hxy hnon
  apply (div_le_div_iff₀ hy0 hx0).mpr
  nlinarith

private theorem nearPair_bound (n H : ℕ) :
    (∑ j ∈ Finset.Ioc n (n + H), |xiHeatCassiniWoldNatIncrement n * xiHeatCassiniWoldNatIncrement j|) ≤
      (H : ℝ) * ((Real.log (n + 1) + 2) / (n + 1)) ^ 2 := by
  have hn : (1 : ℝ) ≤ n + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have hb : 0 ≤ (Real.log (n + 1) + 2) / (n + 1) := by
    exact div_nonneg (by linarith [Real.log_nonneg hn]) (by positivity)
  calc
    _ ≤ ∑ _j ∈ Finset.Ioc n (n + H),
        ((Real.log (n + 1) + 2) / (n + 1)) ^ 2 := by
      apply Finset.sum_le_sum
      intro j hj
      have hjn : n ≤ j := (Finset.mem_Ioc.mp hj).1.le
      have hmono := nearEnvelope_antitone hn
        (show (n : ℝ) + 1 ≤ j + 1 by exact_mod_cast Nat.add_le_add_right hjn 1)
      rw [abs_mul, pow_two]
      exact mul_le_mul (xiHeatCassiniWoldNatIncrement_abs_le n)
        ((xiHeatCassiniWoldNatIncrement_abs_le j).trans hmono) (abs_nonneg _) hb
    _ = _ := by simp

private theorem nearPair_weighted_bound (n : ℕ) (t eta : ℝ) :
    ((n + 1 : ℕ) : ℝ) ^ (2 * t) *
        (∑ j ∈ Finset.Ioc n (n + ⌊((n + 1 : ℕ) : ℝ) ^ eta⌋₊),
          |xiHeatCassiniWoldNatIncrement n * xiHeatCassiniWoldNatIncrement j|) ≤
      (2 * |Real.log ((n + 1 : ℕ) : ℝ)| ^ 2 + 8) *
        ((n + 1 : ℕ) : ℝ) ^ (-(2 - (2 * t + eta))) := by
  let x : ℝ := n + 1
  have hx : 0 < x := by dsimp [x]; positivity
  have hf := Nat.floor_le (Real.rpow_nonneg hx.le eta)
  have hs : (Real.log x + 2) ^ 2 ≤ 2 * |Real.log x| ^ 2 + 8 := by
    rw [sq_abs]
    nlinarith [sq_nonneg (Real.log x - 2)]
  calc
    _ ≤ x ^ (2 * t) *
        ((⌊x ^ eta⌋₊ : ℝ) * ((Real.log x + 2) / x) ^ 2) := by
      simpa only [Nat.cast_add, Nat.cast_one, x] using
        mul_le_mul_of_nonneg_left (nearPair_bound n ⌊x ^ eta⌋₊)
          (Real.rpow_nonneg hx.le (2 * t))
    _ ≤ x ^ (2 * t) * (x ^ eta * ((Real.log x + 2) / x) ^ 2) := by
      gcongr
    _ = (Real.log x + 2) ^ 2 * x ^ (-(2 - (2 * t + eta))) := by
      rw [← mul_assoc, ← Real.rpow_add hx]
      rw [div_pow]
      rw [show x ^ (2 * t + eta) * ((Real.log x + 2) ^ 2 / x ^ (2 : ℕ)) =
        (Real.log x + 2) ^ 2 * (x ^ (2 * t + eta) / x ^ (2 : ℕ)) by ring]
      rw [← Real.rpow_two x, ← Real.rpow_sub hx]
      congr 2
      ring
    _ ≤ _ := by
      simpa only [Nat.cast_add, Nat.cast_one, x] using
        mul_le_mul_of_nonneg_right hs (Real.rpow_nonneg hx.le (-(2 - (2 * t + eta))))

/-- The absolute near-pair interaction is summable below the budget line `2*t+eta=1`. -/
theorem summable_xiHeatCassiniWoldNatNearIncrementCovariance {t eta : ℝ} (h : 2 * t + eta < 1) :
    Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (2 * t) *
      (∑ j ∈ Finset.Ioc n (n + ⌊((n + 1 : ℕ) : ℝ) ^ eta⌋₊),
        |xiHeatCassiniWoldNatIncrement n * xiHeatCassiniWoldNatIncrement j|)) := by
  have hb : 1 < 2 - (2 * t + eta) := by linarith
  have hmajor : Summable (fun n : ℕ =>
      (2 * |Real.log ((n + 1 : ℕ) : ℝ)| ^ 2 + 8) *
        ((n + 1 : ℕ) : ℝ) ^ (-(2 - (2 * t + eta)))) := by
    have hl := (summable_abs_log_natCast_pow_mul_rpow_neg 2 _ hb).mul_left 2
    have hc := (summable_abs_log_natCast_pow_mul_rpow_neg 0 _ hb).mul_left 8
    have hsum := (hl.add hc).comp_injective Nat.succ_injective
    apply hsum.congr
    intro n
    simp only [Function.comp_apply, Nat.succ_eq_add_one, pow_zero, one_mul]
    ring
  exact hmajor.of_nonneg_of_le (fun n => by positivity)
    (fun n => nearPair_weighted_bound n t eta)

end
end RHTower
