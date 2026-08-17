import GaloisForLFunctions.HTGeometry.RpowUnitStepQuotient
import GaloisForLFunctions.HTGeometry.WeightedRpowTailCesaro
import GaloisForLFunctions.RHTower.AdjointCellQuotientScale
import GaloisForLFunctions.RHTower.HarmonicPrimitiveLadder

/-!
# The scale audit of the harmonic primitive ladder

The exact Abel recursion moves a harmonic primitive from the source to a cell difference quotient
on the receiver.  This module measures both moves.

* One harmonic primitive lowers the source exponent by exactly one: if `f_n/n^p → c` with `p < 1`
  then `(𝓗f)_n/n^{p-1} → −c/(1−p)`, because the harmonic weight is `w_m = m^{-2}(1+o(1))` and the
  weighted tail of a convergent sequence inherits the sharp power tail.  Iterating gives the exact
  ladder constants `c_j = (−1)^j c/∏_{ℓ≤j}(ℓ−β)`, all nonzero when `c ≠ 0`.
* One cell difference quotient raises the receiver exponent by exactly one: `𝒟(n^r)/n^{r+1} → −r`,
  since the unit backward difference of `n^r` is `−r n^{r-1}(1+o(1))` and dividing by
  `w_n = (n(n+1))^{-1}` multiplies by `n²(1+o(1))`.

The two moves cancel: at every depth the endpoint product has the same scale `n^{β−1/2}` against
the square-root receiver profile, with a nonzero constant.  So no finite ladder of harmonic
primitives changes the critical exponent — it can only relocate the signed cancellation being
sought.
-/

open Filter Topology GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-! ## The source move -/

/-- **(24.68)** The harmonic tail primitive `(𝓗f)_n = −∑_{m > n} f_m w_m`. -/
def harmonicTailPrimitive (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  -∑' k : ℕ, f (n + 1 + k) * harmonicGap (n + 1 + k)

/-- The harmonic weight is a square reciprocal up to a factor tending to one. -/
theorem tendsto_rpow_two_mul_harmonicGap :
    Tendsto (fun m : ℕ => (m : ℝ) ^ (2 : ℝ) * harmonicGap m) atTop (𝓝 1) := by
  have hbase : Tendsto (fun m : ℕ => 1 / (1 + 1 / (m : ℝ))) atTop (𝓝 (1 / (1 + 0))) := by
    refine Tendsto.div tendsto_const_nhds
      (tendsto_const_nhds.add tendsto_one_div_atTop_nhds_zero_nat) ?_
    norm_num
  rw [add_zero, div_one] at hbase
  refine hbase.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with m hm
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hsq : (m : ℝ) ^ (2 : ℝ) = (m : ℝ) * (m : ℝ) := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    ring
  rw [hsq, harmonicGap_eq_inv_mul hm]
  field_simp

/-- **The source move.**  One harmonic primitive lowers the exponent by exactly one. -/
theorem tendsto_harmonicTailPrimitive {f : ℕ → ℝ} {p c : ℝ} (hp : p < 1)
    (hf : Tendsto (fun n : ℕ => f n / (n : ℝ) ^ p) atTop (𝓝 c)) :
    Tendsto (fun n : ℕ => harmonicTailPrimitive f n / (n : ℝ) ^ (p - 1)) atTop
      (𝓝 (-(c / (1 - p)))) := by
  set g : ℕ → ℝ := fun m => (f m / (m : ℝ) ^ p) * ((m : ℝ) ^ (2 : ℝ) * harmonicGap m) with hgdef
  have hg : Tendsto g atTop (𝓝 c) := by
    have := hf.mul tendsto_rpow_two_mul_harmonicGap
    rwa [mul_one] at this
  have hweight := tendsto_weightedTail_rpow hp hg
  have hterm : ∀ n k : ℕ,
      f (n + 1 + k) * harmonicGap (n + 1 + k)
        = g (n + 1 + k) * ((n : ℝ) + 1 + (k : ℝ)) ^ (p - 2) := by
    intro n k
    have hm1 : (1 : ℕ) ≤ n + 1 + k := by omega
    have hcast : ((n + 1 + k : ℕ) : ℝ) = (n : ℝ) + 1 + (k : ℝ) := by push_cast; ring
    have hm0 : (0 : ℝ) < ((n + 1 + k : ℕ) : ℝ) := by
      rw [hcast]; positivity
    have hsplit : ((n + 1 + k : ℕ) : ℝ) ^ (2 : ℝ) * ((n + 1 + k : ℕ) : ℝ) ^ (p - 2)
        = ((n + 1 + k : ℕ) : ℝ) ^ p := by
      rw [← Real.rpow_add hm0]
      congr 1
      ring
    have hne : ((n + 1 + k : ℕ) : ℝ) ^ p ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hm0 p)
    rw [hgdef]
    simp only
    rw [← hcast]
    field_simp
    linear_combination (-(f (n + 1 + k) * harmonicGap (n + 1 + k))) * hsplit
  have hrewrite : ∀ n : ℕ, harmonicTailPrimitive f n
      = -∑' k : ℕ, g (n + 1 + k) * ((n : ℝ) + 1 + (k : ℝ)) ^ (p - 2) := by
    intro n
    rw [harmonicTailPrimitive]
    congr 1
    exact tsum_congr fun k => hterm n k
  have hneg : Tendsto (fun n : ℕ => -((n : ℝ) ^ (1 - p)
      * ∑' k : ℕ, g (n + 1 + k) * ((n : ℝ) + 1 + (k : ℝ)) ^ (p - 2))) atTop
      (𝓝 (-(c / (1 - p)))) := hweight.neg
  refine hneg.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hinv : (n : ℝ) ^ (1 - p) = ((n : ℝ) ^ (p - 1))⁻¹ := by
    rw [← Real.rpow_neg hn0.le]
    congr 1
    ring
  rw [hrewrite n, hinv]
  field_simp

/-! ## The source ladder -/

/-- The source ladder `f_j = 𝓗^j f`. -/
def sourceLadder (f : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0 => f
  | j + 1 => harmonicTailPrimitive (sourceLadder f j)

/-- **(24.71)** The ladder constants `c_{j+1} = −c_j/(j+1−β)`. -/
def ladderConst (c beta : ℝ) : ℕ → ℝ
  | 0 => c
  | j + 1 => -(ladderConst c beta j) / ((j : ℝ) + 1 - beta)

theorem ladderConst_ne_zero {c beta : ℝ} (hc : c ≠ 0) (hbeta : beta < 1) (j : ℕ) :
    ladderConst c beta j ≠ 0 := by
  induction j with
  | zero => exact hc
  | succ j ih =>
    have hden : ((j : ℝ) + 1 - beta) ≠ 0 := by
      have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
      have hpos : (0 : ℝ) < (j : ℝ) + 1 - beta := by linarith
      exact ne_of_gt hpos
    rw [ladderConst]
    exact div_ne_zero (neg_ne_zero.2 ih) hden

/-- **(24.71)** Every source iterate has the exponent lowered by its depth. -/
theorem tendsto_sourceLadder {f : ℕ → ℝ} {beta c : ℝ} (hbeta : beta < 1)
    (hf : Tendsto (fun n : ℕ => f n / (n : ℝ) ^ beta) atTop (𝓝 c)) (j : ℕ) :
    Tendsto (fun n : ℕ => sourceLadder f j n / (n : ℝ) ^ (beta - (j : ℝ))) atTop
      (𝓝 (ladderConst c beta j)) := by
  induction j with
  | zero =>
    simpa [sourceLadder, ladderConst] using hf
  | succ j ih =>
    have hp : beta - (j : ℝ) < 1 := by
      have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
      linarith
    have hstep := tendsto_harmonicTailPrimitive hp ih
    have hexp : beta - (j : ℝ) - 1 = beta - ((j : ℕ) + 1 : ℕ) := by
      push_cast
      ring
    have hval : -(ladderConst c beta j / (1 - (beta - (j : ℝ))))
        = ladderConst c beta (j + 1) := by
      rw [ladderConst]
      have : (1 : ℝ) - (beta - (j : ℝ)) = (j : ℝ) + 1 - beta := by ring
      rw [this]
      ring
    rw [hexp, hval] at hstep
    exact hstep

/-! ## The receiver move -/

/-- **(24.72)** One cell difference quotient raises the receiver exponent by exactly one. -/
theorem tendsto_discreteDeriv_rpow (r : ℝ) :
    Tendsto (fun n : ℕ =>
        discreteDeriv harmonicGap (fun m : ℕ => (m : ℝ) ^ r) n / (n : ℝ) ^ (r + 1))
      atTop (𝓝 (-r)) := by
  have hquot : Tendsto (fun n : ℕ =>
      ((n : ℝ) ^ r - ((n : ℝ) + 1) ^ r) / (n : ℝ) ^ (r - 1)) atTop (𝓝 (-r)) :=
    (tendsto_rpow_unit_step_quotient r).comp tendsto_natCast_atTop_atTop
  have hshape : Tendsto (fun n : ℕ => 1 + 1 / (n : ℝ)) atTop (𝓝 (1 + 0)) :=
    tendsto_const_nhds.add tendsto_one_div_atTop_nhds_zero_nat
  rw [add_zero] at hshape
  have hprod := hquot.mul hshape
  rw [mul_one] at hprod
  refine hprod.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hgap : harmonicGap n = 1 / ((n : ℝ) * ((n : ℝ) + 1)) := harmonicGap_eq_inv_mul hn
  have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  have hrpow : (n : ℝ) ^ (r + 1) = (n : ℝ) ^ (r - 1) * ((n : ℝ) * (n : ℝ)) := by
    have hsq : (n : ℝ) * (n : ℝ) = (n : ℝ) ^ (2 : ℝ) := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      ring
    rw [hsq, ← Real.rpow_add hn0]
    congr 1
    ring
  have hne : (n : ℝ) ^ (r - 1) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hn0 _)
  rw [discreteDeriv, hgap, hcast, hrpow]
  field_simp

/-! ## The depth invariance -/

/-- **(24.73) The endpoint scale of the ladder is independent of the depth.**  Against the
square-root receiver profile of depth `j` the `(j+1)`-st source iterate has the fixed critical
scale `n^{β−1/2}`, with a nonzero constant at every depth. -/
theorem tendsto_ladderEndpoint_scale {f : ℕ → ℝ} {beta c : ℝ} (hbeta : beta < 1)
    (hf : Tendsto (fun n : ℕ => f n / (n : ℝ) ^ beta) atTop (𝓝 c)) (j : ℕ) :
    Tendsto (fun n : ℕ =>
        sourceLadder f (j + 1) n * (n : ℝ) ^ ((1 : ℝ) / 2 + (j : ℝ)) / (n : ℝ) ^ (beta - 1 / 2))
      atTop (𝓝 (ladderConst c beta (j + 1))) := by
  have hstep := tendsto_sourceLadder hbeta hf (j + 1)
  refine hstep.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hsplit : (n : ℝ) ^ (beta - ((j + 1 : ℕ) : ℝ))
      = (n : ℝ) ^ (beta - 1 / 2) / (n : ℝ) ^ ((1 : ℝ) / 2 + (j : ℝ)) := by
    rw [← Real.rpow_sub hn0]
    congr 1
    push_cast
    ring
  have hne : (n : ℝ) ^ ((1 : ℝ) / 2 + (j : ℝ)) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hn0 _)
  have hne2 : (n : ℝ) ^ (beta - 1 / 2) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hn0 _)
  rw [hsplit]
  field_simp

end

end RHTower
