import GaloisForLFunctions.RHTower.PrimeHigherMertens
import GaloisForLFunctions.RHTower.RapidExponentialFockPotentialGeometry
import GaloisForLFunctions.HTGeometry.MonomialLaplaceComplex

/-!
# Higher prime-log mass in rapid Fock windows

This module generalizes logarithmic prime-window mass to arbitrary natural log power and proves the
fourth-power window vanishes on every fixed rapid-Fock adapted scale.  Higher Mertens convergence
controls the additive remainder; exponential adapted-radius decay absorbs the cubic main scale.
The fourth-power result pays the polynomial loss in the explicit normalized rapid-kernel estimate.
-/

open Filter Topology

namespace RHTower

noncomputable section

def primeLogPowWindowMass (k : ℕ) (x r : ℝ) : ℝ :=
  primeLogPowSum k (Real.exp (x + r)) -
    primeLogPowSum k (Real.exp (x - r))

theorem primeLogPowWindowMass_eq_sum (k : ℕ) (x : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    primeLogPowWindowMass k x r =
      ∑ n ∈ Finset.Ioc ⌊Real.exp (x - r)⌋₊ ⌊Real.exp (x + r)⌋₊,
        primeLogPowWeight k n := by
  have hle : ⌊Real.exp (x - r)⌋₊ ≤ ⌊Real.exp (x + r)⌋₊ :=
    Nat.floor_le_floor (Real.exp_le_exp.mpr (by linarith))
  have hunion : Finset.Icc 0 ⌊Real.exp (x - r)⌋₊
      ∪ Finset.Ioc ⌊Real.exp (x - r)⌋₊ ⌊Real.exp (x + r)⌋₊ =
      Finset.Icc 0 ⌊Real.exp (x + r)⌋₊ := by
    ext n
    simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  have hdisj : Disjoint (Finset.Icc 0 ⌊Real.exp (x - r)⌋₊)
      (Finset.Ioc ⌊Real.exp (x - r)⌋₊ ⌊Real.exp (x + r)⌋₊) := by
    rw [Finset.disjoint_left]
    intro n hn hn'
    exact (not_lt_of_ge (Finset.mem_Icc.mp hn).2) (Finset.mem_Ioc.mp hn').1
  rw [primeLogPowWindowMass, primeLogPowSum, primeLogPowSum,
    ← hunion, Finset.sum_union hdisj]
  ring

theorem tendsto_primeLogPowWindowMass_four_rapidExponentialFockAdaptedRadius_zero
    {a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    Tendsto (fun x : ℝ => primeLogPowWindowMass 4 x
      (c * rapidExponentialFockAdaptedRadius a x)) atTop (nhds 0) := by
  let r : ℝ → ℝ := fun x => c * rapidExponentialFockAdaptedRadius a x
  have hr0 : Tendsto r atTop (nhds 0) := by
    simpa [r] using (tendsto_rapidExponentialFockAdaptedRadius_atTop ha).const_mul c
  have hrpos : ∀ᶠ x : ℝ in atTop, 0 < r x := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact mul_pos hc (rapidExponentialFockAdaptedRadius_pos ha hx)
  have hrone : ∀ᶠ x : ℝ in atTop, |r x| < 1 :=
    by simpa [Real.dist_eq] using
      hr0.eventually (Metric.ball_mem_nhds (0 : ℝ) zero_lt_one)
  have hplusArg : Tendsto (fun x : ℝ => x + r x) atTop atTop := by
    rw [tendsto_atTop]
    intro b
    filter_upwards [eventually_ge_atTop (b + 1), hrone] with x hx hrx
    have : -1 < r x := (abs_lt.mp hrx).1
    linarith
  have hminusArg : Tendsto (fun x : ℝ => x - r x) atTop atTop := by
    rw [tendsto_atTop]
    intro b
    filter_upwards [eventually_ge_atTop (b + 1), hrone] with x hx hrx
    have : r x < 1 := (abs_lt.mp hrx).2
    linarith
  have hplusExp : Tendsto (fun x : ℝ => Real.exp (x + r x)) atTop atTop :=
    Real.tendsto_exp_atTop.comp hplusArg
  have hminusExp : Tendsto (fun x : ℝ => Real.exp (x - r x)) atTop atTop :=
    Real.tendsto_exp_atTop.comp hminusArg
  have hM := tendsto_primeLogPowSum_sub 3
  have hplusRem : Tendsto (fun x : ℝ =>
      primeLogPowSum 4 (Real.exp (x + r x)) - (x + r x) ^ 4 / 4)
      atTop (nhds (mertensLogPowConstantFull 3)) := by
    convert hM.comp hplusExp using 1 <;> norm_num [Function.comp_def]
  have hminusRem : Tendsto (fun x : ℝ =>
      primeLogPowSum 4 (Real.exp (x - r x)) - (x - r x) ^ 4 / 4)
      atTop (nhds (mertensLogPowConstantFull 3)) := by
    convert hM.comp hminusExp using 1 <;> norm_num [Function.comp_def]
  have herr : Tendsto (fun x : ℝ =>
      primeLogPowWindowMass 4 x (r x) -
        ((x + r x) ^ 4 - (x - r x) ^ 4) / 4) atTop (nhds 0) := by
    have hsub := hplusRem.sub hminusRem
    have hsub' : Tendsto (fun x : ℝ =>
        (primeLogPowSum 4 (Real.exp (x + r x)) - (x + r x) ^ 4 / 4) -
          (primeLogPowSum 4 (Real.exp (x - r x)) - (x - r x) ^ 4 / 4))
        atTop (nhds 0) := by simpa using hsub
    refine hsub'.congr' (Filter.Eventually.of_forall fun x => ?_)
    simp only [primeLogPowWindowMass]
    ring
  let K : ℝ := c * (2 * a)⁻¹
  have hK : 0 < K := by dsimp [K]; positivity
  have hrupper : ∀ᶠ x : ℝ in atTop,
      r x ≤ K * Real.exp (-a * x) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    dsimp [r, K]
    simpa [mul_assoc] using mul_le_mul_of_nonneg_left
      (rapidExponentialFockAdaptedRadius_upper ha hx) hc.le
  have hfirst : Tendsto (fun x : ℝ => 2 * x ^ 3 * r x) atTop (nhds 0) := by
    have hmodel :=
      (GaloisForLFunctions.HTGeometry.tendsto_pow_mul_exp_neg_mul_atTop ha 3).const_mul
        (2 * K)
    apply squeeze_zero'
    · filter_upwards [eventually_ge_atTop (0 : ℝ), hrpos] with x hx hrx
      positivity
    · filter_upwards [eventually_ge_atTop (0 : ℝ), hrupper] with x hx hrx
      calc
        2 * x ^ 3 * r x ≤ 2 * x ^ 3 * (K * Real.exp (-a * x)) := by gcongr
        _ = (2 * K) * (x ^ 3 * Real.exp (-(a * x))) := by ring
    · simpa only [mul_zero] using hmodel
  have hsecond : Tendsto (fun x : ℝ => 2 * x * (r x) ^ 3) atTop (nhds 0) := by
    have h3a : 0 < 3 * a := by positivity
    have hmodel :=
      (GaloisForLFunctions.HTGeometry.tendsto_pow_mul_exp_neg_mul_atTop h3a 1).const_mul
        (2 * K ^ 3)
    apply squeeze_zero'
    · filter_upwards [eventually_ge_atTop (0 : ℝ), hrpos] with x hx hrx
      positivity
    · filter_upwards [eventually_ge_atTop (0 : ℝ), hrpos, hrupper] with x hx hrposx hrx
      calc
        2 * x * (r x) ^ 3 ≤ 2 * x * (K * Real.exp (-a * x)) ^ 3 := by gcongr
        _ = (2 * K ^ 3) * (x ^ 1 * Real.exp (-((3 * a) * x))) := by
          rw [mul_pow, ← Real.exp_nat_mul]
          ring
    · simpa only [mul_zero] using hmodel
  have hmain : Tendsto (fun x : ℝ =>
      ((x + r x) ^ 4 - (x - r x) ^ 4) / 4) atTop (nhds 0) := by
    have hsum := hfirst.add hsecond
    simpa only [zero_add] using hsum.congr'
      (Filter.Eventually.of_forall fun x => by ring)
  have htotal := herr.add hmain
  simpa [r] using htotal

end

end RHTower
