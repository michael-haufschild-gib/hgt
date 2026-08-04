import GaloisForLFunctions.RHTower.Sieve.PairFibre
import GaloisForLFunctions.RHTower.Sieve.HarmonicDyadicBlock

/-!
# The trivial size of the balanced pair sum

Bounding every fibre sum by its length gives

    |pairSum f x h|  ≤  h√x · ∑_{a ∈ block} 1/a  +  #block,

and the block is exactly the integer interval `[⌈√x⌉, ⌊2√x⌋]`, whose reciprocal sum tends to `log 2`
and whose cardinality is at most `√x + 1`.  So for any window length tending to infinity the trivial
bound divided by `h√x log 2` tends to `1`:

**the normalising constant of the bilinear all-interval theorem is precisely the trivial size of the
sum it normalises.**  Any nonzero limit of the normalised pair sum is therefore a genuine
correlation, and the theorem's assertion that the limit is the squared block mean is a statement
about total cancellation.
-/

namespace RHTower.Sieve

open Finset Filter Topology

/-- Twice the square root is below the argument from `4` on. -/
theorem two_mul_sqrt_le {x : ℝ} (hx : 4 ≤ x) : 2 * Real.sqrt x ≤ x := by
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have hsq : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx0
  have h2 : (2 : ℝ) ≤ Real.sqrt x := by
    have hle : Real.sqrt 4 ≤ Real.sqrt x := Real.sqrt_le_sqrt hx
    rwa [show Real.sqrt 4 = 2 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] at hle
  nlinarith [Real.sqrt_nonneg x]

/-- **The block is a dyadic integer interval.** -/
theorem outerBlock_eq {x h : ℝ} (hx : 4 ≤ x) (hh : 0 ≤ h) :
    outerBlock x h = Finset.Icc ⌈Real.sqrt x⌉₊ ⌊2 * Real.sqrt x⌋₊ := by
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have hs0 : (0 : ℝ) ≤ Real.sqrt x := Real.sqrt_nonneg x
  have h2 : (2 : ℝ) ≤ Real.sqrt x := by
    have hle : Real.sqrt 4 ≤ Real.sqrt x := Real.sqrt_le_sqrt hx
    rwa [show Real.sqrt 4 = 2 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] at hle
  have hmass : (0 : ℝ) ≤ h * Real.sqrt x := by positivity
  have hsx := two_mul_sqrt_le hx
  ext a
  rw [mem_outerBlock, Finset.mem_Icc]
  constructor
  · rintro ⟨-, hlow, hhigh⟩
    exact ⟨Nat.ceil_le.2 hlow, Nat.le_floor hhigh⟩
  · rintro ⟨hlow, hhigh⟩
    have hb1 : Real.sqrt x ≤ (a : ℝ) := Nat.ceil_le.1 hlow
    have hb2 : (a : ℝ) ≤ 2 * Real.sqrt x := (Nat.le_floor_iff (by positivity)).1 hhigh
    have hone : 1 ≤ a := by
      have : (1 : ℝ) ≤ (a : ℝ) := by linarith
      exact_mod_cast this
    have htop : a ≤ ⌊x + h * Real.sqrt x⌋₊ := by
      refine Nat.le_floor ?_
      linarith
    exact ⟨⟨hone, htop⟩, hb1, hb2⟩

/-- **The block has at most `√x + 1` elements.** -/
theorem card_outerBlock_le {x h : ℝ} (hx : 4 ≤ x) (hh : 0 ≤ h) :
    ((outerBlock x h).card : ℝ) ≤ Real.sqrt x + 1 := by
  have h2 : (2 : ℝ) ≤ Real.sqrt x := by
    have hle : Real.sqrt 4 ≤ Real.sqrt x := Real.sqrt_le_sqrt hx
    rwa [show Real.sqrt 4 = 2 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] at hle
  have hce : ((⌈Real.sqrt x⌉₊ : ℝ)) ≤ Real.sqrt x + 1 :=
    (Nat.ceil_lt_add_one (by linarith)).le
  have hcelow : Real.sqrt x ≤ ((⌈Real.sqrt x⌉₊ : ℝ)) := Nat.le_ceil _
  have hfl : 2 * Real.sqrt x - 1 ≤ ((⌊2 * Real.sqrt x⌋₊ : ℝ)) := by
    have := Nat.lt_floor_add_one (2 * Real.sqrt x)
    linarith
  have hflup : ((⌊2 * Real.sqrt x⌋₊ : ℝ)) ≤ 2 * Real.sqrt x :=
    Nat.floor_le (by linarith)
  have hmn : ⌈Real.sqrt x⌉₊ ≤ ⌊2 * Real.sqrt x⌋₊ + 1 := by
    have : ((⌈Real.sqrt x⌉₊ : ℝ)) ≤ ((⌊2 * Real.sqrt x⌋₊ : ℝ)) + 1 := by linarith
    exact_mod_cast this
  rw [outerBlock_eq hx hh, Nat.card_Icc]
  have hcast : ((⌊2 * Real.sqrt x⌋₊ + 1 - ⌈Real.sqrt x⌉₊ : ℕ) : ℝ)
      = ((⌊2 * Real.sqrt x⌋₊ : ℝ)) + 1 - ((⌈Real.sqrt x⌉₊ : ℝ)) := by
    push_cast [Nat.cast_sub hmn]
    ring
  rw [hcast]
  linarith

/-- **The trivial bound.**  Every fibre sum is at most its length. -/
theorem abs_pairSum_le_trivial {f : ℕ → ℝ} (hf : ∀ n, |f n| ≤ 1) {x h : ℝ}
    (hx : 4 ≤ x) (hh : 0 ≤ h) :
    |pairSum f x h|
      ≤ h * Real.sqrt x
          * (∑ a ∈ Finset.Icc ⌈Real.sqrt x⌉₊ ⌊2 * Real.sqrt x⌋₊, 1 / (a : ℝ))
        + (Real.sqrt x + 1) := by
  classical
  have hx0 : (0 : ℝ) ≤ x := by linarith
  refine le_trans (abs_pairSum_le_sum_abs_fibre hf x h) ?_
  have hterm : ∀ a ∈ outerBlock x h,
      |∑ b ∈ innerFibre x h a, f b| ≤ h * Real.sqrt x / (a : ℝ) + 1 := by
    intro a ha
    rw [mem_outerBlock] at ha
    have hone : 1 ≤ a := ha.1.1
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine le_trans (Finset.sum_le_sum (fun b _ => hf b)) ?_
    rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    exact card_innerFibre_le hx0 hh hone
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hmul : ∑ a ∈ outerBlock x h, h * Real.sqrt x / (a : ℝ)
      = h * Real.sqrt x * ∑ a ∈ outerBlock x h, 1 / (a : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro a _
    ring
  rw [hmul, outerBlock_eq hx hh]
  have hcard := card_outerBlock_le (x := x) (h := h) hx hh
  rw [outerBlock_eq hx hh] at hcard
  linarith

/-- The reciprocal block sum, in the variable of the pair sum. -/
theorem tendsto_block_one_div_sqrt :
    Tendsto (fun x : ℝ => ∑ a ∈ Finset.Icc ⌈Real.sqrt x⌉₊ ⌊2 * Real.sqrt x⌋₊, 1 / (a : ℝ))
      atTop (𝓝 (Real.log 2)) :=
  tendsto_sum_dyadic_one_div.comp Real.tendsto_sqrt_atTop

/-- **The normalisation is the trivial size.**  For any window length tending to infinity the
trivial bound divided by `h√x log 2` tends to `1`. -/
theorem tendsto_trivial_bound_ratio {hh : ℝ → ℝ} (hgrow : Tendsto hh atTop atTop) :
    Tendsto (fun x : ℝ =>
        (hh x * Real.sqrt x
            * (∑ a ∈ Finset.Icc ⌈Real.sqrt x⌉₊ ⌊2 * Real.sqrt x⌋₊, 1 / (a : ℝ))
          + (Real.sqrt x + 1))
        / (hh x * Real.sqrt x * Real.log 2)) atTop (𝓝 1) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hfirst : Tendsto (fun x : ℝ =>
      (∑ a ∈ Finset.Icc ⌈Real.sqrt x⌉₊ ⌊2 * Real.sqrt x⌋₊, 1 / (a : ℝ)) / Real.log 2)
      atTop (𝓝 1) := by
    have := tendsto_block_one_div_sqrt.div_const (Real.log 2)
    rwa [div_self (ne_of_gt hlog2)] at this
  have hsqrtinv : Tendsto (fun x : ℝ => 1 / Real.sqrt x) atTop (𝓝 0) :=
    tendsto_one_div_atTop.comp Real.tendsto_sqrt_atTop
  have hnum : Tendsto (fun x : ℝ => 1 + 1 / Real.sqrt x) atTop (𝓝 1) := by
    have := tendsto_const_nhds (x := (1 : ℝ)) (f := (atTop : Filter ℝ)) |>.add hsqrtinv
    rwa [add_zero] at this
  have hden : Tendsto (fun x : ℝ => hh x * Real.log 2) atTop atTop :=
    hgrow.atTop_mul_const hlog2
  have hsecond : Tendsto (fun x : ℝ => (1 + 1 / Real.sqrt x) / (hh x * Real.log 2))
      atTop (𝓝 0) := hnum.div_atTop hden
  have hsum := hfirst.add hsecond
  rw [add_zero] at hsum
  refine Tendsto.congr' ?_ hsum
  filter_upwards [eventually_gt_atTop (1 : ℝ), hgrow.eventually_gt_atTop 0] with x hx hhx
  have hs0 : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 (by linarith)
  field_simp

end RHTower.Sieve
