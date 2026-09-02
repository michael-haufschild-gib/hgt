import GaloisForLFunctions.RHTower.Sieve.FibreStartSeparation
import GaloisForLFunctions.RHTower.Sieve.WindowStartShift
import GaloisForLFunctions.RHTower.Sieve.GoodStartFibreWindow
import GaloisForLFunctions.RHTower.Sieve.StartFibreLength
import GaloisForLFunctions.RHTower.Sieve.MarkerPrimeSeparation

namespace RHTower.Sieve

open Finset

noncomputable section

/-- Shifting every positive start down by one gives the usual dyadic mean square range. -/
theorem sum_fixedWindowSq_pred_Icc (f : ℕ → ℝ) (ℓ A B : ℕ) (hA : 1 ≤ A) (hAB : A ≤ B) :
    (∑ y ∈ Finset.Icc A B, fixedWindowSq f ℓ (y - 1)) =
      dyadicMeanSquare f ℓ (A - 1) (B - 1) := by
  have hB : 1 ≤ B := le_trans hA hAB
  have hshift := sum_Icc_shift (fun y => fixedWindowSq f ℓ (y - 1)) (A - 1) (B - 1) 1
  have hleft :
      (∑ y ∈ Finset.Icc (A - 1) (B - 1), fixedWindowSq f ℓ (y + 1 - 1)) =
        dyadicMeanSquare f ℓ (A - 1) (B - 1) := by
    rw [dyadicMeanSquare]
    exact Finset.sum_congr rfl (fun y _ => by rw [Nat.add_sub_cancel])
  have hrightA : A - 1 + 1 = A := by omega
  have hrightB : B - 1 + 1 = B := by omega
  rw [hrightA, hrightB, hleft] at hshift
  exact hshift.symm

/-- A variable fibre window is controlled by a fixed window at the same integer start, with the
entire normalization discrepancy exposed as the exact length mismatch. -/
theorem fibreWindowSq_le_fixedWindowSq_add_lengthError (f : ℕ → ℝ)
    (hf : ∀ n, |f n| ≤ 1) (x h : ℝ) (a ℓ : ℕ) :
    fixedWindowSq f (fibreLen x h a) (fibreStartIdx x a)
      ≤ 2 * fixedWindowSq f ℓ (fibreStartIdx x a)
        + 2 * |(fibreLen x h a : ℝ) - (ℓ : ℝ)| ^ 2 := by
  have hbase := fixedWindowSq_le_of_close hf
    (fibreStartIdx x a) (fibreLen x h a) (fibreStartIdx x a) ℓ
  have hend :
      |(((fibreStartIdx x a + fibreLen x h a : ℕ) : ℝ) -
          ((fibreStartIdx x a + ℓ : ℕ) : ℝ))|
        = |(fibreLen x h a : ℝ) - (ℓ : ℝ)| := by
    push_cast
    ring_nf
  simpa [hend] using hbase

/-- The fixed-window encoding also covers the zero-length case. -/
theorem fixedWindowSq_eq_sq_sum_Ioc_all (f : ℕ → ℝ) (ℓ z : ℕ) :
    fixedWindowSq f ℓ z = (∑ n ∈ Finset.Ioc z (z + ℓ), f n) ^ 2 := by
  by_cases hℓ : ℓ = 0
  · simp [hℓ, fixedWindowSq]
  · have hw := window_eq_partialSum f (y := z + 1) (by omega) (ℓ - 1)
    have hidx : z + 1 + (ℓ - 1) = z + ℓ := by omega
    have hpred : z + 1 - 1 = z := by omega
    rw [hidx, hpred] at hw
    rw [fixedWindowSq, ← hw, Finset.Icc_add_one_left_eq_Ioc]

/-- Fibre length differs from its moving real scale by at most the change across one reciprocal
start cell, plus the two integer roundings. -/
theorem abs_fibreLen_sub_localScale_le {x h : ℝ} (hx : 4 < x) (hh : 0 ≤ h)
    {a : ℕ} (ha : a ∈ outerBlock x h) :
    |(fibreLen x h a : ℝ) - h * (fibreStartIdx x a : ℝ) / Real.sqrt x|
      ≤ h / Real.sqrt x + 1 := by
  have hx0 : 0 < x := by linarith
  have hs0 : 0 < Real.sqrt x := Real.sqrt_pos.2 hx0
  have hs2 : 2 < Real.sqrt x := by
    have hs := Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 4) hx
    norm_num at hs ⊢
    exact hs
  have ha1 : 1 ≤ a := by
    rw [mem_outerBlock] at ha
    exact ha.1.1
  have ht1 : 1 ≤ fibreStartIdx x a := by
    have hstartRange := fibreStart_mem_Icc (le_of_lt hx) ha
    rw [Finset.mem_Icc] at hstartRange
    have hceil2 : 2 ≤ ⌈Real.sqrt x / 2⌉₊ := by
      have hlt : (1 : ℝ) < Real.sqrt x / 2 := by linarith
      have hnat : (1 : ℕ) < ⌈Real.sqrt x / 2⌉₊ := Nat.lt_ceil.2 (by
        norm_num
        exact hlt)
      omega
    have hceil : ⌈Real.sqrt x / 2⌉₊ ≤ ⌈x / (a : ℝ)⌉₊ := hstartRange.1
    rw [fibreStartIdx]
    omega
  obtain ⟨halow, hahigh⟩ :=
    start_interval_of_fibreStartIdx hx0 ha1 ht1 (rfl : fibreStartIdx x a = fibreStartIdx x a)
  obtain ⟨hlenLow, hlenHigh⟩ := fibreLen_bounds (le_of_lt hx) hh ht1 ha1 rfl halow hahigh
  have hstep :
      h * ((fibreStartIdx x a : ℝ) + 1) / Real.sqrt x + 1 =
        h * (fibreStartIdx x a : ℝ) / Real.sqrt x + h / Real.sqrt x + 1 := by
    field_simp
  rw [hstep] at hlenHigh
  rw [abs_le]
  constructor <;> linarith [div_nonneg hh hs0.le]

/-- The full mismatch from a fixed integer length splits into moving-scale variation and a uniform
rounding error. -/
theorem abs_fibreLen_sub_fixedLength_le {x h : ℝ} (hx : 4 < x) (hh : 0 ≤ h)
    {a : ℕ} (ha : a ∈ outerBlock x h) (ℓ : ℕ) :
    |(fibreLen x h a : ℝ) - (ℓ : ℝ)|
      ≤ |h * (fibreStartIdx x a : ℝ) / Real.sqrt x - (ℓ : ℝ)|
        + (h / Real.sqrt x + 1) := by
  have htriangle :
      |(fibreLen x h a : ℝ) - (ℓ : ℝ)|
        ≤ |(fibreLen x h a : ℝ) - h * (fibreStartIdx x a : ℝ) / Real.sqrt x|
          + |h * (fibreStartIdx x a : ℝ) / Real.sqrt x - (ℓ : ℝ)| := by
    exact abs_sub_le _ _ _
  linarith [abs_fibreLen_sub_localScale_le hx hh ha]

/-- Summed length mismatch: only moving-scale variation remains after paying the explicit uniform
rounding term. -/
theorem sum_lengthError_sq_le_localScaleError {x h : ℝ} (hx : 4 < x) (hh : 0 ≤ h)
    (ℓ : ℕ) :
    (∑ a ∈ outerBlock x h, |(fibreLen x h a : ℝ) - (ℓ : ℝ)| ^ 2)
      ≤ 2 * ∑ a ∈ outerBlock x h,
          |h * (fibreStartIdx x a : ℝ) / Real.sqrt x - (ℓ : ℝ)| ^ 2
        + 2 * ((outerBlock x h).card : ℝ) * (h / Real.sqrt x + 1) ^ 2 := by
  have hs0 : 0 < Real.sqrt x := Real.sqrt_pos.2 (by linarith)
  have hr0 : 0 ≤ h / Real.sqrt x + 1 := by positivity
  have hpoint : ∀ a ∈ outerBlock x h,
      |(fibreLen x h a : ℝ) - (ℓ : ℝ)| ^ 2
        ≤ 2 * |h * (fibreStartIdx x a : ℝ) / Real.sqrt x - (ℓ : ℝ)| ^ 2
          + 2 * (h / Real.sqrt x + 1) ^ 2 := by
    intro a ha
    have hlen := abs_fibreLen_sub_fixedLength_le hx hh ha ℓ
    have he0 : 0 ≤ |(fibreLen x h a : ℝ) - (ℓ : ℝ)| := abs_nonneg _
    have hv0 : 0 ≤ |h * (fibreStartIdx x a : ℝ) / Real.sqrt x - (ℓ : ℝ)| := abs_nonneg _
    nlinarith [sq_nonneg
      (|h * (fibreStartIdx x a : ℝ) / Real.sqrt x - (ℓ : ℝ)| -
        (h / Real.sqrt x + 1))]
  calc
    (∑ a ∈ outerBlock x h, |(fibreLen x h a : ℝ) - (ℓ : ℝ)| ^ 2)
        ≤ ∑ a ∈ outerBlock x h,
            (2 * |h * (fibreStartIdx x a : ℝ) / Real.sqrt x - (ℓ : ℝ)| ^ 2
              + 2 * (h / Real.sqrt x + 1) ^ 2) := Finset.sum_le_sum hpoint
    _ = 2 * ∑ a ∈ outerBlock x h,
          |h * (fibreStartIdx x a : ℝ) / Real.sqrt x - (ℓ : ℝ)| ^ 2
        + 2 * ((outerBlock x h).card : ℝ) * (h / Real.sqrt x + 1) ^ 2 := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring

/-- Exact finite moving-normalization bridge.  The fibre family is bounded by eight times one
fixed-length integer-start mean square, plus the explicit squared length mismatch. -/
theorem sum_fibreWindowSq_le_dyadic_add_lengthError (f : ℕ → ℝ)
    (hf : ∀ n, |f n| ≤ 1) {x h : ℝ} (hx : 4 ≤ x) (ℓ : ℕ) :
    (∑ a ∈ outerBlock x h,
        fixedWindowSq f (fibreLen x h a) (fibreStartIdx x a))
      ≤ 8 * dyadicMeanSquare f ℓ (⌈Real.sqrt x / 2⌉₊ - 1) (⌈Real.sqrt x⌉₊ - 1)
        + 2 * ∑ a ∈ outerBlock x h, |(fibreLen x h a : ℝ) - (ℓ : ℝ)| ^ 2 := by
  classical
  set A : ℕ := ⌈Real.sqrt x / 2⌉₊ with hAdef
  set B : ℕ := ⌈Real.sqrt x⌉₊ with hBdef
  have hx0 : 0 < x := by linarith
  have hs2 : 2 ≤ Real.sqrt x := by
    have hs := Real.sqrt_le_sqrt hx
    norm_num at hs ⊢
    exact hs
  have hA1 : 1 ≤ A := by
    rw [hAdef]
    exact Nat.one_le_ceil_iff.2 (by linarith)
  have hAB : A ≤ B := by
    rw [hAdef, hBdef]
    exact Nat.ceil_mono (by nlinarith [Real.sqrt_nonneg x])
  have hpoint : ∀ a ∈ outerBlock x h,
      fixedWindowSq f (fibreLen x h a) (fibreStartIdx x a)
        ≤ 2 * fixedWindowSq f ℓ (fibreStartIdx x a)
          + 2 * |(fibreLen x h a : ℝ) - (ℓ : ℝ)| ^ 2 :=
    fun a _ => fibreWindowSq_le_fixedWindowSq_add_lengthError f hf x h a ℓ
  have hsum := Finset.sum_le_sum hpoint
  have hstart :
      (∑ a ∈ outerBlock x h, fixedWindowSq f ℓ (fibreStartIdx x a))
        ≤ 4 * ∑ y ∈ Finset.Icc A B, fixedWindowSq f ℓ (y - 1) := by
    have htransfer := sum_block_comp_start_le (x := x) (h := h) hx
      (G := fun y => fixedWindowSq f ℓ (y - 1))
      (fun y => fixedWindowSq_nonneg f ℓ (y - 1))
    simpa [fibreStartIdx, A, B] using htransfer
  have hreindex := sum_fixedWindowSq_pred_Icc f ℓ A B hA1 hAB
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
  rw [hreindex] at hstart
  nlinarith

/-- Fibre sums themselves satisfy the finite moving-normalization bridge. -/
theorem sum_innerFibre_sq_le_dyadic_add_lengthError (f : ℕ → ℝ)
    (hf : ∀ n, |f n| ≤ 1) {x h : ℝ} (hx : 4 ≤ x) (hh : 0 ≤ h) (ℓ : ℕ) :
    (∑ a ∈ outerBlock x h, (∑ b ∈ innerFibre x h a, f b) ^ 2)
      ≤ 8 * dyadicMeanSquare f ℓ (⌈Real.sqrt x / 2⌉₊ - 1) (⌈Real.sqrt x⌉₊ - 1)
        + 2 * ∑ a ∈ outerBlock x h, |(fibreLen x h a : ℝ) - (ℓ : ℝ)| ^ 2 := by
  have hreindex :
      (∑ a ∈ outerBlock x h, (∑ b ∈ innerFibre x h a, f b) ^ 2) =
        ∑ a ∈ outerBlock x h,
          fixedWindowSq f (fibreLen x h a) (fibreStartIdx x a) := by
    refine Finset.sum_congr rfl (fun a ha => ?_)
    rw [innerFibre_eq_Ioc hx hh ha, fixedWindowSq_eq_sq_sum_Ioc_all]
  rw [hreindex]
  exact sum_fibreWindowSq_le_dyadic_add_lengthError f hf hx ℓ

/-- Final finite normalization inequality.  Integer-start mean square, moving-scale variation, and
rounding loss are separated with explicit constants. -/
theorem sum_innerFibre_sq_le_dyadic_add_localScaleError (f : ℕ → ℝ)
    (hf : ∀ n, |f n| ≤ 1) {x h : ℝ} (hx : 4 < x) (hh : 0 ≤ h) (ℓ : ℕ) :
    (∑ a ∈ outerBlock x h, (∑ b ∈ innerFibre x h a, f b) ^ 2)
      ≤ 8 * dyadicMeanSquare f ℓ (⌈Real.sqrt x / 2⌉₊ - 1) (⌈Real.sqrt x⌉₊ - 1)
        + 4 * ∑ a ∈ outerBlock x h,
            |h * (fibreStartIdx x a : ℝ) / Real.sqrt x - (ℓ : ℝ)| ^ 2
        + 4 * ((outerBlock x h).card : ℝ) * (h / Real.sqrt x + 1) ^ 2 := by
  have hbridge := sum_innerFibre_sq_le_dyadic_add_lengthError f hf (le_of_lt hx) hh ℓ
  have hlength := sum_lengthError_sq_le_localScaleError hx hh ℓ
  nlinarith

end

end RHTower.Sieve

