import GaloisForLFunctions.RHTower.Sieve.FibreFixedWindowNormalization

namespace RHTower.Sieve

open Finset

noncomputable section

theorem sum_fibreWindowSq_le_variableWindowSq_add_lengthError (f : ℕ → ℝ)
    (hf : ∀ n, |f n| ≤ 1) {x h : ℝ} (hx : 4 ≤ x) (L : ℕ → ℕ) :
    (∑ a ∈ outerBlock x h,
        fixedWindowSq f (fibreLen x h a) (fibreStartIdx x a))
      ≤ 8 * ∑ y ∈ Finset.Icc ⌈Real.sqrt x / 2⌉₊ ⌈Real.sqrt x⌉₊,
          fixedWindowSq f (L y) (y - 1)
        + 2 * ∑ a ∈ outerBlock x h,
          |(fibreLen x h a : ℝ) - (L ⌈x / (a : ℝ)⌉₊ : ℝ)| ^ (2 : ℕ) := by
  classical
  have hpoint : ∀ a ∈ outerBlock x h,
      fixedWindowSq f (fibreLen x h a) (fibreStartIdx x a)
        ≤ 2 * fixedWindowSq f (L ⌈x / (a : ℝ)⌉₊) (fibreStartIdx x a)
          + 2 * |(fibreLen x h a : ℝ) - (L ⌈x / (a : ℝ)⌉₊ : ℝ)| ^ (2 : ℕ) :=
    fun a _ => fibreWindowSq_le_fixedWindowSq_add_lengthError f hf x h a _
  have hsum := Finset.sum_le_sum hpoint
  have hstart :
      (∑ a ∈ outerBlock x h,
          fixedWindowSq f (L ⌈x / (a : ℝ)⌉₊) (fibreStartIdx x a))
        ≤ 4 * ∑ y ∈ Finset.Icc ⌈Real.sqrt x / 2⌉₊ ⌈Real.sqrt x⌉₊,
          fixedWindowSq f (L y) (y - 1) := by
    have htransfer := sum_block_comp_start_le (x := x) (h := h) hx
      (G := fun y => fixedWindowSq f (L y) (y - 1))
      (fun y => fixedWindowSq_nonneg f (L y) (y - 1))
    simpa [fibreStartIdx] using htransfer
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
  nlinarith

theorem sum_innerFibre_sq_le_variableWindowSq_add_lengthError (f : ℕ → ℝ)
    (hf : ∀ n, |f n| ≤ 1) {x h : ℝ} (hx : 4 ≤ x) (hh : 0 ≤ h) (L : ℕ → ℕ) :
    (∑ a ∈ outerBlock x h, (∑ b ∈ innerFibre x h a, f b) ^ (2 : ℕ))
      ≤ 8 * ∑ y ∈ Finset.Icc ⌈Real.sqrt x / 2⌉₊ ⌈Real.sqrt x⌉₊,
          fixedWindowSq f (L y) (y - 1)
        + 2 * ∑ a ∈ outerBlock x h,
          |(fibreLen x h a : ℝ) - (L ⌈x / (a : ℝ)⌉₊ : ℝ)| ^ (2 : ℕ) := by
  have hreindex :
      (∑ a ∈ outerBlock x h, (∑ b ∈ innerFibre x h a, f b) ^ (2 : ℕ)) =
        ∑ a ∈ outerBlock x h,
          fixedWindowSq f (fibreLen x h a) (fibreStartIdx x a) := by
    refine Finset.sum_congr rfl (fun a ha => ?_)
    rw [innerFibre_eq_Ioc hx hh ha, fixedWindowSq_eq_sq_sum_Ioc_all]
  rw [hreindex]
  exact sum_fibreWindowSq_le_variableWindowSq_add_lengthError f hf hx L

/-- Integer length obtained by rounding down the natural moving fibre scale at start `y - 1`. -/
def movingFibreWindowLength (x h : ℝ) (y : ℕ) : ℕ :=
  ⌊h * (y - 1 : ℕ) / Real.sqrt x⌋₊

theorem abs_localScale_sub_movingFibreWindowLength_le {x h : ℝ} (hx : 0 < x) (hh : 0 ≤ h)
    (y : ℕ) :
    |h * (y - 1 : ℕ) / Real.sqrt x - (movingFibreWindowLength x h y : ℝ)| ≤ 1 := by
  have hs0 : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  have hu0 : 0 ≤ h * (y - 1 : ℕ) / Real.sqrt x := by positivity
  have hfloor := Nat.floor_le hu0
  have hlt := Nat.lt_floor_add_one (h * (y - 1 : ℕ) / Real.sqrt x)
  rw [movingFibreWindowLength]
  rw [abs_of_nonneg (by linarith)]
  linarith

theorem abs_fibreLen_sub_movingFibreWindowLength_le {x h : ℝ} (hx : 4 < x) (hh : 0 ≤ h)
    {a : ℕ} (ha : a ∈ outerBlock x h) :
    |(fibreLen x h a : ℝ) -
        (movingFibreWindowLength x h ⌈x / (a : ℝ)⌉₊ : ℝ)|
      ≤ h / Real.sqrt x + 2 := by
  have hbase := abs_fibreLen_sub_fixedLength_le hx hh ha
    (movingFibreWindowLength x h ⌈x / (a : ℝ)⌉₊)
  have hround := abs_localScale_sub_movingFibreWindowLength_le
    (x := x) (h := h) (by linarith) hh ⌈x / (a : ℝ)⌉₊
  rw [fibreStartIdx] at hbase
  linarith

theorem sum_innerFibre_sq_le_movingWindowSq_add_rounding (f : ℕ → ℝ)
    (hf : ∀ n, |f n| ≤ 1) {x h : ℝ} (hx : 4 < x) (hh : 0 ≤ h) :
    (∑ a ∈ outerBlock x h, (∑ b ∈ innerFibre x h a, f b) ^ (2 : ℕ))
      ≤ 8 * ∑ y ∈ Finset.Icc ⌈Real.sqrt x / 2⌉₊ ⌈Real.sqrt x⌉₊,
          fixedWindowSq f (movingFibreWindowLength x h y) (y - 1)
        + 2 * ((outerBlock x h).card : ℝ) * (h / Real.sqrt x + 2) ^ (2 : ℕ) := by
  have hbridge := sum_innerFibre_sq_le_variableWindowSq_add_lengthError f hf
    (le_of_lt hx) hh (movingFibreWindowLength x h)
  have herror :
      (∑ a ∈ outerBlock x h,
          |(fibreLen x h a : ℝ) -
            (movingFibreWindowLength x h ⌈x / (a : ℝ)⌉₊ : ℝ)| ^ (2 : ℕ))
        ≤ ((outerBlock x h).card : ℝ) * (h / Real.sqrt x + 2) ^ (2 : ℕ) := by
    calc
      (∑ a ∈ outerBlock x h,
          |(fibreLen x h a : ℝ) -
            (movingFibreWindowLength x h ⌈x / (a : ℝ)⌉₊ : ℝ)| ^ (2 : ℕ))
          ≤ ∑ _a ∈ outerBlock x h, (h / Real.sqrt x + 2) ^ (2 : ℕ) := by
            refine Finset.sum_le_sum (fun a ha => ?_)
            have hlen := abs_fibreLen_sub_movingFibreWindowLength_le hx hh ha
            exact pow_le_pow_left₀ (abs_nonneg _) hlen 2
      _ = ((outerBlock x h).card : ℝ) * (h / Real.sqrt x + 2) ^ (2 : ℕ) := by
        rw [Finset.sum_const, nsmul_eq_mul]
  nlinarith

end

end RHTower.Sieve

