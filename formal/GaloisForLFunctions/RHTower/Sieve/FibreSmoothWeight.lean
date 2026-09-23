import GaloisForLFunctions.RHTower.Sieve.FibreKernelExact
import GaloisForLFunctions.RHTower.Sieve.KernelSmoothSplit

/-!
# The smooth model of the fibre kernel

The kernel at shift `k`, as a function of the inner variable, is the count of integers in
`[fibreLow_fibreKernelExact x i, fibreHigh_fibreKernelExact x h (i+k)]`.  Its smooth model is the length of that interval plus one,
truncated at zero:

```text
fibreSmooth x h k i = max ( fibreHigh_fibreKernelExact x h (i+k) − fibreLow_fibreKernelExact x i + 1 , 0 ) ,
```

and the two differ by at most `2` — uniformly, with no hypothesis on the position of the endpoints.
The model has three further properties the discrete count lacks:

* it never exceeds `3h + 1`;
* it vanishes as soon as `i + k` leaves the window, and as soon as `i` leaves the band
  `[x/(2√x+1), (x + h√x)/(√x−1)]`;
* it is a minimum of four monotone expressions, hence quasi-concave, hence of variation `O(h)`.
-/

noncomputable section

namespace RHTower.Sieve

open Finset

/-- **The integer count of an interval differs from its smooth model by at most two.** -/
theorem abs_card_Icc_sub_smooth_le {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    |((Finset.Icc ⌈A⌉₊ ⌊B⌋₊).card : ℝ) - kernelSmooth A B| ≤ 2 := by
  classical
  rw [Nat.card_Icc]
  rcases le_or_gt ⌈A⌉₊ (⌊B⌋₊ + 1) with hle | hgt
  · have hcast : ((⌊B⌋₊ + 1 - ⌈A⌉₊ : ℕ) : ℝ) = (⌊B⌋₊ : ℝ) + 1 - (⌈A⌉₊ : ℝ) := by
      rw [Nat.cast_sub hle]
      push_cast
      ring
    rw [hcast]
    exact abs_count_sub_smooth_le hA hB (by exact_mod_cast hle)
  · have hzero : ⌊B⌋₊ + 1 - ⌈A⌉₊ = 0 := by omega
    rw [hzero]
    have hBlt : B < ((⌊B⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one B
    have hAgt : ((⌈A⌉₊ : ℕ) : ℝ) < A + 1 := by
      have := Nat.ceil_lt_add_one hA
      exact_mod_cast this
    have hstep : ((⌊B⌋₊ : ℕ) : ℝ) + 2 ≤ ((⌈A⌉₊ : ℕ) : ℝ) := by
      have : (⌊B⌋₊ : ℕ) + 2 ≤ (⌈A⌉₊ : ℕ) := by omega
      exact_mod_cast this
    have hBA : B < A := by linarith
    have hsm : kernelSmooth A B ≤ 1 := by
      rw [kernelSmooth]
      exact max_le (by linarith) (by norm_num)
    have hsm0 : 0 ≤ kernelSmooth A B := le_max_right _ _
    rw [Nat.cast_zero, abs_le]
    constructor <;> linarith

/-- The smooth model of the fibre kernel at shift `k`. -/
def fibreSmooth (x h : ℝ) (k i : ℕ) : ℝ :=
  kernelSmooth (fibreLow_fibreKernelExact x i) (fibreHigh_fibreKernelExact x h (i + k))

theorem fibreSmooth_nonneg (x h : ℝ) (k i : ℕ) : 0 ≤ fibreSmooth x h k i := le_max_right _ _

theorem fibreLow_nonneg (x : ℝ) (n : ℕ) : 0 ≤ fibreLow_fibreKernelExact x n :=
  le_trans (Real.sqrt_nonneg x) (le_max_right _ _)

theorem div_le_fibreLow (x : ℝ) (n : ℕ) : x / (n : ℝ) ≤ fibreLow_fibreKernelExact x n := le_max_left _ _

theorem sqrt_le_fibreLow (x : ℝ) (n : ℕ) : Real.sqrt x ≤ fibreLow_fibreKernelExact x n := le_max_right _ _

theorem fibreHigh_le_div (x h : ℝ) (m : ℕ) :
    fibreHigh_fibreKernelExact x h m ≤ (x + h * Real.sqrt x) / (m : ℝ) := min_le_left _ _

theorem fibreHigh_le_two_sqrt (x h : ℝ) (m : ℕ) : fibreHigh_fibreKernelExact x h m ≤ 2 * Real.sqrt x :=
  min_le_right _ _

/-- **The smooth model never exceeds `3h + 1`.** -/
theorem fibreSmooth_le {x h : ℝ} (hx : 4 ≤ x) (hh : 0 ≤ h) (k : ℕ) {i : ℕ} (hi : 1 ≤ i) :
    fibreSmooth x h k i ≤ 3 * h + 1 := by
  have hs2 : (2 : ℝ) ≤ Real.sqrt x := two_le_sqrt hx
  have hsq : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt (by linarith)
  have hI1 : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi
  have hK0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  rw [fibreSmooth, kernelSmooth]
  refine max_le ?_ (by linarith)
  -- on the support the lower endpoint is at most `2√x + 1`
  rcases le_or_gt (fibreHigh_fibreKernelExact x h (i + k) - fibreLow_fibreKernelExact x i + 1) 0 with hneg | hpos
  · linarith
  have hlow : fibreLow_fibreKernelExact x i ≤ fibreHigh_fibreKernelExact x h (i + k) + 1 := by linarith
  have hhigh2 : fibreHigh_fibreKernelExact x h (i + k) ≤ 2 * Real.sqrt x := fibreHigh_le_two_sqrt x h (i + k)
  have hxi : x / (i : ℝ) ≤ 2 * Real.sqrt x + 1 :=
    le_trans (div_le_fibreLow x i) (by linarith)
  have hI0 : (0 : ℝ) < (i : ℝ) := by linarith
  have hxi' : x ≤ (i : ℝ) * (2 * Real.sqrt x + 1) := by
    rw [div_le_iff₀ hI0] at hxi
    linarith
  have h3I : Real.sqrt x ≤ 3 * (i : ℝ) := by nlinarith [hxi', hs2, hI1, hsq]
  -- and the interval is then short
  have hden : (0 : ℝ) < (i : ℝ) + (k : ℝ) := by linarith
  have hstep : fibreHigh_fibreKernelExact x h (i + k) - fibreLow_fibreKernelExact x i ≤ h * Real.sqrt x / (i : ℝ) := by
    have h1 : fibreHigh_fibreKernelExact x h (i + k)
        ≤ (x + h * Real.sqrt x) / (((i + k : ℕ) : ℝ)) := fibreHigh_le_div x h (i + k)
    have hcast : (((i + k : ℕ) : ℝ)) = (i : ℝ) + (k : ℝ) := by push_cast; ring
    rw [hcast] at h1
    have h2 : (x + h * Real.sqrt x) / ((i : ℝ) + (k : ℝ))
        ≤ (x + h * Real.sqrt x) / (i : ℝ) := by
      refine div_le_div_of_nonneg_left ?_ hI0 (by linarith)
      have hs0 : (0 : ℝ) ≤ Real.sqrt x := Real.sqrt_nonneg x
      nlinarith [hs0, hh]
    have h3 : x / (i : ℝ) ≤ fibreLow_fibreKernelExact x i := div_le_fibreLow x i
    have hsplit : (x + h * Real.sqrt x) / (i : ℝ)
        = x / (i : ℝ) + h * Real.sqrt x / (i : ℝ) := by
      field_simp
    linarith
  have hfin : h * Real.sqrt x / (i : ℝ) ≤ 3 * h := by
    rw [div_le_iff₀ hI0]
    nlinarith [h3I, hh]
  linarith

/-- **The smooth model vanishes once the shifted index leaves the window.** -/
theorem fibreSmooth_eq_zero_of_gt {x h : ℝ} (hx : 4 ≤ x) (hh : 0 ≤ h) (k i : ℕ)
    (hgt : x + h * Real.sqrt x < ((i + k : ℕ) : ℝ)) :
    fibreSmooth x h k i = 0 := by
  have hs2 : (2 : ℝ) ≤ Real.sqrt x := two_le_sqrt hx
  have hden : (0 : ℝ) < ((i + k : ℕ) : ℝ) := by
    have hs0 : (0 : ℝ) ≤ Real.sqrt x := Real.sqrt_nonneg x
    have : (0 : ℝ) ≤ h * Real.sqrt x := by positivity
    linarith
  have hhigh : fibreHigh_fibreKernelExact x h (i + k) < 1 := by
    refine lt_of_le_of_lt (min_le_left _ _) ?_
    rw [div_lt_one hden]
    exact hgt
  have hlow : (2 : ℝ) ≤ fibreLow_fibreKernelExact x i := le_trans hs2 (sqrt_le_fibreLow x i)
  rw [fibreSmooth, kernelSmooth, max_eq_right (by linarith)]

/-- **The smooth model is within two of the fibre kernel.** -/
theorem abs_kernel_sub_fibreSmooth_le {x h : ℝ} (hx : 4 ≤ x) (hh : 0 ≤ h) {k i : ℕ}
    (hi : 1 ≤ i) :
    |((((outerBlock x h).filter
        (fun a => (i + k) ∈ innerFibre x h a ∧ i ∈ innerFibre x h a)).card : ℕ) : ℝ)
      - fibreSmooth x h k i| ≤ 2 := by
  classical
  have hs0 : (0 : ℝ) ≤ Real.sqrt x := Real.sqrt_nonneg x
  rcases le_or_gt (i + k) ⌊x + h * Real.sqrt x⌋₊ with hle | hgt
  · rw [fibre_kernel_eq_Icc hx hh hi (Nat.le_add_right i k) hle, fibreSmooth]
    exact abs_card_Icc_sub_smooth_le (fibreLow_nonneg x i)
      (fibreHigh_nonneg hx hh (i + k))
  · -- outside the window both the kernel and its model vanish
    have hzero : (outerBlock x h).filter
        (fun a => (i + k) ∈ innerFibre x h a ∧ i ∈ innerFibre x h a) = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun a ha => ?_
      rw [Finset.mem_filter, mem_innerFibre] at ha
      exact absurd ha.2.1.1.2 (by omega)
    have hsm : fibreSmooth x h k i = 0 := by
      refine fibreSmooth_eq_zero_of_gt hx hh k i ?_
      have hfl : x + h * Real.sqrt x < (⌊x + h * Real.sqrt x⌋₊ : ℝ) + 1 :=
        Nat.lt_floor_add_one _
      have : (⌊x + h * Real.sqrt x⌋₊ : ℝ) + 1 ≤ ((i + k : ℕ) : ℝ) := by
        have : ⌊x + h * Real.sqrt x⌋₊ + 1 ≤ i + k := by omega
        exact_mod_cast this
      linarith
    rw [hzero, hsm]
    simp

end RHTower.Sieve

end
