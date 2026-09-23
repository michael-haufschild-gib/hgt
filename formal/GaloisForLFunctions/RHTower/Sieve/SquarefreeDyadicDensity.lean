import GaloisForLFunctions.RHTower.Sieve.SquarefreeWindowCount

/-!
# The squarefree density over a dyadic window

Taking `R` just above the square root of the range, the window estimate becomes

    | #{n ∈ (y, 2y] : n squarefree} - y·D | = O(√y),   D = 6/π²,

so the relative count tends to `D`.  This is the second input the bilinear all-interval theorem is
applied to: the mean of `μ²` over the dyadic block `[√x, 2√x]` is `D + o(1)`.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction Filter Topology

/-- The natural square root, below the real one. -/
theorem natSqrt_le_sqrt (m : ℕ) : ((Nat.sqrt m : ℕ) : ℝ) ≤ Real.sqrt (m : ℝ) := by
  have h : Nat.sqrt m ^ (2 : ℕ) ≤ m := Nat.sqrt_le' m
  have hc : ((Nat.sqrt m : ℕ) : ℝ) ^ (2 : ℕ) ≤ (m : ℝ) := by exact_mod_cast h
  calc ((Nat.sqrt m : ℕ) : ℝ)
      = Real.sqrt (((Nat.sqrt m : ℕ) : ℝ) ^ (2 : ℕ)) := (Real.sqrt_sq (by positivity)).symm
    _ ≤ Real.sqrt (m : ℝ) := Real.sqrt_le_sqrt hc

/-- The real square root, below the natural one plus one. -/
theorem sqrt_lt_natSqrt_succ (m : ℕ) :
    Real.sqrt (m : ℝ) < ((Nat.sqrt m + 1 : ℕ) : ℝ) := by
  have h : m < (Nat.sqrt m + 1) ^ (2 : ℕ) := Nat.lt_succ_sqrt' m
  have hc : (m : ℝ) < ((Nat.sqrt m + 1 : ℕ) : ℝ) ^ (2 : ℕ) := by exact_mod_cast h
  calc Real.sqrt (m : ℝ)
      < Real.sqrt (((Nat.sqrt m + 1 : ℕ) : ℝ) ^ (2 : ℕ)) :=
        Real.sqrt_lt_sqrt (by positivity) hc
    _ = ((Nat.sqrt m + 1 : ℕ) : ℝ) := Real.sqrt_sq (by positivity)

/-- **The squarefree density over a dyadic window.** -/
theorem tendsto_window_squarefree_density :
    Tendsto (fun y : ℝ =>
        (∑ n ∈ Finset.Ioc ⌊y⌋₊ ⌊2 * y⌋₊, ((moebius n : ℤ) : ℝ) ^ (2 : ℕ)) / y)
      atTop (𝓝 squarefreeDensity) := by
  have hD0 : 0 ≤ squarefreeDensity := by
    rw [squarefreeDensity_eq]
    positivity
  have hsqrt : Tendsto (fun y : ℝ => Real.sqrt y) atTop atTop := Real.tendsto_sqrt_atTop
  have hmaj : Tendsto (fun y : ℝ =>
      4 / Real.sqrt y + 1 / y + 2 / y * squarefreeDensity) atTop (𝓝 0) := by
    have h1 : Tendsto (fun y : ℝ => 4 / Real.sqrt y) atTop (𝓝 0) := by
      have := hsqrt.inv_tendsto_atTop.const_mul (4 : ℝ)
      simpa [div_eq_mul_inv, mul_zero] using this
    have h2 : Tendsto (fun y : ℝ => 1 / y) atTop (𝓝 0) := by
      simpa [one_div] using tendsto_inv_atTop_zero
    have h3 : Tendsto (fun y : ℝ => 2 / y * squarefreeDensity) atTop (𝓝 0) := by
      have := (tendsto_inv_atTop_zero.const_mul (2 : ℝ)).mul_const squarefreeDensity
      simpa [div_eq_mul_inv] using this
    have := (h1.add h2).add h3
    simpa using this
  have hkey : Tendsto (fun y : ℝ =>
      |(∑ n ∈ Finset.Ioc ⌊y⌋₊ ⌊2 * y⌋₊, ((moebius n : ℤ) : ℝ) ^ (2 : ℕ)) / y - squarefreeDensity|)
      atTop (𝓝 0) := by
    refine squeeze_zero' ?_ ?_ hmaj
    · filter_upwards with y
      exact abs_nonneg _
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with y hy
      have hy0 : (0 : ℝ) < y := by linarith
      set t : ℕ := ⌊y⌋₊ with ht
      set m : ℕ := ⌊2 * y⌋₊ with hm
      have htm : t ≤ m := Nat.floor_le_floor (by linarith)
      set L : ℕ := m - t with hL
      have htL : t + L = m := by omega
      set R : ℕ := Nat.sqrt m + 1 with hR
      have hR1 : 1 ≤ R := by omega
      have hRM : t + L ≤ R ^ (2 : ℕ) := by
        rw [htL, hR]
        exact le_of_lt (Nat.lt_succ_sqrt' m)
      have hbound := abs_window_squarefree_sub_le (t := t) (L := L) hR1 hRM
      rw [htL] at hbound
      -- real estimates on the floors
      have htle : (t : ℝ) ≤ y := Nat.floor_le hy0.le
      have htgt : y < (t : ℝ) + 1 := Nat.lt_floor_add_one y
      have hmle : (m : ℝ) ≤ 2 * y := Nat.floor_le (by linarith)
      have hmgt : 2 * y < (m : ℝ) + 1 := Nat.lt_floor_add_one (2 * y)
      have hLcast : (L : ℝ) = (m : ℝ) - (t : ℝ) := by
        rw [hL]
        push_cast [htm]
        ring
      have hLy : |(L : ℝ) - y| ≤ 2 := by
        rw [hLcast]
        rw [abs_le]
        constructor <;> linarith
      -- the square-root bounds
      have hmy : (y : ℝ) ≤ (m : ℝ) := by linarith
      have hsy : Real.sqrt y ≤ Real.sqrt (m : ℝ) := Real.sqrt_le_sqrt hmy
      have hsy0 : (0 : ℝ) < Real.sqrt y := Real.sqrt_pos.2 hy0
      have hRlow : Real.sqrt (m : ℝ) < (R : ℝ) := by
        rw [hR]; exact sqrt_lt_natSqrt_succ m
      have hRpos : (0 : ℝ) < (R : ℝ) := lt_of_le_of_lt (Real.sqrt_nonneg _) hRlow
      have hRhigh : (R : ℝ) ≤ Real.sqrt (m : ℝ) + 1 := by
        rw [hR]
        push_cast
        have := natSqrt_le_sqrt m
        linarith
      have hsqrt2y : Real.sqrt (m : ℝ) ≤ 2 * Real.sqrt y := by
        have h2 : Real.sqrt (m : ℝ) ≤ Real.sqrt (4 * y) := by
          refine Real.sqrt_le_sqrt ?_
          linarith
        have h4 : Real.sqrt (4 * y) = 2 * Real.sqrt y := by
          rw [show (4 : ℝ) * y = 2 ^ (2 : ℕ) * y by ring, Real.sqrt_mul (by positivity),
            Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
        linarith [h2, h4.le, h4.ge]
      have hLle : (L : ℝ) ≤ 2 * y := by rw [hLcast]; linarith
      have hLR : (L : ℝ) / (R : ℝ) ≤ 2 * Real.sqrt y := by
        rw [div_le_iff₀ hRpos]
        have hstep : (L : ℝ) ≤ 2 * y := hLle
        have hRge : Real.sqrt y ≤ (R : ℝ) := le_trans hsy hRlow.le
        have hyy : y = Real.sqrt y * Real.sqrt y := (Real.mul_self_sqrt hy0.le).symm
        nlinarith [hsy0, hRge, hstep, hyy]
      have herr : (R : ℝ) + (L : ℝ) / (R : ℝ) ≤ 4 * Real.sqrt y + 1 := by
        linarith [hRhigh, hsqrt2y, hLR]
      -- assemble
      have hsplit : |(∑ n ∈ Finset.Ioc t m, ((moebius n : ℤ) : ℝ) ^ (2 : ℕ)) / y - squarefreeDensity|
          ≤ (4 * Real.sqrt y + 1) / y + (2 / y) * squarefreeDensity := by
        have hA : |(∑ n ∈ Finset.Ioc t m, ((moebius n : ℤ) : ℝ) ^ (2 : ℕ)) - (L : ℝ) * squarefreeDensity|
            ≤ 4 * Real.sqrt y + 1 := le_trans hbound herr
        have hB : |((L : ℝ) - y) * squarefreeDensity| ≤ 2 * squarefreeDensity := by
          rw [abs_mul, abs_of_nonneg hD0]
          exact mul_le_mul_of_nonneg_right hLy hD0
        have hC : |(∑ n ∈ Finset.Ioc t m, ((moebius n : ℤ) : ℝ) ^ (2 : ℕ))
              - y * squarefreeDensity|
            ≤ (4 * Real.sqrt y + 1) + 2 * squarefreeDensity := by
          have := abs_sub_le (∑ n ∈ Finset.Ioc t m, ((moebius n : ℤ) : ℝ) ^ (2 : ℕ))
            ((L : ℝ) * squarefreeDensity) (y * squarefreeDensity)
          have hrw : |(L : ℝ) * squarefreeDensity - y * squarefreeDensity|
              = |((L : ℝ) - y) * squarefreeDensity| := by
            congr 1
            ring
          linarith [this, hrw ▸ hB]
        have hdiv : |(∑ n ∈ Finset.Ioc t m, ((moebius n : ℤ) : ℝ) ^ (2 : ℕ)) / y - squarefreeDensity|
            = |(∑ n ∈ Finset.Ioc t m, ((moebius n : ℤ) : ℝ) ^ (2 : ℕ)) - y * squarefreeDensity| / y := by
          rw [show (∑ n ∈ Finset.Ioc t m, ((moebius n : ℤ) : ℝ) ^ (2 : ℕ)) / y - squarefreeDensity
                = ((∑ n ∈ Finset.Ioc t m, ((moebius n : ℤ) : ℝ) ^ (2 : ℕ))
                  - y * squarefreeDensity) / y by field_simp,
            abs_div, abs_of_pos hy0]
        rw [hdiv, div_le_iff₀ hy0]
        have hrw2 : ((4 * Real.sqrt y + 1) / y + 2 / y * squarefreeDensity) * y
            = (4 * Real.sqrt y + 1) + 2 * squarefreeDensity := by field_simp
        rw [hrw2]
        exact hC
      have hid : Real.sqrt y / y = 1 / Real.sqrt y := by
        rw [div_eq_div_iff (ne_of_gt hy0) (ne_of_gt hsy0), Real.mul_self_sqrt hy0.le]
        ring
      have hfinal : (4 * Real.sqrt y + 1) / y = 4 / Real.sqrt y + 1 / y := by
        rw [add_div, mul_div_assoc, hid]
        ring
      linarith [hsplit, hfinal]
  have := (tendsto_const_nhds (x := squarefreeDensity) (f := atTop (α := ℝ))).add
    (tendsto_zero_iff_abs_tendsto_zero _ |>.2 hkey)
  simpa using this

end RHTower.Sieve
