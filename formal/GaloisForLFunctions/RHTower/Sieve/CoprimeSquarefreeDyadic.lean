import GaloisForLFunctions.RHTower.Sieve.CoprimeSquarefreeWindow
import GaloisForLFunctions.RHTower.Sieve.SquarefreeDyadicDensity

/-!
# The card's equation (8)

Combining the window count with the value of the deleted series,

    (1 - 1/p)·S_p = D·p/(p+1),

and the dyadic window then gives

    (1/y) ∑_{y < m ≤ 2y} μ²(m)·1_{p ∤ m} → D·p/(p+1),

which is exactly the card's `(8)`: excluding one prime rescales the squarefree density by `p/(p+1)`.
-/

namespace RHTower.Sieve

open Finset Nat Filter Topology
open scoped ArithmeticFunction.Moebius

/-- **Card equation (8), the density value.** -/
theorem coprime_density_eq {p : ℕ} (hp : p.Prime) :
    (1 - 1 / (p : ℝ)) * coprimeSquarefreeSum p
      = squarefreeDensity * (p : ℝ) / ((p : ℝ) + 1) := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hp0 : (p : ℝ) ≠ 0 := by intro h; rw [h] at hp2; linarith
  have hp1 : (p : ℝ) + 1 ≠ 0 := by intro h; linarith
  have hmul := coprimeSquarefreeSum_mul_eq hp
  field_simp at hmul ⊢
  linarith [hmul]

/-- The deleted density is nonnegative. -/
theorem coprime_density_nonneg {p : ℕ} (hp : p.Prime) :
    0 ≤ (1 - 1 / (p : ℝ)) * coprimeSquarefreeSum p := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hD : 0 ≤ squarefreeDensity := by
    rw [squarefreeDensity_eq]
    positivity
  rw [coprime_density_eq hp]
  positivity

/-- **The dyadic density of squarefree integers coprime to `p`.** -/
theorem tendsto_window_coprime_squarefree_density {p : ℕ} (hp : p.Prime) :
    Tendsto (fun y : ℝ =>
        (∑ n ∈ Finset.Ioc ⌊y⌋₊ ⌊2 * y⌋₊, (if p ∣ n then 0 else ((μ n : ℤ) : ℝ) ^ (2 : ℕ))) / y)
      atTop (𝓝 (squarefreeDensity * (p : ℝ) / ((p : ℝ) + 1))) := by
  set δ : ℝ := (1 - 1 / (p : ℝ)) * coprimeSquarefreeSum p with hδ
  have hδ0 : 0 ≤ δ := coprime_density_nonneg hp
  have hsqrt : Tendsto (fun y : ℝ => Real.sqrt y) atTop atTop := Real.tendsto_sqrt_atTop
  have hmaj : Tendsto (fun y : ℝ => 6 / Real.sqrt y + 2 / y + 2 / y * δ) atTop (𝓝 0) := by
    have h1 : Tendsto (fun y : ℝ => 6 / Real.sqrt y) atTop (𝓝 0) := by
      have := hsqrt.inv_tendsto_atTop.const_mul (6 : ℝ)
      simpa [div_eq_mul_inv, mul_zero] using this
    have h2 : Tendsto (fun y : ℝ => 2 / y) atTop (𝓝 0) := by
      have := tendsto_inv_atTop_zero.const_mul (2 : ℝ)
      simpa [div_eq_mul_inv] using this
    have h3 : Tendsto (fun y : ℝ => 2 / y * δ) atTop (𝓝 0) := by
      have := (tendsto_inv_atTop_zero.const_mul (2 : ℝ)).mul_const δ
      simpa [div_eq_mul_inv] using this
    have := (h1.add h2).add h3
    simpa using this
  have hkey : Tendsto (fun y : ℝ =>
      |(∑ n ∈ Finset.Ioc ⌊y⌋₊ ⌊2 * y⌋₊, (if p ∣ n then 0 else ((μ n : ℤ) : ℝ) ^ (2 : ℕ))) / y - δ|)
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
      have hbound := abs_window_coprime_squarefree_sub_le (p := p) (t := t) (L := L) hp hR1 hRM
      rw [htL, ← hδ] at hbound
      have htle : (t : ℝ) ≤ y := Nat.floor_le hy0.le
      have htgt : y < (t : ℝ) + 1 := Nat.lt_floor_add_one y
      have hmle : (m : ℝ) ≤ 2 * y := Nat.floor_le (by linarith)
      have hmgt : 2 * y < (m : ℝ) + 1 := Nat.lt_floor_add_one (2 * y)
      have hLcast : (L : ℝ) = (m : ℝ) - (t : ℝ) := by
        rw [hL]
        push_cast [htm]
        ring
      have hLy : |(L : ℝ) - y| ≤ 2 := by
        rw [hLcast, abs_le]
        constructor <;> linarith
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
        have hRge : Real.sqrt y ≤ (R : ℝ) := le_trans hsy hRlow.le
        have hyy : y = Real.sqrt y * Real.sqrt y := (Real.mul_self_sqrt hy0.le).symm
        nlinarith [hsy0, hRge, hLle, hyy]
      have herr : 2 * (R : ℝ) + (L : ℝ) / (R : ℝ) ≤ 6 * Real.sqrt y + 2 := by
        linarith [hRhigh, hsqrt2y, hLR]
      have hsplit : |(∑ n ∈ Finset.Ioc t m,
              (if p ∣ n then 0 else ((μ n : ℤ) : ℝ) ^ (2 : ℕ))) / y - δ|
          ≤ (6 * Real.sqrt y + 2) / y + (2 / y) * δ := by
        have hA : |(∑ n ∈ Finset.Ioc t m, (if p ∣ n then 0 else ((μ n : ℤ) : ℝ) ^ (2 : ℕ)))
              - (L : ℝ) * δ| ≤ 6 * Real.sqrt y + 2 := le_trans hbound herr
        have hB : |((L : ℝ) - y) * δ| ≤ 2 * δ := by
          rw [abs_mul, abs_of_nonneg hδ0]
          exact mul_le_mul_of_nonneg_right hLy hδ0
        have hC : |(∑ n ∈ Finset.Ioc t m, (if p ∣ n then 0 else ((μ n : ℤ) : ℝ) ^ (2 : ℕ)))
              - y * δ| ≤ (6 * Real.sqrt y + 2) + 2 * δ := by
          have hts := abs_sub_le
            (∑ n ∈ Finset.Ioc t m, (if p ∣ n then 0 else ((μ n : ℤ) : ℝ) ^ (2 : ℕ)))
            ((L : ℝ) * δ) (y * δ)
          have hrw : |(L : ℝ) * δ - y * δ| = |((L : ℝ) - y) * δ| := by
            congr 1
            ring
          linarith [hts, hrw ▸ hB]
        have hdiv : |(∑ n ∈ Finset.Ioc t m,
              (if p ∣ n then 0 else ((μ n : ℤ) : ℝ) ^ (2 : ℕ))) / y - δ|
            = |(∑ n ∈ Finset.Ioc t m, (if p ∣ n then 0 else ((μ n : ℤ) : ℝ) ^ (2 : ℕ)))
              - y * δ| / y := by
          rw [show (∑ n ∈ Finset.Ioc t m, (if p ∣ n then 0 else ((μ n : ℤ) : ℝ) ^ (2 : ℕ))) / y - δ
                = ((∑ n ∈ Finset.Ioc t m, (if p ∣ n then 0 else ((μ n : ℤ) : ℝ) ^ (2 : ℕ)))
                  - y * δ) / y by field_simp,
            abs_div, abs_of_pos hy0]
        rw [hdiv, div_le_iff₀ hy0]
        have hrw2 : ((6 * Real.sqrt y + 2) / y + 2 / y * δ) * y
            = (6 * Real.sqrt y + 2) + 2 * δ := by field_simp
        rw [hrw2]
        exact hC
      have hid : Real.sqrt y / y = 1 / Real.sqrt y := by
        rw [div_eq_div_iff (ne_of_gt hy0) (ne_of_gt hsy0), Real.mul_self_sqrt hy0.le]
        ring
      have hfinal : (6 * Real.sqrt y + 2) / y = 6 / Real.sqrt y + 2 / y := by
        rw [add_div, mul_div_assoc, hid]
        ring
      linarith [hsplit, hfinal]
  have hlim := (tendsto_const_nhds (x := δ) (f := atTop (α := ℝ))).add
    (tendsto_zero_iff_abs_tendsto_zero _ |>.2 hkey)
  rw [← coprime_density_eq hp, ← hδ]
  simpa using hlim

end RHTower.Sieve
