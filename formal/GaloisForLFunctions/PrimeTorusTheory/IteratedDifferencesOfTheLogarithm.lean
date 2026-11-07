import Mathlib

/-!
# Iterated differences of the logarithm

The `j`-th forward difference of `log` at `x > 0` has the exact form

`Δ^{j+1} log x = (−1)^j ∫₀¹ j! / Π_{i ≤ j} (x + u + i) du`,

so it has sign `(−1)^j`, and `j!/(x+j+1)^{j+1} ≤ |Δ^{j+1} log x| ≤ j!/x^{j+1}`. The integrand is obtained from
`Δ^j (1/x) = (−1)^j j!/Π_{i ≤ j}(x + i)` by partial fractions, one difference at a time.
-/

open Finset Real
open scoped fwdDiff

namespace GaloisForLFunctions.PrimeTorusTheory

noncomputable section

/-- The rational kernel `j!/Π_{i ≤ j}(y + i)`. -/
def diffKernel (j : ℕ) (y : ℝ) : ℝ := (j.factorial : ℝ) / ∏ i ∈ range (j + 1), (y + i)

theorem prod_add_pos {j : ℕ} {y : ℝ} (hy : 0 < y) : 0 < ∏ i ∈ range (j + 1), (y + i) :=
  Finset.prod_pos fun i _ => by positivity

theorem diffKernel_pos {j : ℕ} {y : ℝ} (hy : 0 < y) : 0 < diffKernel j y :=
  div_pos (by positivity) (prod_add_pos hy)

/-- One difference of the kernel is minus the next kernel. -/
theorem diffKernel_sub {j : ℕ} {y : ℝ} (hy : 0 < y) :
    diffKernel j (y + 1) - diffKernel j y = -diffKernel (j + 1) y := by
  unfold diffKernel
  have h1 : ∏ i ∈ range (j + 1), (y + 1 + (i : ℝ)) = ∏ i ∈ range (j + 1), (y + ((i + 1 : ℕ) : ℝ)) :=
    Finset.prod_congr rfl fun i _ => by push_cast; ring
  have h2 : ∏ i ∈ range (j + 1 + 1), (y + (i : ℝ)) =
      (∏ i ∈ range (j + 1), (y + ((i + 1 : ℕ) : ℝ))) * (y + ((0 : ℕ) : ℝ)) :=
    Finset.prod_range_succ' _ _
  have h3 : ∏ i ∈ range (j + 1 + 1), (y + (i : ℝ)) =
      (∏ i ∈ range (j + 1), (y + (i : ℝ))) * (y + ((j + 1 : ℕ) : ℝ)) :=
    Finset.prod_range_succ _ _
  set A := ∏ i ∈ range (j + 1), (y + ((i + 1 : ℕ) : ℝ)) with hA
  set B := ∏ i ∈ range (j + 1), (y + (i : ℝ)) with hB
  have hApos : 0 < A := Finset.prod_pos fun i _ => by positivity
  have hBpos : 0 < B := prod_add_pos hy
  have hrel : A * y = B * (y + ((j + 1 : ℕ) : ℝ)) := by
    rw [← h3, h2]; simp
  rw [h1, h2, Nat.factorial_succ]
  push_cast at hrel ⊢
  have hy' : y ≠ 0 := hy.ne'
  have hjy : y + ((j : ℝ) + 1) ≠ 0 := by positivity
  field_simp
  have hB' : B = A * y / (y + ((j : ℝ) + 1)) := by
    field_simp
    linarith
  rw [hB']
  field_simp
  ring

theorem continuousOn_diffKernel (j : ℕ) {x : ℝ} (hx : 0 < x) :
    ContinuousOn (fun u : ℝ => diffKernel j (x + u)) (Set.uIcc 0 1) := by
  unfold diffKernel
  refine ContinuousOn.div continuousOn_const ?_ ?_
  · exact continuous_finsetProd _ (fun i _ => by fun_prop) |>.continuousOn
  · intro u hu
    rw [Set.uIcc_of_le zero_le_one] at hu
    exact (prod_add_pos (by linarith [hu.1])).ne'

/-- The exact form of the differences of `log`: `Δ^{j+1} log x = (−1)^j ∫₀¹ diffKernel j (x + u) du`. -/
theorem fwdDiff_iter_log {j : ℕ} {x : ℝ} (hx : 0 < x) :
    (fwdDiff (1 : ℝ))^[j + 1] Real.log x =
      (-1) ^ j * ∫ u in (0 : ℝ)..1, diffKernel j (x + u) := by
  induction j generalizing x with
  | zero =>
    simp only [zero_add, Function.iterate_one, fwdDiff, pow_zero, one_mul]
    have h : ∀ u : ℝ, diffKernel 0 (x + u) = (x + u)⁻¹ := by
      intro u; simp [diffKernel]
    simp_rw [h]
    rw [intervalIntegral.integral_comp_add_left (fun y => y⁻¹) x, add_zero, integral_inv_of_pos hx
      (by linarith), Real.log_div (by linarith) hx.ne']
  | succ j ih =>
    rw [Function.iterate_succ_apply', fwdDiff, ih hx, ih (by linarith : 0 < x + 1), pow_succ]
    have hi : ∀ z : ℝ, 0 < z → IntervalIntegrable (fun u : ℝ => diffKernel j (z + u)) MeasureTheory.volume 0 1 :=
      fun z hz => (continuousOn_diffKernel j hz).intervalIntegrable
    have e : ∫ u in (0 : ℝ)..1, diffKernel (j + 1) (x + u) =
        -((∫ u in (0 : ℝ)..1, diffKernel j (x + 1 + u)) - ∫ u in (0 : ℝ)..1, diffKernel j (x + u)) := by
      rw [← intervalIntegral.integral_sub (hi _ (by linarith)) (hi _ hx),
        ← intervalIntegral.integral_neg]
      refine intervalIntegral.integral_congr fun u hu => ?_
      rw [Set.uIcc_of_le zero_le_one] at hu
      have hpos : 0 < x + u := by linarith [hu.1]
      have := diffKernel_sub (j := j) hpos
      rw [show x + 1 + u = x + u + 1 by ring, this]
      ring
    rw [e]
    ring

/-- `diffKernel j y ≤ j!/y^{j+1}`. -/
theorem diffKernel_le {j : ℕ} {y : ℝ} (hy : 0 < y) :
    diffKernel j y ≤ (j.factorial : ℝ) / y ^ (j + 1) := by
  unfold diffKernel
  refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
  calc y ^ (j + 1) = ∏ _i ∈ range (j + 1), y := by simp
    _ ≤ ∏ i ∈ range (j + 1), (y + i) :=
      Finset.prod_le_prod (fun _ _ => hy.le) fun i _ => by
        have : (0 : ℝ) ≤ i := by positivity
        linarith

/-- `j!/(y+j)^{j+1} ≤ diffKernel j y`. -/
theorem le_diffKernel {j : ℕ} {y : ℝ} (hy : 0 < y) :
    (j.factorial : ℝ) / (y + j) ^ (j + 1) ≤ diffKernel j y := by
  unfold diffKernel
  refine div_le_div_of_nonneg_left (by positivity) (prod_add_pos hy) ?_
  calc ∏ i ∈ range (j + 1), (y + i) ≤ ∏ _i ∈ range (j + 1), (y + j) :=
        Finset.prod_le_prod (fun i _ => by positivity) fun i hi => by
          have : (i : ℝ) ≤ j := by
            exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
          linarith
    _ = (y + j) ^ (j + 1) := by simp

/-- Upper bound for the differences of `log`. -/
theorem abs_fwdDiff_iter_log_le {j : ℕ} {x : ℝ} (hx : 0 < x) :
    |(fwdDiff (1 : ℝ))^[j + 1] Real.log x| ≤ (j.factorial : ℝ) / x ^ (j + 1) := by
  rw [fwdDiff_iter_log hx, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  have hint : IntervalIntegrable (fun u : ℝ => diffKernel j (x + u)) MeasureTheory.volume 0 1 :=
    (continuousOn_diffKernel j hx).intervalIntegrable
  have hnn : 0 ≤ ∫ u in (0 : ℝ)..1, diffKernel j (x + u) :=
    intervalIntegral.integral_nonneg zero_le_one fun u hu =>
      (diffKernel_pos (by linarith [hu.1])).le
  rw [abs_of_nonneg hnn]
  have hle : ∫ u in (0 : ℝ)..1, diffKernel j (x + u) ≤
      ∫ _u in (0 : ℝ)..1, (j.factorial : ℝ) / x ^ (j + 1) := by
    refine intervalIntegral.integral_mono_on zero_le_one hint (by simp) fun u hu => ?_
    have hy : 0 < x + u := by linarith [hu.1]
    refine (diffKernel_le hy).trans ?_
    refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
    exact pow_le_pow_left₀ hx.le (by linarith [hu.1]) _
  simpa using hle

/-- Lower bound for the differences of `log`. -/
theorem le_abs_fwdDiff_iter_log {j : ℕ} {x : ℝ} (hx : 0 < x) :
    (j.factorial : ℝ) / (x + j + 1) ^ (j + 1) ≤ |(fwdDiff (1 : ℝ))^[j + 1] Real.log x| := by
  rw [fwdDiff_iter_log hx, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  have hint : IntervalIntegrable (fun u : ℝ => diffKernel j (x + u)) MeasureTheory.volume 0 1 :=
    (continuousOn_diffKernel j hx).intervalIntegrable
  have hle : ∫ _u in (0 : ℝ)..1, (j.factorial : ℝ) / (x + j + 1) ^ (j + 1) ≤
      ∫ u in (0 : ℝ)..1, diffKernel j (x + u) := by
    refine intervalIntegral.integral_mono_on zero_le_one (by simp) hint fun u hu => ?_
    have hy : 0 < x + u := by linarith [hu.1]
    refine le_trans ?_ (le_diffKernel hy)
    refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
    refine pow_le_pow_left₀ (by positivity) ?_ _
    linarith [hu.2]
  have h2 : ∫ _u in (0 : ℝ)..1, (j.factorial : ℝ) / (x + j + 1) ^ (j + 1) =
      (j.factorial : ℝ) / (x + j + 1) ^ (j + 1) := by simp
  rw [h2] at hle
  exact hle.trans (le_abs_self _)

end

end GaloisForLFunctions.PrimeTorusTheory
