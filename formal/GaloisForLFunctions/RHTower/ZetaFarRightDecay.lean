import GaloisForLFunctions.RHTower.Deninger.DeningerZetaLowerBound
import Mathlib.Analysis.Complex.Liouville

/-!
# Geometric decay of `ζ - 1` far to the right

The Dirichlet tail `∑_{n≥2} n^{-s}` is at most `2^{-m}` times the Basel tail once `Re s ≥ 2 + m`,
because every term gains the factor `(n+2)^{-(Re s - 2)} ≤ 2^{-m}`.  Cauchy's estimate on the unit
disc then transfers the bound to `ζ'`, since `ζ' = (ζ-1)'`.

These are the two elementary inputs that make the right edge of a Levinson rectangle harmless: at
`Re s = 4` both `ζ - 1` and `ζ'` are smaller than `1/2`.
-/

open scoped Real
open Complex Metric

noncomputable section

namespace RHTower

theorem riemannZeta_eq_one_add_zetaTail {s : ℂ} (hs : 2 ≤ s.re) :
    riemannZeta s = 1 + ∑' n : ℕ, 1 / ((n : ℂ) + 2) ^ s := by
  have hs1 : 1 < s.re := by linarith
  have hzeta := zeta_eq_tsum_one_div_nat_cpow hs1
  have hsummable : Summable fun n : ℕ => 1 / ((n : ℂ)) ^ s := by
    refine (Complex.summable_one_div_nat_cpow (p := s)).mpr ?_
    linarith
  have hzero : (1 : ℂ) / ((0 : ℕ) : ℂ) ^ s = 0 := by
    have hs0 : s ≠ 0 := by
      intro h
      rw [h] at hs
      norm_num at hs
    rw [Nat.cast_zero, Complex.zero_cpow hs0, div_zero]
  rw [hzeta, hsummable.tsum_eq_zero_add, hzero, zero_add]
  have hsummable' : Summable fun n : ℕ => 1 / (((n + 1 : ℕ) : ℂ)) ^ s :=
    (summable_nat_add_iff 1).mpr hsummable
  rw [hsummable'.tsum_eq_zero_add]
  have hfirst : (1 : ℂ) / (((0 + 1 : ℕ) : ℂ)) ^ s = 1 := by norm_num
  rw [hfirst]
  congr 1
  refine tsum_congr fun n => ?_
  congr 2
  push_cast
  ring

/-- The tail gains a factor `2^{-m}` once the abscissa exceeds `2` by `m`. -/
theorem norm_zetaTail_le_scaled {s : ℂ} {m : ℝ} (hm : 0 ≤ m) (hs : 2 + m ≤ s.re) :
    ‖∑' n : ℕ, 1 / ((n : ℂ) + 2) ^ s‖ ≤ (3 / 4) * ((2 : ℝ) ^ m)⁻¹ := by
  have hs2 : (2 : ℝ) ≤ s.re := by linarith
  have hmpow : (0 : ℝ) < (2 : ℝ) ^ m := Real.rpow_pos_of_pos (by norm_num) m
  have hterm : ∀ n : ℕ, ‖1 / ((n : ℂ) + 2) ^ s‖
      ≤ ((2 : ℝ) ^ m)⁻¹ * (1 / (((n + 2 : ℕ) : ℝ)) ^ (2 : ℕ)) := by
    intro n
    have hb0 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    have hb : (2 : ℝ) ≤ (n : ℝ) + 2 := by
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    have hsplit : ((n : ℝ) + 2) ^ s.re
        = ((n : ℝ) + 2) ^ (2 : ℝ) * ((n : ℝ) + 2) ^ (s.re - 2) := by
      rw [← Real.rpow_add hb0]
      congr 1
      ring
    have hge : (2 : ℝ) ^ m ≤ ((n : ℝ) + 2) ^ (s.re - 2) := by
      calc (2 : ℝ) ^ m
          ≤ (2 : ℝ) ^ (s.re - 2) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ ≤ ((n : ℝ) + 2) ^ (s.re - 2) :=
            Real.rpow_le_rpow (by norm_num) hb (by linarith)
    have hsq : ((n : ℝ) + 2) ^ (2 : ℝ) = (((n + 2 : ℕ) : ℝ)) ^ (2 : ℕ) := by
      rw [Real.rpow_two]
      push_cast
      ring
    have hA : (0 : ℝ) < (((n + 2 : ℕ) : ℝ)) ^ (2 : ℕ) := by positivity
    have hkey : (((n + 2 : ℕ) : ℝ)) ^ (2 : ℕ) * (2 : ℝ) ^ m
        ≤ (((n + 2 : ℕ) : ℝ)) ^ (2 : ℕ) * ((n : ℝ) + 2) ^ (s.re - 2) :=
      mul_le_mul_of_nonneg_left hge hA.le
    have hrw : ((2 : ℝ) ^ m)⁻¹ * (1 / (((n + 2 : ℕ) : ℝ)) ^ (2 : ℕ))
        = 1 / ((((n + 2 : ℕ) : ℝ)) ^ (2 : ℕ) * (2 : ℝ) ^ m) := by
      field_simp
    rw [norm_zetaTail_term, hsplit, hsq, hrw]
    exact one_div_le_one_div_of_le (by positivity) hkey
  have htail : Summable fun n : ℕ => (1 : ℝ) / (((n + 2 : ℕ) : ℝ)) ^ (2 : ℕ) :=
    (summable_nat_add_iff 2).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
  have hcomp : Summable fun n : ℕ =>
      ((2 : ℝ) ^ m)⁻¹ * (1 / (((n + 2 : ℕ) : ℝ)) ^ (2 : ℕ)) := htail.mul_left _
  have hnormsummable : Summable fun n : ℕ => ‖1 / ((n : ℂ) + 2) ^ s‖ :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hterm hcomp
  have hsum_eq : (∑' n : ℕ, (1 : ℝ) / (((n + 2 : ℕ) : ℝ)) ^ (2 : ℕ)) = π ^ 2 / 6 - 1 := by
    have hfull := hasSum_zeta_two
    have hsummable2 : Summable fun n : ℕ => (1 : ℝ) / ((n : ℝ)) ^ (2 : ℕ) :=
      Real.summable_one_div_nat_pow.mpr one_lt_two
    have hsplit := hsummable2.sum_add_tsum_nat_add 2
    have hfin : (∑ n ∈ Finset.range 2, (1 : ℝ) / ((n : ℝ)) ^ (2 : ℕ)) = 1 := by norm_num
    rw [hfin] at hsplit
    have hstep : (∑' n : ℕ, (1 : ℝ) / (((n + 2 : ℕ) : ℝ)) ^ (2 : ℕ))
        = (∑' n : ℕ, (1 : ℝ) / ((n : ℝ)) ^ (2 : ℕ)) - 1 := by linarith [hsplit]
    rw [hstep, hfull.tsum_eq]
  have hpi : π ^ 2 / 6 - 1 ≤ 3 / 4 := by
    have h1 : π < 3.15 := Real.pi_lt_d2
    have h2 : 0 < π := Real.pi_pos
    nlinarith
  calc ‖∑' n : ℕ, 1 / ((n : ℂ) + 2) ^ s‖
      ≤ ∑' n : ℕ, ‖1 / ((n : ℂ) + 2) ^ s‖ := norm_tsum_le_tsum_norm hnormsummable
    _ ≤ ∑' n : ℕ, ((2 : ℝ) ^ m)⁻¹ * (1 / (((n + 2 : ℕ) : ℝ)) ^ (2 : ℕ)) :=
        hnormsummable.tsum_le_tsum hterm hcomp
    _ = ((2 : ℝ) ^ m)⁻¹ * ∑' n : ℕ, (1 : ℝ) / (((n + 2 : ℕ) : ℝ)) ^ (2 : ℕ) := tsum_mul_left
    _ = ((2 : ℝ) ^ m)⁻¹ * (π ^ 2 / 6 - 1) := by rw [hsum_eq]
    _ ≤ ((2 : ℝ) ^ m)⁻¹ * (3 / 4) := by
        exact mul_le_mul_of_nonneg_left hpi (le_of_lt (by positivity))
    _ = (3 / 4) * ((2 : ℝ) ^ m)⁻¹ := by ring

theorem norm_riemannZeta_sub_one_le_scaled {s : ℂ} {m : ℝ} (hm : 0 ≤ m) (hs : 2 + m ≤ s.re) :
    ‖riemannZeta s - 1‖ ≤ (3 / 4) * ((2 : ℝ) ^ m)⁻¹ := by
  have hs2 : (2 : ℝ) ≤ s.re := by linarith
  rw [riemannZeta_eq_one_add_zetaTail hs2]
  have h : (1 : ℂ) + (∑' n : ℕ, 1 / ((n : ℂ) + 2) ^ s) - 1
      = ∑' n : ℕ, 1 / ((n : ℂ) + 2) ^ s := by ring
  rw [h]
  exact norm_zetaTail_le_scaled hm hs

theorem norm_riemannZeta_sub_one_le_of_three_le {s : ℂ} (hs : 3 ≤ s.re) :
    ‖riemannZeta s - 1‖ ≤ 3 / 8 := by
  have h := norm_riemannZeta_sub_one_le_scaled (m := 1) (by norm_num) (by linarith)
  rwa [Real.rpow_one, show (3 / 4 : ℝ) * (2 : ℝ)⁻¹ = 3 / 8 by norm_num] at h

theorem norm_riemannZeta_sub_one_le_of_four_le {s : ℂ} (hs : 4 ≤ s.re) :
    ‖riemannZeta s - 1‖ ≤ 3 / 16 := by
  have h := norm_riemannZeta_sub_one_le_scaled (m := 2) (by norm_num) (by linarith)
  rw [Real.rpow_two] at h
  rwa [show ((2 : ℝ) ^ 2)⁻¹ = (4 : ℝ)⁻¹ by norm_num,
    show (3 / 4 : ℝ) * (4 : ℝ)⁻¹ = 3 / 16 by norm_num] at h

/-- **Cauchy's estimate for `ζ'` far to the right.** -/
theorem norm_deriv_riemannZeta_le_of_four_le {s : ℂ} (hs : 4 ≤ s.re) :
    ‖deriv riemannZeta s‖ ≤ 3 / 8 := by
  set f : ℂ → ℂ := fun w => riemannZeta w - 1 with hf
  have hre : ∀ w : ℂ, ‖w - s‖ ≤ 1 → 3 ≤ w.re := by
    intro w hw
    have h := Complex.abs_re_le_norm (w - s)
    rw [Complex.sub_re] at h
    have : |w.re - s.re| ≤ 1 := le_trans h hw
    rw [abs_le] at this
    linarith [this.1]
  have hne : ∀ w : ℂ, ‖w - s‖ ≤ 1 → w ≠ 1 := by
    intro w hw heq
    have := hre w hw
    rw [heq, Complex.one_re] at this
    norm_num at this
  have hdcc : DiffContOnCl ℂ f (ball s 1) := by
    constructor
    · intro w hw
      rw [mem_ball, Complex.dist_eq] at hw
      exact ((differentiableAt_riemannZeta (hne w hw.le)).sub_const 1).differentiableWithinAt
    · rw [closure_ball s (by norm_num : (1 : ℝ) ≠ 0)]
      intro w hw
      rw [mem_closedBall, Complex.dist_eq] at hw
      exact ((differentiableAt_riemannZeta (hne w hw)).sub_const
        1).continuousAt.continuousWithinAt
  have hC : ∀ z ∈ sphere s (1 : ℝ), ‖f z‖ ≤ 3 / 8 := by
    intro z hz
    rw [mem_sphere, Complex.dist_eq] at hz
    exact norm_riemannZeta_sub_one_le_of_three_le (hre z hz.le)
  have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by norm_num : (0 : ℝ) < 1) hdcc hC
  have hderiv : deriv f s = deriv riemannZeta s := by
    rw [hf]
    exact deriv_sub_const 1
  rw [hderiv] at h
  simpa using h

end RHTower

end
