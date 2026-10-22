import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# An elementary lower bound for zeta far to the right

On the half plane `Re s ≥ 2` the Dirichlet series of the zeta function is dominated by its first
term: the tail is bounded by the Basel tail `π²/6 − 1 < 3/4`, so the modulus of the zeta function
is at least `1/4` there.

This is the only quantitative input about `ζ` needed to invert it on a vertical line far to the
right, and it needs no zero-free region: the Euler product region is elementary.

* `zetaTail_summable`, `norm_zetaTail_le` : the tail of the Dirichlet series is at most `3/4`.
* `norm_riemannZeta_ge_of_two_le_re` : **`|ζ(s)| ≥ 1/4` for `Re s ≥ 2`.**
-/

open scoped Real
open Complex

noncomputable section

namespace RHTower

theorem zetaTail_summable {s : ℂ} (hs : 2 ≤ s.re) :
    Summable fun n : ℕ => 1 / ((n : ℂ) + 2) ^ s := by
  have hbase : Summable fun n : ℕ => 1 / ((n : ℂ)) ^ s := by
    refine (Complex.summable_one_div_nat_cpow (p := s)).mpr ?_
    linarith
  have hshift : Summable fun n : ℕ => 1 / (((n + 2 : ℕ) : ℂ)) ^ s :=
    (summable_nat_add_iff 2).mpr hbase
  refine hshift.congr fun n => ?_
  push_cast
  ring_nf

theorem norm_zetaTail_term (s : ℂ) (n : ℕ) :
    ‖1 / ((n : ℂ) + 2) ^ s‖ = 1 / ((n : ℝ) + 2) ^ s.re := by
  have hpos : (0 : ℕ) < n + 2 := by omega
  have hcast : ((n : ℂ) + 2) = (((n + 2 : ℕ) : ℕ) : ℂ) := by
    push_cast
    ring
  rw [hcast, norm_div, norm_one, Complex.norm_natCast_cpow_of_pos hpos]
  congr 1
  push_cast
  ring

theorem norm_zetaTail_le {s : ℂ} (hs : 2 ≤ s.re) :
    ‖∑' n : ℕ, 1 / ((n : ℂ) + 2) ^ s‖ ≤ 3 / 4 := by
  have hsummable := zetaTail_summable hs
  have hnormsummable : Summable fun n : ℕ => ‖1 / ((n : ℂ) + 2) ^ s‖ := by
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
      (f := fun n : ℕ => 1 / ((n : ℝ) + 2) ^ (2 : ℝ)) ?_
    · rw [norm_zetaTail_term]
      have hbase : (1 : ℝ) ≤ (n : ℝ) + 2 := by
        have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith
      refine div_le_div_of_nonneg_left one_pos.le (by positivity) ?_
      exact Real.rpow_le_rpow_of_exponent_le hbase hs
    · have h2 : Summable fun n : ℕ => (1 : ℝ) / ((n : ℝ)) ^ (2 : ℕ) :=
        Real.summable_one_div_nat_pow.mpr one_lt_two
      have hshift : Summable fun n : ℕ => (1 : ℝ) / (((n + 2 : ℕ) : ℝ)) ^ (2 : ℕ) :=
        (summable_nat_add_iff 2).mpr h2
      refine hshift.congr fun n => ?_
      rw [Real.rpow_two]
      push_cast
      ring_nf
  have hbasel := hasSum_zeta_two
  have htail : Summable fun n : ℕ => (1 : ℝ) / (((n + 2 : ℕ) : ℝ)) ^ (2 : ℕ) :=
    (summable_nat_add_iff 2).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
  have hsum_eq : (∑' n : ℕ, (1 : ℝ) / (((n + 2 : ℕ) : ℝ)) ^ (2 : ℕ)) = π ^ 2 / 6 - 1 := by
    have hfull := hbasel.tsum_eq
    have hsummable2 : Summable fun n : ℕ => (1 : ℝ) / ((n : ℝ)) ^ (2 : ℕ) :=
      Real.summable_one_div_nat_pow.mpr one_lt_two
    have hsplit := hsummable2.sum_add_tsum_nat_add 2
    have hfin : (∑ n ∈ Finset.range 2, (1 : ℝ) / ((n : ℝ)) ^ (2 : ℕ)) = 1 := by
      norm_num
    rw [hfin] at hsplit
    have : (∑' n : ℕ, (1 : ℝ) / (((n + 2 : ℕ) : ℝ)) ^ (2 : ℕ))
        = (∑' n : ℕ, (1 : ℝ) / ((n : ℝ)) ^ (2 : ℕ)) - 1 := by
      linarith [hsplit]
    rw [this, hfull]
  have hle : ∑' n : ℕ, ‖1 / ((n : ℂ) + 2) ^ s‖
      ≤ ∑' n : ℕ, (1 : ℝ) / (((n + 2 : ℕ) : ℝ)) ^ (2 : ℕ) := by
    refine hnormsummable.tsum_le_tsum (fun n => ?_) htail
    rw [norm_zetaTail_term]
    have hbase : (1 : ℝ) ≤ (n : ℝ) + 2 := by
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    have hcast : (((n + 2 : ℕ) : ℝ)) = (n : ℝ) + 2 := by push_cast; ring
    rw [hcast, ← Real.rpow_two ((n : ℝ) + 2)]
    refine div_le_div_of_nonneg_left one_pos.le (by positivity) ?_
    exact Real.rpow_le_rpow_of_exponent_le hbase hs
  have hpi : π ^ 2 / 6 - 1 ≤ 3 / 4 := by
    have h1 : π < 3.15 := Real.pi_lt_d2
    have h2 : 0 < π := Real.pi_pos
    nlinarith
  calc ‖∑' n : ℕ, 1 / ((n : ℂ) + 2) ^ s‖
      ≤ ∑' n : ℕ, ‖1 / ((n : ℂ) + 2) ^ s‖ := norm_tsum_le_tsum_norm hnormsummable
    _ ≤ ∑' n : ℕ, (1 : ℝ) / (((n + 2 : ℕ) : ℝ)) ^ (2 : ℕ) := hle
    _ = π ^ 2 / 6 - 1 := hsum_eq
    _ ≤ 3 / 4 := hpi

/-- **The zeta function is bounded below far to the right**: on `Re s ≥ 2` the first term of the
Dirichlet series dominates the tail. -/
theorem norm_riemannZeta_ge_of_two_le_re {s : ℂ} (hs : 2 ≤ s.re) :
    (1 : ℝ) / 4 ≤ ‖riemannZeta s‖ := by
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
  have hone : (1 : ℂ) / ((1 : ℕ) : ℂ) ^ s = 1 := by
    rw [Nat.cast_one, Complex.one_cpow, div_one]
  have hsplit : riemannZeta s = 1 + ∑' n : ℕ, 1 / ((n : ℂ) + 2) ^ s := by
    rw [hzeta, hsummable.tsum_eq_zero_add, hzero, zero_add]
    have hsummable' : Summable fun n : ℕ => 1 / (((n + 1 : ℕ) : ℂ)) ^ s :=
      (summable_nat_add_iff 1).mpr hsummable
    rw [hsummable'.tsum_eq_zero_add]
    have hfirst : (1 : ℂ) / (((0 + 1 : ℕ) : ℂ)) ^ s = 1 := by
      norm_num
    rw [hfirst]
    congr 1
    refine tsum_congr fun n => ?_
    congr 2
    push_cast
    ring
  have htail := norm_zetaTail_le hs
  have hge : (1 : ℝ) - 3 / 4 ≤ ‖riemannZeta s‖ := by
    rw [hsplit]
    have h := norm_sub_norm_le (1 : ℂ) (-(∑' n : ℕ, 1 / ((n : ℂ) + 2) ^ s))
    have hsub : (1 : ℂ) - -(∑' n : ℕ, 1 / ((n : ℂ) + 2) ^ s)
        = 1 + ∑' n : ℕ, 1 / ((n : ℂ) + 2) ^ s := by ring
    rw [hsub, norm_one, norm_neg] at h
    linarith
  linarith

end RHTower

end
