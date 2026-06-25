/-
# Hurwitz zeta as a function of the (complex) shift, and its local expansion

mathlib's `hurwitzZeta` carries the shift in `UnitAddCircle` (for Dirichlet L-functions); the Hurwitz
quadratic descent instead needs `ζ(s,a) = ∑_{m≥0} (m+a)^{-s}` as a function of the **complex** variable
`a`, with its singular expansion `ζ(s+k, -n+x) = x^{-s-k} + R_{n,k}(x)` near `a = -n`. This file builds
that object from the convergent series (`Re s > 1`), starting with summability.

* `summable_hurwitzSeries` — `∑_m (m+a)^{-s}` converges for `Re s > 1`, by comparison with the real
  `p`-series. The bound: `‖z^{-s}‖ ≤ ‖z‖^{-Re s} · e^{arg z · Im s}` (`Complex.norm_cpow_le`); the `arg`
  factor is `≤ e^{π|Im s|}`, and for `m` past `2‖a‖` the base `‖(m:ℂ)+a‖ ≥ (m+M) - ‖a‖ ≥ (m+M)/2`.
-/
import Mathlib

open Complex Filter

namespace HurwitzZetaShift

/-- **Summability of the Hurwitz series in the complex shift.** For `Re s > 1` and any `a`, the family
`m ↦ (m+a)^{-s}` is summable. -/
theorem summable_hurwitzSeries {s : ℂ} (hs : 1 < s.re) (a : ℂ) :
    Summable (fun m : ℕ => ((m : ℂ) + a) ^ (-s)) := by
  obtain ⟨M, hM⟩ := exists_nat_gt (2 * ‖a‖)
  rw [← summable_nat_add_iff M]
  set C : ℝ := Real.exp (Real.pi * |s.im|) with hCdef
  have hsne : -s.re ≤ 0 := by linarith
  -- comparison `p`-series summable
  have hpser : Summable (fun n : ℕ => (n : ℝ) ^ (-s.re)) := by
    have h := (Real.summable_nat_rpow_inv (p := s.re)).mpr hs
    exact h.congr (fun n => by rw [Real.rpow_neg (Nat.cast_nonneg n)])
  have hshift : Summable (fun m : ℕ => ((m : ℝ) + M) ^ (-s.re)) := by
    have h := (summable_nat_add_iff M).mpr hpser
    exact h.congr (fun m => by push_cast; ring_nf)
  refine Summable.of_norm_bounded (g := fun m : ℕ => C * (((m : ℝ) + M) / 2) ^ (-s.re)) ?_ ?_
  · -- summability of the comparison function
    have heq : (fun m : ℕ => C * (((m : ℝ) + M) / 2) ^ (-s.re))
        = fun m : ℕ => (C * (2 : ℝ) ^ s.re) * ((m : ℝ) + M) ^ (-s.re) := by
      funext m
      have hb : (0 : ℝ) ≤ ((m : ℝ) + M) := by positivity
      rw [Real.div_rpow hb (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
        div_eq_mul_inv, inv_inv]
      ring
    rw [heq]; exact hshift.mul_left _
  · -- the norm bound
    intro m
    have hbasepos : (0 : ℝ) < ((m : ℝ) + M) / 2 := by
      have : (0 : ℝ) < (M : ℝ) := lt_of_le_of_lt (by positivity) hM
      have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      positivity
    set z : ℂ := (↑(m + M) : ℂ) + a with hzdef
    have hmM : ((m : ℝ) + M) / 2 ≤ ‖z‖ := by
      have hge : ‖(↑(m + M) : ℂ)‖ - ‖a‖ ≤ ‖z‖ := by
        have h := norm_add_le z (-a)
        simp only [hzdef, add_neg_cancel_right, norm_neg] at h
        linarith
      rw [Complex.norm_natCast] at hge
      push_cast at hge
      have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      have hM' : 2 * ‖a‖ < (M : ℝ) := hM
      nlinarith [norm_nonneg a]
    calc ‖z ^ (-s)‖
        ≤ ‖z‖ ^ (-s).re / Real.exp (z.arg * (-s).im) := Complex.norm_cpow_le z (-s)
      _ = ‖z‖ ^ (-s.re) * Real.exp (z.arg * s.im) := by
          rw [Complex.neg_re, Complex.neg_im, div_eq_mul_inv]
          congr 1
          rw [show z.arg * -s.im = -(z.arg * s.im) from by ring, Real.exp_neg, inv_inv]
      _ ≤ (((m : ℝ) + M) / 2) ^ (-s.re) * Real.exp (Real.pi * |s.im|) := by
          refine mul_le_mul (Real.rpow_le_rpow_of_nonpos hbasepos hmM hsne)
            (Real.exp_le_exp.mpr ?_) (Real.exp_nonneg _) (Real.rpow_nonneg hbasepos.le _)
          calc z.arg * s.im ≤ |z.arg * s.im| := le_abs_self _
            _ = |z.arg| * |s.im| := abs_mul _ _
            _ ≤ Real.pi * |s.im| := by
                apply mul_le_mul_of_nonneg_right (Complex.abs_arg_le_pi z) (abs_nonneg _)
      _ = C * (((m : ℝ) + M) / 2) ^ (-s.re) := by rw [hCdef]; ring

/-- **Hurwitz zeta in the complex shift:** `ζ(s,a) = ∑_{m≥0} (m+a)^{-s}` (the convergent series form,
`Re s > 1`). -/
noncomputable def hzeta (s a : ℂ) : ℂ := ∑' m : ℕ, ((m : ℂ) + a) ^ (-s)

/-- **Split off the `m = n` term.** For `Re s > 1`, `ζ(s,a) = (n+a)^{-s} + ∑_{m≠n}(m+a)^{-s}`. -/
theorem hzeta_split {s : ℂ} (hs : 1 < s.re) (a : ℂ) (n : ℕ) :
    hzeta s a = ((n : ℂ) + a) ^ (-s)
      + ∑' m : ℕ, (if m = n then 0 else ((m : ℂ) + a) ^ (-s)) := by
  classical
  exact (summable_hurwitzSeries hs a).tsum_eq_add_tsum_ite n

/-- **Local singular split near `a = -n`.** Writing `a = -n + x`, the `m = n` term is the singular
`x^{-s}` and the remaining tail `R_{n}(x) = ∑_{m≠n}(m-n+x)^{-s}` is the regular part:
`ζ(s, -n+x) = x^{-s} + R_n(x)`. This is the local expansion the Hurwitz quadratic descent feeds to the
exponent filtration (singular `x^{-s-k}`) and the row descent (regular tail). -/
theorem hzeta_local_split {s : ℂ} (hs : 1 < s.re) (n : ℕ) (x : ℂ) :
    hzeta s (-(n : ℂ) + x)
      = x ^ (-s) + ∑' m : ℕ, (if m = n then 0 else ((m : ℂ) + (-(n : ℂ) + x)) ^ (-s)) := by
  rw [hzeta_split hs (-(n : ℂ) + x) n, show ((n : ℂ) + (-(n : ℂ) + x)) = x from by ring]

end HurwitzZetaShift
