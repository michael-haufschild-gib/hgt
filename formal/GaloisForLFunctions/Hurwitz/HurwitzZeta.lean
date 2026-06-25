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

/-- **Negative-base branch of `cpow`.** For `r > 0`, `(-r)^w = r^w · e^{iπ w}` (principal branch:
`log(-r) = log r + iπ`). With `w = -s` this is the factor `η = e^{-iπ s}` relating the negative-`j`
terms of the Hurwitz tail to the harmonic sum `H_n^{(s)}`. -/
theorem neg_real_cpow {r : ℝ} (hr : 0 < r) (w : ℂ) :
    (-(r : ℂ)) ^ w = (r : ℂ) ^ w * Complex.exp ((Real.pi : ℂ) * Complex.I * w) := by
  have hrne : (-(r : ℂ)) ≠ 0 := by
    simp only [ne_eq, neg_eq_zero, Complex.ofReal_eq_zero]; exact ne_of_gt hr
  have hrne' : (r : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]; exact ne_of_gt hr
  rw [Complex.cpow_def_of_ne_zero hrne, Complex.cpow_def_of_ne_zero hrne', ← Complex.exp_add]
  congr 1
  have harg : (-(r : ℂ)).arg = Real.pi := by
    rw [← Complex.ofReal_neg]; exact Complex.arg_ofReal_of_neg (by linarith)
  have hlog : Complex.log (-(r : ℂ)) = Complex.log (r : ℂ) + (Real.pi : ℂ) * Complex.I := by
    apply Complex.ext
    · simp [Complex.log_re, abs_of_pos hr]
    · simp [Complex.log_im, harg, Complex.arg_ofReal_of_nonneg hr.le]
  rw [hlog]; ring

/-- **Tail value at `x = 0`: `ζ(s,-n) = ζ(s) + η·H_n^{(s)}`** with `η = e^{-iπs}` and
`H_n^{(s)} = ∑_{l=1}^{n} l^{-s}`. Split `∑_m (m-n)^{-s}` at `m = n`: the `m ≥ n` tail reindexes to
`∑_m m^{-s} = ζ(s) = ζ(s,0)`, and the finite `m < n` part is `∑_{i<n}(-(i+1))^{-s} = η·∑_{i<n}(i+1)^{-s}`
via `neg_real_cpow`. This is the regular-part value `R_{n,0}(0)` the Hurwitz row descent uses (its
finite difference is `η·n^{-s}`, a non-integer power). -/
theorem hzeta_neg_nat {s : ℂ} (hs : 1 < s.re) (n : ℕ) :
    hzeta s (-(n : ℂ)) = hzeta s 0
      + Complex.exp (-((Real.pi : ℂ) * Complex.I * s))
        * ∑ l ∈ Finset.range n, ((l : ℂ) + 1) ^ (-s) := by
  have hsum : Summable (fun m : ℕ => ((m : ℂ) + (-(n : ℂ))) ^ (-s)) := summable_hurwitzSeries hs _
  rw [hzeta, ← Summable.sum_add_tsum_nat_add n hsum]
  have htail : ∑' i : ℕ, ((↑(i + n) : ℂ) + (-(n : ℂ))) ^ (-s) = hzeta s 0 := by
    rw [hzeta]; exact tsum_congr (fun i => by push_cast; ring_nf)
  have hfin : ∑ i ∈ Finset.range n, ((i : ℂ) + (-(n : ℂ))) ^ (-s)
      = Complex.exp (-((Real.pi : ℂ) * Complex.I * s))
        * ∑ l ∈ Finset.range n, ((l : ℂ) + 1) ^ (-s) := by
    rw [Finset.mul_sum, ← Finset.sum_range_reflect (fun i => ((i : ℂ) + (-(n : ℂ))) ^ (-s)) n]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    have hbase : ((↑(n - 1 - i) : ℂ) + (-(n : ℂ))) = -(((i : ℝ) + 1 : ℝ) : ℂ) := by
      rw [Nat.cast_sub (by omega : i ≤ n - 1), Nat.cast_sub (by omega : 1 ≤ n)]
      push_cast; ring
    rw [hbase, neg_real_cpow (by positivity)]
    push_cast
    ring_nf
  rw [htail, hfin, add_comm]

/-- **Finite difference of the tail value: `ζ(s,-n) - ζ(s,-(n-1)) = η·n^{-s}`** (`η = e^{-iπs}`,
`n ≥ 1`). The `H_n^{(s)}` sums telescope to the single new term `((n-1)+1)^{-s} = n^{-s}`. This is the
exact non-integer-power obstruction the N=2 Hurwitz descent uses: a finite difference of a rational
function has integral-power asymptotics and cannot equal `η·n^{-s}` for nonintegral `s`. -/
theorem hzeta_neg_nat_diff {s : ℂ} (hs : 1 < s.re) {n : ℕ} (hn : 1 ≤ n) :
    hzeta s (-(n : ℂ)) - hzeta s (-((n - 1 : ℕ) : ℂ))
      = Complex.exp (-((Real.pi : ℂ) * Complex.I * s)) * (n : ℂ) ^ (-s) := by
  rw [hzeta_neg_nat hs n, hzeta_neg_nat hs (n - 1)]
  have hsucc : Finset.range n = Finset.range ((n - 1) + 1) := by congr 1; omega
  rw [hsucc, Finset.sum_range_succ]
  have hcast : ((↑(n - 1) : ℂ) + 1) = (n : ℂ) := by
    rw [Nat.cast_sub hn]; push_cast; ring
  rw [hcast]; ring

/-- **The shifted ladder `F_k = ζ(s+k, ·)` near `a = -n`.** Since `Re(s+k) = Re s + k > 1`, the local
split applies to each shift: `ζ(s+k, -n+x) = x^{-(s+k)} + R_{n,k}(x)`. These singular terms `x^{-(s+k)}`
(`k = 0,…,N`) are the linear exponents of the Hurwitz ladder; their pairwise products give the quadratic
exponents `x^{-(2s+i+j)}` the descent's exponent filtration separates. -/
theorem hzeta_local_split_shift {s : ℂ} (hs : 1 < s.re) (k : ℕ) (n : ℕ) (x : ℂ) :
    hzeta (s + k) (-(n : ℂ) + x)
      = x ^ (-(s + k))
        + ∑' m : ℕ, (if m = n then 0 else ((m : ℂ) + (-(n : ℂ) + x)) ^ (-(s + k))) := by
  refine hzeta_local_split ?_ n x
  rw [Complex.add_re, Complex.natCast_re]
  have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  linarith

end HurwitzZetaShift
