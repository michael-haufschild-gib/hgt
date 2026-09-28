import GaloisForLFunctions.RHTower.ChronologicalHeatMellin
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
import Mathlib.NumberTheory.ZetaValues

/-!
# The coth partial fractions of the Bose defect and its odd Taylor remainder

For `z > 0` the Mittag-Leffler expansion of `π cot(πx)` at `x = iz/(2π)` gives

  `h(z) = 1/z - 1/(e^z - 1) = 1/2 - 2z Σ_{n ≥ 1} 1/(z² + (2πn)²)`.

Expanding `1/(z² + a²)` to order `m` with its exact geometric remainder and summing with Euler's
values `Σ_{n ≥ 1} (2πn)^{-2j} = (-1)^{j+1} B_{2j}/(2 (2j)!)` gives

  `h(z) = 1/2 - Σ_{j=1}^m B_{2j} z^{2j-1}/(2j)! + R_m(z)`,
  `R_m(z) = (-1)^{m+1} 2 z^{2m+1} Σ_{n ≥ 1} 1/((2πn)^{2m} (z² + (2πn)²))`,

with `|R_m(z)| ≤ 4 z^{2m+1}/(2π)^{2m+2}` since `Σ n^{-2m-2} ≤ ζ(2) < 2`.
-/

open Complex Set Filter
open scoped Topology Nat Real
open GaloisForLFunctions.HTGeometry.ChronologicalTensor

noncomputable section

namespace RHTower

/-- `cosh(z/2)/sinh(z/2) - 2/z = 1 - 2h(z)` for `z > 0`. -/
theorem coth_half_sub_eq {z : ℝ} (hz : 0 < z) :
    Real.cosh (z / 2) / Real.sinh (z / 2) - 2 / z = 1 - 2 * fusionBoseDefect z := by
  have he : 1 < Real.exp z := Real.one_lt_exp_iff.mpr hz
  have hed : Real.exp z - 1 ≠ 0 := by linarith
  set p := Real.exp (z / 2) with hp
  set q := Real.exp (-(z / 2)) with hq
  have hsq : p * p = Real.exp z := by rw [hp, ← Real.exp_add]; ring_nf
  have hinv : q * p = 1 := by rw [hp, hq, ← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hden : p - q ≠ 0 := by
    have := Real.exp_lt_exp.mpr (show -(z / 2) < z / 2 by linarith); rw [← hp, ← hq] at this
    linarith
  have hkey : (p + q) / (p - q) = (Real.exp z + 1) / (Real.exp z - 1) := by
    rw [div_eq_div_iff hden hed]
    linear_combination (-2 * q) * hsq + (2 * p) * hinv
  rw [fusionBoseDefect, if_pos hz, Real.cosh_eq, Real.sinh_eq, ← hp, ← hq,
    div_div_div_cancel_right₀ (two_ne_zero), hkey]
  field_simp
  ring

/-- **Partial fractions of the Bose defect.** `Σ_{n ≥ 1} 2z/(z² + (2πn)²) = 1/2 - h(z)`. -/
theorem hasSum_bose_partial_fraction {z : ℝ} (hz : 0 < z) :
    HasSum (fun n : ℕ => 2 * z / (z ^ 2 + (2 * π * (n + 1)) ^ 2)) (1 / 2 - fusionBoseDefect z) := by
  have hpi : 0 < π := Real.pi_pos
  set c : ℝ := z / (2 * π) with hc
  have hc0 : 0 < c := by positivity
  set x : ℂ := (c : ℂ) * I with hx
  have hxre : x.re = 0 := by simp [hx]
  have hxim : x.im = c := by simp [hx]
  have hxmem : x ∈ Complex.integerComplement := by
    rintro ⟨n, hn⟩
    have := congrArg Complex.im hn
    rw [Complex.intCast_im, hxim] at this
    linarith
  have hsum := (summable_cotTerm hxmem).hasSum
  rw [← cot_series_rep' hxmem] at hsum
  have him := Complex.imCLM.hasSum hsum
  simp only [Complex.imCLM_apply] at him
  -- the terms
  have hterm : ∀ n : ℕ, (cotTerm x n).im = -(4 * π) * (z / (z ^ 2 + (2 * π * (n + 1)) ^ 2)) := by
    intro n
    have hw0 : (0 : ℝ) < n + 1 := by positivity
    have hn1 : Complex.normSq (x - ((n : ℂ) + 1)) = (n + 1) ^ 2 + c ^ 2 := by
      rw [Complex.normSq_apply]; simp [hxre, hxim]; ring
    have hn2 : Complex.normSq (x + ((n : ℂ) + 1)) = (n + 1) ^ 2 + c ^ 2 := by
      rw [Complex.normSq_apply]; simp [hxre, hxim]; ring
    have him1 : (x - ((n : ℂ) + 1)).im = c := by simp [hxim]
    have him2 : (x + ((n : ℂ) + 1)).im = c := by simp [hxim]
    rw [cotTerm, Complex.add_im, one_div, one_div, Complex.inv_im, Complex.inv_im, hn1, hn2,
      him1, him2, hc]
    have hd : ((n : ℝ) + 1) ^ 2 + (z / (2 * π)) ^ 2 ≠ 0 := by positivity
    have hd' : z ^ 2 + (2 * π * (n + 1)) ^ 2 ≠ 0 := by positivity
    field_simp
    ring
  -- the value
  have hval : (π * (π * x).cot - 1 / x).im = -π * (1 - 2 * fusionBoseDefect z) := by
    have hpx : (π : ℂ) * x = ((z / 2 : ℝ) : ℂ) * I := by
      rw [hx, hc]; push_cast; field_simp
    have hs : Real.sinh (z / 2) ≠ 0 := (Real.sinh_pos_iff.mpr (by positivity)).ne'
    have e1 : (π * x).cot = ((Real.cosh (z / 2) / Real.sinh (z / 2) : ℝ) : ℂ) * (-I) := by
      rw [hpx, Complex.cot_eq_cos_div_sin, Complex.cos_mul_I, Complex.sin_mul_I,
        ← Complex.ofReal_cosh, ← Complex.ofReal_sinh, div_mul_eq_div_div, div_eq_mul_inv _ I,
        Complex.inv_I, Complex.ofReal_div]
    have e2 : 1 / x = ((1 / c : ℝ) : ℂ) * (-I) := by
      rw [hx, one_div, mul_inv, Complex.inv_I, ← Complex.ofReal_inv, one_div]
    rw [e1, e2, ← coth_half_sub_eq hz]
    simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im, Complex.mul_re]
    rw [hc]
    field_simp
    ring
  simp only [hterm, hval] at him
  have H := him.mul_left (-(1 / (2 * π)))
  have hf : (fun n : ℕ => -(1 / (2 * π)) * (-(4 * π) * (z / (z ^ 2 + (2 * π * (n + 1)) ^ 2)))) =
      fun n : ℕ => 2 * z / (z ^ 2 + (2 * π * (n + 1)) ^ 2) := by
    funext n
    have hd' : z ^ 2 + (2 * π * (n + 1)) ^ 2 ≠ 0 := by positivity
    field_simp
    ring
  have hv : -(1 / (2 * π)) * (-π * (1 - 2 * fusionBoseDefect z)) = 1 / 2 - fusionBoseDefect z := by
    field_simp
  rw [hf, hv] at H
  exact H

/-! ### The exact odd Taylor remainder -/

/-- The odd Taylor remainder of order `m`:
`R_m(z) = (-1)^{m+1} 2 z^{2m+1} Σ_{n ≥ 1} 1/((2πn)^{2m} (z² + (2πn)²))`. -/
def boseRemainder (m : ℕ) (z : ℝ) : ℝ :=
  (-1) ^ (m + 1) * 2 * z ^ (2 * m + 1) *
    ∑' n : ℕ, 1 / ((2 * π * (n + 1)) ^ (2 * m) * (z ^ 2 + (2 * π * (n + 1)) ^ 2))

/-- The finite geometric expansion `1/(z² + a²) = Σ_{j<m} (-1)^j z^{2j}/a^{2j+2} + (-1)^m z^{2m}/(a^{2m}(z² + a²))`. -/
theorem inv_sq_add_sq_expansion {a : ℝ} (ha : a ≠ 0) (z : ℝ) (m : ℕ) :
    1 / (z ^ 2 + a ^ 2) = ∑ j ∈ Finset.range m, (-1) ^ j * z ^ (2 * j) / a ^ (2 * j + 2) +
      (-1) ^ m * z ^ (2 * m) / (a ^ (2 * m) * (z ^ 2 + a ^ 2)) := by
  have hden : z ^ 2 + a ^ 2 ≠ 0 := by positivity
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    field_simp
    ring

/-- `Σ_{n ≥ 1} (2πn)^{-2k} = (-1)^{k+1} B_{2k}/(2 (2k)!)`. -/
theorem hasSum_inv_two_pi_mul_pow {k : ℕ} (hk : k ≠ 0) :
    HasSum (fun n : ℕ => 1 / (2 * π * (n + 1)) ^ (2 * k))
      ((-1) ^ (k + 1) * (bernoulli (2 * k) : ℝ) / (2 * (2 * k)!)) := by
  have h := (hasSum_nat_add_iff' 1).mpr (hasSum_zeta_nat hk)
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, zero_pow (by omega : 2 * k ≠ 0),
    div_zero, sub_zero, Nat.cast_add, Nat.cast_one] at h
  have h2 := h.mul_left (1 / (2 * π) ^ (2 * k))
  have hf : (fun i : ℕ => 1 / (2 * π) ^ (2 * k) * (1 / ((i : ℝ) + 1) ^ (2 * k))) =
      fun n : ℕ => 1 / (2 * π * (n + 1)) ^ (2 * k) := by
    funext n; rw [mul_pow (2 * π), one_div_mul_one_div]
  have hv : 1 / (2 * π) ^ (2 * k) * ((-1) ^ (k + 1) * 2 ^ (2 * k - 1) * π ^ (2 * k) *
      (bernoulli (2 * k) : ℝ) / (2 * k)!) =
      (-1) ^ (k + 1) * (bernoulli (2 * k) : ℝ) / (2 * (2 * k)!) := by
    have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
    have h2 : (2 : ℝ) ^ (2 * k) = 2 * 2 ^ (2 * k - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [mul_pow, h2]
    field_simp
  rw [hf, hv] at h2
  exact h2

theorem summable_bose_remainder_terms (m : ℕ) (z : ℝ) :
    Summable fun n : ℕ => 1 / ((2 * π * (n + 1)) ^ (2 * m) * (z ^ 2 + (2 * π * (n + 1)) ^ 2)) := by
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    (hasSum_inv_two_pi_mul_pow (k := m + 1) (by omega)).summable
  have hpos : 0 < (2 * π * (n + 1)) := by positivity
  rw [show 2 * (m + 1) = 2 * m + 2 by ring, pow_add]
  exact one_div_le_one_div_of_le (by positivity)
    (mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg z]) (by positivity))

/-- **The exact odd Taylor expansion of the Bose defect.**  For `z > 0` and every `m`,
`h(z) = 1/2 - Σ_{j=1}^m B_{2j} z^{2j-1}/(2j)! + R_m(z)`. -/
theorem fusionBoseDefect_eq_taylor_add_remainder {z : ℝ} (hz : 0 < z) (m : ℕ) :
    fusionBoseDefect z = 1 / 2 - ∑ j ∈ Finset.range m,
      (bernoulli (2 * (j + 1)) : ℝ) * z ^ (2 * j + 1) / (2 * (j + 1))! +
      boseRemainder m z := by
  set a : ℕ → ℝ := fun n => 2 * π * (n + 1) with ha
  have ha0 : ∀ n, a n ≠ 0 := fun n => by positivity
  -- termwise expansion of the partial-fraction terms
  have hterm : ∀ n : ℕ, 2 * z / (z ^ 2 + a n ^ 2) =
      ∑ j ∈ Finset.range m, 2 * (-1) ^ j * z ^ (2 * j + 1) * (1 / a n ^ (2 * (j + 1))) +
        2 * (-1) ^ m * z ^ (2 * m + 1) * (1 / (a n ^ (2 * m) * (z ^ 2 + a n ^ 2))) := by
    intro n
    calc 2 * z / (z ^ 2 + a n ^ 2) = 2 * z * (1 / (z ^ 2 + a n ^ 2)) := by ring
      _ = 2 * z * (∑ j ∈ Finset.range m, (-1) ^ j * z ^ (2 * j) / a n ^ (2 * j + 2) +
          (-1) ^ m * z ^ (2 * m) / (a n ^ (2 * m) * (z ^ 2 + a n ^ 2))) := by
          rw [inv_sq_add_sq_expansion (ha0 n) z m]
      _ = _ := by
          rw [mul_add, Finset.mul_sum]
          congr 1
          · refine Finset.sum_congr rfl fun j _ => ?_
            rw [show 2 * (j + 1) = 2 * j + 2 by ring]
            ring
          · ring
  have hfin : HasSum (fun n : ℕ => ∑ j ∈ Finset.range m,
      2 * (-1) ^ j * z ^ (2 * j + 1) * (1 / a n ^ (2 * (j + 1))))
      (∑ j ∈ Finset.range m, 2 * (-1) ^ j * z ^ (2 * j + 1) *
        ((-1) ^ (j + 1 + 1) * (bernoulli (2 * (j + 1)) : ℝ) / (2 * (2 * (j + 1))!))) :=
    hasSum_sum fun j _ => (hasSum_inv_two_pi_mul_pow (k := j + 1) (by omega)).mul_left _
  have hrem := (summable_bose_remainder_terms m z).hasSum.mul_left (2 * (-1) ^ m * z ^ (2 * m + 1))
  have htot := hfin.add hrem
  have hpf := hasSum_bose_partial_fraction hz
  rw [show (fun n : ℕ => 2 * z / (z ^ 2 + (2 * π * (n + 1)) ^ 2)) =
      fun n => 2 * z / (z ^ 2 + a n ^ 2) from rfl] at hpf
  simp only [hterm] at hpf
  have huniq := hpf.unique htot
  have hcoef : ∀ j : ℕ, 2 * (-1) ^ j * z ^ (2 * j + 1) *
      ((-1) ^ (j + 1 + 1) * (bernoulli (2 * (j + 1)) : ℝ) / (2 * (2 * (j + 1))!)) =
      (bernoulli (2 * (j + 1)) : ℝ) * z ^ (2 * j + 1) / (2 * (j + 1))! := by
    intro j
    have hf : ((2 * (j + 1))! : ℝ) ≠ 0 := by positivity
    have hs : ((-1 : ℝ)) ^ j * (-1) ^ (j + 1 + 1) = 1 := by
      rw [← pow_add, show j + (j + 1 + 1) = 2 * (j + 1) by ring, pow_mul]; norm_num
    calc 2 * (-1) ^ j * z ^ (2 * j + 1) *
          ((-1) ^ (j + 1 + 1) * (bernoulli (2 * (j + 1)) : ℝ) / (2 * (2 * (j + 1))!))
        = ((-1 : ℝ) ^ j * (-1) ^ (j + 1 + 1)) *
            ((bernoulli (2 * (j + 1)) : ℝ) * z ^ (2 * j + 1) / (2 * (j + 1))!) := by
          field_simp
      _ = _ := by rw [hs, one_mul]
  simp only [hcoef] at huniq
  have hm : ((-1 : ℝ)) ^ (m + 1) = -(-1) ^ m := by rw [pow_succ]; ring
  rw [boseRemainder, hm]
  linarith [huniq]

/-- **The remainder bound.** `|R_m(z)| ≤ 4 z^{2m+1}/(2π)^{2m+2}` for `z ≥ 0`. -/
theorem abs_boseRemainder_le (m : ℕ) {z : ℝ} (hz : 0 ≤ z) :
    |boseRemainder m z| ≤ 4 * z ^ (2 * m + 1) / (2 * π) ^ (2 * m + 2) := by
  have hS := summable_bose_remainder_terms m z
  have hZ := hasSum_inv_two_pi_mul_pow (k := m + 1) (by omega)
  have hle : ∑' n : ℕ, 1 / ((2 * π * (n + 1)) ^ (2 * m) * (z ^ 2 + (2 * π * (n + 1)) ^ 2)) ≤
      ∑' n : ℕ, 1 / (2 * π * (n + 1)) ^ (2 * (m + 1)) := by
    refine hS.tsum_le_tsum (fun n => ?_) hZ.summable
    rw [show 2 * (m + 1) = 2 * m + 2 by ring, pow_add]
    exact one_div_le_one_div_of_le (by positivity)
      (mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg z]) (by positivity))
  -- `Σ_{n ≥ 1} n^{-2m-2} ≤ ζ(2) < 2`
  have hzeta : ∑' n : ℕ, 1 / (2 * π * (n + 1)) ^ (2 * (m + 1)) ≤ 2 / (2 * π) ^ (2 * m + 2) := by
    have h2 := (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two
    simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, zero_pow two_ne_zero,
      div_zero, sub_zero, Nat.cast_add, Nat.cast_one] at h2
    have hcmp : ∀ n : ℕ, 1 / (2 * π * (n + 1)) ^ (2 * (m + 1)) ≤
        (1 / (2 * π) ^ (2 * m + 2)) * (1 / ((n : ℝ) + 1) ^ 2) := by
      intro n
      have hn1 : (1 : ℝ) ≤ n + 1 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      rw [show 2 * (m + 1) = 2 * m + 2 by ring, mul_pow, one_div_mul_one_div]
      exact one_div_le_one_div_of_le (by positivity)
        (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hn1 (by omega)) (by positivity))
    refine (hZ.summable.tsum_le_tsum hcmp ((h2.mul_left _).summable)).trans ?_
    rw [(h2.mul_left _).tsum_eq]
    have hpi2 : π ^ 2 / 6 ≤ 2 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
    calc 1 / (2 * π) ^ (2 * m + 2) * (π ^ 2 / 6) ≤ 1 / (2 * π) ^ (2 * m + 2) * 2 :=
          mul_le_mul_of_nonneg_left hpi2 (by positivity)
      _ = 2 / (2 * π) ^ (2 * m + 2) := by ring
  have hnn : 0 ≤ ∑' n : ℕ, 1 / ((2 * π * (n + 1)) ^ (2 * m) * (z ^ 2 + (2 * π * (n + 1)) ^ 2)) :=
    tsum_nonneg fun n => by positivity
  rw [boseRemainder, abs_mul, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_two, abs_of_nonneg (pow_nonneg hz _), abs_of_nonneg hnn]
  calc 2 * z ^ (2 * m + 1) * ∑' n : ℕ, 1 / ((2 * π * (n + 1)) ^ (2 * m) *
        (z ^ 2 + (2 * π * (n + 1)) ^ 2))
      ≤ 2 * z ^ (2 * m + 1) * (2 / (2 * π) ^ (2 * m + 2)) :=
        mul_le_mul_of_nonneg_left (hle.trans hzeta) (by positivity)
    _ = 4 * z ^ (2 * m + 1) / (2 * π) ^ (2 * m + 2) := by ring

/-- **The cosh/sinh decomposition of a moment-matched residual.**  If `Σ a_k = -2` and
`Σ a_k k^{2j-1} = -2j/B_{2j}` for `1 ≤ j ≤ m`, then for `t > 0`
`r_N(t) = cosh t - 1 - [sinh t - Σ_{j=1}^m t^{2j-1}/(2j-1)!] + Σ_k a_k R_m(kt)`. -/
theorem heatError_eq_cosh_sinh_remainder {a : ℕ → ℝ} {N m : ℕ}
    (hsum : ∑ k ∈ Finset.Ioc 0 N, a k = -2)
    (hodd : ∀ j < m, ∑ k ∈ Finset.Ioc 0 N, a k * (k : ℝ) ^ (2 * j + 1) =
      -(2 * (j + 1)) / (bernoulli (2 * (j + 1)) : ℝ))
    (hB : ∀ j < m, (bernoulli (2 * (j + 1)) : ℝ) ≠ 0) {t : ℝ} (ht : 0 < t) :
    chronologicalHeatError a N t = Real.cosh t - 1 -
      (Real.sinh t - ∑ j ∈ Finset.range m, t ^ (2 * j + 1) / (2 * j + 1)!) +
      ∑ k ∈ Finset.Ioc 0 N, a k * boseRemainder m (k * t) := by
  have hexp : ∀ k ∈ Finset.Ioc 0 N, a k * fusionBoseDefect (k * t) =
      a k / 2 - ∑ j ∈ Finset.range m, (bernoulli (2 * (j + 1)) : ℝ) * t ^ (2 * j + 1) /
        (2 * (j + 1))! * (a k * (k : ℝ) ^ (2 * j + 1)) + a k * boseRemainder m (k * t) := by
    intro k hk
    have hk0 : (0 : ℝ) < k := by exact_mod_cast (Finset.mem_Ioc.mp hk).1
    have hs : ∑ j ∈ Finset.range m, a k * ((bernoulli (2 * (j + 1)) : ℝ) * (k * t) ^ (2 * j + 1) /
        (2 * (j + 1))!) = ∑ j ∈ Finset.range m, (bernoulli (2 * (j + 1)) : ℝ) * t ^ (2 * j + 1) /
        (2 * (j + 1))! * (a k * (k : ℝ) ^ (2 * j + 1)) :=
      Finset.sum_congr rfl fun j _ => by rw [mul_pow]; ring
    rw [fusionBoseDefect_eq_taylor_add_remainder (mul_pos hk0 ht) m, mul_add, mul_sub,
      Finset.mul_sum, hs]
    ring
  rw [chronologicalHeatError, Finset.sum_congr rfl hexp, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ← Finset.sum_div, hsum, Finset.sum_comm, ← Real.cosh_sub_sinh]
  have hj : ∀ j ∈ Finset.range m, ∑ k ∈ Finset.Ioc 0 N, (bernoulli (2 * (j + 1)) : ℝ) *
      t ^ (2 * j + 1) / (2 * (j + 1))! * (a k * (k : ℝ) ^ (2 * j + 1)) =
      -(t ^ (2 * j + 1) / (2 * j + 1)!) := by
    intro j hjm
    rw [← Finset.mul_sum, hodd j (Finset.mem_range.mp hjm)]
    have hBj := hB j (Finset.mem_range.mp hjm)
    have hfac : ((2 * (j + 1))! : ℝ) = (2 * (j + 1) : ℕ) * (2 * j + 1)! := by
      rw [show 2 * (j + 1) = (2 * j + 1) + 1 by ring, Nat.factorial_succ]; push_cast; ring
    rw [hfac]
    have hf1 : ((2 * j + 1)! : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp
  rw [Finset.sum_congr rfl hj, Finset.sum_neg_distrib]
  ring

end RHTower
