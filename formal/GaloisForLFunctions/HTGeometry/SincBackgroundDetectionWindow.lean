import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.LinearCombination

/-!
# Detection window of an off-line pair against a dense critical background

Let `L > 0` and `δ > 0`, and let

  `f(z) = (z² + δ²) · sin(Lz/2)/(Lz/2)`:

real zeros at `2πk/L` (`k ≠ 0`, density `L/2π`) and the non-real pair `±iδ` at the ordinate `0`.
Its slice at the ordinate is (`sincPairSlice_eq`)

  `f(ix) f(−ix) = (δ² − x²)² (sinh(Lx/2)/(Lx/2))² = Σ_m c_m x^{2m}`   (`hasSum_sincSliceCoeff`),

with `(sinh(Lx/2)/(Lx/2))² = Σ_m b_m x^{2m}`, `b_m = 2L^{2m}/(2m+2)!` (`hasSum_sincSqCoeff`) and
`c_m = δ⁴ b_m − 2δ² b_{m−1} + b_{m−2}`.

**Sign law** (`sincSliceCoeff_neg_iff`).  For `m ≥ 2`, with `P = (2m+1)(2m+2)`,

  `c_m < 0  ⟺  ((δL)² − P)² < P (8m + 2)`.

So the negative coefficients are those with `|m − δL/2| ≲ √(δL)/2`.  The order `m` with
`(2m+1)(2m+2) ≤ (δL)² < (2m+3)(2m+4)` is negative once `m ≥ 3` (`sincSliceCoeff_neg_of_mem`), and every
order with `2m + 2 + √(2m+2) ≤ δL` is nonnegative (`sincSliceCoeff_nonneg_of_le`).

**Window–abscissa reading.**  At height `t` the zeros of `ξ` have local density `L/2π` with
`L = log(t/2π)`.  An off-line zero at `Re ρ = ½ + δ` against such a background is detected at
`y`-order `≈ δL/2`.  The edge of the critical strip, `δ = ½`, gives `L/4`: the quarter-log window
`c_{2k}(t) > 0` for `k ≥ (¼ + ε) log t` is the detection order of a zero on `Re s = 1`.  Lowering the
window to `(¼ − η) log t` would leave a model zero at `Re s = 1 − 2η` undetected.
-/

open Real

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The coefficients of `(sinh(Lx/2)/(Lx/2))²` in `y = x²`. -/
def sincSqCoeff (L : ℝ) (m : ℕ) : ℝ :=
  2 * L ^ (2 * m) / ((2 * m + 2).factorial : ℝ)

theorem hasSum_sincSqCoeff (L x : ℝ) (hx : L * x ≠ 0) :
    HasSum (fun m => sincSqCoeff L m * (x ^ 2) ^ m) ((Real.sinh (L * x / 2) / (L * x / 2)) ^ 2) := by
  set u := L * x / 2 with hu
  have hu0 : u ≠ 0 := by rw [hu]; exact div_ne_zero hx two_ne_zero
  have hL : L ≠ 0 := left_ne_zero_of_mul hx
  have hx0 : x ≠ 0 := right_ne_zero_of_mul hx
  have h := Real.hasSum_cosh (2 * u)
  rw [← hasSum_nat_add_iff' 1] at h
  simp only [Finset.range_one, Finset.sum_singleton, mul_zero, pow_zero, Nat.factorial_zero,
    Nat.cast_one, div_one] at h
  have h2 := h.mul_left (1 / (2 * u ^ 2))
  have efun : (fun m => sincSqCoeff L m * (x ^ 2) ^ m) =
      fun i => 1 / (2 * u ^ 2) * ((2 * u) ^ (2 * (i + 1)) / ((2 * (i + 1)).factorial : ℝ)) := by
    funext m
    rw [sincSqCoeff, hu, show 2 * (m + 1) = 2 * m + 2 by ring]
    field_simp
    ring
  have eval : (Real.sinh u / u) ^ 2 = 1 / (2 * u ^ 2) * (Real.cosh (2 * u) - 1) := by
    rw [Real.cosh_two_mul, Real.cosh_sq]
    field_simp
    ring
  rw [efun, eval]
  exact h2

/-- The slice coefficients of `(z² + δ²) sin(Lz/2)/(Lz/2)` at the ordinate, in `y = x²`. -/
def sincSliceCoeff (L δ : ℝ) : ℕ → ℝ
  | 0 => δ ^ 4 * sincSqCoeff L 0
  | 1 => δ ^ 4 * sincSqCoeff L 1 - 2 * δ ^ 2 * sincSqCoeff L 0
  | m + 2 => δ ^ 4 * sincSqCoeff L (m + 2) - 2 * δ ^ 2 * sincSqCoeff L (m + 1) + sincSqCoeff L m

theorem hasSum_sincSliceCoeff (L δ x : ℝ) (hx : L * x ≠ 0) :
    HasSum (fun m => sincSliceCoeff L δ m * (x ^ 2) ^ m)
      ((δ ^ 2 - x ^ 2) ^ 2 * (Real.sinh (L * x / 2) / (L * x / 2)) ^ 2) := by
  have h0 := hasSum_sincSqCoeff L x hx
  have h1 := (hasSum_nat_add_iff' 1).mpr h0
  have h2 := (hasSum_nat_add_iff' 2).mpr h0
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add] at h1 h2
  rw [← hasSum_nat_add_iff' 2]
  have hsum := ((h2.mul_left (δ ^ 4)).add (h1.mul_left (-2 * δ ^ 2 * x ^ 2))).add
    (h0.mul_left ((x ^ 2) ^ 2))
  have efun : (fun n => sincSliceCoeff L δ (n + 2) * (x ^ 2) ^ (n + 2)) =
      fun n => δ ^ 4 * (sincSqCoeff L (n + 2) * (x ^ 2) ^ (n + 2)) +
        -2 * δ ^ 2 * x ^ 2 * (sincSqCoeff L (n + 1) * (x ^ 2) ^ (n + 1)) +
          (x ^ 2) ^ 2 * (sincSqCoeff L n * (x ^ 2) ^ n) := by
    funext n
    simp only [sincSliceCoeff]
    ring
  have hval : (δ ^ 2 - x ^ 2) ^ 2 * (Real.sinh (L * x / 2) / (L * x / 2)) ^ 2 -
      ∑ i ∈ Finset.range 2, sincSliceCoeff L δ i * (x ^ 2) ^ i =
      δ ^ 4 * ((Real.sinh (L * x / 2) / (L * x / 2)) ^ 2 -
          (sincSqCoeff L 0 * (x ^ 2) ^ 0 + sincSqCoeff L 1 * (x ^ 2) ^ 1)) +
        -2 * δ ^ 2 * x ^ 2 * ((Real.sinh (L * x / 2) / (L * x / 2)) ^ 2 -
          sincSqCoeff L 0 * (x ^ 2) ^ 0) +
        (x ^ 2) ^ 2 * (Real.sinh (L * x / 2) / (L * x / 2)) ^ 2 := by
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add, sincSliceCoeff]
    ring
  rw [efun, hval]
  exact hsum

/-- The closed form `c_{m+2} = 2L^{2m}/(2m+6)! · (((δL)² − P)² − P(8m + 18))`,
`P = (2m+5)(2m+6)`. -/
theorem sincSliceCoeff_add_two_eq (L δ : ℝ) (m : ℕ) :
    sincSliceCoeff L δ (m + 2) = 2 * L ^ (2 * m) / ((2 * m + 6).factorial : ℝ) *
      (((δ * L) ^ 2 - (2 * (m : ℝ) + 5) * (2 * m + 6)) ^ 2 -
        (2 * (m : ℝ) + 5) * (2 * m + 6) * (8 * m + 18)) := by
  simp only [sincSliceCoeff, sincSqCoeff]
  rw [show 2 * (m + 2) + 2 = (2 * m + 5) + 1 by ring, show 2 * (m + 1) + 2 = (2 * m + 3) + 1 by ring,
    show 2 * m + 6 = (2 * m + 5) + 1 by ring, show 2 * (m + 2) = 2 * m + 4 by ring,
    show 2 * (m + 1) = 2 * m + 2 by ring]
  rw [Nat.factorial_succ (2 * m + 5), show 2 * m + 5 = (2 * m + 4) + 1 by ring,
    Nat.factorial_succ (2 * m + 4), show 2 * m + 4 = (2 * m + 3) + 1 by ring,
    Nat.factorial_succ (2 * m + 3), show 2 * m + 3 = (2 * m + 2) + 1 by ring,
    Nat.factorial_succ (2 * m + 2)]
  have hf : ((2 * m + 2).factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  push_cast
  field_simp
  ring

/-- **Sign law.**  For `m ≥ 2` and `P = (2m+1)(2m+2)`: `c_m < 0 ⟺ ((δL)² − P)² < P(8m + 2)`. -/
theorem sincSliceCoeff_neg_iff (L δ : ℝ) (hL : L ≠ 0) {m : ℕ} (hm : 2 ≤ m) :
    sincSliceCoeff L δ m < 0 ↔
      ((δ * L) ^ 2 - (2 * (m : ℝ) + 1) * (2 * m + 2)) ^ 2 <
        (2 * (m : ℝ) + 1) * (2 * m + 2) * (8 * m + 2) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  rw [sincSliceCoeff_add_two_eq]
  have hpos : 0 < 2 * L ^ (2 * k) / ((2 * k + 6).factorial : ℝ) := by
    have : 0 < L ^ (2 * k) := by
      rw [pow_mul]
      exact pow_pos (by positivity) k
    positivity
  have e5 : (2 * ((k + 2 : ℕ) : ℝ) + 1) = 2 * (k : ℝ) + 5 := by push_cast; ring
  have e6 : (2 * ((k + 2 : ℕ) : ℝ) + 2) = 2 * (k : ℝ) + 6 := by push_cast; ring
  have e8 : (8 * ((k + 2 : ℕ) : ℝ) + 2) = 8 * (k : ℝ) + 18 := by push_cast; ring
  rw [e5, e6, e8]
  constructor
  · intro h
    by_contra hc
    push Not at hc
    have := mul_nonneg hpos.le (sub_nonneg.mpr hc)
    linarith
  · intro h
    exact mul_neg_of_pos_of_neg hpos (sub_neg.mpr h)

/-- **Location of the detection.**  For `m ≥ 3`, if `(2m+1)(2m+2) ≤ (δL)² < (2m+3)(2m+4)`, the
coefficient `c_m` is negative. -/
theorem sincSliceCoeff_neg_of_mem (L δ : ℝ) (hL : L ≠ 0) {m : ℕ} (hm : 3 ≤ m)
    (hlo : (2 * (m : ℝ) + 1) * (2 * m + 2) ≤ (δ * L) ^ 2)
    (hhi : (δ * L) ^ 2 < (2 * (m : ℝ) + 3) * (2 * m + 4)) :
    sincSliceCoeff L δ m < 0 := by
  rw [sincSliceCoeff_neg_iff L δ hL (by omega)]
  have hm' : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have h0 : 0 ≤ (δ * L) ^ 2 - (2 * (m : ℝ) + 1) * (2 * m + 2) := by linarith
  have h1 : (δ * L) ^ 2 - (2 * (m : ℝ) + 1) * (2 * m + 2) < 8 * m + 10 := by nlinarith
  have h2 : (8 * (m : ℝ) + 10) ^ 2 ≤ (2 * (m : ℝ) + 1) * (2 * m + 2) * (8 * m + 2) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hm') (sub_nonneg.mpr hm'),
      mul_nonneg (mul_nonneg (sub_nonneg.mpr hm') (sub_nonneg.mpr hm')) (sub_nonneg.mpr hm')]
  nlinarith

/-- **Nothing below the window.**  For `m ≥ 2`, if `2m + 2 + √(2m+2) ≤ δL`, then `c_m ≥ 0`. -/
theorem sincSliceCoeff_nonneg_of_le (L δ : ℝ) (hL : L ≠ 0) {m : ℕ} (hm : 2 ≤ m)
    (hδL : 2 * (m : ℝ) + 2 + Real.sqrt (2 * m + 2) ≤ δ * L) :
    0 ≤ sincSliceCoeff L δ m := by
  by_contra hneg
  push Not at hneg
  rw [sincSliceCoeff_neg_iff L δ hL hm] at hneg
  set a : ℝ := 2 * m + 2 with ha
  set s := Real.sqrt a with hs
  have ha1 : 6 ≤ a := by
    have : (2 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  have hs2 : s ^ 2 = a := Real.sq_sqrt (by linarith)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg a
  have hP : (2 * (m : ℝ) + 1) * (2 * m + 2) = a ^ 2 - a := by rw [ha]; ring
  have h8 : 8 * (m : ℝ) + 2 = 4 * a - 6 := by rw [ha]; ring
  rw [hP, h8] at hneg
  have hsq : (a + s) ^ 2 ≤ (δ * L) ^ 2 := by
    have : 0 ≤ a + s := by linarith
    nlinarith
  have hdiff : 2 * a + 2 * a * s ≤ (δ * L) ^ 2 - (a ^ 2 - a) := by nlinarith
  have hbig : (2 * a + 2 * a * s) ^ 2 ≤ ((δ * L) ^ 2 - (a ^ 2 - a)) ^ 2 := by
    have : 0 ≤ 2 * a + 2 * a * s := by positivity
    nlinarith
  have hcube : (a ^ 2 - a) * (4 * a - 6) ≤ (2 * a + 2 * a * s) ^ 2 := by
    nlinarith [sq_nonneg s, mul_nonneg (by linarith : (0 : ℝ) ≤ a) hs0]
  linarith

/-- **Slice identity.**  For `f(z) = (z² + δ²) sin(Lz/2)/(Lz/2)` and `Lx ≠ 0`,
`f(ix) f(−ix) = (δ² − x²)² (sinh(Lx/2)/(Lx/2))²`. -/
theorem sincPairSlice_eq (L δ x : ℝ) (hx : L * x ≠ 0) :
    ((((x : ℂ) * Complex.I) ^ 2 + (δ : ℂ) ^ 2) *
        (Complex.sin ((L : ℂ) * ((x : ℂ) * Complex.I) / 2) / ((L : ℂ) * ((x : ℂ) * Complex.I) / 2))) *
      (((-((x : ℂ) * Complex.I)) ^ 2 + (δ : ℂ) ^ 2) *
        (Complex.sin ((L : ℂ) * (-((x : ℂ) * Complex.I)) / 2) /
          ((L : ℂ) * (-((x : ℂ) * Complex.I)) / 2))) =
      (((δ ^ 2 - x ^ 2) ^ 2 * (Real.sinh (L * x / 2) / (L * x / 2)) ^ 2 : ℝ) : ℂ) := by
  obtain ⟨u, hudef⟩ : ∃ u : ℝ, u = L * x / 2 := ⟨_, rfl⟩
  rw [← hudef]
  have hu0 : u ≠ 0 := by rw [hudef]; exact div_ne_zero hx two_ne_zero
  have hu0' : (u : ℂ) ≠ 0 := by exact_mod_cast hu0
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  have hI2 : Complex.I ^ 2 = -1 := Complex.I_sq
  have e1 : (L : ℂ) * ((x : ℂ) * Complex.I) / 2 = (u : ℂ) * Complex.I := by
    rw [hudef]
    push_cast
    ring
  have e2 : (L : ℂ) * (-((x : ℂ) * Complex.I)) / 2 = ((-u : ℝ) : ℂ) * Complex.I := by
    rw [hudef]
    push_cast
    ring
  have s1 : Complex.sin ((u : ℂ) * Complex.I) / ((u : ℂ) * Complex.I) =
      ((Real.sinh u / u : ℝ) : ℂ) := by
    rw [Complex.sin_mul_I, ← Complex.ofReal_sinh, Complex.ofReal_div]
    field_simp
  have s2 : Complex.sin (((-u : ℝ) : ℂ) * Complex.I) / (((-u : ℝ) : ℂ) * Complex.I) =
      ((Real.sinh u / u : ℝ) : ℂ) := by
    rw [Complex.sin_mul_I, ← Complex.ofReal_sinh, Real.sinh_neg, Complex.ofReal_div,
      Complex.ofReal_neg, Complex.ofReal_neg]
    field_simp
  have q1 : ((x : ℂ) * Complex.I) ^ 2 + (δ : ℂ) ^ 2 = ((δ ^ 2 - x ^ 2 : ℝ) : ℂ) := by
    push_cast
    linear_combination (x : ℂ) ^ 2 * hI2
  have q2 : (-((x : ℂ) * Complex.I)) ^ 2 + (δ : ℂ) ^ 2 = ((δ ^ 2 - x ^ 2 : ℝ) : ℂ) := by
    push_cast
    linear_combination (x : ℂ) ^ 2 * hI2
  rw [e1, e2, s1, s2, q1, q2]
  push_cast
  ring

end

end GaloisForLFunctions.HTGeometry
