import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Direct-slice detection of a multiple mixed class

Let a critical zero of multiplicity `m ≥ 1` sit at the ordinate `γ` of an off-line pair
`γ ± iδ`.  In the variable `v = x²`, the direct slice `Ξ(t − ix)Ξ(t + ix)` of these zeros at the
height `t = γ + d` is, up to a positive constant,

`(1 + α v)^m (1 + b v + c v²)`,  with `α = d⁻²`, `b = 2(d² − δ²)/R²`, `c = 1/R²`, `R = d² + δ²`,

since a zero `z` contributes `1 + v/(t − z)²` and the pair contributes
`1 + 2 Re((t−z)⁻²) v + |t−z|⁻⁴ v²`.

* `coeff_directMixedMultiple`: the `v^{m+1}`-coefficient equals
  `α^{m−1}((m + 2)d² − 2δ²)/(d² R²)`.
* `coeff_directMixedMultiple_neg_iff`: it is negative exactly when `(m + 2)d² < 2δ²`.

So the direct slice detects the pair on the whole interval `0 < |t − γ| < δ √(2/(m+2))`, for
every companion multiplicity `m`.  For `m = 1` this is the interval `|t − γ| < √(2/3)|δ|` of
`directMixedCoeff_two_neg_iff`.  The interval shrinks like `δ√(2/m)` but never closes.  The
reciprocal slice, by contrast, is blind to the mixed class for every `m ≥ 1`
(`coeff_reciprocalPairModel_pos_mixed_all`; higher multiplicity multiplies that positive series by
further positive geometric factors).
-/

open Polynomial

namespace RHTower

noncomputable section

theorem coeff_one_add_C_mul_X_pow {α : ℝ} (hα : α ≠ 0) (n j : ℕ) (hj : j ≤ n) :
    ((1 + C α * X) ^ n).coeff j = α ^ j * (n.choose j : ℝ) := by
  have e : (1 + C α * X : ℝ[X]) = C α * (X + C α⁻¹) := by
    rw [mul_add, ← C_mul, mul_inv_cancel₀ hα, C_1]; ring
  rw [e, mul_pow, ← C_pow, coeff_C_mul, coeff_X_add_C_pow, inv_pow,
    show α ^ n = α ^ j * α ^ (n - j) by rw [← pow_add, Nat.add_sub_cancel' hj]]
  field_simp

theorem natDegree_one_add_C_mul_X_pow_le (α : ℝ) (n : ℕ) :
    ((1 + C α * X : ℝ[X]) ^ n).natDegree ≤ n := by
  refine natDegree_pow_le.trans ?_
  have h : (1 + C α * X : ℝ[X]).natDegree ≤ 1 := by
    refine (natDegree_add_le _ _).trans (max_le (by simp) ?_)
    simpa using natDegree_C_mul_X_pow_le α 1
  calc n * (1 + C α * X : ℝ[X]).natDegree ≤ n * 1 := Nat.mul_le_mul_left n h
    _ = n := mul_one n

/-- **The `v^{m+1}`-coefficient of the multiple mixed direct slice** (multiplicity `m = k + 1`). -/
theorem coeff_directMixedMultiple (k : ℕ) {d δ : ℝ} (hd : d ≠ 0) :
    ((1 + C (d ^ 2)⁻¹ * X) ^ (k + 1)
        * (1 + C (2 * (d ^ 2 - δ ^ 2) / (d ^ 2 + δ ^ 2) ^ 2) * X
          + C (1 / (d ^ 2 + δ ^ 2) ^ 2) * X ^ 2)).coeff (k + 2)
      = ((d ^ 2)⁻¹) ^ k * (((k : ℝ) + 3) * d ^ 2 - 2 * δ ^ 2)
          / (d ^ 2 * (d ^ 2 + δ ^ 2) ^ 2) := by
  have hd2 : d ^ 2 ≠ 0 := pow_ne_zero 2 hd
  have hα : (d ^ 2)⁻¹ ≠ 0 := inv_ne_zero hd2
  have hR : (d ^ 2 + δ ^ 2) ≠ 0 := by positivity
  set P : ℝ[X] := (1 + C (d ^ 2)⁻¹ * X) ^ (k + 1) with hP
  set b : ℝ := 2 * (d ^ 2 - δ ^ 2) / (d ^ 2 + δ ^ 2) ^ 2 with hb
  set c : ℝ := 1 / (d ^ 2 + δ ^ 2) ^ 2 with hc
  have hsplit : P * (1 + C b * X + C c * X ^ 2) = P + C b * (X * P) + C c * (X ^ 2 * P) := by
    ring
  have hP0 : P.coeff (k + 2) = 0 :=
    coeff_eq_zero_of_natDegree_lt ((natDegree_one_add_C_mul_X_pow_le _ _).trans_lt (by omega))
  have hP1 : (X * P).coeff (k + 2) = ((d ^ 2)⁻¹) ^ (k + 1) := by
    rw [show k + 2 = (k + 1) + 1 by omega, coeff_X_mul, hP,
      coeff_one_add_C_mul_X_pow hα _ _ le_rfl, Nat.choose_self, Nat.cast_one, mul_one]
  have hP2 : (X ^ 2 * P).coeff (k + 2) = ((d ^ 2)⁻¹) ^ k * ((k : ℝ) + 1) := by
    rw [coeff_X_pow_mul, hP, coeff_one_add_C_mul_X_pow hα _ _ (by omega),
      Nat.choose_succ_self_right]
    push_cast; ring
  rw [hsplit, coeff_add, coeff_add, coeff_C_mul, coeff_C_mul, hP0, hP1, hP2, pow_succ]
  have key : (d ^ 2)⁻¹ * b + ((k : ℝ) + 1) * c
      = (((k : ℝ) + 3) * d ^ 2 - 2 * δ ^ 2) / (d ^ 2 * (d ^ 2 + δ ^ 2) ^ 2) := by
    rw [hb, hc]; field_simp; ring
  calc 0 + b * ((d ^ 2)⁻¹ ^ k * (d ^ 2)⁻¹) + c * ((d ^ 2)⁻¹ ^ k * ((k : ℝ) + 1))
      = (d ^ 2)⁻¹ ^ k * ((d ^ 2)⁻¹ * b + ((k : ℝ) + 1) * c) := by ring
    _ = _ := by rw [key]; ring

/-- **Detection interval.**  The `v^{m+1}`-coefficient (`m = k + 1`) is negative exactly when
`(m + 2) d² < 2 δ²`. -/
theorem coeff_directMixedMultiple_neg_iff (k : ℕ) {d δ : ℝ} (hd : d ≠ 0) :
    ((1 + C (d ^ 2)⁻¹ * X) ^ (k + 1)
        * (1 + C (2 * (d ^ 2 - δ ^ 2) / (d ^ 2 + δ ^ 2) ^ 2) * X
          + C (1 / (d ^ 2 + δ ^ 2) ^ 2) * X ^ 2)).coeff (k + 2) < 0
      ↔ ((k : ℝ) + 3) * d ^ 2 < 2 * δ ^ 2 := by
  rw [coeff_directMixedMultiple k hd]
  have hd2 : 0 < d ^ 2 := by positivity
  have hpos : 0 < ((d ^ 2)⁻¹) ^ k / (d ^ 2 * (d ^ 2 + δ ^ 2) ^ 2) := by positivity
  rw [mul_div_right_comm]
  constructor
  · intro h
    by_contra hcon
    replace hcon := not_lt.mp hcon
    have : 0 ≤ ((d ^ 2)⁻¹) ^ k / (d ^ 2 * (d ^ 2 + δ ^ 2) ^ 2)
        * (((k : ℝ) + 3) * d ^ 2 - 2 * δ ^ 2) :=
      mul_nonneg hpos.le (by linarith)
    linarith
  · intro h
    exact mul_neg_of_pos_of_neg hpos (by linarith)


/-- The `v^m`-coefficient of the multiple mixed direct slice (multiplicity `m = k + 2`):
`α^m + m α^{m−1} b + C(m,2) α^{m−2} c`. -/
theorem coeff_directMixedMultiple_diag (k : ℕ) {α b c : ℝ} (hα : α ≠ 0) :
    ((1 + C α * X) ^ (k + 2) * (1 + C b * X + C c * X ^ 2)).coeff (k + 2)
      = α ^ (k + 2) + ((k : ℝ) + 2) * α ^ (k + 1) * b
        + (((k : ℝ) + 2) * ((k : ℝ) + 1) / 2) * α ^ k * c := by
  set P : ℝ[X] := (1 + C α * X) ^ (k + 2) with hP
  have hsplit : P * (1 + C b * X + C c * X ^ 2) = P + C b * (X * P) + C c * (X ^ 2 * P) := by
    ring
  have h0 : P.coeff (k + 2) = α ^ (k + 2) := by
    rw [hP, coeff_one_add_C_mul_X_pow hα _ _ le_rfl, Nat.choose_self, Nat.cast_one, mul_one]
  have h1 : (X * P).coeff (k + 2) = ((k : ℝ) + 2) * α ^ (k + 1) := by
    rw [show k + 2 = (k + 1) + 1 by omega, coeff_X_mul, hP,
      coeff_one_add_C_mul_X_pow hα _ _ (by omega), Nat.choose_succ_self_right]
    push_cast; ring
  have h2 : (X ^ 2 * P).coeff (k + 2) = (((k : ℝ) + 2) * ((k : ℝ) + 1) / 2) * α ^ k := by
    rw [coeff_X_pow_mul, hP, coeff_one_add_C_mul_X_pow hα _ _ (by omega)]
    have hc : ((k + 2).choose k : ℝ) = ((k : ℝ) + 2) * ((k : ℝ) + 1) / 2 := by
      rw [Nat.choose_symm_add, Nat.cast_choose_two]
      push_cast
      ring
    rw [hc]; ring
  rw [hsplit, coeff_add, coeff_add, coeff_C_mul, coeff_C_mul, h0, h1, h2]
  ring

/-- **The lower coefficient enlarges the bad set.**  For multiplicity `9` and the height with
`21 d² = 4 δ²`, the `v⁹`-coefficient of the mixed direct slice is negative while the `v¹⁰`
criterion of `coeff_directMixedMultiple_neg_iff` fails (`11 d² ≥ 2 δ²`).  So the exact bad set is
strictly larger than the window `|t − γ| < δ √(2/(m+2))`. -/
theorem directMixedMultiple_nine_enlarged {d δ : ℝ} (hd : d ≠ 0) (h : 21 * d ^ 2 = 4 * δ ^ 2) :
    ((1 + C (d ^ 2)⁻¹ * X) ^ (7 + 2)
        * (1 + C (2 * (d ^ 2 - δ ^ 2) / (d ^ 2 + δ ^ 2) ^ 2) * X
          + C (1 / (d ^ 2 + δ ^ 2) ^ 2) * X ^ 2)).coeff (7 + 2) < 0
      ∧ ¬ (((8 : ℕ) : ℝ) + 3) * d ^ 2 < 2 * δ ^ 2 := by
  have hd2 : 0 < d ^ 2 := by positivity
  have hα : (d ^ 2)⁻¹ ≠ 0 := inv_ne_zero hd2.ne'
  refine ⟨?_, ?_⟩
  · rw [coeff_directMixedMultiple_diag 7 hα]
    have hδ2 : δ ^ 2 = 21 * d ^ 2 / 4 := by linarith
    rw [hδ2]
    generalize hD : d ^ 2 = D at *
    have hD0 : D ≠ 0 := hd2.ne'
    rw [show D + 21 * D / 4 = 25 * D / 4 by ring]
    push_cast
    calc _ = -(23 / 625) * D⁻¹ ^ 9 := by field_simp; ring
      _ < 0 := by
        have : 0 < D⁻¹ ^ 9 := by positivity
        linarith
  · push_cast
    nlinarith

end

end RHTower
