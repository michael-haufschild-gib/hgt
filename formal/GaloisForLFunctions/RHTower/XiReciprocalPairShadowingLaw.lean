import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# One critical zero shadows one off-line pair in the reciprocal slice

At a height `t`, in the variable `v = σ²`, a critical zero `γ` contributes the factor
`1/(1 − α v)` to the reciprocal slice `1/(Ξ(t+σ)Ξ(t−σ))`, with `α = (t − γ)⁻²`.  An off-line pair
`z, z̄` contributes `1/((1 − β v)(1 − β̄ v))`, with `β = (t − z)⁻²`.  For `z` off the line the pair
factor alone has coefficients of both signs.  This file shows that a single critical copy close
enough to `t` makes the three-factor product coefficient-positive.

* `one_sub_mul_one_sub_mul_sum_pairHom`: with `h_m(x,y) = Σ_{j ≤ m} x^j y^{m−j}`,
  `(1 − x)(1 − y) Σ_{m ≤ n} h_m(x,y) = 1 − h_{n+1}(x,y) + x y h_n(x,y)`.
* `sum_pairHom_conj_pos`: if `‖b‖ < ½`, every partial sum `Σ_{m ≤ n} h_m(b, b̄)` is a positive
  real number.  The threshold is sharp (`re_sum_pairHom_one_neg`).
* `sum_pairHom_conj_pos_of_im`: angle criterion.  If `|b| ≤ 1` and `|b| · |b − |b|²| < |Im b|`,
  every partial sum is positive; this reaches past `|b| = ½` when `b` is far from the real axis.
* `coeff_reciprocalPairModel_pos`: for `α > 0`, the `n`-th Taylor coefficient of
  `1/((1 − α b v)(1 − α b̄ v)(1 − α v))` is `αⁿ Σ_{m ≤ n} h_m(b, b̄)`, hence positive with it.
* `coeff_reciprocalPairModel_pos_of_shadow`: the critical zero `γ` shadows the pair `z, z̄` at `t`
  whenever `2 (t − γ)² < |t − z|²`.
* `coeff_reciprocalPairModel_pos_mixed`, `coeff_reciprocalPairModel_pos_mixed_all`: for a pair at
  the ordinate of the critical zero, `z = γ + iδ`, the ½-criterion covers the exposure window
  `0 < |t − γ| < |δ|`, and the angle criterion covers every height `t ≠ γ`.  The reciprocal slice
  of this configuration is coefficient-positive everywhere: it cannot detect the pair.
* `directMixedCoeffs`, `directMixedCoeff_two_neg_iff`: the direct slice of the same configuration
  has a negative coefficient exactly on `3 (t − γ)² < 2 δ²`.  The two slices are complementary:
  the direct one detects the mixed pair on `|t − γ| < √(2/3)|δ|`, the reciprocal one nowhere.
* `reciprocalPairModel_globally_pos_iff`: the reciprocal model of `{γ', γ ± iδ}` is
  coefficient-positive at every height `t ≠ γ'` if and only if `γ' = γ`.  For `γ' ≠ γ` a height on
  the pair's side of the bisector gives `b^K = −R^K` with `R > 1`, and the partial sums over two
  periods differ by the negative factor `1 − R^K`.
* `coeff_mixedSextic_reciprocal_pos`: the even polynomial `(t² − γ²)((t − γ)² + δ²)((t + γ)² + δ²)`
  has non-real zeros, yet its reciprocal slices are coefficient-positive at every admissible
  height.  Coefficient-level reciprocal positivity is not a real-rootedness criterion.
* `re_sum_pairHom_one_neg`, `coeff_one_reciprocalPairModel_neg`: the constant `½` cannot be
  raised.  For `b = −s` with `s > ½` the partial sum `1 + h_1(b, b̄) = 1 − 2s` is negative; in slice
  terms, a pair `t ± iδ` at the height `t` itself is not shadowed once `δ² < 2 (t − γ)²`.

The partial sums `Σ_{m ≤ n} h_m(b, b̄)` are the coefficients of the model divided by `αⁿ`.  For
`n ≤ 1` they are `1` and `1 + 2 Re b`.  For `n ≥ 2` the identity turns their sign into the bound
`|h_{n+1}| + |b|²|h_n| < 1`, which follows from `|h_m| ≤ (m+1)|b|^m` and `3n + 5 < 2^{n+2}`.
-/

open Complex Finset PowerSeries ComplexConjugate
open scoped ComplexOrder

namespace RHTower

noncomputable section

/-- The complete homogeneous symmetric polynomial of degree `m` in two variables. -/
def pairHom (x y : ℂ) (m : ℕ) : ℂ := ∑ j ∈ range (m + 1), x ^ j * y ^ (m - j)

theorem pairHom_zero (x y : ℂ) : pairHom x y 0 = 1 := by simp [pairHom]

theorem pairHom_succ (x y : ℂ) (m : ℕ) :
    pairHom x y (m + 1) = x ^ (m + 1) + y * pairHom x y m := by
  unfold pairHom
  rw [sum_range_succ, Nat.sub_self, pow_zero, mul_one, add_comm, mul_sum]
  congr 1
  refine sum_congr rfl fun j hj => ?_
  have hj' : j ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hj)
  rw [show m + 1 - j = (m - j) + 1 by omega, pow_succ]
  ring

theorem pairHom_succ_succ (x y : ℂ) (m : ℕ) :
    pairHom x y (m + 2) = (x + y) * pairHom x y (m + 1) - x * y * pairHom x y m := by
  rw [show m + 2 = m + 1 + 1 from rfl, pairHom_succ x y (m + 1), pairHom_succ x y m]
  ring

theorem sub_mul_pairHom (x y : ℂ) (m : ℕ) :
    (x - y) * pairHom x y m = x ^ (m + 1) - y ^ (m + 1) := by
  induction m with
  | zero => simp [pairHom_zero]
  | succ m ih =>
    rw [pairHom_succ, mul_add, mul_left_comm, ih]
    ring

/-- **Partial-sum identity.** -/
theorem one_sub_mul_one_sub_mul_sum_pairHom (x y : ℂ) (n : ℕ) :
    (1 - x) * (1 - y) * ∑ m ∈ range (n + 1), pairHom x y m
      = 1 - pairHom x y (n + 1) + x * y * pairHom x y n := by
  induction n with
  | zero =>
    have h1 : pairHom x y 1 = x + y := by simp [pairHom, sum_range_succ, add_comm]
    rw [sum_range_one, pairHom_zero, zero_add, h1]
    ring
  | succ n ih =>
    rw [sum_range_succ, mul_add, ih, pairHom_succ_succ]
    ring

theorem norm_pairHom_le {x y : ℂ} {r : ℝ} (hx : ‖x‖ ≤ r) (hy : ‖y‖ ≤ r) (m : ℕ) :
    ‖pairHom x y m‖ ≤ ((m : ℝ) + 1) * r ^ m := by
  have hr : 0 ≤ r := (norm_nonneg _).trans hx
  unfold pairHom
  calc ‖∑ j ∈ range (m + 1), x ^ j * y ^ (m - j)‖
      ≤ ∑ j ∈ range (m + 1), ‖x ^ j * y ^ (m - j)‖ := norm_sum_le _ _
    _ ≤ ∑ _j ∈ range (m + 1), r ^ m := by
        refine sum_le_sum fun j hj => ?_
        have hj' : j ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hj)
        rw [norm_mul, norm_pow, norm_pow]
        calc ‖x‖ ^ j * ‖y‖ ^ (m - j) ≤ r ^ j * r ^ (m - j) :=
              mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hx j)
                (pow_le_pow_left₀ (norm_nonneg _) hy _) (by positivity) (by positivity)
          _ = r ^ m := by rw [← pow_add, Nat.add_sub_cancel' hj']
    _ = ((m : ℝ) + 1) * r ^ m := by
        rw [sum_const, card_range, nsmul_eq_mul]
        push_cast
        ring

theorem pairHom_comm (x y : ℂ) (m : ℕ) : pairHom x y m = pairHom y x m := by
  unfold pairHom
  rw [← sum_range_reflect (fun j => x ^ j * y ^ (m - j)) (m + 1)]
  refine sum_congr rfl fun j hj => ?_
  have hj' : j ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hj)
  rw [show m + 1 - 1 - j = m - j by omega, show m - (m - j) = j by omega, mul_comm]

theorem conj_pairHom (x y : ℂ) (m : ℕ) :
    conj (pairHom x y m) = pairHom (conj x) (conj y) m := by
  simp [pairHom, map_sum, map_mul, map_pow]

theorem pairHom_conj_im (b : ℂ) (m : ℕ) : (pairHom b (conj b) m).im = 0 := by
  rw [← conj_eq_iff_im, conj_pairHom, conj_conj, pairHom_comm]

theorem pairHom_mul_mul (a x y : ℂ) (m : ℕ) :
    pairHom (a * x) (a * y) m = a ^ m * pairHom x y m := by
  unfold pairHom
  rw [mul_sum]
  refine sum_congr rfl fun j hj => ?_
  have hj' : j ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hj)
  have ha : a ^ m = a ^ j * a ^ (m - j) := by rw [← pow_add, Nat.add_sub_cancel' hj']
  rw [mul_pow, mul_pow, ha]
  ring

theorem pairHom_tail_bound_lt_one {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ 1 / 2) (k : ℕ) :
    ((k : ℝ) + 4) * s ^ (k + 3) + s ^ 2 * (((k : ℝ) + 3) * s ^ (k + 2)) < 1 := by
  have hk : k + 1 ≤ 2 ^ k := Nat.lt_two_pow_self
  have hk' : (k : ℝ) + 1 ≤ 2 ^ k := by exact_mod_cast hk
  have h3 : s ^ (k + 3) ≤ (1 / 2) ^ (k + 3) := pow_le_pow_left₀ hs0 hs _
  have h4 : s ^ (k + 4) ≤ (1 / 2) ^ (k + 4) := pow_le_pow_left₀ hs0 hs _
  have e : s ^ 2 * (((k : ℝ) + 3) * s ^ (k + 2)) = ((k : ℝ) + 3) * s ^ (k + 4) := by ring
  rw [e]
  have hb : ((k : ℝ) + 4) * s ^ (k + 3) + ((k : ℝ) + 3) * s ^ (k + 4)
      ≤ ((k : ℝ) + 4) * (1 / 2) ^ (k + 3) + ((k : ℝ) + 3) * (1 / 2) ^ (k + 4) := by
    gcongr
  refine hb.trans_lt ?_
  have e2 : ((k : ℝ) + 4) * (1 / 2) ^ (k + 3) + ((k : ℝ) + 3) * (1 / 2) ^ (k + 4)
      = (3 * (k : ℝ) + 11) / (16 * 2 ^ k) := by
    have q3 : (1 / 2 : ℝ) ^ (k + 3) = 1 / (8 * 2 ^ k) := by
      rw [one_div_pow, pow_add]; norm_num; ring
    have q4 : (1 / 2 : ℝ) ^ (k + 4) = 1 / (16 * 2 ^ k) := by
      rw [one_div_pow, pow_add]; norm_num; ring
    rw [q3, q4]
    field_simp
    ring
  rw [e2, div_lt_one (by positivity)]
  nlinarith

/-- **Positivity of the conjugate-pair partial sums below the sharp threshold `½`.** -/
theorem sum_pairHom_conj_pos {b : ℂ} (hb : ‖b‖ < 1 / 2) (n : ℕ) :
    0 < ∑ m ∈ range (n + 1), pairHom b (conj b) m := by
  set S := ∑ m ∈ range (n + 1), pairHom b (conj b) m with hS
  have hSim : S.im = 0 := by
    rw [hS, im_sum]
    exact sum_eq_zero fun m _ => pairHom_conj_im b m
  rcases n with _ | _ | k
  · rw [hS, sum_range_one, pairHom_zero]
    exact one_pos
  · have h1 : pairHom b (conj b) 1 = b + conj b := by simp [pairHom, sum_range_succ, add_comm]
    have hre : S.re = 1 + 2 * b.re := by
      rw [hS, sum_range_succ, sum_range_one, pairHom_zero, h1]
      simp only [add_re, one_re, conj_re]
      ring
    have hlo : -‖b‖ ≤ b.re := by linarith [neg_abs_le b.re, abs_re_le_norm b]
    exact pos_iff.mpr ⟨by rw [hre]; linarith, hSim.symm⟩
  · have hb1 : ‖b‖ < 1 := by linarith
    have hne : (1 : ℂ) - b ≠ 0 := by
      intro h
      have hb' : b = 1 := by linear_combination -h
      rw [hb', norm_one] at hb1
      exact lt_irrefl _ hb1
    have hpos : 0 < normSq (1 - b) := normSq_pos.mpr hne
    have hid := one_sub_mul_one_sub_mul_sum_pairHom b (conj b) (k + 2)
    have hfac : (1 - b) * (1 - conj b) = (normSq (1 - b) : ℂ) := by
      rw [← mul_conj, map_sub, map_one]
    rw [hfac, mul_conj b, ← hS] at hid
    have hre := congrArg Complex.re hid
    rw [re_ofReal_mul, add_re, sub_re, one_re, re_ofReal_mul] at hre
    have hnb : ‖conj b‖ ≤ ‖b‖ := (norm_conj b).le
    have h1 : (pairHom b (conj b) (k + 2 + 1)).re ≤ ((k : ℝ) + 4) * ‖b‖ ^ (k + 3) := by
      refine (re_le_norm _).trans ((norm_pairHom_le le_rfl hnb (k + 2 + 1)).trans_eq ?_)
      push_cast
      ring
    have h2 : -(((k : ℝ) + 3) * ‖b‖ ^ (k + 2)) ≤ (pairHom b (conj b) (k + 2)).re := by
      have := (abs_re_le_norm (pairHom b (conj b) (k + 2))).trans
        (norm_pairHom_le le_rfl hnb (k + 2))
      push_cast at this
      linarith [neg_abs_le (pairHom b (conj b) (k + 2)).re]
    have hnsq : normSq b = ‖b‖ ^ 2 := normSq_eq_norm_sq b
    have htail := pairHom_tail_bound_lt_one (norm_nonneg b) hb.le k
    have hrhs : 0 < normSq (1 - b) * S.re := by
      rw [hre, hnsq]
      nlinarith [mul_le_mul_of_nonneg_left h2 (sq_nonneg ‖b‖)]
    have hSre : 0 < S.re := pos_of_mul_pos_right hrhs hpos.le
    exact pos_iff.mpr ⟨hSre, hSim.symm⟩

/-- **Angle criterion for the conjugate-pair partial sums.**  If `|b| ≤ 1` and
`|b| · |b − |b|²| < |Im b|`, every partial sum `Σ_{m ≤ n} h_m(b, b̄)` is a positive real number.
Here `(b − b̄)(h_{n+1} − |b|² h_n) = w − w̄` with `w = b^{n+1}(b − |b|²)`, so
`|h_{n+1} − |b|² h_n| ≤ |b|^{n+1} |b − |b|²| / |Im b| < 1`. -/
theorem sum_pairHom_conj_pos_of_im {b : ℂ} (hb1 : normSq b ≤ 1)
    (hb : normSq b * normSq (b - normSq b) < b.im ^ 2) (n : ℕ) :
    0 < ∑ m ∈ range (n + 1), pairHom b (conj b) m := by
  set S := ∑ m ∈ range (n + 1), pairHom b (conj b) m with hS
  have hSim : S.im = 0 := by
    rw [hS, im_sum]
    exact sum_eq_zero fun m _ => pairHom_conj_im b m
  have hnb1 : ‖b‖ ≤ 1 := (sq_le_one_iff₀ (norm_nonneg b)).mp (by rwa [← normSq_eq_norm_sq])
  have hprod : ‖b‖ * ‖b - (normSq b : ℂ)‖ < |b.im| := by
    refine lt_of_pow_lt_pow_left₀ 2 (abs_nonneg _) ?_
    rw [mul_pow, ← normSq_eq_norm_sq, ← normSq_eq_norm_sq, sq_abs]
    exact hb
  have him : b.im ≠ 0 := by
    intro h
    rw [h, abs_zero] at hprod
    exact absurd hprod (not_lt.mpr (by positivity))
  have hne : (1 : ℂ) - b ≠ 0 := by
    intro h
    apply him
    have hb' : b = 1 := by linear_combination -h
    rw [hb', one_im]
  have hpos : 0 < normSq (1 - b) := normSq_pos.mpr hne
  set D := pairHom b (conj b) (n + 1) - b * conj b * pairHom b (conj b) n with hD
  set w := b ^ (n + 1) * (b - b * conj b) with hw
  have hDw : (b - conj b) * D = w - conj w := by
    rw [hD, hw, map_mul, map_pow, map_sub, map_mul, conj_conj]
    linear_combination (sub_mul_pairHom b (conj b) (n + 1))
      - b * conj b * (sub_mul_pairHom b (conj b) n)
  have hnorm := congrArg norm hDw
  rw [norm_mul, sub_conj, sub_conj, norm_mul, norm_mul, norm_I, mul_one, mul_one, norm_real,
    norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul] at hnorm
  have hwle : |w.im| ≤ ‖b‖ * ‖b - (normSq b : ℂ)‖ := by
    refine (abs_im_le_norm w).trans ?_
    rw [hw, norm_mul, norm_pow, mul_conj]
    exact mul_le_mul_of_nonneg_right (pow_le_of_le_one (norm_nonneg b) hnb1 (Nat.succ_ne_zero n))
      (norm_nonneg _)
  have hDlt : ‖D‖ < 1 := by
    have h2 : |b.im| * ‖D‖ ≤ ‖b‖ * ‖b - (normSq b : ℂ)‖ := by
      have : |(2 : ℝ)| * |b.im| * ‖D‖ = |(2 : ℝ)| * |w.im| := hnorm
      rw [abs_two] at this
      linarith
    by_contra hcon
    have := mul_le_mul_of_nonneg_left (not_lt.mp hcon) (abs_nonneg b.im)
    linarith
  have hid := one_sub_mul_one_sub_mul_sum_pairHom b (conj b) n
  have hfac : (1 - b) * (1 - conj b) = (normSq (1 - b) : ℂ) := by
    rw [← mul_conj, map_sub, map_one]
  rw [hfac, ← hS, show (1 : ℂ) - pairHom b (conj b) (n + 1) + b * conj b * pairHom b (conj b) n
    = 1 - D by rw [hD]; ring] at hid
  have hre := congrArg Complex.re hid
  rw [re_ofReal_mul, sub_re, one_re] at hre
  have hDre : D.re ≤ ‖D‖ := re_le_norm D
  have hSre : 0 < S.re := pos_of_mul_pos_right (by rw [hre]; linarith) hpos.le
  exact pos_iff.mpr ⟨hSre, hSim.symm⟩

/-- The reciprocal three-zero model `1/((1 − β v)(1 − β' v)(1 − α v))`, as a product of geometric
series. -/
def reciprocalPairModel (α β β' : ℂ) : PowerSeries ℂ :=
  (mk fun n => β ^ n) * (mk fun n => β' ^ n) * mk fun n => α ^ n

theorem geom_mul_one_sub (a : ℂ) : (mk fun n => a ^ n) * (1 - C a * X) = 1 := by
  ext n
  rw [mul_sub, mul_one, map_sub, coeff_one]
  rcases n with _ | n
  · rw [← mul_assoc, coeff_zero_mul_X, coeff_mk]
    simp
  · rw [← mul_assoc, coeff_succ_mul_X, coeff_mul_C, coeff_mk, coeff_mk, pow_succ, sub_self]
    simp

/-- The model is the reciprocal of `(1 − β v)(1 − β' v)(1 − α v)`. -/
theorem reciprocalPairModel_mul (α β β' : ℂ) :
    reciprocalPairModel α β β' * ((1 - C β * X) * (1 - C β' * X) * (1 - C α * X)) = 1 := by
  unfold reciprocalPairModel
  calc _ = ((mk fun n => β ^ n) * (1 - C β * X)) * ((mk fun n => β' ^ n) * (1 - C β' * X))
          * ((mk fun n => α ^ n) * (1 - C α * X)) := by ring
    _ = 1 := by rw [geom_mul_one_sub, geom_mul_one_sub, geom_mul_one_sub, one_mul, one_mul]

theorem coeff_geom_mul_geom (β β' : ℂ) (m : ℕ) :
    coeff m ((mk fun n => β ^ n) * mk fun n => β' ^ n) = pairHom β β' m := by
  rw [coeff_mul]
  simp only [coeff_mk]
  exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => β ^ i * β' ^ j) m

theorem coeff_reciprocalPairModel (α β β' : ℂ) (n : ℕ) :
    coeff n (reciprocalPairModel α β β')
      = ∑ m ∈ range (n + 1), pairHom β β' m * α ^ (n - m) := by
  unfold reciprocalPairModel
  rw [coeff_mul]
  simp only [coeff_geom_mul_geom, coeff_mk]
  exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => pairHom β β' i * α ^ j) n

theorem coeff_reciprocalPairModel_eq (α : ℝ) (b : ℂ) (n : ℕ) :
    coeff n (reciprocalPairModel α (α * b) (α * conj b))
      = (α : ℂ) ^ n * ∑ m ∈ range (n + 1), pairHom b (conj b) m := by
  rw [coeff_reciprocalPairModel, mul_sum]
  refine sum_congr rfl fun m hm => ?_
  have hm' : m ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hm)
  have ha : (α : ℂ) ^ n = (α : ℂ) ^ m * (α : ℂ) ^ (n - m) := by
    rw [← pow_add, Nat.add_sub_cancel' hm']
  rw [pairHom_mul_mul, ha]
  ring

/-- **Shadowing of one pair by one critical copy**, normalized form. -/
theorem coeff_reciprocalPairModel_pos {α : ℝ} (hα : 0 < α) {b : ℂ} {n : ℕ}
    (hb : 0 < ∑ m ∈ range (n + 1), pairHom b (conj b) m) :
    0 < coeff n (reciprocalPairModel α (α * b) (α * conj b)) := by
  rw [coeff_reciprocalPairModel_eq]
  have hαn : (0 : ℂ) < (α : ℂ) ^ n := by
    rw [← ofReal_pow]
    exact zero_lt_real.mpr (pow_pos hα n)
  exact mul_pos hαn hb

/-- The slice model in normalized form: with `α = (t − γ)⁻²` and `b = (t − γ)²/(t − z)²`. -/
theorem reciprocalPairModel_slice_eq {t γ : ℝ} {z : ℂ} (hγ : t ≠ γ) (hz : (t : ℂ) ≠ z) :
    reciprocalPairModel ((((t - γ : ℝ) : ℂ)) ^ 2)⁻¹ (((t : ℂ) - z) ^ 2)⁻¹
        (((t : ℂ) - conj z) ^ 2)⁻¹
      = reciprocalPairModel (((t - γ) ^ 2)⁻¹ : ℝ)
          ((((t - γ) ^ 2)⁻¹ : ℝ) * (((t : ℂ) - γ) ^ 2 / ((t : ℂ) - z) ^ 2))
          ((((t - γ) ^ 2)⁻¹ : ℝ) * conj (((t : ℂ) - γ) ^ 2 / ((t : ℂ) - z) ^ 2)) := by
  have hdC : ((t : ℂ) - γ) ≠ 0 := by
    rw [← ofReal_sub]; exact ofReal_ne_zero.mpr (sub_ne_zero.mpr hγ)
  have hzC : (t : ℂ) - z ≠ 0 := sub_ne_zero.mpr hz
  have hzC' : (t : ℂ) - conj z ≠ 0 := by
    intro h
    apply hzC
    have := congrArg conj h
    rwa [map_sub, conj_ofReal, conj_conj, map_zero] at this
  congr 1
  · rw [ofReal_inv, ofReal_pow]
  · rw [ofReal_inv, ofReal_pow, ofReal_sub]
    field_simp
  · rw [map_div₀, map_pow, map_pow, map_sub, map_sub, conj_ofReal, conj_ofReal, ofReal_inv,
      ofReal_pow, ofReal_sub]
    field_simp

theorem norm_slice_b {t γ : ℝ} {z : ℂ} :
    ‖((t : ℂ) - γ) ^ 2 / ((t : ℂ) - z) ^ 2‖ = (t - γ) ^ 2 / ‖(t : ℂ) - z‖ ^ 2 := by
  rw [norm_div, norm_pow, norm_pow, ← ofReal_sub, norm_real, Real.norm_eq_abs, sq_abs]

/-- **Shadowing law in slice coordinates.**  A critical zero `γ` and an off-line pair `z, z̄` at
the height `t`: if `2 (t − γ)² < |t − z|²`, every Taylor coefficient of
`1/(((t − z)² − v)((t − z̄)² − v)((t − γ)² − v))`, normalized at `v = 0`, is positive. -/
theorem coeff_reciprocalPairModel_pos_of_shadow {t γ : ℝ} {z : ℂ} (hγ : t ≠ γ)
    (hz : (t : ℂ) ≠ z) (hs : 2 * (t - γ) ^ 2 < ‖(t : ℂ) - z‖ ^ 2) (n : ℕ) :
    0 < coeff n (reciprocalPairModel ((((t - γ : ℝ) : ℂ)) ^ 2)⁻¹ (((t : ℂ) - z) ^ 2)⁻¹
      (((t : ℂ) - conj z) ^ 2)⁻¹) := by
  have hd : 0 < (t - γ) ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2
    (sub_ne_zero.mpr hγ)))
  have hz2 : 0 < ‖(t : ℂ) - z‖ ^ 2 := by
    have : (t : ℂ) - z ≠ 0 := sub_ne_zero.mpr hz
    positivity
  have hb2 : ‖((t : ℂ) - γ) ^ 2 / ((t : ℂ) - z) ^ 2‖ < 1 / 2 := by
    rw [norm_slice_b, div_lt_iff₀ hz2]; linarith
  rw [reciprocalPairModel_slice_eq hγ hz]
  exact coeff_reciprocalPairModel_pos (inv_pos.mpr hd) (sum_pairHom_conj_pos hb2 n)

/-- **Mixed class: the critical zero hides the pair on its whole exposure window.**  For a
critical zero at `γ` and the pair `γ ± iδ`, every height with `0 < |t − γ| < |δ|` has a
coefficient-positive three-zero reciprocal model. -/
theorem coeff_reciprocalPairModel_pos_mixed {t γ δ : ℝ} (hγ : t ≠ γ)
    (hδ : (t - γ) ^ 2 < δ ^ 2) (n : ℕ) :
    0 < coeff n (reciprocalPairModel ((((t - γ : ℝ) : ℂ)) ^ 2)⁻¹
      (((t : ℂ) - (γ + δ * I)) ^ 2)⁻¹ (((t : ℂ) - (γ - δ * I)) ^ 2)⁻¹) := by
  have hconj : conj ((γ : ℂ) + δ * I) = γ - δ * I := by
    rw [map_add, map_mul, conj_ofReal, conj_ofReal, conj_I]; ring
  have hz : (t : ℂ) ≠ γ + δ * I := by
    intro h
    have := congrArg Complex.re h
    simp at this
    exact hγ this
  have hnorm : ‖(t : ℂ) - (γ + δ * I)‖ ^ 2 = (t - γ) ^ 2 + δ ^ 2 := by
    have e : (t : ℂ) - (γ + δ * I) = ((t - γ : ℝ) : ℂ) + ((-δ : ℝ) : ℂ) * I := by
      push_cast; ring
    rw [e, ← normSq_eq_norm_sq, normSq_add_mul_I]
    ring
  have hs : 2 * (t - γ) ^ 2 < ‖(t : ℂ) - (γ + δ * I)‖ ^ 2 := by
    rw [hnorm]; linarith
  have h := coeff_reciprocalPairModel_pos_of_shadow hγ hz hs n
  rwa [hconj] at h

/-- **Mixed class: the reciprocal slice is blind at every height.**  For a critical zero at `γ`
and the pair `γ ± iδ` (`δ ≠ 0`), the three-zero reciprocal model is coefficient-positive at every
height `t ≠ γ`.  With `d = t − γ` and `r = d² + δ²`, `b = d²(d + iδ)²/r²` satisfies the angle
criterion: `|Im b|² − |b|²|b − |b|²|² = d⁶δ⁴(7d² + 4δ²)/r⁶ > 0`. -/
theorem coeff_reciprocalPairModel_pos_mixed_all {t γ δ : ℝ} (hγ : t ≠ γ) (hδ : δ ≠ 0) (n : ℕ) :
    0 < coeff n (reciprocalPairModel ((((t - γ : ℝ) : ℂ)) ^ 2)⁻¹
      (((t : ℂ) - (γ + δ * I)) ^ 2)⁻¹ (((t : ℂ) - (γ - δ * I)) ^ 2)⁻¹) := by
  have hconj : conj ((γ : ℂ) + δ * I) = γ - δ * I := by
    rw [map_add, map_mul, conj_ofReal, conj_ofReal, conj_I]; ring
  have hz : (t : ℂ) ≠ γ + δ * I := by
    intro h
    have := congrArg Complex.re h
    simp at this
    exact hγ this
  set d : ℝ := t - γ with hd_def
  have hd0 : d ≠ 0 := sub_ne_zero.mpr hγ
  set r : ℝ := d ^ 2 + δ ^ 2 with hr_def
  have hr : 0 < r := by positivity
  set X : ℝ := d ^ 2 * (d ^ 2 - δ ^ 2) / r ^ 2 with hX
  set Y : ℝ := 2 * d ^ 3 * δ / r ^ 2 with hY
  have hb_eq : ((t : ℂ) - γ) ^ 2 / ((t : ℂ) - (γ + δ * I)) ^ 2 = (X : ℂ) + (Y : ℂ) * I := by
    have e1 : (t : ℂ) - γ = (d : ℂ) := by rw [hd_def]; push_cast; ring
    have e2 : (t : ℂ) - (γ + δ * I) = (d : ℂ) - δ * I := by rw [hd_def]; push_cast; ring
    have hw : ((d : ℂ) - δ * I) ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      simp at this
      exact hd0 this
    have hrC : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr.ne'
    have hprod : ((d : ℂ) - δ * I) * ((d : ℂ) + δ * I) = (r : ℂ) := by
      rw [hr_def]; push_cast; ring_nf; rw [I_sq]; ring
    rw [e1, e2, hX, hY]
    have hwr : ((d : ℂ) - δ * I) ^ 2 = (r : ℂ) ^ 2 / ((d : ℂ) + δ * I) ^ 2 := by
      have hw' : ((d : ℂ) + δ * I) ≠ 0 := by
        intro h
        have := congrArg Complex.re h
        simp at this
        exact hd0 this
      rw [eq_div_iff (pow_ne_zero 2 hw'), ← mul_pow, hprod]
    rw [hwr]
    push_cast
    field_simp
    ring_nf
    rw [I_sq]
    ring
  have hq : X ^ 2 + Y ^ 2 = d ^ 4 / r ^ 2 := by
    rw [hX, hY]; field_simp; rw [hr_def]; ring
  have hnormSq : normSq ((X : ℂ) + (Y : ℂ) * I) = d ^ 4 / r ^ 2 := by
    rw [normSq_add_mul_I, hq]
  have hsub : (X : ℂ) + (Y : ℂ) * I - (normSq ((X : ℂ) + (Y : ℂ) * I) : ℂ)
      = ((-(d ^ 2 * δ ^ 2 / r ^ 2) : ℝ) : ℂ) + (Y : ℂ) * I := by
    rw [hnormSq, hX]
    have : d ^ 2 * (d ^ 2 - δ ^ 2) / r ^ 2 - d ^ 4 / r ^ 2 = -(d ^ 2 * δ ^ 2 / r ^ 2) := by
      field_simp; ring
    rw [← this]; push_cast; ring
  have hcrit1 : normSq ((X : ℂ) + (Y : ℂ) * I) ≤ 1 := by
    rw [hnormSq, div_le_one (by positivity), hr_def]
    nlinarith [sq_nonneg δ, sq_nonneg d, mul_nonneg (sq_nonneg d) (sq_nonneg δ)]
  have hcrit2 : normSq ((X : ℂ) + (Y : ℂ) * I)
      * normSq ((X : ℂ) + (Y : ℂ) * I - (normSq ((X : ℂ) + (Y : ℂ) * I) : ℂ))
      < ((X : ℂ) + (Y : ℂ) * I).im ^ 2 := by
    rw [hsub, hnormSq, normSq_add_mul_I]
    simp only [add_im, ofReal_im, mul_im, ofReal_re, I_re, I_im, mul_zero, mul_one, zero_add]
    have key : Y ^ 2 - d ^ 4 / r ^ 2 * ((-(d ^ 2 * δ ^ 2 / r ^ 2)) ^ 2 + Y ^ 2)
        = d ^ 6 * δ ^ 4 * (7 * d ^ 2 + 4 * δ ^ 2) / r ^ 6 := by
      rw [hY]; field_simp; rw [hr_def]; ring
    have hpos : 0 < d ^ 6 * δ ^ 4 * (7 * d ^ 2 + 4 * δ ^ 2) / r ^ 6 := by positivity
    linarith
  have hsum := sum_pairHom_conj_pos_of_im hcrit1 hcrit2 n
  rw [← hb_eq] at hsum
  have hd2 : 0 < (t - γ) ^ 2 := by rw [← hd_def]; positivity
  have h := reciprocalPairModel_slice_eq hγ hz
  rw [hconj] at h
  rw [h]
  exact coeff_reciprocalPairModel_pos (inv_pos.mpr hd2) hsum

/-- **Direct slice of the mixed triple.**  The direct slice `Ξ(t−ix)Ξ(t+ix)` of the zeros
`γ, γ ± iδ` is `(1 + α v)(1 + β v)(1 + β̄ v)` in `v = x²`, with `α = (t − γ)⁻²`,
`β = (t − γ − iδ)⁻²`.  Its `v`-coefficients are `α + β + β̄`, `α(β + β̄) + β β̄` and `α β β̄`;
with `d = t − γ`, `r = d² + δ²` they equal `(3d⁴ + δ⁴)/(d² r²)`, `(3d² − 2δ²)/(d² r²)` and
`1/(d² r²)`. -/
theorem directMixedCoeffs {t γ δ : ℝ} (hγ : t ≠ γ) :
    let α : ℂ := (((t - γ : ℝ) : ℂ) ^ 2)⁻¹
    let β : ℂ := (((t : ℂ) - (γ + δ * I)) ^ 2)⁻¹
    α + β + conj β = (((3 * (t - γ) ^ 4 + δ ^ 4) / ((t - γ) ^ 2 * ((t - γ) ^ 2 + δ ^ 2) ^ 2) : ℝ)
        : ℂ) ∧
      α * (β + conj β) + β * conj β
        = (((3 * (t - γ) ^ 2 - 2 * δ ^ 2) / ((t - γ) ^ 2 * ((t - γ) ^ 2 + δ ^ 2) ^ 2) : ℝ) : ℂ) := by
  intro α β
  set d : ℝ := t - γ with hd_def
  have hd0 : d ≠ 0 := sub_ne_zero.mpr hγ
  set r : ℝ := d ^ 2 + δ ^ 2 with hr_def
  have hr : 0 < r := by positivity
  have hrC : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr.ne'
  have hdC : (d : ℂ) ≠ 0 := ofReal_ne_zero.mpr hd0
  have hw : ((d : ℂ) - δ * I) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    exact hd0 this
  have hw' : ((d : ℂ) + δ * I) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    exact hd0 this
  have hprod : ((d : ℂ) - δ * I) * ((d : ℂ) + δ * I) = (r : ℂ) := by
    rw [hr_def]; push_cast; ring_nf; rw [I_sq]; ring
  have hβ : β = ((d : ℂ) + δ * I) ^ 2 / (r : ℂ) ^ 2 := by
    have e2 : (t : ℂ) - (γ + δ * I) = (d : ℂ) - δ * I := by rw [hd_def]; push_cast; ring
    show (((t : ℂ) - (γ + δ * I)) ^ 2)⁻¹ = _
    rw [e2, eq_div_iff (pow_ne_zero 2 hrC), ← hprod, mul_pow]
    field_simp
  have hβc : conj β = ((d : ℂ) - δ * I) ^ 2 / (r : ℂ) ^ 2 := by
    rw [hβ, map_div₀, map_pow, map_pow, map_add, map_mul, conj_ofReal, conj_ofReal, conj_ofReal,
      conj_I]
    ring
  have hα : α = ((d : ℂ) ^ 2)⁻¹ := by
    show (((t - γ : ℝ) : ℂ) ^ 2)⁻¹ = _
    rw [hd_def]
  rw [hα, hβc, hβ]
  constructor
  · push_cast
    field_simp
    rw [hr_def]
    push_cast
    ring_nf
    rw [I_sq]
    ring
  · have hI4 : I ^ 4 = 1 := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, I_sq]; norm_num
    push_cast
    field_simp
    rw [hr_def]
    push_cast
    ring_nf
    simp only [I_sq, hI4]
    ring

/-- **Exact detection interval of the direct slice in the mixed triple.**  The second
`v`-coefficient is negative exactly on `3 (t − γ)² < 2 δ²`; the other two are always positive. -/
theorem directMixedCoeff_two_neg_iff {t γ δ : ℝ} (hγ : t ≠ γ) :
    ((((t - γ : ℝ) : ℂ) ^ 2)⁻¹ * ((((t : ℂ) - (γ + δ * I)) ^ 2)⁻¹
        + conj ((((t : ℂ) - (γ + δ * I)) ^ 2)⁻¹))
      + (((t : ℂ) - (γ + δ * I)) ^ 2)⁻¹ * conj ((((t : ℂ) - (γ + δ * I)) ^ 2)⁻¹)).re < 0
      ↔ 3 * (t - γ) ^ 2 < 2 * δ ^ 2 := by
  rw [(directMixedCoeffs hγ).2, ofReal_re]
  have hd : 0 < (t - γ) ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2
    (sub_ne_zero.mpr hγ)))
  have hden : 0 < (t - γ) ^ 2 * ((t - γ) ^ 2 + δ ^ 2) ^ 2 := by positivity
  rw [div_neg_iff]
  constructor
  · rintro (⟨_, h⟩ | ⟨h, _⟩)
    · exact absurd h (not_lt.mpr hden.le)
    · linarith
  · intro h
    exact Or.inr ⟨by linarith, hden⟩

/-- **The threshold is at most `½`.**  For `b = −s` with `s > ½` the partial sum `1 + h_1(b, b̄)`
equals `1 − 2s < 0`. -/
theorem re_sum_pairHom_one_neg {s : ℝ} (hs : 1 / 2 < s) :
    (∑ m ∈ range 2, pairHom (-(s : ℂ)) (conj (-(s : ℂ))) m).re < 0 := by
  simp [sum_range_succ, pairHom]
  linarith

theorem coeff_one_reciprocalPairModel (α β β' : ℂ) :
    coeff 1 (reciprocalPairModel α β β') = α + β + β' := by
  rw [coeff_reciprocalPairModel]
  simp [sum_range_succ, pairHom]
  ring

/-- **Sharpness in slice coordinates.**  A pair `t ± iδ` at the height `t` itself is not shadowed
by a critical zero `γ` with `δ² < 2 (t − γ)²`: the first coefficient of the model is
`(t − γ)⁻² − 2δ⁻² < 0`. -/
theorem coeff_one_reciprocalPairModel_neg {t γ δ : ℝ} (hδ : δ ≠ 0)
    (h : δ ^ 2 < 2 * (t - γ) ^ 2) :
    (coeff 1 (reciprocalPairModel ((((t - γ : ℝ) : ℂ)) ^ 2)⁻¹
      (((t : ℂ) - (t + δ * I)) ^ 2)⁻¹ (((t : ℂ) - (t - δ * I)) ^ 2)⁻¹)).re < 0 := by
  have e1 : ((t : ℂ) - (t + δ * I)) ^ 2 = ((-δ ^ 2 : ℝ) : ℂ) := by
    push_cast; ring_nf; rw [I_sq]; ring
  have e2 : ((t : ℂ) - (t - δ * I)) ^ 2 = ((-δ ^ 2 : ℝ) : ℂ) := by
    push_cast; ring_nf; rw [I_sq]; ring
  rw [coeff_one_reciprocalPairModel, e1, e2]
  have e3 : ((((t - γ : ℝ) : ℂ)) ^ 2)⁻¹ + (((-δ ^ 2 : ℝ) : ℂ))⁻¹ + (((-δ ^ 2 : ℝ) : ℂ))⁻¹
      = ((((t - γ) ^ 2)⁻¹ - 2 * (δ ^ 2)⁻¹ : ℝ) : ℂ) := by
    push_cast; ring
  rw [e3, ofReal_re]
  have hδ2 : 0 < δ ^ 2 := by positivity
  have hd : 0 < (t - γ) ^ 2 := by linarith
  have : ((t - γ) ^ 2)⁻¹ < 2 * (δ ^ 2)⁻¹ := by
    rw [← div_eq_mul_inv, inv_lt_iff_one_lt_mul₀ hd, div_mul_eq_mul_div, one_lt_div hδ2]
    linarith
  linarith


theorem pairHom_add_period {b c : ℂ} (hb : b ≠ conj b) {k : ℕ} (hc : b ^ k = c)
    (hc' : conj b ^ k = c) (m : ℕ) :
    pairHom b (conj b) (m + k) = c * pairHom b (conj b) m := by
  apply mul_left_cancel₀ (sub_ne_zero.mpr hb)
  rw [sub_mul_pairHom, mul_left_comm, sub_mul_pairHom,
    show m + k + 1 = (m + 1) + k by ring, pow_add b (m + 1) k, pow_add (conj b) (m + 1) k, hc, hc']
  ring

theorem sum_pairHom_two_periods {b c : ℂ} (hb : b ≠ conj b) {k : ℕ} (hc : b ^ k = c)
    (hc' : conj b ^ k = c) :
    ∑ m ∈ range (k + k), pairHom b (conj b) m
      = (1 + c) * ∑ m ∈ range k, pairHom b (conj b) m := by
  rw [sum_range_add, add_mul, one_mul, mul_sum]
  congr 1
  refine sum_congr rfl fun m _ => ?_
  rw [add_comm k m, pairHom_add_period hb hc hc']

/-- If `b^{k+1}` is a real number below `−1`, some partial sum `Σ_{m ≤ n} h_m(b, b̄)` is not
positive: the sums over two consecutive periods differ by the factor `1 + b^{k+1} < 0`. -/
theorem exists_sum_pairHom_not_pos {b : ℂ} (hb : b ≠ conj b) {k : ℕ} {c : ℝ}
    (hc : b ^ (k + 1) = c) (hc1 : c < -1) :
    ∃ n, ¬ 0 < ∑ m ∈ range (n + 1), pairHom b (conj b) m := by
  have hc' : conj b ^ (k + 1) = c := by rw [← map_pow, hc, conj_ofReal]
  by_cases hS : 0 < ∑ m ∈ range (k + 1), pairHom b (conj b) m
  · refine ⟨2 * k + 1, fun hpos => ?_⟩
    rw [show 2 * k + 1 + 1 = (k + 1) + (k + 1) by ring, sum_pairHom_two_periods hb hc hc',
      show (1 : ℂ) + (c : ℂ) = ((1 + c : ℝ) : ℂ) by push_cast; ring] at hpos
    have hre := (pos_iff.mp hS).1
    have hre' := (pos_iff.mp hpos).1
    rw [re_ofReal_mul] at hre'
    have := mul_neg_of_neg_of_pos (by linarith : 1 + c < 0) hre
    linarith
  · exact ⟨k, hS⟩

theorem not_pos_ofReal_pow_mul {α : ℝ} (hα : 0 < α) {S : ℂ} (hS : ¬ 0 < S) (n : ℕ) :
    ¬ 0 < (α : ℂ) ^ n * S := by
  intro h
  apply hS
  rw [← ofReal_pow] at h
  obtain ⟨h1, h2⟩ := pos_iff.mp h
  rw [re_ofReal_mul] at h1
  rw [im_ofReal_mul] at h2
  have hαn : 0 < α ^ n := pow_pos hα n
  refine pos_iff.mpr ⟨pos_of_mul_pos_right h1 hαn.le, ?_⟩
  rcases mul_eq_zero.mp h2.symm with h | h
  · exact absurd h hαn.ne'
  · exact h.symm

theorem reciprocalPairModel_comm (α β β' : ℂ) :
    reciprocalPairModel α β β' = reciprocalPairModel α β' β := by
  unfold reciprocalPairModel; ring

/-- **A critical zero below the pair's ordinate leaves the pair visible.**  For `γ' < γ` there is
a height `t = γ + δ cot θ`, `θ = π/(2K)`, above the pair where `b = R e^{2iθ}` with `R > 1`, so
`b^K = −R^K < −1` and some reciprocal coefficient is not positive. -/
theorem exists_height_not_pos_of_lt {γ γ' δ : ℝ} (hδ : 0 < δ) (he : γ' < γ) :
    ∃ t : ℝ, t ≠ γ' ∧ ∃ n, ¬ 0 < coeff n (reciprocalPairModel ((((t - γ' : ℝ) : ℂ)) ^ 2)⁻¹
      (((t : ℂ) - (γ + δ * I)) ^ 2)⁻¹ (((t : ℂ) - (γ - δ * I)) ^ 2)⁻¹) := by
  set e : ℝ := γ - γ' with he_def
  have he0 : 0 < e := by rw [he_def]; linarith
  obtain ⟨k, hk⟩ := exists_nat_gt (Real.pi ^ 2 * δ / (8 * e))
  set K : ℕ := k + 2 with hK
  have hkK : (k : ℝ) + 2 = K := by rw [hK]; push_cast; ring
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hK0 : (0 : ℝ) < K := by rw [← hkK]; linarith
  set θ : ℝ := Real.pi / (2 * K) with hθ
  have hθ0 : 0 < θ := by rw [hθ]; positivity
  have hθ4 : θ ≤ Real.pi / 4 := by
    rw [hθ, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [Real.pi_pos]
  have hk' : Real.pi ^ 2 * δ < 8 * e * k := by
    rw [div_lt_iff₀ (by positivity)] at hk; linarith
  have hθs : θ * (Real.pi * δ) < 4 * e := by
    rw [hθ, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [Real.pi_pos]
  have hsin : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ0 (by linarith [Real.pi_pos])
  have hkey : δ < δ * Real.cos θ + e * Real.sin θ := by
    have h1 := Real.one_sub_sq_div_two_le_cos (x := θ)
    have h2 := Real.mul_le_sin hθ0.le (by linarith [Real.pi_pos])
    have h3 : δ * (θ ^ 2 / 2) < e * (2 / Real.pi * θ) := by
      rw [show e * (2 / Real.pi * θ) = (2 * e * θ) / Real.pi by ring, lt_div_iff₀ Real.pi_pos]
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_left h1 hδ.le, mul_le_mul_of_nonneg_left h2 he0.le]
  set t : ℝ := γ + δ * (Real.cos θ / Real.sin θ) with ht_def
  have htγ' : t - γ' = (δ * Real.cos θ + e * Real.sin θ) / Real.sin θ := by
    rw [ht_def, he_def]; field_simp; ring
  have hnum : 0 < δ * Real.cos θ + e * Real.sin θ := by linarith
  have ht : t ≠ γ' := by
    intro h
    have h0 : t - γ' = 0 := sub_eq_zero.mpr h
    rw [htγ'] at h0
    have : 0 < (δ * Real.cos θ + e * Real.sin θ) / Real.sin θ := div_pos hnum hsin
    linarith
  set R : ℝ := ((δ * Real.cos θ + e * Real.sin θ) / δ) ^ 2 with hR_def
  have hR1 : 1 < R := one_lt_pow₀ ((one_lt_div hδ).mpr hkey) two_ne_zero
  set w : ℂ := cexp ((θ : ℂ) * I) with hw
  have hw_ne : w ≠ 0 := Complex.exp_ne_zero _
  have hs : (Real.sin θ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hsin.ne'
  have hs' : Complex.sin (θ : ℂ) ≠ 0 := by rw [← ofReal_sin]; exact hs
  have hδC : (δ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hδ.ne'
  have hz_eq : (t : ℂ) - (γ + δ * I) = ((δ / Real.sin θ : ℝ) : ℂ) * w⁻¹ := by
    rw [hw, ← Complex.exp_neg, show -((θ : ℂ) * I) = ((-θ : ℝ) : ℂ) * I by push_cast; ring,
      Complex.exp_mul_I, ← ofReal_cos, ← ofReal_sin, Real.cos_neg, Real.sin_neg, ht_def]
    push_cast
    field_simp
    ring
  have hb : ((t : ℂ) - γ') ^ 2 / ((t : ℂ) - (γ + δ * I)) ^ 2 = (R : ℂ) * w ^ 2 := by
    rw [hz_eq, ← ofReal_sub, htγ', hR_def]
    push_cast
    field_simp
  have hw2K : w ^ (2 * K) = -1 := by
    rw [hw, ← Complex.exp_nat_mul]
    have h2K : ((2 * K : ℕ) : ℂ) * ((θ : ℂ) * I) = (Real.pi : ℂ) * I := by
      rw [hθ]; push_cast
      have hKC : (K : ℂ) ≠ 0 := by exact_mod_cast hK0.ne'
      field_simp
    rw [h2K, Complex.exp_pi_mul_I]
  set c : ℝ := -(R ^ K) with hc_def
  have hc : ((R : ℂ) * w ^ 2) ^ (k + 1 + 1) = (c : ℂ) := by
    rw [show k + 1 + 1 = K from rfl, mul_pow, ← pow_mul, hw2K, hc_def]
    push_cast
    ring
  have hc1 : c < -1 := by
    rw [hc_def]
    have := one_lt_pow₀ hR1 (show K ≠ 0 by rw [hK]; omega)
    linarith
  have hbim : ((R : ℂ) * w ^ 2).im ≠ 0 := by
    rw [im_ofReal_mul, hw, ← Complex.exp_nat_mul,
      show ((2 : ℕ) : ℂ) * ((θ : ℂ) * I) = ((2 * θ : ℝ) : ℂ) * I by push_cast; ring,
      Complex.exp_ofReal_mul_I_im]
    have h2 : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
    exact (mul_pos (by linarith) h2).ne'
  have hbconj : (R : ℂ) * w ^ 2 ≠ conj ((R : ℂ) * w ^ 2) :=
    fun h => hbim (conj_eq_iff_im.mp h.symm)
  obtain ⟨n, hn⟩ := exists_sum_pairHom_not_pos hbconj hc hc1
  refine ⟨t, ht, n, ?_⟩
  have hz : (t : ℂ) ≠ γ + δ * I := by
    intro h
    have := congrArg Complex.im h
    simp at this
    linarith
  have hconj : conj ((γ : ℂ) + δ * I) = γ - δ * I := by
    rw [map_add, map_mul, conj_ofReal, conj_ofReal, conj_I]; ring
  have h := reciprocalPairModel_slice_eq ht hz
  rw [hconj] at h
  rw [h, coeff_reciprocalPairModel_eq, hb]
  have hd2 : 0 < (t - γ') ^ 2 :=
    lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 (sub_ne_zero.mpr ht)))
  exact not_pos_ofReal_pow_mul (inv_pos.mpr hd2) hn n

theorem exists_height_not_pos_of_gt {γ γ' δ : ℝ} (hδ : 0 < δ) (he : γ < γ') :
    ∃ t : ℝ, t ≠ γ' ∧ ∃ n, ¬ 0 < coeff n (reciprocalPairModel ((((t - γ' : ℝ) : ℂ)) ^ 2)⁻¹
      (((t : ℂ) - (γ + δ * I)) ^ 2)⁻¹ (((t : ℂ) - (γ - δ * I)) ^ 2)⁻¹) := by
  obtain ⟨t, ht, n, hn⟩ :=
    exists_height_not_pos_of_lt (γ := γ) (γ' := 2 * γ - γ') hδ (by linarith)
  refine ⟨2 * γ - t, fun h => ht (by linarith), n, ?_⟩
  have e1 : ((((2 * γ - t) - γ' : ℝ) : ℂ)) ^ 2 = (((t - (2 * γ - γ') : ℝ) : ℂ)) ^ 2 := by
    push_cast; ring
  have e2 : (((2 * γ - t : ℝ) : ℂ) - (γ + δ * I)) ^ 2 = ((t : ℂ) - (γ - δ * I)) ^ 2 := by
    push_cast; ring
  have e3 : (((2 * γ - t : ℝ) : ℂ) - (γ - δ * I)) ^ 2 = ((t : ℂ) - (γ + δ * I)) ^ 2 := by
    push_cast; ring
  rw [e1, e2, e3, reciprocalPairModel_comm]
  exact hn

/-- **Global reciprocal blindness characterizes the exact mixed class.**  For the critical zero
`γ'` and the pair `γ ± iδ` (`δ > 0`), the three-zero reciprocal model is coefficient-positive at
every height `t ≠ γ'` if and only if `γ' = γ`. -/
theorem reciprocalPairModel_globally_pos_iff {γ γ' δ : ℝ} (hδ : 0 < δ) :
    (∀ t : ℝ, t ≠ γ' → ∀ n, 0 < coeff n (reciprocalPairModel ((((t - γ' : ℝ) : ℂ)) ^ 2)⁻¹
      (((t : ℂ) - (γ + δ * I)) ^ 2)⁻¹ (((t : ℂ) - (γ - δ * I)) ^ 2)⁻¹)) ↔ γ' = γ := by
  constructor
  · intro h
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · obtain ⟨t, ht, n, hn⟩ := exists_height_not_pos_of_lt hδ hlt
      exact hn (h t ht n)
    · obtain ⟨t, ht, n, hn⟩ := exists_height_not_pos_of_gt hδ hgt
      exact hn (h t ht n)
  · rintro rfl t ht n
    exact coeff_reciprocalPairModel_pos_mixed_all ht hδ.ne' n


/-- The even polynomial `f(t) = (t² − γ²)((t − γ)² + δ²)((t + γ)² + δ²)`, with zeros `±γ` and
`±γ ± iδ`. -/
def mixedSextic (γ δ : ℝ) (t : ℂ) : ℂ :=
  (t ^ 2 - (γ : ℂ) ^ 2) * ((t - γ) ^ 2 + (δ : ℂ) ^ 2) * ((t + γ) ^ 2 + (δ : ℂ) ^ 2)

theorem mixedSextic_eq_zero (γ δ : ℝ) : mixedSextic γ δ ((γ : ℂ) + δ * I) = 0 := by
  unfold mixedSextic
  rw [show ((γ : ℂ) + δ * I - γ) ^ 2 + (δ : ℂ) ^ 2 = 0 by ring_nf; rw [I_sq]; ring]
  ring

/-- `mixedSextic` as the product of its six linear factors. -/
theorem mixedSextic_eq_prod (γ δ : ℝ) (t : ℂ) :
    mixedSextic γ δ t = (t - γ) * (t - (-γ : ℝ)) * ((t - (γ + δ * I)) * (t - (γ - δ * I)))
      * ((t - ((-γ : ℝ) + δ * I)) * (t - ((-γ : ℝ) - δ * I))) := by
  have hI4 : I ^ 4 = 1 := by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, I_sq]; norm_num
  unfold mixedSextic
  push_cast
  ring_nf
  simp only [I_sq, hI4]
  ring

/-- Each zero `z` contributes `(t + σ − z)(t − σ − z) = (t − z)² (1 − σ²/(t − z)²)`. -/
theorem pair_factor_eq {t z σ : ℂ} (hz : t - z ≠ 0) :
    (t + σ - z) * (t - σ - z) = (t - z) ^ 2 * (1 - σ ^ 2 / (t - z) ^ 2) := by
  field_simp
  ring

/-- The slice of `mixedSextic` factors over its six zeros: `f(t+σ)f(t−σ) = f(t)² Π_z (1 −
σ²/(t − z)²)`, so its reciprocal is `f(t)⁻²` times the product of the two mixed-triple models in
`v = σ²` (`reciprocalPairModel_mul`). -/
theorem mixedSextic_slice_eq {t γ δ : ℝ} (h1 : t ≠ γ) (h2 : t ≠ -γ) (hδ : δ ≠ 0) (σ : ℂ) :
    mixedSextic γ δ (t + σ) * mixedSextic γ δ (t - σ) = mixedSextic γ δ t ^ 2 *
      ((1 - σ ^ 2 / ((t : ℂ) - γ) ^ 2) * (1 - σ ^ 2 / ((t : ℂ) - (-γ : ℝ)) ^ 2)
        * ((1 - σ ^ 2 / ((t : ℂ) - (γ + δ * I)) ^ 2) * (1 - σ ^ 2 / ((t : ℂ) - (γ - δ * I)) ^ 2))
        * ((1 - σ ^ 2 / ((t : ℂ) - ((-γ : ℝ) + δ * I)) ^ 2)
          * (1 - σ ^ 2 / ((t : ℂ) - ((-γ : ℝ) - δ * I)) ^ 2))) := by
  have hre : ∀ a : ℝ, t ≠ a → (t : ℂ) - a ≠ 0 := fun a ha => by
    rw [← ofReal_sub]; exact ofReal_ne_zero.mpr (sub_ne_zero.mpr ha)
  have him : ∀ a b : ℝ, b ≠ 0 → (t : ℂ) - (a + b * I) ≠ 0 := fun a b hb h => by
    have := congrArg Complex.im h
    simp at this
    exact hb (by linarith)
  have him' : ∀ a b : ℝ, b ≠ 0 → (t : ℂ) - (a - b * I) ≠ 0 := fun a b hb h => by
    have := congrArg Complex.im h
    simp at this
    exact hb this
  rw [mixedSextic_eq_prod γ δ ((t : ℂ) + σ), mixedSextic_eq_prod γ δ ((t : ℂ) - σ),
    mixedSextic_eq_prod γ δ (t : ℂ)]
  calc _ = ((t + σ - γ) * (t - σ - γ)) * ((t + σ - (-γ : ℝ)) * (t - σ - (-γ : ℝ)))
        * (((t + σ - (γ + δ * I)) * (t - σ - (γ + δ * I)))
          * ((t + σ - (γ - δ * I)) * (t - σ - (γ - δ * I))))
        * (((t + σ - ((-γ : ℝ) + δ * I)) * (t - σ - ((-γ : ℝ) + δ * I)))
          * ((t + σ - ((-γ : ℝ) - δ * I)) * (t - σ - ((-γ : ℝ) - δ * I)))) := by ring
    _ = _ := by
      rw [pair_factor_eq (hre γ h1), pair_factor_eq (hre (-γ) h2), pair_factor_eq (him γ δ hδ),
        pair_factor_eq (him' γ δ hδ), pair_factor_eq (him (-γ) δ hδ),
        pair_factor_eq (him' (-γ) δ hδ)]
      generalize 1 - σ ^ 2 / ((t : ℂ) - γ) ^ 2 = F₁
      generalize 1 - σ ^ 2 / ((t : ℂ) - (-γ : ℝ)) ^ 2 = F₂
      generalize 1 - σ ^ 2 / ((t : ℂ) - (γ + δ * I)) ^ 2 = F₃
      generalize 1 - σ ^ 2 / ((t : ℂ) - (γ - δ * I)) ^ 2 = F₄
      generalize 1 - σ ^ 2 / ((t : ℂ) - ((-γ : ℝ) + δ * I)) ^ 2 = F₅
      generalize 1 - σ ^ 2 / ((t : ℂ) - ((-γ : ℝ) - δ * I)) ^ 2 = F₆
      generalize (t : ℂ) - γ = A₁
      generalize (t : ℂ) - (-γ : ℝ) = A₂
      generalize (t : ℂ) - (γ + δ * I) = A₃
      generalize (t : ℂ) - (γ - δ * I) = A₄
      generalize (t : ℂ) - ((-γ : ℝ) + δ * I) = A₅
      generalize (t : ℂ) - ((-γ : ℝ) - δ * I) = A₆
      ring

/-- **Reciprocal coefficient positivity does not force real zeros.**  The reciprocal slice
`1/(f(t+σ)f(t−σ))` of `f = mixedSextic γ δ` is, up to the positive factor `f(t)⁻²`, the product of
the two mixed-triple models at `γ` and `−γ` (`reciprocalPairModel_mul`, `pair_factor_eq`).  At
every height `t ∉ {γ, −γ}` all its Taylor coefficients in `v = σ²` are positive, although `f` has
the non-real zeros `±γ ± iδ` (`mixedSextic_eq_zero`).  Coefficient-level reciprocal positivity at
every admissible height is therefore not a real-rootedness criterion for even real entire
functions; only total positivity is.  Compared with the octic countermodel
`GaloisForLFunctions.HTGeometry.reciprocalTPUpTo_one_shadowLift`, whose real zeros are double
(`evenRecipNonneg_doubleShadow`), simple real zeros suffice here: a simple critical zero at the
exact ordinate of the pair shadows it at every height (`coeff_reciprocalPairModel_pos_mixed_all`). -/
theorem coeff_mixedSextic_reciprocal_pos {t γ δ : ℝ} (h1 : t ≠ γ) (h2 : t ≠ -γ) (hδ : δ ≠ 0)
    (n : ℕ) :
    0 < coeff n
      (reciprocalPairModel ((((t - γ : ℝ) : ℂ)) ^ 2)⁻¹ (((t : ℂ) - (γ + δ * I)) ^ 2)⁻¹
          (((t : ℂ) - (γ - δ * I)) ^ 2)⁻¹
        * reciprocalPairModel ((((t - (-γ) : ℝ) : ℂ)) ^ 2)⁻¹
          (((t : ℂ) - ((-γ : ℝ) + δ * I)) ^ 2)⁻¹ (((t : ℂ) - ((-γ : ℝ) - δ * I)) ^ 2)⁻¹) := by
  rw [coeff_mul]
  refine Finset.sum_pos (fun p _ => mul_pos ?_ ?_) ⟨(0, n), by simp⟩
  · exact coeff_reciprocalPairModel_pos_mixed_all h1 hδ p.1
  · exact coeff_reciprocalPairModel_pos_mixed_all h2 hδ p.2

end

end RHTower
