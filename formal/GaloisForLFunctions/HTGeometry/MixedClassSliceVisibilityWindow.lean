import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Complex.BigOperators
import Mathlib.Tactic.LinearCombination

/-!
# Visibility window of a mixed critical/off-line class in slice coefficients

Let `f(z) = zⁿ (z² + 1)`: a real zero of multiplicity `n` at the ordinate `0` of the non-real pair
`±i`.  Its horizontal slice at height `t` is a polynomial in `y = x²` (`mixedSliceProduct_eq_eval`):

  `f(t + ix) f(t − ix) = (y + u)ⁿ (y² + 2(u − 1)y + (u + 1)²)`,   `u = t²`,

and `(y + u)ⁿ (y² + 2(u − 1)y + (u + 1)²) = (y + u)ⁿ⁺² − 2(y + u)ⁿ⁺¹ + (4u + 1)(y + u)ⁿ`.

**Theorem** (`forall_height_coeff_mixedSlicePoly_nonneg_iff`).  For `j ≤ n + 1` the coefficient of
`y^j` is `≥ 0` at every height `t` iff `n + 2 ≤ (2(n + 1 − j) + 1)²`.

So the non-real pair is invisible, at every height, to all orders `j` with
`(2(n + 1 − j) + 1)² ≥ n + 2`.  It is visible exactly at the orders `j = n + 1 − b` with
`(2b + 1)² < n + 2`, a block of about `√n / 2` consecutive orders ending at `n + 1`.  At the
ordinate itself the first nonzero coefficient is `y^n` (value `1`) and the next is `y^{n+1}` (value
`−2`) (`coeff_mixedSlicePoly_zero_height`).  Moving off the ordinate therefore detects the pair
`⌊(√(n + 2) − 1)/2⌋` orders earlier, and no earlier.

Proof.  For `j ≤ n` the coefficient is `u^{n−j} Q_j(u)` with
`Q_j(u) = C(n+2, j)u² + (4C(n, j) − 2C(n+1, j))u + C(n, j)`.  A real quadratic with positive outer
coefficients is `≥ 0` on `[0, ∞)` iff its middle coefficient is `≥ 0` or its discriminant is `≤ 0`
(`quadratic_nonneg_on_Ici_iff`).  With `b = n + 1 − j`, `b C(n+1, j) = (n + 1) C(n, j)` and
`(b + 1) C(n+2, j) = (n + 2) C(n+1, j)`, so the discriminant condition reads
`j (4b² + 3b − j) ≥ 0`.  The coefficient of `y^{n+1}` is `(n + 2)u − 2`, negative at `u = 0`.

**Bounded order never certifies real zeros** (`bounded_order_slice_nonneg_with_nonreal_zero`).  For
every `K` and every finite family of reals `a_i`, the polynomial `z^{2K}(z² + 1) ∏ (z² − a_i²)` has the
non-real zero `i`, yet all its slice coefficients of order `≤ K` in `y` are `≥ 0` at every height.  The
slice of `z² − a²` has nonnegative coefficients (`coeff_realZeroSlicePoly_nonneg`), and multiplying by
a polynomial with nonnegative coefficients keeps nonnegative low-order coefficients nonnegative.
-/

open Polynomial Complex Finset

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The slice of `zⁿ(z² + 1)` at a height `t`, with `u = t²`, in the variable `y = x²`. -/
def mixedSlicePoly (n : ℕ) (u : ℝ) : ℝ[X] :=
  (X + C u) ^ n * (X ^ 2 + C (2 * (u - 1)) * X + C ((u + 1) ^ 2))

/-- The slice of `z² − a²` at a height `t`, with `u = t²`, in the variable `y = x²`. -/
def realZeroSlicePoly (a u : ℝ) : ℝ[X] :=
  X ^ 2 + C (2 * (u + a ^ 2)) * X + C ((u - a ^ 2) ^ 2)

/-- The slice identity for `zⁿ(z² + 1)`. -/
theorem mixedSliceProduct_eq_eval (n : ℕ) (t x : ℝ) :
    ((t : ℂ) + x * I) ^ n * (((t : ℂ) + x * I) ^ 2 + 1) *
        (((t : ℂ) - x * I) ^ n * (((t : ℂ) - x * I) ^ 2 + 1)) =
      (((mixedSlicePoly n (t ^ 2)).eval (x ^ 2) : ℝ) : ℂ) := by
  have hI : I ^ 2 = -1 := I_sq
  have h1 : ((t : ℂ) + x * I) * ((t : ℂ) - x * I) = ((t ^ 2 + x ^ 2 : ℝ) : ℂ) := by
    push_cast
    linear_combination (-(x : ℂ) ^ 2) * hI
  have h2 : (((t : ℂ) + x * I) ^ 2 + 1) * (((t : ℂ) - x * I) ^ 2 + 1) =
      (((x ^ 2) ^ 2 + 2 * (t ^ 2 - 1) * x ^ 2 + (t ^ 2 + 1) ^ 2 : ℝ) : ℂ) := by
    push_cast
    linear_combination (2 * ((t : ℂ) ^ 2 + 1 - (x : ℂ) ^ 2) * (x : ℂ) ^ 2 +
      (x : ℂ) ^ 4 * (I ^ 2 + 1) - 4 * (t : ℂ) ^ 2 * (x : ℂ) ^ 2) * hI
  rw [mul_mul_mul_comm, ← mul_pow, h1, h2, ← ofReal_pow, ← ofReal_mul]
  congr 1
  simp only [mixedSlicePoly, eval_mul, eval_pow, eval_add, eval_X, eval_C]
  ring

/-- The slice identity for `z² − a²`. -/
theorem realZeroSliceProduct_eq_eval (a t x : ℝ) :
    (((t : ℂ) + x * I) ^ 2 - (a : ℂ) ^ 2) * (((t : ℂ) - x * I) ^ 2 - (a : ℂ) ^ 2) =
      (((realZeroSlicePoly a (t ^ 2)).eval (x ^ 2) : ℝ) : ℂ) := by
  have hI : I ^ 2 = -1 := I_sq
  simp only [realZeroSlicePoly, eval_add, eval_mul, eval_pow, eval_X, eval_C]
  push_cast
  linear_combination (2 * ((t : ℂ) ^ 2 - (a : ℂ) ^ 2 - (x : ℂ) ^ 2) * (x : ℂ) ^ 2 +
    (x : ℂ) ^ 4 * (I ^ 2 + 1) - 4 * (t : ℂ) ^ 2 * (x : ℂ) ^ 2) * hI

theorem mixedSlicePoly_eq (n : ℕ) (u : ℝ) :
    mixedSlicePoly n u =
      (X + C u) ^ (n + 2) - C 2 * (X + C u) ^ (n + 1) + C (4 * u + 1) * (X + C u) ^ n := by
  unfold mixedSlicePoly
  simp only [map_add, map_sub, map_mul, map_pow, map_one, map_ofNat]
  ring

theorem coeff_mixedSlicePoly (n j : ℕ) (u : ℝ) :
    (mixedSlicePoly n u).coeff j =
      u ^ (n + 2 - j) * ((n + 2).choose j : ℝ) - 2 * (u ^ (n + 1 - j) * ((n + 1).choose j : ℝ)) +
        (4 * u + 1) * (u ^ (n - j) * (n.choose j : ℝ)) := by
  rw [mixedSlicePoly_eq, coeff_add, coeff_sub, coeff_C_mul, coeff_C_mul, coeff_X_add_C_pow,
    coeff_X_add_C_pow, coeff_X_add_C_pow]

/-- **At the ordinate** the slice starts at `y^n` with coefficient `1`, followed by `−2 y^{n+1}`. -/
theorem coeff_mixedSlicePoly_zero_height (n : ℕ) :
    (∀ j < n, (mixedSlicePoly n 0).coeff j = 0) ∧ (mixedSlicePoly n 0).coeff n = 1 ∧
      (mixedSlicePoly n 0).coeff (n + 1) = -2 := by
  refine ⟨fun j hj => ?_, ?_, ?_⟩
  · rw [coeff_mixedSlicePoly, zero_pow (by omega), zero_pow (by omega), zero_pow (by omega)]
    ring
  · rw [coeff_mixedSlicePoly, show n + 2 - n = 2 by omega, show n + 1 - n = 1 by omega,
      Nat.sub_self, Nat.choose_self]
    norm_num
  · rw [coeff_mixedSlicePoly, show n + 2 - (n + 1) = 1 by omega, Nat.sub_self,
      show n - (n + 1) = 0 by omega, Nat.choose_self, Nat.choose_succ_self]
    norm_num

/-- A real quadratic `A u² + B u + D` with `A, D > 0` is `≥ 0` on `[0, ∞)` iff `B ≥ 0` or
`B² ≤ 4AD`. -/
theorem quadratic_nonneg_on_Ici_iff {A B D : ℝ} (hA : 0 < A) (hD : 0 < D) :
    (∀ u : ℝ, 0 ≤ u → 0 ≤ A * u ^ 2 + B * u + D) ↔ (0 ≤ B ∨ B ^ 2 ≤ 4 * A * D) := by
  constructor
  · intro h
    by_contra hc
    push Not at hc
    obtain ⟨hB, hdisc⟩ := hc
    have hu : 0 ≤ -B / (2 * A) := div_nonneg (by linarith) (by linarith)
    have hval := h _ hu
    have e : A * (-B / (2 * A)) ^ 2 + B * (-B / (2 * A)) + D = D - B ^ 2 / (4 * A) := by
      field_simp
      ring
    rw [e, sub_nonneg, div_le_iff₀ (by linarith)] at hval
    linarith
  · rintro (hB | hdisc) u hu
    · exact add_nonneg (add_nonneg (mul_nonneg hA.le (sq_nonneg u)) (mul_nonneg hB hu)) hD.le
    · have h4 : 0 ≤ 4 * A * (A * u ^ 2 + B * u + D) := by
        nlinarith [sq_nonneg (2 * A * u + B)]
      by_contra hneg
      push Not at hneg
      have : 4 * A * (A * u ^ 2 + B * u + D) < 0 := mul_neg_of_pos_of_neg (by positivity) hneg
      linarith

/-- The discriminant condition of `Q_j` in closed form. -/
theorem mixedSlice_quadratic_condition_iff {n j : ℕ} (hj : j ≤ n) :
    (0 ≤ 4 * (n.choose j : ℝ) - 2 * ((n + 1).choose j : ℝ) ∨
        (4 * (n.choose j : ℝ) - 2 * ((n + 1).choose j : ℝ)) ^ 2 ≤
          4 * ((n + 2).choose j : ℝ) * (n.choose j : ℝ)) ↔
      j ≤ 4 * (n + 1 - j) ^ 2 + 3 * (n + 1 - j) := by
  set b := n + 1 - j with hbdef
  have hb : n + 1 = j + b := by omega
  have hb1 : 1 ≤ b := by omega
  have r1 := Nat.choose_mul_succ_eq n j
  have r2 := Nat.choose_mul_succ_eq (n + 1) j
  rw [show n + 1 - j = b by omega] at r1
  rw [show n + 1 + 1 - j = b + 1 by omega] at r2
  have hc : (0 : ℝ) < (n.choose j : ℝ) := by exact_mod_cast Nat.choose_pos hj
  set c : ℝ := (n.choose j : ℝ) with hcdef
  set c1 : ℝ := ((n + 1).choose j : ℝ) with hc1def
  set c2 : ℝ := ((n + 2).choose j : ℝ) with hc2def
  have hB : (1 : ℝ) ≤ b := by exact_mod_cast hb1
  have hBpos : (0 : ℝ) < b := by linarith
  have hnb : (n : ℝ) + 1 = j + b := by exact_mod_cast hb
  have hr1 : c * ((n : ℝ) + 1) = c1 * b := by
    have := congrArg (Nat.cast : ℕ → ℝ) r1
    push_cast at this
    exact this
  have hr2 : c1 * ((n : ℝ) + 1 + 1) = c2 * ((b : ℝ) + 1) := by
    have := congrArg (Nat.cast : ℕ → ℝ) r2
    push_cast at this
    exact this
  have hc1 : c1 = ((j : ℝ) + b) * c / b := by
    field_simp
    rw [← hnb]
    linarith
  have hc2 : c2 = ((j : ℝ) + b + 1) * ((j : ℝ) + b) * c / ((b : ℝ) * (b + 1)) := by
    field_simp
    have : c1 * ((n : ℝ) + 1 + 1) = c2 * ((b : ℝ) + 1) := hr2
    rw [hc1, show (n : ℝ) + 1 + 1 = j + b + 1 by linarith] at this
    field_simp at this
    linarith
  have hmid : 4 * c - 2 * c1 = 2 * c / b * ((b : ℝ) - j) := by
    rw [hc1]
    field_simp
    ring
  have hdisc : 4 * c2 * c - (4 * c - 2 * c1) ^ 2 =
      4 * c ^ 2 / ((b : ℝ) ^ 2 * (b + 1)) * ((j : ℝ) * (4 * b ^ 2 + 3 * b - j)) := by
    rw [hc2, hc1]
    field_simp
    ring
  have hpos1 : 0 < 2 * c / (b : ℝ) := by positivity
  have hpos2 : 0 < 4 * c ^ 2 / ((b : ℝ) ^ 2 * (b + 1)) := by positivity
  have hJ : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hcast : (j ≤ 4 * b ^ 2 + 3 * b) ↔ (j : ℝ) ≤ 4 * (b : ℝ) ^ 2 + 3 * b := by
    constructor
    · intro h
      exact_mod_cast h
    · intro h
      exact_mod_cast h
  rw [hcast]
  constructor
  · rintro (h | h)
    · rw [hmid, mul_nonneg_iff_of_pos_left hpos1, sub_nonneg] at h
      nlinarith
    · have h' : 0 ≤ 4 * c2 * c - (4 * c - 2 * c1) ^ 2 := by linarith
      rw [hdisc, mul_nonneg_iff_of_pos_left hpos2] at h'
      rcases hJ.eq_or_lt with h0 | hJpos
      · rw [← h0]
        positivity
      · have := (mul_nonneg_iff_of_pos_left hJpos).mp h'
        linarith
  · intro hjr
    right
    have : 0 ≤ 4 * c ^ 2 / ((b : ℝ) ^ 2 * (b + 1)) * ((j : ℝ) * (4 * b ^ 2 + 3 * b - j)) :=
      mul_nonneg hpos2.le (mul_nonneg hJ (by linarith))
    rw [← hdisc] at this
    linarith

/-- **Visibility window, `u`-form.**  For `j ≤ n + 1` the coefficient of `y^j` in the slice of
`zⁿ(z² + 1)` is `≥ 0` for every `u = t² ≥ 0` iff `j ≤ 4b² + 3b`, `b = n + 1 − j`. -/
theorem forall_coeff_mixedSlicePoly_nonneg_iff {n j : ℕ} (hj : j ≤ n + 1) :
    (∀ u : ℝ, 0 ≤ u → 0 ≤ (mixedSlicePoly n u).coeff j) ↔
      j ≤ 4 * (n + 1 - j) ^ 2 + 3 * (n + 1 - j) := by
  rcases Nat.lt_or_ge n j with hnj | hjn
  · have hj' : j = n + 1 := by omega
    subst hj'
    rw [Nat.sub_self]
    constructor
    · intro h
      have h0 := (coeff_mixedSlicePoly_zero_height n).2.2
      have := h 0 le_rfl
      rw [h0] at this
      norm_num at this
    · intro h
      simp at h
  · have hQ : ∀ u : ℝ, (mixedSlicePoly n u).coeff j = u ^ (n - j) *
        (((n + 2).choose j : ℝ) * u ^ 2 +
          (4 * (n.choose j : ℝ) - 2 * ((n + 1).choose j : ℝ)) * u + (n.choose j : ℝ)) := by
      intro u
      rw [coeff_mixedSlicePoly, show n + 2 - j = (n - j) + 2 by omega,
        show n + 1 - j = (n - j) + 1 by omega, pow_add, pow_add]
      ring
    have hc : (0 : ℝ) < n.choose j := by exact_mod_cast Nat.choose_pos hjn
    have hc2 : (0 : ℝ) < (n + 2).choose j := by exact_mod_cast Nat.choose_pos (by omega)
    rw [← mixedSlice_quadratic_condition_iff hjn, ← quadratic_nonneg_on_Ici_iff hc2 hc]
    constructor
    · intro h u hu
      rcases hu.eq_or_lt with h0 | hu'
      · subst h0
        simp
      · have := h u hu
        rw [hQ] at this
        exact (mul_nonneg_iff_of_pos_left (pow_pos hu' _)).mp this
    · intro h u hu
      rw [hQ]
      exact mul_nonneg (pow_nonneg hu _) (h u hu)

/-- **Visibility window.**  For `j ≤ n + 1` the coefficient of `y^j` in the slice of `zⁿ(z² + 1)`
is `≥ 0` at every height iff `n + 2 ≤ (2(n + 1 − j) + 1)²`. -/
theorem forall_height_coeff_mixedSlicePoly_nonneg_iff {n j : ℕ} (hj : j ≤ n + 1) :
    (∀ t : ℝ, 0 ≤ (mixedSlicePoly n (t ^ 2)).coeff j) ↔ n + 2 ≤ (2 * (n + 1 - j) + 1) ^ 2 := by
  have e : (∀ t : ℝ, 0 ≤ (mixedSlicePoly n (t ^ 2)).coeff j) ↔
      ∀ u : ℝ, 0 ≤ u → 0 ≤ (mixedSlicePoly n u).coeff j := by
    constructor
    · intro h u hu
      have := h (Real.sqrt u)
      rwa [Real.sq_sqrt hu] at this
    · intro h t
      exact h _ (sq_nonneg t)
  rw [e, forall_coeff_mixedSlicePoly_nonneg_iff hj]
  have hb : n + 1 = j + (n + 1 - j) := by omega
  generalize n + 1 - j = b at hb ⊢
  constructor <;> intro h <;> nlinarith [hb]

theorem coeff_realZeroSlicePoly_nonneg (a : ℝ) {u : ℝ} (hu : 0 ≤ u) (j : ℕ) :
    0 ≤ (realZeroSlicePoly a u).coeff j := by
  have h1 : 0 ≤ 2 * (u + a ^ 2) := by nlinarith [sq_nonneg a]
  have h0 : 0 ≤ (u - a ^ 2) ^ 2 := sq_nonneg _
  simp only [realZeroSlicePoly, coeff_add, coeff_X_pow, coeff_C_mul, coeff_X, coeff_C]
  split_ifs <;> linarith

/-- Nonnegative low-order coefficients survive multiplication by a polynomial with nonnegative
coefficients. -/
theorem coeff_mul_nonneg_of_low_order {P Q : ℝ[X]} {K : ℕ} (hP : ∀ j ≤ K, 0 ≤ P.coeff j)
    (hQ : ∀ j, 0 ≤ Q.coeff j) {j : ℕ} (hj : j ≤ K) : 0 ≤ (P * Q).coeff j := by
  rw [coeff_mul]
  refine Finset.sum_nonneg fun x hx => mul_nonneg (hP _ ?_) (hQ _)
  have := Finset.mem_antidiagonal.mp hx
  omega

theorem coeff_prod_nonneg_of_forall {ι : Type*} (s : Finset ι) (Q : ι → ℝ[X])
    (hQ : ∀ i ∈ s, ∀ j, 0 ≤ (Q i).coeff j) (j : ℕ) : 0 ≤ (∏ i ∈ s, Q i).coeff j := by
  revert j
  refine Finset.prod_induction Q (fun P => ∀ j, 0 ≤ P.coeff j) ?_ ?_ hQ
  · intro P R hP hR j
    rw [coeff_mul]
    exact Finset.sum_nonneg fun x _ => mul_nonneg (hP _) (hR _)
  · intro j
    rw [coeff_one]
    split_ifs <;> norm_num

/-- The slice identity for `zⁿ(z² + 1) ∏ (z² − a_i²)`. -/
theorem mixedSlice_mul_realZeros_eq_eval {ι : Type*} (s : Finset ι) (a : ι → ℝ) (n : ℕ)
    (t x : ℝ) :
    ((t : ℂ) + x * I) ^ n * (((t : ℂ) + x * I) ^ 2 + 1) *
          (∏ i ∈ s, (((t : ℂ) + x * I) ^ 2 - (a i : ℂ) ^ 2)) *
        (((t : ℂ) - x * I) ^ n * (((t : ℂ) - x * I) ^ 2 + 1) *
          (∏ i ∈ s, (((t : ℂ) - x * I) ^ 2 - (a i : ℂ) ^ 2))) =
      (((mixedSlicePoly n (t ^ 2) * ∏ i ∈ s, realZeroSlicePoly (a i) (t ^ 2)).eval (x ^ 2) : ℝ) :
        ℂ) := by
  rw [eval_mul, eval_prod, ofReal_mul, ofReal_prod, ← mixedSliceProduct_eq_eval,
    Finset.prod_congr rfl fun i _ => (realZeroSliceProduct_eq_eval (a i) t x).symm,
    Finset.prod_mul_distrib]
  ring

/-- **Bounded-order slice positivity never certifies real zeros.**  For every `K` and every finite
family of reals `a_i`, `z^{2K}(z² + 1) ∏ (z² − a_i²)` vanishes at `i`, yet its slice coefficients of
order `≤ K` in `y = x²` are `≥ 0` at every height. -/
theorem bounded_order_slice_nonneg_with_nonreal_zero {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (K : ℕ) :
    I ^ (2 * K) * (I ^ 2 + 1) * (∏ i ∈ s, (I ^ 2 - (a i : ℂ) ^ 2)) = 0 ∧
      ∀ j ≤ K, ∀ t : ℝ,
        0 ≤ (mixedSlicePoly (2 * K) (t ^ 2) * ∏ i ∈ s, realZeroSlicePoly (a i) (t ^ 2)).coeff j := by
  refine ⟨by rw [I_sq]; ring, fun j hj t => ?_⟩
  refine coeff_mul_nonneg_of_low_order (K := j) (fun i hi => ?_)
    (coeff_prod_nonneg_of_forall s _ fun i _ => coeff_realZeroSlicePoly_nonneg (a i) (sq_nonneg t))
    le_rfl
  have hi' : i ≤ 2 * K + 1 := by omega
  refine (forall_height_coeff_mixedSlicePoly_nonneg_iff hi').2 ?_ t
  have hb : K + 1 ≤ 2 * K + 1 - i := by omega
  generalize 2 * K + 1 - i = b at hb ⊢
  nlinarith [hb]

end

end GaloisForLFunctions.HTGeometry
