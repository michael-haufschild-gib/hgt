import GaloisForLFunctions.HTGeometry.OffLinePairDetectionMaclaurinBound
import GaloisForLFunctions.RHTower.TuranNewtonFloor

/-!
# The detection order of a simple off-line pair is `σ − √σ + O(1)`

Let `x_1, …, x_N > 0`, `σ = Σ x_i` and `E(Y) = ∏ (1 + x_i Y)`.  At the ordinate `γ` of a simple
off-line pair `γ ± iδ` whose other zeros `γ_i` are real, the normalized slice in `Y = x²/δ²` is
`(1 − Y)² E(Y)` with `x_i = δ²/(γ − γ_i)²`.

**Theorem** (`add_sqrt_le_mass_of_coeff_nonneg`).  If the coefficients of `(1 − Y)² E` of orders
`1, …, J` are `≥ 0` and `J ≥ 2`, then `J + √J ≤ σ`.

So the first negative coefficient sits at an order `j` with `j ≤ 2` or `(j − 1) + √(j − 1) ≤ σ`
(`exists_first_coeff_neg_add_sqrt_le_mass`), i.e. `j ≤ σ − √σ + O(1)`.  The Poisson profile
`e_j = μ^j/j!` keeps every coefficient of order `≤ μ − √μ` nonnegative
(`poisson_secondDifference_nonneg`), so the bound is sharp up to `O(1)`.

Proof.  Write `a = e_{J−2}`, `b = e_{J−1}`, `c = e_J`.  Nonnegativity up to `J` gives first
differences `≥ 1` (`one_le_coeff_of_one_sub_X_mul_nonneg`), so `b ≥ a + 1`, `e_J > 0` and `J ≤ N`.
Convexity at `J` gives `c ≥ 2b − a`; Newton's floor `J·ac ≤ (J − 1)b²` (`newton_floor_finite`) then
gives `(J − 1)b² − 2J ab + J a² ≥ 0`.  With `s = √J`,

  `(J − 1)·((J − 1)b² − 2Jab + Ja²) = ((J − 1)b − (J + s)a)·((J − 1)b − (J − s)a)`,

and the second factor is positive because `b > a` and `s ≥ 1`.  Hence `(J − 1)b ≥ (J + s)a`, and
Maclaurin's `(J − 1)b ≤ σa` gives `J + s ≤ σ`.
-/

open Polynomial Finset

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The coefficients of `∏ (1 + x_i X)` are the elementary symmetric functions. -/
theorem coeff_prod_one_add_C_mul_X_eq_esymmFin {N : ℕ} (x : Fin N → ℝ) (j : ℕ) :
    (∏ i, (1 + C (x i) * X)).coeff j = esymmFin x j := by
  classical
  rw [Finset.prod_one_add, finsetSum_coeff, esymmFin, Finset.powersetCard_eq_filter,
    Finset.sum_filter]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.prod_mul_distrib, Finset.prod_const, ← map_prod, coeff_C_mul_X_pow]
  by_cases h : t.card = j
  · rw [if_pos h.symm, if_pos h]
  · rw [if_neg (Ne.symm h), if_neg h]

theorem coeff_one_sub_X_mul_succ (P : ℝ[X]) (k : ℕ) :
    ((1 - X) * P).coeff (k + 1) = P.coeff (k + 1) - P.coeff k := by
  rw [sub_mul, one_mul, coeff_sub, coeff_X_mul]

/-- **Sharp detection order.**  If the coefficients of `(1 − X)² ∏ (1 + x_i X)` (`x_i > 0`) of
orders `0, …, J` are `≥ 0` and `J ≥ 2`, then `J + √J ≤ Σ x_i`. -/
theorem add_sqrt_le_mass_of_coeff_nonneg {N : ℕ} (x : Fin N → ℝ) (hx : ∀ i, 0 < x i) {J : ℕ}
    (hJ : 2 ≤ J) (h : ∀ j ≤ J, 0 ≤ ((1 - X) ^ 2 * ∏ i, (1 + C (x i) * X)).coeff j) :
    (J : ℝ) + Real.sqrt J ≤ ∑ i, x i := by
  set E := ∏ i, (1 + C (x i) * X) with hE
  set σ := ∑ i, x i with hσ
  have h0 : E.coeff 0 = 1 := coeff_prod_one_add_C_mul_X_zero Finset.univ x
  have hnn : ∀ n, 0 ≤ E.coeff n :=
    coeff_prod_nonneg_of_forall _ _ fun i _ n => coeff_one_add_C_mul_X_nonneg (hx i).le n
  have h1 := one_le_coeff_of_one_sub_X_mul_nonneg (P := (1 - X) * E)
    (by rw [← pow_one (1 - X : ℝ[X]), coeff_one_sub_X_pow_mul_zero, h0])
    (fun i hi => by rw [← mul_assoc, ← pow_two]; exact h i hi)
  have hdiff : ∀ k, k + 1 ≤ J → E.coeff k + 1 ≤ E.coeff (k + 1) := by
    intro k hk
    have := h1 (k + 1) hk
    rw [coeff_one_sub_X_mul_succ] at this
    linarith
  have hJN : J ≤ N := by
    by_contra hc
    push Not at hc
    have hz : E.coeff J = 0 := by
      rw [coeff_prod_one_add_C_mul_X_eq_esymmFin, esymmFin,
        Finset.powersetCard_eq_empty.mpr (by simpa using hc)]
      simp
    have := hdiff (J - 1) (by omega)
    rw [show J - 1 + 1 = J by omega, hz] at this
    linarith [hnn (J - 1)]
  obtain ⟨n, rfl⟩ : ∃ n, J = n + 2 := ⟨J - 2, by omega⟩
  set a := E.coeff n with ha_def
  set b := E.coeff (n + 1) with hb_def
  set c := E.coeff (n + 2) with hc_def
  have ha : 0 < a := by
    rw [ha_def, coeff_prod_one_add_C_mul_X_eq_esymmFin]
    exact esymmFin_pos hx (by omega)
  have hab : a + 1 ≤ b := hdiff n (by omega)
  have hconv : 0 ≤ c - 2 * b + a := by
    have := h (n + 2) le_rfl
    rw [pow_two, mul_assoc, show n + 2 = (n + 1) + 1 by ring, coeff_one_sub_X_mul_succ,
      coeff_one_sub_X_mul_succ, coeff_one_sub_X_mul_succ] at this
    linarith
  have hnewton : ((n : ℝ) + 1 + 1) * (a * c) ≤ ((n : ℝ) + 1) * b ^ 2 := by
    have := newton_floor_finite x (n := n + 1) (by omega) (by omega)
    rw [← coeff_prod_one_add_C_mul_X_eq_esymmFin, ← coeff_prod_one_add_C_mul_X_eq_esymmFin,
      ← coeff_prod_one_add_C_mul_X_eq_esymmFin, show n + 1 - 1 = n by omega] at this
    push_cast at this
    exact this
  have hmac : ((n : ℝ) + 1) * b ≤ σ * a :=
    maclaurin_coeff_prod_one_add_C_mul_X Finset.univ x (fun i _ => (hx i).le) n
  set s := Real.sqrt ((n : ℝ) + 2) with hs_def
  have hs2 : s ^ 2 = (n : ℝ) + 2 := Real.sq_sqrt (by positivity)
  have hs1 : 1 ≤ s := by
    rw [hs_def, show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hq : 0 ≤ ((n : ℝ) + 1) * b ^ 2 - 2 * ((n : ℝ) + 2) * a * b + ((n : ℝ) + 2) * a ^ 2 := by
    have hc' : 2 * b - a ≤ c := by linarith
    have : ((n : ℝ) + 2) * a * (2 * b - a) ≤ ((n : ℝ) + 2) * a * c :=
      mul_le_mul_of_nonneg_left hc' (by positivity)
    nlinarith
  have hfac : ((n : ℝ) + 1) * (((n : ℝ) + 1) * b ^ 2 - 2 * ((n : ℝ) + 2) * a * b +
      ((n : ℝ) + 2) * a ^ 2) = (((n : ℝ) + 1) * b - ((n : ℝ) + 2 + s) * a) *
        (((n : ℝ) + 1) * b - ((n : ℝ) + 2 - s) * a) := by
    linear_combination a ^ 2 * hs2
  have hQ : 0 < ((n : ℝ) + 1) * b - ((n : ℝ) + 2 - s) * a := by nlinarith
  have hP : 0 ≤ ((n : ℝ) + 1) * b - ((n : ℝ) + 2 + s) * a := by
    have hprod : 0 ≤ (((n : ℝ) + 1) * b - ((n : ℝ) + 2 + s) * a) *
        (((n : ℝ) + 1) * b - ((n : ℝ) + 2 - s) * a) := by
      rw [← hfac]
      positivity
    by_contra hneg
    push Not at hneg
    have : (((n : ℝ) + 1) * b - ((n : ℝ) + 2 + s) * a) *
        (((n : ℝ) + 1) * b - ((n : ℝ) + 2 - s) * a) < 0 := mul_neg_of_neg_of_pos hneg hQ
    linarith
  have hfinal : ((n : ℝ) + 2 + s) * a ≤ σ * a := by linarith
  have : (n : ℝ) + 2 + s ≤ σ := le_of_mul_le_mul_right hfinal ha
  push_cast
  linarith

/-- **First negative coefficient.**  For `x_i > 0`, the polynomial `(1 − X)² ∏ (1 + x_i X)` has a
first negative coefficient, at an order `j ≥ 1` with `j ≤ 2` or `(j − 1) + √(j − 1) ≤ Σ x_i`. -/
theorem exists_first_coeff_neg_add_sqrt_le_mass {N : ℕ} (x : Fin N → ℝ) (hx : ∀ i, 0 < x i) :
    ∃ j : ℕ, 1 ≤ j ∧ ((1 - X) ^ 2 * ∏ i, (1 + C (x i) * X)).coeff j < 0 ∧
      (∀ i < j, 0 ≤ ((1 - X) ^ 2 * ∏ i, (1 + C (x i) * X)).coeff i) ∧
      (j ≤ 2 ∨ ((j : ℝ) - 1) + Real.sqrt ((j : ℝ) - 1) ≤ ∑ i, x i) := by
  classical
  have hex : ∃ j, ((1 - X) ^ 2 * ∏ i, (1 + C (x i) * X)).coeff j < 0 := by
    obtain ⟨j, -, -, hneg⟩ := exists_coeff_neg_one_sub_X_pow_mul_prod Finset.univ x
      (fun i _ => (hx i).le) (m := 1) le_rfl
    exact ⟨j, by simpa using hneg⟩
  set j := Nat.find hex with hj
  have hneg : ((1 - X) ^ 2 * ∏ i, (1 + C (x i) * X)).coeff j < 0 := Nat.find_spec hex
  have hmin : ∀ i < j, 0 ≤ ((1 - X) ^ 2 * ∏ i, (1 + C (x i) * X)).coeff i := fun i hi =>
    not_lt.mp (Nat.find_min hex hi)
  have h0 : ((1 - X) ^ 2 * ∏ i, (1 + C (x i) * X)).coeff 0 = 1 := by
    rw [coeff_one_sub_X_pow_mul_zero, coeff_prod_one_add_C_mul_X_zero]
  have hj1 : 1 ≤ j := by
    by_contra hc
    have : j = 0 := by omega
    rw [this, h0] at hneg
    norm_num at hneg
  refine ⟨j, hj1, hneg, hmin, ?_⟩
  by_cases hj2 : j ≤ 2
  · exact Or.inl hj2
  · right
    have key := add_sqrt_le_mass_of_coeff_nonneg x hx (J := j - 1) (by omega)
      (fun i hi => hmin i (by omega))
    have hcast : ((j - 1 : ℕ) : ℝ) = (j : ℝ) - 1 := by
      rw [Nat.cast_sub hj1]
      norm_num
    rw [hcast] at key
    exact key

end

end GaloisForLFunctions.HTGeometry
