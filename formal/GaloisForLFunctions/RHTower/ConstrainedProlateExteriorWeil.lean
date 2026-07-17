import GaloisForLFunctions.RHTower.EulerFisherCurvature

open scoped BigOperators

namespace GaloisForLFunctions

/-!
# Universal coefficient in the constrained-prolate exterior Weil law

The constrained-prolate paper theorem isolates the archimedean leading coefficient

```text
D_arch = (8 / (11π)) * ∑_{k ≥ 1} arcsin(1 / k) / k.
```

This file formalizes that coefficient without assuming any prolate asymptotic, Weil-operator
positivity, spectral floor, or Riemann-hypothesis statement.  The series is represented with
zero-based Lean indexing, so index `n` is the paper index `k = n + 1`.

The formal conclusions are:

* every summand is nonnegative;
* Jordan's sine inequality bounds the summand by a constant multiple of `1 / (n + 1)²`;
* the series is summable and has strictly positive sum;
* `D_arch > 0`, with the stronger explicit lower bound `4 / 11 ≤ D_arch`.

The lower bound is already supplied by the `k = 1` summand.
-/

noncomputable section

/-- The `k = n + 1` summand in
`∑_{k ≥ 1} arcsin(1 / k) / k`. -/
def constrainedProlateArchSeriesTerm (n : ℕ) : ℝ :=
  Real.arcsin (1 / ((n : ℝ) + 1)) / ((n : ℝ) + 1)

/-- Jordan's sine inequality, transported through `arcsin` on `[0, 1]`. -/
lemma arcsin_le_pi_div_two_mul {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.arcsin x ≤ (Real.pi / 2) * x := by
  have ha0 : 0 ≤ Real.arcsin x := Real.arcsin_nonneg.mpr hx0
  have ha1 : Real.arcsin x ≤ Real.pi / 2 := Real.arcsin_le_pi_div_two x
  have hsin := Real.mul_le_sin ha0 ha1
  rw [Real.sin_arcsin (by linarith) hx1] at hsin
  calc
    Real.arcsin x = (Real.pi / 2) * (2 / Real.pi * Real.arcsin x) := by
      field_simp [Real.pi_ne_zero]
    _ ≤ (Real.pi / 2) * x :=
      mul_le_mul_of_nonneg_left hsin (by positivity)

/-- Every summand in the universal archimedean coefficient is nonnegative. -/
lemma constrainedProlateArchSeriesTerm_nonneg (n : ℕ) :
    0 ≤ constrainedProlateArchSeriesTerm n := by
  unfold constrainedProlateArchSeriesTerm
  exact div_nonneg (Real.arcsin_nonneg.mpr (by positivity)) (by positivity)

/-- The coefficient series is dominated termwise by a shifted inverse-square series. -/
lemma constrainedProlateArchSeriesTerm_le (n : ℕ) :
    constrainedProlateArchSeriesTerm n ≤
      (Real.pi / 2) * (1 / (((n : ℝ) + 1) ^ 2)) := by
  have hn : 0 < (n : ℝ) + 1 := by positivity
  have hx0 : 0 ≤ 1 / ((n : ℝ) + 1) := by positivity
  have hx1 : 1 / ((n : ℝ) + 1) ≤ 1 := by
    exact (div_le_one hn).2 (by norm_num)
  have h := arcsin_le_pi_div_two_mul hx0 hx1
  unfold constrainedProlateArchSeriesTerm
  calc
    Real.arcsin (1 / ((n : ℝ) + 1)) / ((n : ℝ) + 1)
        ≤ ((Real.pi / 2) * (1 / ((n : ℝ) + 1))) / ((n : ℝ) + 1) :=
          div_le_div_of_nonneg_right h hn.le
    _ = (Real.pi / 2) * (1 / (((n : ℝ) + 1) ^ 2)) := by field_simp

/-- Absolute convergence of the coefficient series. -/
lemma summable_constrainedProlateArchSeriesTerm :
    Summable constrainedProlateArchSeriesTerm := by
  have hs : Summable (fun n : ℕ => (1 : ℝ) / (((n : ℝ) + 1) ^ 2)) := by
    have h := (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
    exact ((summable_nat_add_iff 1).mpr h).congr (fun n => by push_cast; ring)
  have hscaled : Summable (fun n : ℕ =>
      (Real.pi / 2) * (1 / (((n : ℝ) + 1) ^ 2))) := hs.mul_left _
  exact hscaled.of_nonneg_of_le constrainedProlateArchSeriesTerm_nonneg
    constrainedProlateArchSeriesTerm_le

/-- The unscaled coefficient series is strictly positive. -/
lemma tsum_constrainedProlateArchSeriesTerm_pos :
    0 < ∑' n : ℕ, constrainedProlateArchSeriesTerm n := by
  refine summable_constrainedProlateArchSeriesTerm.tsum_pos
    constrainedProlateArchSeriesTerm_nonneg 0 ?_
  simp [constrainedProlateArchSeriesTerm, Real.arcsin_one, Real.pi_pos]

/-- The first summand alone gives the lower bound `π / 2`. -/
lemma pi_div_two_le_tsum_constrainedProlateArchSeriesTerm :
    Real.pi / 2 ≤ ∑' n : ℕ, constrainedProlateArchSeriesTerm n := by
  have h := Summable.sum_le_tsum {0}
    (fun n _ => constrainedProlateArchSeriesTerm_nonneg n)
    summable_constrainedProlateArchSeriesTerm
  simpa [constrainedProlateArchSeriesTerm, Real.arcsin_one] using h

/-- The universal leading coefficient from the constrained-prolate exterior Weil law. -/
def constrainedProlateArchConstant : ℝ :=
  (8 / (11 * Real.pi)) * ∑' n : ℕ, constrainedProlateArchSeriesTerm n

/-- The universal constrained-prolate archimedean coefficient is strictly positive. -/
theorem constrainedProlateArchConstant_pos : 0 < constrainedProlateArchConstant := by
  unfold constrainedProlateArchConstant
  exact mul_pos (by positivity) tsum_constrainedProlateArchSeriesTerm_pos

/-- An explicit unconditional lower bound for the universal coefficient.
It uses only the positive `k = 1` summand. -/
theorem constrainedProlateArchConstant_ge_four_div_eleven :
    (4 : ℝ) / 11 ≤ constrainedProlateArchConstant := by
  unfold constrainedProlateArchConstant
  calc
    (4 : ℝ) / 11 = (8 / (11 * Real.pi)) * (Real.pi / 2) := by
      field_simp [Real.pi_ne_zero]
      norm_num
    _ ≤ (8 / (11 * Real.pi)) *
        ∑' n : ℕ, constrainedProlateArchSeriesTerm n :=
      mul_le_mul_of_nonneg_left pi_div_two_le_tsum_constrainedProlateArchSeriesTerm (by positivity)

/-! ## Lower-order radial prime coefficient -/

/-- The divisor collapse used by the radial prime diagonal: removing the divisor `1` does not
change the von Mangoldt divisor sum, so the remaining charge is exactly `log k`. -/
theorem constrainedProlate_sum_vonMangoldt_divisors_ge_two (k : ℕ) :
    ∑ m ∈ k.divisors.filter (fun m => 2 ≤ m), ArithmeticFunction.vonMangoldt m =
      Real.log k := by
  rw [← ArithmeticFunction.vonMangoldt_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro m hm
  by_cases h2 : 2 ≤ m
  · simp [h2]
  · have hm1 : m = 1 := by
      have hmpos := Nat.pos_of_mem_divisors hm
      omega
    simp [hm1, ArithmeticFunction.vonMangoldt_apply_one]

/-- The `k = n + 2` summand in the lower-order radial prime coefficient
`∑_{k ≥ 2} log(k) arcsin(1 / k) / k`. -/
def constrainedProlatePrimeSeriesTerm (n : ℕ) : ℝ :=
  let k : ℝ := ((n + 2 : ℕ) : ℝ)
  Real.log k / k * Real.arcsin (1 / k)

/-- Every summand in the radial prime coefficient is nonnegative. -/
lemma constrainedProlatePrimeSeriesTerm_nonneg (n : ℕ) :
    0 ≤ constrainedProlatePrimeSeriesTerm n := by
  unfold constrainedProlatePrimeSeriesTerm
  have hk : (1 : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ n + 2 by omega)
  exact mul_nonneg (div_nonneg (Real.log_nonneg hk) (by positivity))
    (Real.arcsin_nonneg.mpr (by positivity))

/-- The logarithmically weighted inverse-square series is summable. -/
lemma summable_log_nat_div_sq :
    Summable (fun n : ℕ => Real.log n / (n : ℝ) ^ 2) := by
  have h := RHTower.summable_abs_log_natCast_pow_mul_rpow_neg 1 2 (by norm_num)
  apply h.congr
  intro n
  rcases n with _ | n
  · simp
  have hn : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  have hlog : 0 ≤ Real.log ((n + 1 : ℕ) : ℝ) :=
    Real.log_nonneg (by norm_num)
  rw [abs_of_nonneg hlog, pow_one, Real.rpow_neg hn.le]
  rw [show ((n + 1 : ℕ) : ℝ) ^ (2 : ℝ) = ((n + 1 : ℕ) : ℝ) ^ (2 : ℕ) by
    exact Real.rpow_natCast _ 2]
  field_simp

/-- The radial prime series is dominated by a logarithmically weighted inverse-square series. -/
lemma constrainedProlatePrimeSeriesTerm_le (n : ℕ) :
    constrainedProlatePrimeSeriesTerm n ≤
      (Real.pi / 2) * (Real.log ((n + 2 : ℕ) : ℝ) / (((n + 2 : ℕ) : ℝ) ^ 2)) := by
  let k : ℝ := ((n + 2 : ℕ) : ℝ)
  have hk : 0 < k := by
    dsimp [k]
    exact_mod_cast (show 0 < n + 2 by omega)
  have hk_one : 1 ≤ k := by
    dsimp [k]
    exact_mod_cast (show 1 ≤ n + 2 by omega)
  have hk1 : 1 / k ≤ 1 := (div_le_one hk).2 hk_one
  have ha := arcsin_le_pi_div_two_mul (show 0 ≤ 1 / k by positivity) hk1
  have hlog : 0 ≤ Real.log k / k :=
    div_nonneg (Real.log_nonneg hk_one) hk.le
  unfold constrainedProlatePrimeSeriesTerm
  change Real.log k / k * Real.arcsin (1 / k) ≤ _
  calc
    Real.log k / k * Real.arcsin (1 / k)
        ≤ Real.log k / k * ((Real.pi / 2) * (1 / k)) :=
      mul_le_mul_of_nonneg_left ha hlog
    _ = (Real.pi / 2) * (Real.log k / k ^ 2) := by field_simp

/-- Absolute convergence of the lower-order radial prime coefficient. -/
lemma summable_constrainedProlatePrimeSeriesTerm :
    Summable constrainedProlatePrimeSeriesTerm := by
  have hs : Summable (fun n : ℕ =>
      Real.log ((n + 2 : ℕ) : ℝ) / (((n + 2 : ℕ) : ℝ) ^ 2)) := by
    exact ((summable_nat_add_iff 2).mpr summable_log_nat_div_sq).congr (fun n => by simp)
  have hscaled : Summable (fun n : ℕ =>
      (Real.pi / 2) *
        (Real.log ((n + 2 : ℕ) : ℝ) / (((n + 2 : ℕ) : ℝ) ^ 2))) := hs.mul_left _
  exact hscaled.of_nonneg_of_le constrainedProlatePrimeSeriesTerm_nonneg
    constrainedProlatePrimeSeriesTerm_le

/-- The unscaled lower-order radial prime series is strictly positive. -/
lemma tsum_constrainedProlatePrimeSeriesTerm_pos :
    0 < ∑' n : ℕ, constrainedProlatePrimeSeriesTerm n := by
  refine summable_constrainedProlatePrimeSeriesTerm.tsum_pos
    constrainedProlatePrimeSeriesTerm_nonneg 0 ?_
  unfold constrainedProlatePrimeSeriesTerm
  exact mul_pos (div_pos (Real.log_pos (by norm_num)) (by norm_num))
    (Real.arcsin_pos.mpr (by norm_num))

/-- The signed lower-order radial prime coefficient from equation (13) of the paper card. -/
def constrainedProlatePrimeConstant : ℝ :=
  -(16 / (11 * Real.pi)) * ∑' n : ℕ, constrainedProlatePrimeSeriesTerm n

/-- The lower-order radial prime coefficient is strictly negative. -/
theorem constrainedProlatePrimeConstant_neg : constrainedProlatePrimeConstant < 0 := by
  unfold constrainedProlatePrimeConstant
  exact mul_neg_of_neg_of_pos (neg_neg_of_pos (by positivity))
    tsum_constrainedProlatePrimeSeriesTerm_pos

end

end GaloisForLFunctions
