import GaloisForLFunctions.HTGeometry.UltrametricResolventHT
import GaloisForLFunctions.HTGeometry.UltrametricResolventSusceptibility

/-!
# Shell expansions

The Taylor expansion at the origin of an inverse shell power `1/(x + a)^m` is the rescaled
negative binomial series.  Reading its coefficients identifies the expansion of the two-shell
resolvent defect with its displayed coefficient sequence.
-/

namespace GaloisForLFunctions.HTGeometry

open PowerSeries

open scoped RatFunc

noncomputable section

variable {k : Type*} [Field k]

private theorem rescale_neg_one_one_sub_X :
    PowerSeries.rescale (-1 : k) (1 - PowerSeries.X) = 1 + PowerSeries.X := by
  rw [map_sub, map_one, PowerSeries.rescale_X]
  simp

/-- The negative binomial series of the first shell. -/
def shellSeries (a : k) (m : ℕ) : PowerSeries k :=
  PowerSeries.rescale (-a) ((PowerSeries.invOneSubPow k m).val)

theorem coeff_shellSeries (a : k) {m : ℕ} (hm : 0 < m) (n : ℕ) :
    PowerSeries.coeff n (shellSeries a m)
      = (-a) ^ n * ((m - 1 + n).choose (m - 1) : k) := by
  rw [shellSeries, PowerSeries.coeff_rescale,
    PowerSeries.invOneSubPow_val_eq_mk_sub_one_add_choose_of_pos (S := k) (d := m) hm,
    PowerSeries.coeff_mk]

theorem invOneSubPow_val_mul (m : ℕ) :
    ((PowerSeries.invOneSubPow k m).val) * (1 - PowerSeries.X) ^ m = 1 := by
  cases m with
  | zero => simp [PowerSeries.invOneSubPow_zero]
  | succ d => exact (PowerSeries.invOneSubPow k (d + 1)).val_inv

theorem shellSeries_mul (a : k) (m : ℕ) :
    shellSeries a m * (1 + PowerSeries.C a * PowerSeries.X) ^ m = 1 := by
  have h := invOneSubPow_val_mul (k := k) m
  have hres := congrArg (PowerSeries.rescale (-a)) h
  rw [map_mul, map_one, map_pow, map_sub, map_one, PowerSeries.rescale_X] at hres
  rw [shellSeries, show (1 + PowerSeries.C a * PowerSeries.X : PowerSeries k)
      = 1 - PowerSeries.C (-a) * PowerSeries.X from by
    rw [map_neg]
    ring]
  exact hres

/-! ## The Laurent expansion of an inverse shell power -/

theorem algebraMap_shell_poly (a : k) (m : ℕ) :
    algebraMap (RatFunc k) (LaurentSeries k)
        (((RatFunc.X : RatFunc k) + algebraMap k (RatFunc k) a) ^ m)
      = ((((PowerSeries.X + PowerSeries.C a) ^ m : PowerSeries k)) : LaurentSeries k) := by
  have hX : algebraMap (RatFunc k) (LaurentSeries k) (RatFunc.X : RatFunc k)
      = ((PowerSeries.X : PowerSeries k) : LaurentSeries k) := by
    rw [algebraMap_ratFuncX, laurentCoord]
    refine HahnSeries.coeff_inj.mp (funext fun n => ?_)
    rw [PowerSeries.coeff_coe]
    by_cases h : n < 0
    · rw [HahnSeries.coeff_single_of_ne (by omega : n ≠ 1), if_pos h]
    · rw [if_neg h]
      by_cases h1 : n = 1
      · subst h1
        rw [HahnSeries.coeff_single_same]
        simp
      · rw [HahnSeries.coeff_single_of_ne h1]
        have hne : n.natAbs ≠ 1 := by omega
        simp [PowerSeries.coeff_X, hne]
  have hC : algebraMap (RatFunc k) (LaurentSeries k) (algebraMap k (RatFunc k) a)
      = (((PowerSeries.C a : PowerSeries k)) : LaurentSeries k) := by
    rw [algebraMap_const_laurentSeries]
    refine HahnSeries.coeff_inj.mp (funext fun n => ?_)
    rw [PowerSeries.coeff_coe]
    by_cases h : n < 0
    · rw [HahnSeries.coeff_single_of_ne (by omega : n ≠ 0), if_pos h]
    · rw [if_neg h]
      by_cases h0 : n = 0
      · subst h0
        rw [HahnSeries.coeff_single_same]
        simp
      · rw [HahnSeries.coeff_single_of_ne h0]
        have hne : n.natAbs ≠ 0 := by omega
        simp [PowerSeries.coeff_C, hne]
  rw [map_pow, map_add, hX, hC, ← map_add, ← map_pow]

theorem algebraMap_inv_shell (a : k) (ha : a ≠ 0) (m : ℕ) :
    algebraMap (RatFunc k) (LaurentSeries k)
        (1 / ((RatFunc.X : RatFunc k) + algebraMap k (RatFunc k) a) ^ m)
      = (((PowerSeries.C (a⁻¹ ^ m) * shellSeries (a⁻¹) m : PowerSeries k)) : LaurentSeries k) := by
  have hfac : (PowerSeries.C (a⁻¹ ^ m) * shellSeries (a⁻¹) m)
      * (PowerSeries.X + PowerSeries.C a) ^ m = 1 := by
    have hsplit : ((PowerSeries.X + PowerSeries.C a : PowerSeries k)) ^ m
        = PowerSeries.C (a ^ m) * (1 + PowerSeries.C (a⁻¹) * PowerSeries.X) ^ m := by
      rw [map_pow, ← mul_pow]
      congr 1
      rw [mul_add, mul_one, ← mul_assoc, ← map_mul, mul_inv_cancel₀ ha, map_one, one_mul]
      ring
    rw [hsplit, show (PowerSeries.C (a⁻¹ ^ m) * shellSeries (a⁻¹) m)
        * (PowerSeries.C (a ^ m) * (1 + PowerSeries.C (a⁻¹) * PowerSeries.X) ^ m)
        = (PowerSeries.C (a⁻¹ ^ m) * PowerSeries.C (a ^ m))
          * (shellSeries (a⁻¹) m * (1 + PowerSeries.C (a⁻¹) * PowerSeries.X) ^ m) from by ring,
      shellSeries_mul, mul_one, ← map_mul, ← mul_pow, inv_mul_cancel₀ ha, one_pow, map_one]
  have hmul : (((PowerSeries.C (a⁻¹ ^ m) * shellSeries (a⁻¹) m : PowerSeries k))
        : LaurentSeries k)
      * algebraMap (RatFunc k) (LaurentSeries k)
        (((RatFunc.X : RatFunc k) + algebraMap k (RatFunc k) a) ^ m) = 1 := by
    rw [algebraMap_shell_poly, ← map_mul, hfac, map_one]
  rw [map_div₀, map_one]
  exact (eq_one_div_of_mul_eq_one_left hmul).symm

/-! ## The expansion of the two-shell defect -/

theorem coeff_coe_powerSeries_nat (f : PowerSeries k) (n : ℕ) :
    ((f : LaurentSeries k)).coeff (n : ℤ) = PowerSeries.coeff n f := by
  rw [PowerSeries.coeff_coe, if_neg (by omega : ¬ ((n : ℤ)) < 0),
    show ((n : ℤ)).natAbs = n from by omega]

set_option maxHeartbeats 1000000 in
/-- **The Taylor coefficients of the two-shell defect.** -/
theorem coeff_algebraMap_resolventDefect [CharZero k] {p : ℕ} (hp : 1 < p) {m : ℕ} (hm : 0 < m)
    (n : ℕ) :
    (algebraMap (RatFunc k) (LaurentSeries k) (resolventDefect (k := k) p m)).coeff (n : ℤ)
      = (-1 : k) ^ n * (((m - 1 + n).choose (m - 1) : ℕ) : k)
        * ((((p : k)) - 2) + (((p : k))⁻¹) ^ (m + n)) := by
  have hpk : ((p : k)) ≠ 0 := natCast_ne_zero_of_one_lt hp
  have hone : ((RatFunc.X : RatFunc k) + 1) = (RatFunc.X : RatFunc k) + algebraMap k (RatFunc k) 1
      := by rw [map_one]
  have hinv : ∀ a : k, a ≠ 0 → ((algebraMap (RatFunc k) (LaurentSeries k)
      (((RatFunc.X : RatFunc k) + algebraMap k (RatFunc k) a) ^ m))⁻¹)
      = (((PowerSeries.C (a⁻¹ ^ m) * shellSeries (a⁻¹) m : PowerSeries k)) : LaurentSeries k) := by
    intro a ha
    rw [← algebraMap_inv_shell a ha m, map_div₀, map_one, one_div]
  rw [resolventDefect_eq, map_add, HahnSeries.coeff_add, map_div₀, map_div₀, map_one, hone,
    div_eq_mul_inv, div_eq_mul_inv, one_mul, hinv 1 one_ne_zero, hinv ((p : k)) hpk,
    algebraMap_const_laurentSeries, ← HahnSeries.C_apply, coeff_C_mul_hahn,
    coeff_coe_powerSeries_nat, coeff_coe_powerSeries_nat, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_C_mul, coeff_shellSeries _ hm, coeff_shellSeries _ hm, inv_one,
    show ((-(((p : k))⁻¹)) ^ n) = (-1 : k) ^ n * (((p : k))⁻¹) ^ n from by
      rw [← neg_one_mul, mul_pow],
    show ((-(1 : k)) ^ n) = (-1 : k) ^ n from rfl, pow_add]
  ring

/-! ## The Taylor coefficients of the resolvent trace -/

theorem coeff_algebraMap_X_pow_mul (j : ℕ) (f : LaurentSeries k) (n : ℤ) :
    (algebraMap (RatFunc k) (LaurentSeries k) ((RatFunc.X : RatFunc k) ^ j) * f).coeff n
      = f.coeff (n - j) := by
  rw [map_pow, algebraMap_ratFuncX, laurentCoord, HahnSeries.single_pow, one_pow,
    show (j • (1 : ℤ)) = (j : ℤ) from by simp, HahnSeries.coeff_single_mul, one_mul]

set_option maxHeartbeats 1000000 in
/-- **The Taylor coefficients of the resolvent trace** are the defect coefficients divided by the
scale resonance. -/
theorem coeff_resolventTrace [CharZero k] {p : ℕ} (hp : 1 < p) {m : ℕ} (hm : 1 < m) (n : ℤ) :
    (resolventTrace (k := k) p m).coeff n
      = (algebraMap (RatFunc k) (LaurentSeries k) (resolventDefect (k := k) p m)).coeff n
        / (1 - (((p : k))⁻¹) ^ (n + ((m : ℤ) - 1))) := by
  have hgerm : resolventGerm (k := k) p m
      = algebraMap (RatFunc k) (LaurentSeries k) ((RatFunc.X : RatFunc k) ^ (m - 1))
        * resolventTrace p m := resolventGerm_eq_trace_mul p m
  have hcoeff : (resolventGerm (k := k) p m).coeff (n + ((m : ℤ) - 1))
      = (resolventTrace (k := k) p m).coeff n := by
    rw [hgerm, coeff_algebraMap_X_pow_mul]
    congr 1
    have : ((m - 1 : ℕ) : ℤ) = (m : ℤ) - 1 := by
      push_cast [Nat.cast_sub (by omega : 1 ≤ m)]
      ring
    rw [this]
    ring
  have hinc : (algebraMap (RatFunc k) (LaurentSeries k)
      (resolventIncrement (k := k) p m)).coeff (n + ((m : ℤ) - 1))
      = -(algebraMap (RatFunc k) (LaurentSeries k)
        (resolventDefect (k := k) p m)).coeff n := by
    rw [resolventIncrement_eq, map_neg, map_mul, HahnSeries.coeff_neg,
      mul_comm (algebraMap (RatFunc k) (LaurentSeries k) (resolventDefect (k := k) p m)),
      coeff_algebraMap_X_pow_mul]
    congr 2
    have : ((m - 1 : ℕ) : ℤ) = (m : ℤ) - 1 := by
      push_cast [Nat.cast_sub (by omega : 1 ≤ m)]
      ring
    rw [this]
    ring
  rw [← hcoeff, resolventGerm, coeff_qDifferenceSolution, HahnSeries.coeff_neg, hinc, one_mul]
  ring

set_option maxHeartbeats 1000000 in
/-- **The displayed Taylor coefficient**: the germ selected by the scale-defect equation has the
coefficients recorded by the formal susceptibility. -/
theorem coeff_resolventTrace_eq_susceptibility {p m : ℕ} (hp : 1 < p) (hm : 1 < m) (n : ℕ) :
    (resolventTrace (k := ℚ) p m).coeff (n : ℤ)
      = ultrametricResolventCoefficient p m n := by
  have hpQ : ((p : ℚ)) ≠ 0 := natCast_ne_zero_of_one_lt hp
  have hchoose : (m - 1 + n).choose (m - 1) = (m + n - 1).choose n := by
    have h1 : m - 1 + n = m + n - 1 := by omega
    rw [h1, ← Nat.choose_symm (by omega : m - 1 ≤ m + n - 1)]
    congr 1
    omega
  have hexp : ((n : ℤ) + ((m : ℤ) - 1)) = ((n + m - 1 : ℕ) : ℤ) := by
    push_cast [Nat.cast_sub (by omega : 1 ≤ n + m)]
    ring
  rw [coeff_resolventTrace hp hm, coeff_algebraMap_resolventDefect hp (by omega : 0 < m),
    ultrametricResolventCoefficient, ultrametricResolventBoundaryCoefficient,
    ultrametricResolventCoefficientScale, hchoose, hexp, zpow_natCast]
  have hden : (((p : ℚ))⁻¹) ^ (n + m - 1) = (p : ℚ) / (p : ℚ) ^ (m + n) := by
    rw [inv_pow, eq_div_iff (pow_ne_zero _ hpQ), inv_mul_eq_div, div_eq_iff (pow_ne_zero _ hpQ),
      ← pow_succ']
    congr 1
    omega
  have hnum : (((p : ℚ)) - 2) + (((p : ℚ))⁻¹) ^ (m + n) = (p : ℚ) - 2 + 1 / (p : ℚ) ^ (m + n) := by
    rw [inv_pow, one_div]
  rw [hden, hnum]

end

end GaloisForLFunctions.HTGeometry
