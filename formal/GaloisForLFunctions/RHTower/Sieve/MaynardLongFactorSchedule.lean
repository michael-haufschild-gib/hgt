import GaloisForLFunctions.RHTower.Sieve.MaynardLongFactorExclusion

/-!
# Fixed derivative-test schedule for every canonical long factor

At Route T's canonical threshold, `mu >= 4/3` makes every long factor satisfy
`N >= T0^(1/45)`.  This one inequality supports the uniform derivative order `k0=47`: eventually
`46! <= N`, while `y <= 2*T0` lies below the order-47 upper window.  Long-factor exclusion is
therefore reduced to the lower derivative window and one explicit polylogarithmic absorption.
-/

noncomputable section
namespace RHTower.Sieve

open Finset ArithmeticFunction

theorem dyadic_length_ge_fortyFive_root_of_maynard_long
    {T0 t mu : ℝ} (hT0 : 1 < T0) (hmu : 4 / 3 ≤ mu)
    (ht : t = mu / 120) {q : ℕ}
    (hlong : 2 * t < dyadicLogExponent T0 q) :
    T0 ^ (1 / 45 : ℝ) ≤ (((2 ^ q : ℕ) : ℝ)) := by
  have halpha : (1 / 45 : ℝ) < dyadicLogExponent T0 q := by
    rw [ht] at hlong
    linarith
  have hpow := (Real.strictMono_rpow_of_base_gt_one hT0).monotone halpha.le
  rwa [rpow_dyadicLogExponent hT0 q] at hpow

theorem maynard_long_fixedOrder_high_window
    {T0 t mu y : ℝ} (hT0 : 1 < T0) (hmu : 4 / 3 ≤ mu)
    (ht : t = mu / 120) {q : ℕ}
    (hlong : 2 * t < dyadicLogExponent T0 q)
    (hy : y ≤ 2 * T0) :
    y ≤ 2 * Real.pi * 2 ^ (47 : ℕ) *
      (((2 ^ q : ℕ) : ℝ)) ^ ((47 : ℕ) - 1) *
      (((2 ^ q : ℕ) : ℝ)) ^ (-(1 / 3) : ℝ) := by
  let N : ℝ := (((2 ^ q : ℕ) : ℝ))
  have hNbase : T0 ^ (1 / 45 : ℝ) ≤ N :=
    dyadic_length_ge_fortyFive_root_of_maynard_long hT0 hmu ht hlong
  have hbase0 : 0 ≤ T0 ^ (1 / 45 : ℝ) := Real.rpow_nonneg (by linarith) _
  have hpow45 := pow_le_pow_left₀ hbase0 hNbase 45
  have hcollapse : (T0 ^ (1 / 45 : ℝ)) ^ (45 : ℕ) = T0 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith : 0 ≤ T0)]
    norm_num
  rw [hcollapse] at hpow45
  have hN1 : 1 ≤ N := by
    have hroot1 : 1 ≤ T0 ^ (1 / 45 : ℝ) :=
      Real.one_le_rpow hT0.le (by norm_num)
    exact hroot1.trans hNbase
  have hshape : N ^ (45 : ℕ) ≤ N ^ (46 : ℕ) * N ^ (-(1 / 3) : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast,
      ← Real.rpow_add (by positivity : 0 < N)]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
  have hconstant : (2 : ℝ) ≤ 2 * Real.pi * 2 ^ (47 : ℕ) := by
    nlinarith [Real.pi_gt_three]
  calc
    y ≤ 2 * T0 := hy
    _ ≤ 2 * N ^ (45 : ℕ) := mul_le_mul_of_nonneg_left hpow45 (by norm_num)
    _ ≤ 2 * (N ^ (46 : ℕ) * N ^ (-(1 / 3) : ℝ)) :=
      mul_le_mul_of_nonneg_left hshape (by norm_num)
    _ ≤ (2 * Real.pi * 2 ^ (47 : ℕ)) *
        (N ^ (46 : ℕ) * N ^ (-(1 / 3) : ℝ)) := by
      exact mul_le_mul_of_nonneg_right hconstant (by positivity)
    _ = 2 * Real.pi * 2 ^ (47 : ℕ) * N ^ ((47 : ℕ) - 1) *
        N ^ (-(1 / 3) : ℝ) := by norm_num; ring

theorem maynard_long_fixedOrder_factorial
    {T0 t mu : ℝ} (hT0 : 1 < T0) (hmu : 4 / 3 ≤ mu)
    (ht : t = mu / 120) {q : ℕ}
    (hlong : 2 * t < dyadicLogExponent T0 q)
    (hfactorial : ((Nat.factorial 46 : ℕ) : ℝ) ≤ T0 ^ (1 / 45 : ℝ)) :
    Nat.factorial ((47 : ℕ) - 1) ≤ 2 ^ q := by
  have hNbase :=
    dyadic_length_ge_fortyFive_root_of_maynard_long hT0 hmu ht hlong
  have hreal : ((Nat.factorial 46 : ℕ) : ℝ) ≤ (((2 ^ q : ℕ) : ℝ)) :=
    hfactorial.trans hNbase
  exact_mod_cast hreal

/-- Under the ambient `mu <= 19/9` scale, every literal zeta/logarithm factor lies below
`T0^(19/9)`.  A fixed `T0^(8/27)` reserve therefore supplies the lower derivative window. -/
theorem maynard_zeta_log_factor_low_window
    {L X k : ℕ} (c : HeathBrownBoxChoice L X k)
    (j : HeathBrownBoxFactorIndex k c.m)
    (hkind : heathBrownBoxFactorKind k c.m j = .zeta ∨
      heathBrownBoxFactorKind k c.m j = .log)
    (hX : 1 ≤ X) {T0 mu y : ℝ} (hT0 : 1 < T0)
    (hmu : mu ≤ 19 / 9)
    (hXscale : (X : ℝ) ≤ T0 ^ mu)
    (hy : T0 ≤ y) (hpi : 8 * Real.pi ≤ T0 ^ (8 / 27 : ℝ)) :
    8 * Real.pi *
        (((2 ^ heathBrownBoxFactorExponent c.a c.b c.q j : ℕ) : ℝ)) ^
          ((1 : ℝ) / 3) ≤ y := by
  let N : ℝ :=
    (((2 ^ heathBrownBoxFactorExponent c.a c.b c.q j : ℕ) : ℝ))
  have hq := c.factorExponent_le_log_X_of_zeta_or_log j hkind
  have hNnat : 2 ^ heathBrownBoxFactorExponent c.a c.b c.q j ≤ X :=
    (Nat.pow_le_pow_right (by norm_num) hq).trans
      (Nat.pow_log_le_self 2 (by omega : X ≠ 0))
  have hNX : N ≤ (X : ℝ) := by
    dsimp [N]
    exact_mod_cast hNnat
  have hN0 : 0 ≤ N := by dsimp [N]; positivity
  have hX0 : 0 ≤ (X : ℝ) := by positivity
  have hthird : N ^ ((1 : ℝ) / 3) ≤ (X : ℝ) ^ ((1 : ℝ) / 3) :=
    Real.rpow_le_rpow hN0 hNX (by norm_num)
  have hmu3 : mu / 3 ≤ 19 / 27 := by linarith
  have hT00 : 0 ≤ T0 := by linarith
  have hXpow : (X : ℝ) ^ ((1 : ℝ) / 3) ≤ T0 ^ (19 / 27 : ℝ) := by
    calc
      (X : ℝ) ^ ((1 : ℝ) / 3) ≤ (T0 ^ mu) ^ ((1 : ℝ) / 3) :=
        Real.rpow_le_rpow hX0 hXscale (by norm_num)
      _ = T0 ^ (mu / 3) := by
        rw [← Real.rpow_mul hT00]
        congr 1
        ring
      _ ≤ T0 ^ (19 / 27 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hT0.le hmu3
  calc
    8 * Real.pi * N ^ ((1 : ℝ) / 3)
        ≤ T0 ^ (8 / 27 : ℝ) * T0 ^ (19 / 27 : ℝ) :=
      mul_le_mul hpi (hthird.trans hXpow) (Real.rpow_nonneg hN0 _)
        (Real.rpow_nonneg hT00 _)
    _ = T0 := by
      rw [← Real.rpow_add (by linarith : 0 < T0)]
      norm_num
    _ ≤ y := hy

/-- Canonical long zeta/logarithm factor exclusion at fixed order `47`. -/
theorem not_heathBrown_box_core_large_of_maynard_long_schedule
    (L X k : ℕ) (c : HeathBrownBoxChoice L X k)
    (j : HeathBrownBoxFactorIndex k c.m)
    (hkind : heathBrownBoxFactorKind k c.m j = .zeta ∨
      heathBrownBoxFactorKind k c.m j = .log)
    (hX : 1 ≤ X) {T0 t mu sigma y : ℝ}
    (hT0 : 1 < T0) (hmu : 4 / 3 ≤ mu) (ht : t = mu / 120)
    (hlong : 2 * t < dyadicLogExponent T0
      (heathBrownBoxFactorExponent c.a c.b c.q j))
    (hsigma : 0 ≤ sigma) (hy0 : 0 < y) (hyupper : y ≤ 2 * T0)
    (hfactorial : ((Nat.factorial 46 : ℕ) : ℝ) ≤ T0 ^ (1 / 45 : ℝ))
    (hlow : 8 * Real.pi *
        (((2 ^ heathBrownBoxFactorExponent c.a c.b c.q j : ℕ) : ℝ)) ^
          ((1 : ℝ) / 3) ≤ y)
    (habsorb :
      (heathBrownDerivativeConstant X
          (heathBrownBoxFactorKind k c.m j)
          (heathBrownBoxFactorExponent c.a c.b c.q j) *
        heathBrownComplementTrivialConstant c j) *
          (((2 ^ heathBrownBoxFactorExponent c.a c.b c.q j : ℕ) : ℝ)) ^
            (-maynardDerivativeDeficit 47) < 1) :
    ¬ (groupedDyadicLower
        (heathBrownBoxFactorExponent c.a c.b c.q) : ℝ) ^ (1 - sigma) ≤
      ‖heathBrownDyadicCoreProduct L X k c.m c.a c.b c.q
        ((sigma : ℂ) + (y : ℝ) * Complex.I)‖ := by
  apply not_heathBrown_box_core_large_of_derivative_factor
    L X k c j hkind hX hsigma hy0 (k₀ := 47) (by norm_num)
  · exact maynard_long_fixedOrder_factorial hT0 hmu ht hlong hfactorial
  · exact hlow
  · exact maynard_long_fixedOrder_high_window hT0 hmu ht hlong hyupper
  · exact habsorb

/-- Full geometric long-factor schedule.  On ordinates `y in [T0,2*T0]`, ambient scale
`X <= T0^mu`, and `4/3 <= mu <= 19/9`, only eventual factorial and polylog absorption remain. -/
theorem not_heathBrown_box_core_large_of_maynard_long_scale
    (L X k : ℕ) (c : HeathBrownBoxChoice L X k)
    (j : HeathBrownBoxFactorIndex k c.m)
    (hkind : heathBrownBoxFactorKind k c.m j = .zeta ∨
      heathBrownBoxFactorKind k c.m j = .log)
    (hX : 1 ≤ X) {T0 t mu sigma y : ℝ}
    (hT0 : 1 < T0) (hmu_lo : 4 / 3 ≤ mu) (hmu_hi : mu ≤ 19 / 9)
    (ht : t = mu / 120)
    (hlong : 2 * t < dyadicLogExponent T0
      (heathBrownBoxFactorExponent c.a c.b c.q j))
    (hXscale : (X : ℝ) ≤ T0 ^ mu)
    (hsigma : 0 ≤ sigma) (hylo : T0 ≤ y) (hyupper : y ≤ 2 * T0)
    (hpi : 8 * Real.pi ≤ T0 ^ (8 / 27 : ℝ))
    (hfactorial : ((Nat.factorial 46 : ℕ) : ℝ) ≤ T0 ^ (1 / 45 : ℝ))
    (habsorb :
      (heathBrownDerivativeConstant X
          (heathBrownBoxFactorKind k c.m j)
          (heathBrownBoxFactorExponent c.a c.b c.q j) *
        heathBrownComplementTrivialConstant c j) *
          (((2 ^ heathBrownBoxFactorExponent c.a c.b c.q j : ℕ) : ℝ)) ^
            (-maynardDerivativeDeficit 47) < 1) :
    ¬ (groupedDyadicLower
        (heathBrownBoxFactorExponent c.a c.b c.q) : ℝ) ^ (1 - sigma) ≤
      ‖heathBrownDyadicCoreProduct L X k c.m c.a c.b c.q
        ((sigma : ℂ) + (y : ℝ) * Complex.I)‖ := by
  apply not_heathBrown_box_core_large_of_maynard_long_schedule
    L X k c j hkind hX hT0 hmu_lo ht hlong hsigma
      (lt_trans zero_lt_one (hT0.trans_le hylo)) hyupper hfactorial
  · exact maynard_zeta_log_factor_low_window
      c j hkind hX hT0 hmu_hi hXscale hylo hpi
  · exact habsorb

end RHTower.Sieve
