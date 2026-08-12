import GaloisForLFunctions.RHTower.Sieve.MaynardLongFactorSchedule

/-!
# Polylogarithmic absorption for canonical long factors

One envelope bounds both possible derivative-test constants and the unique complementary
logarithmic atom.  Consequently a single scalar inequality in `T0` absorbs every literal long
zeta/logarithm factor, uniformly in packet degree and box choice.
-/

noncomputable section
namespace RHTower.Sieve

open Finset ArithmeticFunction

def maynardLongPolylogEnvelope (X : ℕ) : ℝ :=
  1 + Real.log (((2 * (X + 1) : ℕ) : ℝ))

theorem one_le_maynardLongPolylogEnvelope (X : ℕ) :
    1 ≤ maynardLongPolylogEnvelope X := by
  have hbase : (1 : ℝ) ≤ ((2 * (X + 1) : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 1 ≤ 2 * (X + 1))
  exact le_add_of_nonneg_right (Real.log_nonneg hbase)

theorem heathBrown_log_trivialConstant_le_polylogEnvelope
    {L X k : ℕ} (c : HeathBrownBoxChoice L X k) (hX : 1 ≤ X) :
    Real.log (((2 ^ (c.q + 1) : ℕ) : ℝ)) ≤ maynardLongPolylogEnvelope X := by
  have hq : c.q ≤ Nat.log 2 X := by
    have h := c.2.1.isLt
    change c.q < Nat.log 2 X + 1 at h
    omega
  have hpow : 2 ^ c.q ≤ X :=
    (Nat.pow_le_pow_right (by norm_num) hq).trans
      (Nat.pow_log_le_self 2 (by omega : X ≠ 0))
  have hpow' : 2 ^ (c.q + 1) ≤ 2 * (X + 1) := by
    rw [pow_succ]
    nlinarith
  have hlog : Real.log (((2 ^ (c.q + 1) : ℕ) : ℝ)) ≤
      Real.log ((2 * (X + 1) : ℕ) : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hpow'
  dsimp [maynardLongPolylogEnvelope]
  linarith

theorem log_heathBrownDyadicFactorTop_le_polylogEnvelope
    {X q : ℕ} (hX : 1 ≤ X) :
    Real.log (heathBrownDyadicFactorTop X q : ℝ) ≤
      maynardLongPolylogEnvelope X := by
  have htop2 : 2 ≤ heathBrownDyadicFactorTop X q := by
    rw [heathBrownDyadicFactorTop, Nat.le_min]
    constructor
    · omega
    · calc
        2 = 2 ^ (1 : ℕ) := by norm_num
        _ ≤ 2 ^ (q + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have htop : heathBrownDyadicFactorTop X q ≤ 2 * (X + 1) :=
    (min_le_left _ _).trans (by omega)
  have hlog : Real.log (heathBrownDyadicFactorTop X q : ℝ) ≤
      Real.log ((2 * (X + 1) : ℕ) : ℝ) := by
    apply Real.log_le_log (by exact_mod_cast (by omega : 0 < heathBrownDyadicFactorTop X q))
    exact_mod_cast htop
  dsimp [maynardLongPolylogEnvelope]
  linarith

/-- Product of distinguished derivative constant and complete complementary trivial constant is
bounded by one squared logarithmic envelope. -/
theorem heathBrown_long_constants_le_polylogEnvelope_sq
    {L X k : ℕ} (c : HeathBrownBoxChoice L X k)
    (j : HeathBrownBoxFactorIndex k c.m)
    (hkind : heathBrownBoxFactorKind k c.m j = .zeta ∨
      heathBrownBoxFactorKind k c.m j = .log)
    (hX : 1 ≤ X) :
    heathBrownDerivativeConstant X
        (heathBrownBoxFactorKind k c.m j)
        (heathBrownBoxFactorExponent c.a c.b c.q j) *
      heathBrownComplementTrivialConstant c j ≤
        5120 * (maynardLongPolylogEnvelope X) ^ 2 := by
  rw [heathBrownComplementTrivialConstant_eq]
  rcases j with j | j
  · simp [heathBrownBoxFactorKind] at hkind
  · rcases j with j | j
    · change 2560 * Real.log (((2 ^ (c.q + 1) : ℕ) : ℝ)) ≤
        5120 * (maynardLongPolylogEnvelope X) ^ 2
      have hE := one_le_maynardLongPolylogEnvelope X
      have hlog := heathBrown_log_trivialConstant_le_polylogEnvelope c hX
      calc
        2560 * Real.log (((2 ^ (c.q + 1) : ℕ) : ℝ)) ≤
            2560 * maynardLongPolylogEnvelope X :=
          mul_le_mul_of_nonneg_left hlog (by norm_num)
        _ ≤ 5120 * (maynardLongPolylogEnvelope X) ^ 2 := by nlinarith
    · rcases j with ⟨⟩
      simp only [heathBrownBoxFactorKind, heathBrownBoxFactorExponent,
        heathBrownDerivativeConstant, if_pos, mul_one]
      change 5120 * Real.log (heathBrownDyadicFactorTop X c.q : ℝ) ≤
        5120 * (maynardLongPolylogEnvelope X) ^ 2
      have hE := one_le_maynardLongPolylogEnvelope X
      have hlog := log_heathBrownDyadicFactorTop_le_polylogEnvelope
        (X := X) (q := c.q) hX
      calc
        5120 * Real.log (heathBrownDyadicFactorTop X c.q : ℝ) ≤
            5120 * maynardLongPolylogEnvelope X :=
          mul_le_mul_of_nonneg_left hlog (by norm_num)
        _ ≤ 5120 * (maynardLongPolylogEnvelope X) ^ 2 := by nlinarith

/-- Scalar ambient polylog absorption implies the exact literal-box absorption condition. -/
theorem maynard_long_absorption_of_polylog
    {L X k : ℕ} (c : HeathBrownBoxChoice L X k)
    (j : HeathBrownBoxFactorIndex k c.m)
    (hkind : heathBrownBoxFactorKind k c.m j = .zeta ∨
      heathBrownBoxFactorKind k c.m j = .log)
    (hX : 1 ≤ X) {T0 t mu : ℝ} (hT0 : 1 < T0)
    (hmu : 4 / 3 ≤ mu) (ht : t = mu / 120)
    (hlong : 2 * t < dyadicLogExponent T0
      (heathBrownBoxFactorExponent c.a c.b c.q j))
    (hpoly : 5120 * (maynardLongPolylogEnvelope X) ^ 2 <
      T0 ^ ((1 / 45 : ℝ) * maynardDerivativeDeficit 47)) :
    (heathBrownDerivativeConstant X
        (heathBrownBoxFactorKind k c.m j)
        (heathBrownBoxFactorExponent c.a c.b c.q j) *
      heathBrownComplementTrivialConstant c j) *
        (((2 ^ heathBrownBoxFactorExponent c.a c.b c.q j : ℕ) : ℝ)) ^
          (-maynardDerivativeDeficit 47) < 1 := by
  let N : ℝ :=
    (((2 ^ heathBrownBoxFactorExponent c.a c.b c.q j : ℕ) : ℝ))
  let delta : ℝ := maynardDerivativeDeficit 47
  have hdelta : 0 < delta := by
    dsimp [delta, maynardDerivativeDeficit]
    positivity
  have hNbase : T0 ^ (1 / 45 : ℝ) ≤ N :=
    dyadic_length_ge_fortyFive_root_of_maynard_long hT0 hmu ht hlong
  have hroot0 : 0 ≤ T0 ^ (1 / 45 : ℝ) := Real.rpow_nonneg (by linarith) _
  have hNpow : T0 ^ ((1 / 45 : ℝ) * delta) ≤ N ^ delta := by
    calc
      T0 ^ ((1 / 45 : ℝ) * delta) =
          (T0 ^ (1 / 45 : ℝ)) ^ delta := by
        rw [← Real.rpow_mul (by linarith : 0 ≤ T0)]
      _ ≤ N ^ delta := Real.rpow_le_rpow hroot0 hNbase hdelta.le
  have hconst := heathBrown_long_constants_le_polylogEnvelope_sq c j hkind hX
  have hless : heathBrownDerivativeConstant X
        (heathBrownBoxFactorKind k c.m j)
        (heathBrownBoxFactorExponent c.a c.b c.q j) *
      heathBrownComplementTrivialConstant c j < N ^ delta :=
    hconst.trans_lt (hpoly.trans_le (by simpa [delta] using hNpow))
  have hN0 : 0 < N := by dsimp [N]; positivity
  have hinv0 : 0 < N ^ (-delta) := Real.rpow_pos_of_pos hN0 _
  have hmul := mul_lt_mul_of_pos_right hless hinv0
  have hcancel : N ^ delta * N ^ (-delta) = 1 := by
    rw [← Real.rpow_add hN0]
    simp
  rw [hcancel] at hmul
  simpa [N, delta] using hmul

theorem maynardLongPolylogEnvelope_le_eight_log
    {X : ℕ} (hX : 1 ≤ X) {T mu : ℝ}
    (hT : 0 < T) (hlogT : 1 ≤ Real.log T) (hmu : mu ≤ 19 / 9)
    (hXscale : (X : ℝ) ≤ T ^ mu) :
    maynardLongPolylogEnvelope X ≤ 8 * Real.log T := by
  have hXcast : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hTpow0 : 0 ≤ T ^ mu := Real.rpow_nonneg hT.le _
  have harg : (((2 * (X + 1) : ℕ) : ℝ)) ≤ 4 * T ^ mu := by
    push_cast
    calc
      2 * ((X : ℝ) + 1) ≤ 4 * (X : ℝ) := by nlinarith
      _ ≤ 4 * T ^ mu := mul_le_mul_of_nonneg_left hXscale (by norm_num)
  have hlogarg : Real.log (((2 * (X + 1) : ℕ) : ℝ)) ≤
      Real.log (4 * T ^ mu) := by
    apply Real.log_le_log (by positivity)
    exact harg
  have hlog4 : Real.log 4 ≤ 3 := by
    nlinarith [Real.log_le_sub_one_of_pos (x := (4 : ℝ)) (by norm_num)]
  have hsplit : Real.log (4 * T ^ mu) = Real.log 4 + mu * Real.log T := by
    rw [Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hT _).ne', Real.log_rpow hT]
  rw [hsplit] at hlogarg
  dsimp [maynardLongPolylogEnvelope]
  have hlog0 : 0 ≤ Real.log T := by linarith
  have hmumul : mu * Real.log T ≤ (19 / 9 : ℝ) * Real.log T :=
    mul_le_mul_of_nonneg_right hmu hlog0
  linarith

/-- The fixed order-47 saving eventually absorbs the complete literal long-factor constant,
uniformly over all cutoffs `X <= T^mu` and all `mu <= 19/9`. -/
theorem eventually_maynardLong_polylog_absorbed :
    ∀ᶠ T : ℝ in Filter.atTop,
      ∀ X : ℕ, 1 ≤ X → ∀ mu : ℝ, mu ≤ 19 / 9 → (X : ℝ) ≤ T ^ mu →
        5120 * (maynardLongPolylogEnvelope X) ^ 2 <
          T ^ ((1 / 45 : ℝ) * maynardDerivativeDeficit 47) := by
  let eps : ℝ := (1 / 45 : ℝ) * maynardDerivativeDeficit 47
  have heps : 0 < eps := by
    dsimp [eps, maynardDerivativeDeficit]
    positivity
  have hlo := (_root_.isLittleO_log_rpow_rpow_atTop 2 heps).def
    (by norm_num : (0 : ℝ) < 1 / 655360)
  filter_upwards [hlo, Real.tendsto_log_atTop.eventually_ge_atTop 1,
    Filter.eventually_gt_atTop (0 : ℝ)] with T hsmall hlogT hT
  intro X hX mu hmu hXscale
  have hE := maynardLongPolylogEnvelope_le_eight_log hX hT hlogT hmu hXscale
  have hlog0 : 0 ≤ Real.log T := by linarith
  have hTpow0 : 0 < T ^ eps := Real.rpow_pos_of_pos hT _
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hlog0 _), abs_of_nonneg hTpow0.le] at hsmall
  have hlogtwo : Real.log T ^ (2 : ℝ) = (Real.log T) ^ (2 : ℕ) := by
    rw [Real.rpow_two]
  rw [hlogtwo] at hsmall
  have hhalf : 327680 * (Real.log T) ^ 2 ≤ (1 / 2 : ℝ) * T ^ eps := by
    nlinarith
  have hE0 := one_le_maynardLongPolylogEnvelope X
  have hEsq : (maynardLongPolylogEnvelope X) ^ 2 ≤
      (8 * Real.log T) ^ 2 := pow_le_pow_left₀ (by linarith) hE 2
  calc
    5120 * (maynardLongPolylogEnvelope X) ^ 2
        ≤ 5120 * (8 * Real.log T) ^ 2 :=
      mul_le_mul_of_nonneg_left hEsq (by norm_num)
    _ = 327680 * (Real.log T) ^ 2 := by ring
    _ ≤ (1 / 2 : ℝ) * T ^ eps := hhalf
    _ < T ^ eps := by linarith
    _ = T ^ ((1 / 45 : ℝ) * maynardDerivativeDeficit 47) := by rfl

/-- All eventual scalar conditions needed by canonical long-factor exclusion. -/
def IsMaynardLongScaleReady (T : ℝ) : Prop :=
  1 < T ∧
  8 * Real.pi ≤ T ^ (8 / 27 : ℝ) ∧
  ((Nat.factorial 46 : ℕ) : ℝ) ≤ T ^ (1 / 45 : ℝ) ∧
  ∀ X : ℕ, 1 ≤ X → ∀ mu : ℝ, mu ≤ 19 / 9 → (X : ℝ) ≤ T ^ mu →
    5120 * (maynardLongPolylogEnvelope X) ^ 2 <
      T ^ ((1 / 45 : ℝ) * maynardDerivativeDeficit 47)

/-- Canonical long-factor readiness holds at every sufficiently large height. -/
theorem eventually_isMaynardLongScaleReady :
    ∀ᶠ T : ℝ in Filter.atTop, IsMaynardLongScaleReady T := by
  have hpi : Filter.Tendsto (fun T : ℝ => T ^ (8 / 27 : ℝ))
      Filter.atTop Filter.atTop := tendsto_rpow_atTop (by norm_num)
  have hfac : Filter.Tendsto (fun T : ℝ => T ^ (1 / 45 : ℝ))
      Filter.atTop Filter.atTop := tendsto_rpow_atTop (by norm_num)
  filter_upwards [Filter.eventually_gt_atTop (1 : ℝ),
    hpi.eventually_ge_atTop (8 * Real.pi),
    hfac.eventually_ge_atTop (((Nat.factorial 46 : ℕ) : ℝ)),
    eventually_maynardLong_polylog_absorbed] with T hT hpiT hfacT hpoly
  exact ⟨hT, hpiT, hfacT, hpoly⟩

/-- At a ready height, every canonical long zeta/logarithm factor contradicts full literal-core
threshold size.  No further factorwise or schedule hypothesis remains. -/
theorem not_heathBrown_box_core_large_of_ready_maynard_long_scale
    (L X k : ℕ) (c : HeathBrownBoxChoice L X k)
    (j : HeathBrownBoxFactorIndex k c.m)
    (hkind : heathBrownBoxFactorKind k c.m j = .zeta ∨
      heathBrownBoxFactorKind k c.m j = .log)
    (hX : 1 ≤ X) {T0 t mu sigma y : ℝ}
    (hready : IsMaynardLongScaleReady T0)
    (hmu_lo : 4 / 3 ≤ mu) (hmu_hi : mu ≤ 19 / 9)
    (ht : t = mu / 120)
    (hlong : 2 * t < dyadicLogExponent T0
      (heathBrownBoxFactorExponent c.a c.b c.q j))
    (hXscale : (X : ℝ) ≤ T0 ^ mu)
    (hsigma : 0 ≤ sigma) (hylo : T0 ≤ y) (hyupper : y ≤ 2 * T0) :
    ¬ (groupedDyadicLower
        (heathBrownBoxFactorExponent c.a c.b c.q) : ℝ) ^ (1 - sigma) ≤
      ‖heathBrownDyadicCoreProduct L X k c.m c.a c.b c.q
        ((sigma : ℂ) + (y : ℝ) * Complex.I)‖ := by
  rcases hready with ⟨hT0, hpi, hfactorial, hpoly⟩
  apply not_heathBrown_box_core_large_of_maynard_long_scale
    L X k c j hkind hX hT0 hmu_lo hmu_hi ht hlong hXscale
      hsigma hylo hyupper hpi hfactorial
  exact maynard_long_absorption_of_polylog c j hkind hX hT0 hmu_lo ht hlong
    (hpoly X hX mu hmu_hi hXscale)

end RHTower.Sieve
