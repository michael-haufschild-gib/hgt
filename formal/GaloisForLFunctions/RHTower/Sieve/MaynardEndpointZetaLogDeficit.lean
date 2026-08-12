import GaloisForLFunctions.RHTower.Sieve.MaynardEndpointAmplitudeExclusion
import GaloisForLFunctions.RHTower.Sieve.MaynardLongFactorAbsorption
import GaloisForLFunctions.RHTower.Sieve.MaynardLongAmplitudeExclusion

/-!
# Endpoint-long zeta and logarithm factors have a fixed power deficit

Maynard's endpoint cutoff is much shorter than the earlier Route-T long-factor cutoff.  It still
has one decisive feature: in an eligible degree-`60` box, every endpoint-long factor has length at
least `T^(1/216000)`.  Since the ordinate is in `[T,2T]`, the already formalized arbitrary-order
derivative test applies at the single fixed order `216002`.  Its tiny but fixed power deficit
eventually dominates every vanishing Vinogradov--Korobov endpoint gap.

Thus zeta and logarithm atoms are not part of the remaining endpoint obstruction.  Only endpoint-
long Möbius atoms require new cancellation.
-/

noncomputable section
namespace RHTower.Sieve

open Finset ArithmeticFunction

/-- Fixed derivative order needed at the literal degree-`60` endpoint cutoff. -/
def maynardEndpointDerivativeOrder : ℕ := 216002

/-- Fixed local power deficit delivered by the endpoint derivative schedule. -/
def maynardEndpointDerivativeDeficit : ℝ :=
  maynardDerivativeDeficit maynardEndpointDerivativeOrder

theorem maynardEndpointDerivativeDeficit_pos :
    0 < maynardEndpointDerivativeDeficit := by
  dsimp [maynardEndpointDerivativeDeficit, maynardDerivativeDeficit,
    maynardEndpointDerivativeOrder]
  positivity

/-- Eligibility and the `1/(40k)` endpoint cutoff imply the absolute length
`N >= T^(1/216000)` when `k=60`. -/
theorem dyadic_length_ge_maynard_endpoint_root
    {L X : ℕ} (box : HeathBrownBoxChoice L X 60)
    {T mu : ℝ} (hT : 1 < T) (hmu : 4 / 3 ≤ mu)
    (helig : IsHeathBrownBoxEligible L X 60 T (mu / 120) box)
    (j : HeathBrownBoxFactorIndex 60 box.m)
    (hlong : heathBrownBoxTotalExponent L X 60 T box / (40 * 60 : ℕ) ≤
      dyadicLogExponent T
        (heathBrownBoxFactorExponent box.a box.b box.q j)) :
    T ^ (1 / 216000 : ℝ) ≤
      (((2 ^ heathBrownBoxFactorExponent box.a box.b box.q j : ℕ) : ℝ)) := by
  have htotal : mu / 120 ≤ heathBrownBoxTotalExponent L X 60 T box := by
    simpa [IsHeathBrownBoxEligible] using helig
  have htotalMin : (1 / 90 : ℝ) ≤ heathBrownBoxTotalExponent L X 60 T box := by
    linarith
  have hcut : (1 / 216000 : ℝ) ≤
      heathBrownBoxTotalExponent L X 60 T box / (40 * 60 : ℕ) := by
    norm_num
    linarith
  have hweight : (1 / 216000 : ℝ) ≤
      dyadicLogExponent T
        (heathBrownBoxFactorExponent box.a box.b box.q j) := hcut.trans hlong
  have hpow := (Real.strictMono_rpow_of_base_gt_one hT).monotone hweight
  rwa [rpow_dyadicLogExponent hT
    (heathBrownBoxFactorExponent box.a box.b box.q j)] at hpow

/-- The fixed factorial required by order `216002` is eventually below every endpoint-long
factor. -/
theorem maynard_endpoint_fixedOrder_factorial
    {L X : ℕ} (box : HeathBrownBoxChoice L X 60)
    {T mu : ℝ} (hT : 1 < T) (hmu : 4 / 3 ≤ mu)
    (helig : IsHeathBrownBoxEligible L X 60 T (mu / 120) box)
    (j : HeathBrownBoxFactorIndex 60 box.m)
    (hlong : heathBrownBoxTotalExponent L X 60 T box / (40 * 60 : ℕ) ≤
      dyadicLogExponent T
        (heathBrownBoxFactorExponent box.a box.b box.q j))
    (hfactorial : ((Nat.factorial 216001 : ℕ) : ℝ) ≤ T ^ (1 / 216000 : ℝ)) :
    Nat.factorial (maynardEndpointDerivativeOrder - 1) ≤
      2 ^ heathBrownBoxFactorExponent box.a box.b box.q j := by
  have hN := dyadic_length_ge_maynard_endpoint_root box hT hmu helig j hlong
  have hreal : ((Nat.factorial 216001 : ℕ) : ℝ) ≤
      (((2 ^ heathBrownBoxFactorExponent box.a box.b box.q j : ℕ) : ℝ)) :=
    hfactorial.trans hN
  change Nat.factorial 216001 ≤ 2 ^ heathBrownBoxFactorExponent box.a box.b box.q j
  exact Nat.cast_le.mp hreal

/-- The same endpoint root controls the upper derivative-test window at fixed order `216002`. -/
theorem maynard_endpoint_fixedOrder_high_window
    {L X : ℕ} (box : HeathBrownBoxChoice L X 60)
    {T mu y : ℝ} (hT : 1 < T) (hmu : 4 / 3 ≤ mu)
    (helig : IsHeathBrownBoxEligible L X 60 T (mu / 120) box)
    (j : HeathBrownBoxFactorIndex 60 box.m)
    (hlong : heathBrownBoxTotalExponent L X 60 T box / (40 * 60 : ℕ) ≤
      dyadicLogExponent T
        (heathBrownBoxFactorExponent box.a box.b box.q j))
    (hy : y ≤ 2 * T) :
    y ≤ 2 * Real.pi * 2 ^ maynardEndpointDerivativeOrder *
      (((2 ^ heathBrownBoxFactorExponent box.a box.b box.q j : ℕ) : ℝ)) ^
        (maynardEndpointDerivativeOrder - 1) *
      (((2 ^ heathBrownBoxFactorExponent box.a box.b box.q j : ℕ) : ℝ)) ^
        (-(1 / 3) : ℝ) := by
  let N : ℝ :=
    (((2 ^ heathBrownBoxFactorExponent box.a box.b box.q j : ℕ) : ℝ))
  have hNbase : T ^ (1 / 216000 : ℝ) ≤ N :=
    dyadic_length_ge_maynard_endpoint_root box hT hmu helig j hlong
  have hbase0 : 0 ≤ T ^ (1 / 216000 : ℝ) := Real.rpow_nonneg (by linarith) _
  have hpow := Real.rpow_le_rpow hbase0 hNbase (by norm_num : (0 : ℝ) ≤ 216000)
  have hcollapse : (T ^ (1 / 216000 : ℝ)) ^ (216000 : ℝ) = T := by
    rw [← Real.rpow_mul (by linarith : 0 ≤ T)]
    norm_num
  rw [hcollapse] at hpow
  have hN1 : 1 ≤ N := by
    have hroot1 : 1 ≤ T ^ (1 / 216000 : ℝ) :=
      Real.one_le_rpow hT.le (by norm_num)
    exact hroot1.trans hNbase
  have hshape : N ^ (216000 : ℕ) ≤
      N ^ (216001 : ℕ) * N ^ (-(1 / 3) : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast,
      ← Real.rpow_add (by positivity : 0 < N)]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
  have hpowerNat : T ≤ N ^ (216000 : ℕ) := by
    simpa [Real.rpow_natCast] using hpow
  have hconstant : (2 : ℝ) ≤
      2 * Real.pi * 2 ^ maynardEndpointDerivativeOrder := by
    have hpi := Real.pi_gt_three
    have hone : (1 : ℝ) ≤ 2 ^ maynardEndpointDerivativeOrder := one_le_pow₀ (by norm_num)
    nlinarith
  calc
    y ≤ 2 * T := hy
    _ ≤ 2 * N ^ (216000 : ℕ) := mul_le_mul_of_nonneg_left hpowerNat (by norm_num)
    _ ≤ 2 * (N ^ (216001 : ℕ) * N ^ (-(1 / 3) : ℝ)) :=
      mul_le_mul_of_nonneg_left hshape (by norm_num)
    _ ≤ (2 * Real.pi * 2 ^ maynardEndpointDerivativeOrder) *
        (N ^ (216001 : ℕ) * N ^ (-(1 / 3) : ℝ)) := by
      exact mul_le_mul_of_nonneg_right hconstant (by positivity)
    _ = 2 * Real.pi * 2 ^ maynardEndpointDerivativeOrder *
        N ^ (maynardEndpointDerivativeOrder - 1) * N ^ (-(1 / 3) : ℝ) := by
      dsimp [maynardEndpointDerivativeOrder]
      norm_num
      ring

/-- Exact endpoint-long zeta/log factor theorem at fixed order `216002`. -/
theorem maynard_heathBrown_endpoint_zeta_log_amplitude_le_one_sub_half
    {L X : ℕ} (box : HeathBrownBoxChoice L X 60)
    (j : HeathBrownBoxFactorIndex 60 box.m)
    (hkind : heathBrownBoxFactorKind 60 box.m j = .zeta ∨
      heathBrownBoxFactorKind 60 box.m j = .log)
    (hX : 1 ≤ X) {T mu c y : ℝ}
    (hT : 1 < T) (hmu_lo : 4 / 3 ≤ mu) (hmu_hi : mu ≤ 19 / 9)
    (hXscale : (X : ℝ) ≤ T ^ mu)
    (helig : IsHeathBrownBoxEligible L X 60 T (mu / 120) box)
    (hlong : heathBrownBoxTotalExponent L X 60 T box / (40 * 60 : ℕ) ≤
      dyadicLogExponent T
        (heathBrownBoxFactorExponent box.a box.b box.q j))
    (hc : 0 ≤ c) (hylo : T ≤ y) (hyupper : y ≤ 2 * T)
    (hpi : 8 * Real.pi ≤ T ^ (8 / 27 : ℝ))
    (hfactorial : ((Nat.factorial 216001 : ℕ) : ℝ) ≤ T ^ (1 / 216000 : ℝ))
    (hsize : 2 * Real.log
        (heathBrownDerivativeConstant X
          (heathBrownBoxFactorKind 60 box.m j)
          (heathBrownBoxFactorExponent box.a box.b box.q j)) ≤
      maynardEndpointDerivativeDeficit *
        Real.log
          (((2 ^ heathBrownBoxFactorExponent box.a box.b box.q j : ℕ) : ℝ)))
    (hV : 0 < ‖heathBrownBoxFactorValue L X 60 box
      ((c : ℂ) + (y : ℝ) * Complex.I) j‖) :
    maynardAmplitude c
        (((2 ^ heathBrownBoxFactorExponent box.a box.b box.q j : ℕ) : ℝ))
        ‖heathBrownBoxFactorValue L X 60 box
          ((c : ℂ) + (y : ℝ) * Complex.I) j‖ ≤
      1 - maynardEndpointDerivativeDeficit / 2 := by
  let q := heathBrownBoxFactorExponent box.a box.b box.q j
  let N : ℝ := (((2 ^ q : ℕ) : ℝ))
  let C : ℝ := heathBrownDerivativeConstant X
    (heathBrownBoxFactorKind 60 box.m j) q
  have hNbase := dyadic_length_ge_maynard_endpoint_root box hT hmu_lo helig j hlong
  have hroot1 : 1 < T ^ (1 / 216000 : ℝ) := by
    simpa using (Real.strictMono_rpow_of_base_gt_one hT)
      (by norm_num : (0 : ℝ) < 1 / 216000)
  have hN : 1 < N := hroot1.trans_le hNbase
  have hC : 1 ≤ C := by
    dsimp [C, q]
    exact one_le_heathBrownDerivativeConstant_of_zeta_or_log _ _ hX hkind
  have hfac := maynard_endpoint_fixedOrder_factorial box hT hmu_lo helig j hlong hfactorial
  have hlow := maynard_zeta_log_factor_low_window
    box j hkind hX hT hmu_hi hXscale hylo hpi
  have hhigh := maynard_endpoint_fixedOrder_high_window
    box hT hmu_lo helig j hlong hyupper
  have hy0 : 0 < y := lt_trans zero_lt_one (hT.trans_le hylo)
  have hqX := box.factorExponent_le_log_X_of_zeta_or_log j hkind
  have hupper := norm_heathBrownBoxFactorValue_le_derivative_defect
    L X 60 box j hkind hX hc hy0
      (k₀ := maynardEndpointDerivativeOrder) (by
        dsimp [maynardEndpointDerivativeOrder]
        norm_num) hqX hfac hlow hhigh
  exact maynardAmplitude_le_one_sub_half_of_pointwise_power_saving
    hN hV hC (by simpa [N, C, q, maynardEndpointDerivativeDeficit] using hsize)
      (by simpa [N, C, q, maynardEndpointDerivativeDeficit] using hupper)

/-- Uniform eventual absorption of every endpoint-long zeta/log derivative constant. -/
theorem eventually_maynard_endpoint_zeta_log_size_ready :
    ∀ᶠ T : ℝ in Filter.atTop,
      ∀ X : ℕ, 1 ≤ X → ∀ mu : ℝ, mu ≤ 19 / 9 → (X : ℝ) ≤ T ^ mu →
        ∀ L : ℕ, ∀ box : HeathBrownBoxChoice L X 60,
          ∀ j : HeathBrownBoxFactorIndex 60 box.m,
            (heathBrownBoxFactorKind 60 box.m j = .zeta ∨
              heathBrownBoxFactorKind 60 box.m j = .log) →
            IsHeathBrownBoxEligible L X 60 T (mu / 120) box →
            4 / 3 ≤ mu →
            heathBrownBoxTotalExponent L X 60 T box / (40 * 60 : ℕ) ≤
              dyadicLogExponent T
                (heathBrownBoxFactorExponent box.a box.b box.q j) →
            2 * Real.log
                (heathBrownDerivativeConstant X
                  (heathBrownBoxFactorKind 60 box.m j)
                  (heathBrownBoxFactorExponent box.a box.b box.q j)) ≤
              maynardEndpointDerivativeDeficit *
                Real.log
                  (((2 ^ heathBrownBoxFactorExponent box.a box.b box.q j : ℕ) : ℝ)) := by
  let eps : ℝ := maynardEndpointDerivativeDeficit / (4 * 216000)
  have heps : 0 < eps := by
    dsimp [eps]
    positivity [maynardEndpointDerivativeDeficit_pos]
  have hconst : ∀ᶠ T : ℝ in Filter.atTop,
      Real.log 5120 ≤ eps * Real.log T := by
    have hlogGrow : Filter.Tendsto (fun T : ℝ => eps * Real.log T)
        Filter.atTop Filter.atTop :=
      Filter.Tendsto.const_mul_atTop heps Real.tendsto_log_atTop
    exact hlogGrow.eventually_ge_atTop (Real.log 5120)
  filter_upwards [eventually_log_maynardLongPolylogEnvelope_le heps,
    hconst, Filter.eventually_gt_atTop (1 : ℝ)] with T hE hconstT hT
  intro X hX mu hmu_hi hXscale L box j hkind helig hmu_lo hlong
  let C : ℝ := heathBrownDerivativeConstant X
    (heathBrownBoxFactorKind 60 box.m j)
    (heathBrownBoxFactorExponent box.a box.b box.q j)
  let N : ℝ :=
    (((2 ^ heathBrownBoxFactorExponent box.a box.b box.q j : ℕ) : ℝ))
  have hC : 0 < C := by
    dsimp [C]
    exact heathBrownDerivativeConstant_pos_of_zeta_or_log _ _ hX hkind
  have hCup : C ≤ 5120 * maynardLongPolylogEnvelope X :=
    heathBrownDerivativeConstant_le_polylogEnvelope box j hkind hX
  have hlogC : Real.log C ≤ Real.log 5120 +
      Real.log (maynardLongPolylogEnvelope X) := by
    have hEpos : 0 < maynardLongPolylogEnvelope X :=
      lt_of_lt_of_le zero_lt_one (one_le_maynardLongPolylogEnvelope X)
    calc
      Real.log C ≤ Real.log (5120 * maynardLongPolylogEnvelope X) :=
        Real.log_le_log hC hCup
      _ = Real.log 5120 + Real.log (maynardLongPolylogEnvelope X) := by
        rw [Real.log_mul (by norm_num) hEpos.ne']
  have hlogE := hE X hX mu hmu_hi hXscale
  have hlogCsmall : Real.log C ≤ 2 * eps * Real.log T := by
    linarith
  have hN := dyadic_length_ge_maynard_endpoint_root box hT hmu_lo helig j hlong
  have hT0 : 0 < T := lt_trans zero_lt_one hT
  have hroot0 : 0 < T ^ (1 / 216000 : ℝ) := Real.rpow_pos_of_pos hT0 _
  have hN0 : 0 < N := hroot0.trans_le hN
  have hlogN : (1 / 216000 : ℝ) * Real.log T ≤ Real.log N := by
    have h := Real.log_le_log hroot0 hN
    rwa [Real.log_rpow hT0] at h
  have hdelta : 0 ≤ maynardEndpointDerivativeDeficit :=
    maynardEndpointDerivativeDeficit_pos.le
  have hscaled := mul_le_mul_of_nonneg_left hlogN hdelta
  calc
    2 * Real.log C ≤ 4 * eps * Real.log T := by linarith
    _ = maynardEndpointDerivativeDeficit * ((1 / 216000 : ℝ) * Real.log T) := by
      dsimp [eps]
      ring
    _ ≤ maynardEndpointDerivativeDeficit * Real.log N := hscaled

/-- **Unconditional endpoint zeta/log exclusion.**  At all sufficiently large heights, every
endpoint-long zeta or logarithm factor of every eligible degree-`60` box has one fixed local
amplitude deficit. -/
theorem eventually_maynard_endpoint_zeta_log_amplitude_deficit :
    ∀ᶠ T : ℝ in Filter.atTop,
      ∀ X : ℕ, 1 ≤ X → ∀ mu : ℝ, 4 / 3 ≤ mu → mu ≤ 19 / 9 →
        (X : ℝ) ≤ T ^ mu →
        ∀ L : ℕ, ∀ box : HeathBrownBoxChoice L X 60,
          IsHeathBrownBoxEligible L X 60 T (mu / 120) box →
          ∀ j : HeathBrownBoxFactorIndex 60 box.m,
            (heathBrownBoxFactorKind 60 box.m j = .zeta ∨
              heathBrownBoxFactorKind 60 box.m j = .log) →
            heathBrownBoxTotalExponent L X 60 T box / (40 * 60 : ℕ) ≤
              dyadicLogExponent T
                (heathBrownBoxFactorExponent box.a box.b box.q j) →
            ∀ c y : ℝ, 0 ≤ c → T ≤ y → y ≤ 2 * T →
              0 < ‖heathBrownBoxFactorValue L X 60 box
                ((c : ℂ) + (y : ℝ) * Complex.I) j‖ →
              maynardAmplitude c
                  (((2 ^ heathBrownBoxFactorExponent box.a box.b box.q j : ℕ) : ℝ))
                  ‖heathBrownBoxFactorValue L X 60 box
                    ((c : ℂ) + (y : ℝ) * Complex.I) j‖ ≤
                1 - maynardEndpointDerivativeDeficit / 2 := by
  have hpi : Filter.Tendsto (fun T : ℝ => T ^ (8 / 27 : ℝ))
      Filter.atTop Filter.atTop := tendsto_rpow_atTop (by norm_num)
  have hfac : Filter.Tendsto (fun T : ℝ => T ^ (1 / 216000 : ℝ))
      Filter.atTop Filter.atTop := tendsto_rpow_atTop (by norm_num)
  filter_upwards [Filter.eventually_gt_atTop (1 : ℝ),
    hpi.eventually_ge_atTop (8 * Real.pi),
    hfac.eventually_ge_atTop (((Nat.factorial 216001 : ℕ) : ℝ)),
    eventually_maynard_endpoint_zeta_log_size_ready]
      with T hT hpiT hfacT hsize
  intro X hX mu hmu_lo hmu_hi hXscale L box helig j hkind hlong
    c y hc hylo hyupper hV
  exact maynard_heathBrown_endpoint_zeta_log_amplitude_le_one_sub_half
    box j hkind hX hT hmu_lo hmu_hi hXscale helig hlong hc hylo hyupper
      hpiT hfacT (hsize X hX mu hmu_hi hXscale L box j hkind helig hmu_lo hlong) hV

end RHTower.Sieve
