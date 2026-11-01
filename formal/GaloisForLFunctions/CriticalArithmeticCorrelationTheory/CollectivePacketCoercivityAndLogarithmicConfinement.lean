import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TelescopedConductorSplitAndOneNinthWeilPositivity
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheCompleteWeilLogarithmicReserveSurvivesGrowingOverlap

/-!
# Collective Packet Coercivity Below One Quarter and Power-of-Logarithm Defect Confinement

This module establishes two unconditional structural advances for the complete Weil quadratic form:

1. **Collective Packet Coercivity Below `α = 1 / 4`:**
   On any mid-band conductor packet subspace
   `conductorSubspace ⌊N^θ⌋₊ N ⊓ (conductorSubspace ⌊(log N)^q⌋₊ N)ᗮ` with `0 < α < 1 / 4`,
   `q > 3 * α`, and `0 < θ ≤ 1 / 4096`, splitting the packet at the stretched-exponential bridge
   `R₀ = ⌊exp((log N)^(1/2))⌋₊` combines the quadratic-overlap Band-0 coercivity estimate with the
   three-block telescoped Band-1 packet estimate and collective Band 0–1 cross suppression.
   Moreover, we prove a two-sided Riesz sandwich comparing finite-horizon prime-power dilation
   defect `poleDefect N (primeHorizonExtension u)` directly with the infinite-horizon conductor
   adjunction mass `primeAdjunctionMass Q a`:
   `(3 / 4) * primeAdjunctionMass Q a ≤ poleDefect N (primeHorizonExtension u) ≤ (3 / 2) * primeAdjunctionMass Q a`.
   This retains an explicit `(1 / 64) * poleDefect N (primeHorizonExtension u)` reserve alongside
   the spectral floor `(tiltedSplineSpectralFloorConstant + 2) * ‖u‖^2` across the entire collective
   packet band up to `α < 1 / 4`.

2. **Direct Logarithmic-Reserve Confinement on `(V_{⌊N^θ⌋})ᗮ` up to `α < 1 / 4` and Power-of-Logarithm
   All-Vector Defect Confinement Below `α = 1 / 9`:**
   - On `(conductorSubspace ⌊N^θ⌋₊ N)ᗮ` (`θ > 0`), the prime-power dilation defect satisfies
     `poleDefect N (primeHorizonExtension z) ≥ (θ / (2 * D₀)) * log N * ‖z‖^2`, while the center
     and separated-cross terms grow at most as `O(c^2 * ‖z‖^2)`. Consequently, the prime-center-
     separated-cross energy dominates `(1 / 2) * poleDefect N (primeHorizonExtension z) + c_orth * log N * ‖z‖^2`
     across `1 ≤ c ≤ (log N)^α` for every `0 < α < 1 / 4`.
   - Retaining half of the terminal prime-defect reserve `(a / (2 * c^7)) * poleDefect N (primeHorizonExtension w)`
     in the asymmetric two-region decomposition on `(V_{Q₁})ᗮ` and combining it with the unused
     prime-adjunction mass on Bands 0 and 1 and with `logarithmicReserve_conductor_floor` on `V_{Q₁}`
     yields an all-vector logarithmic defect reserve across `1 ≤ c ≤ (log N)^α` (`0 < α < 1 / 9`):
     `(a₀ / c^7) * (poleDefect N (primeHorizonExtension x) - C * log (2 * c) * ‖x‖^2) + (κ₀ / (2 * c^7)) * ‖x‖^2 ≤ completeWeilEnergy tiltedUnitSpline c N x`.
   - As immediate corollaries, every unit vector in the sublevel set
     `completeWeilEnergy tiltedUnitSpline c N x ≤ (κ₀ / (2 * c^7)) * ‖x‖^2` satisfies the logarithmic
     confinement bound `poleDefect N (primeHorizonExtension x) ≤ C * log (2 * c) ≤ C * c^2`, and
     the all-vector positive defect reserve is sharpened from `c^(-23)` to `c^(-8)`.
-/

noncomputable section

open scoped BigOperators Real InnerProductSpace
open Finset Filter

namespace GaloisForLFunctions
namespace CriticalArithmeticCorrelationTheory

/-- The `1 / 4` power-of-logarithm overlap exponent threshold for collective packet coercivity
and orthogonal prime-center confinement. -/
noncomputable def oneQuarterPowerLogExponent : ℝ := 1 / 4

theorem oneQuarterPowerLogExponent_pos :
    0 < oneQuarterPowerLogExponent := by
  unfold oneQuarterPowerLogExponent
  norm_num

theorem oneEighthPowerLogExponent_lt_oneQuarterPowerLogExponent :
    oneEighthPowerLogExponent < oneQuarterPowerLogExponent := by
  unfold oneEighthPowerLogExponent oneQuarterPowerLogExponent
  norm_num

theorem oneNinthPowerLogExponent_lt_oneQuarterPowerLogExponent :
    oneNinthPowerLogExponent < oneQuarterPowerLogExponent := by
  unfold oneNinthPowerLogExponent oneQuarterPowerLogExponent
  norm_num

/-!
## Quadratic Subadditivity of `poleDefect` and Upper Sandwich on Ramanujan Packets
-/

/-- Cauchy–Schwarz triangle inequality for the quadratic prime-power dilation defect `poleDefect`:
`poleDefect N (x + y) ≤ 2 * poleDefect N x + 2 * poleDefect N y`. -/
theorem poleDefect_add_le
    (N : ℕ) (x y : PrimeHorizonSpace N) :
    poleDefect N (x + y) ≤ 2 * poleDefect N x + 2 * poleDefect N y := by
  unfold poleDefect
  rw [← mul_sum, ← mul_sum, ← sum_add_distrib]
  refine sum_le_sum fun k _ => ?_
  have hweight : 0 ≤ ArithmeticFunction.vonMangoldt k / (k : ℝ) :=
    div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg k)
  rw [← mul_left_comm 2, ← mul_left_comm 2, ← mul_add]
  refine mul_le_mul_of_nonneg_left ?_ hweight
  rw [← mul_sum, ← mul_sum, ← sum_add_distrib]
  refine sum_le_sum fun n _ => ?_
  have hpoint :
      (((x + y).ofLp (k * n) - (x + y).ofLp n) ^ 2) / (n : ℝ) ≤
        2 * (((x.ofLp (k * n) - x.ofLp n) ^ 2) / (n : ℝ)) +
          2 * (((y.ofLp (k * n) - y.ofLp n) ^ 2) / (n : ℝ)) := by
    have hadd_kn : (x + y).ofLp (k * n) = x.ofLp (k * n) + y.ofLp (k * n) := rfl
    have hadd_n : (x + y).ofLp n = x.ofLp n + y.ofLp n := rfl
    rw [hadd_kn, hadd_n]
    have hsq :
        ((x.ofLp (k * n) + y.ofLp (k * n)) - (x.ofLp n + y.ofLp n)) ^ 2 ≤
          2 * (x.ofLp (k * n) - x.ofLp n) ^ 2 + 2 * (y.ofLp (k * n) - y.ofLp n) ^ 2 := by
      have hdiff :
          0 ≤ ((x.ofLp (k * n) - x.ofLp n) - (y.ofLp (k * n) - y.ofLp n)) ^ 2 := sq_nonneg _
      nlinarith [hdiff]
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    calc
      (((x.ofLp (k * n) + y.ofLp (k * n)) - (x.ofLp n + y.ofLp n)) ^ 2) / (n : ℝ)
          ≤ (2 * (x.ofLp (k * n) - x.ofLp n) ^ 2 +
              2 * (y.ofLp (k * n) - y.ofLp n) ^ 2) / (n : ℝ) :=
        div_le_div_of_nonneg_right hsq hn
      _ = 2 * (((x.ofLp (k * n) - x.ofLp n) ^ 2) / (n : ℝ)) +
            2 * (((y.ofLp (k * n) - y.ofLp n) ^ 2) / (n : ℝ)) := by ring
  exact hpoint

/-- Quadratic subadditivity of `poleDefect` composed with the linear extension
`primeHorizonExtension`. -/
theorem poleDefect_primeHorizonExtension_add_le
    (N : ℕ) (x y : HorizonSpace N) :
    poleDefect N (primeHorizonExtension (x + y)) ≤
      2 * poleDefect N (primeHorizonExtension x) +
        2 * poleDefect N (primeHorizonExtension y) := by
  rw [ContinuousLinearMap.map_add]
  exact poleDefect_add_le N (primeHorizonExtension x) (primeHorizonExtension y)

/-- Three-term quadratic subadditivity of `poleDefect` composed with `primeHorizonExtension`. -/
theorem poleDefect_primeHorizonExtension_three_add_le
    (N : ℕ) (x y z : HorizonSpace N) :
    poleDefect N (primeHorizonExtension (x + y + z)) ≤
      4 * poleDefect N (primeHorizonExtension x) +
        4 * poleDefect N (primeHorizonExtension y) +
        2 * poleDefect N (primeHorizonExtension z) := by
  have h12 := poleDefect_primeHorizonExtension_add_le N (x + y) z
  have hxy := poleDefect_primeHorizonExtension_add_le N x y
  linarith

/-- Upper Riesz bound for the prime-power dilation defect on normalized Ramanujan packets:
whenever `2 ≤ Q`, `Q * Q ≤ N`, and `18 * (1 + Real.log Q) ≤ Real.log N`, the finite-horizon
prime-power dilation defect is bounded above by `(3 / 2) * primeAdjunctionMass Q a`.
Together with `poleDefect_normalizedRamanujanPacket_ge_logarithmic`, this sandwiches
`poleDefect N (primeHorizonExtension u)` within a factor of `2` of `primeAdjunctionMass Q a`. -/
theorem poleDefect_normalizedRamanujanPacket_le_three_halves_primeAdjunctionMass
    {Q N : ℕ} (hQ : 2 ≤ Q) (hQN : Q * Q ≤ N)
    (hlog : 18 * (1 + Real.log (Q : ℝ)) ≤ Real.log (N : ℝ)) (a : ℕ → ℝ) :
    poleDefect N
        (primeHorizonExtension
          (∑ m ∈ Icc 1 Q, a m • normalizedRamanujanHorizonVector m N)) ≤
      (3 / 2 : ℝ) * primeAdjunctionMass Q a := by
  have hlogN_pos : 0 < Real.log (N : ℝ) := by
    have hlogQ_nonneg : 0 ≤ Real.log (Q : ℝ) :=
      Real.log_nonneg (by exact_mod_cast ( by omega : 1 ≤ Q ))
    linarith
  have hsqrt_pos : 0 < Real.sqrt (Real.log (N : ℝ)) := Real.sqrt_pos.mpr hlogN_pos
  have hsqrt_ne : Real.sqrt (Real.log (N : ℝ)) ≠ 0 := ne_of_gt hsqrt_pos
  let b : ℕ → ℝ := fun m => a m / Real.sqrt (Real.log (N : ℝ))
  have hpacket_eq :
      (∑ m ∈ Icc 1 Q, a m • normalizedRamanujanHorizonVector m N) =
        ramanujanPacket Q N b := by
    unfold ramanujanPacket
    refine sum_congr rfl fun m _ => ?_
    ext n
    simp only [normalizedRamanujanHorizonVector, b, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
    rw [div_eq_inv_mul, div_eq_inv_mul]
    ring
  rw [hpacket_eq, poleDefect_ramanujanPacket_eq Q N b]
  have hriesz := half_and_three_halves_riesz_of_log_le hQ hQN hlog
  have hterm_le :
      ∀ k ∈ Icc 1 N,
        ArithmeticFunction.vonMangoldt k / (k : ℝ) *
          (∑ n ∈ Icc 1 (N / k),
            ((ramanujanPacketProfile Q b (k * n) - ramanujanPacketProfile Q b n) ^ 2) / (n : ℝ)) ≤
        (3 / 2 : ℝ) *
          (ArithmeticFunction.vonMangoldt k / (k : ℝ) *
            ∑ m ∈ Icc 1 Q, primeConductorDilationJump Q b k m ^ 2 * Real.log (N : ℝ)) := by
    intro k hk
    have hweight : 0 ≤ ArithmeticFunction.vonMangoldt k / (k : ℝ) :=
      div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg k)
    have hsum_n :
        (∑ n ∈ Icc 1 (N / k),
          ((ramanujanPacketProfile Q b (k * n) - ramanujanPacketProfile Q b n) ^ 2) / (n : ℝ)) ≤
        ‖∑ m ∈ Icc 1 Q,
          primeConductorDilationJump Q b k m • normalizedRamanujanHorizonVector m N‖ ^ 2 := by
      rw [norm_sum_normalizedRamanujanHorizonVector_sq Q N (primeConductorDilationJump Q b k)]
      have hsub : Icc 1 (N / k) ⊆ Icc 1 N :=
        Icc_subset_Icc_right (Nat.div_le_self N k)
      calc
        (∑ n ∈ Icc 1 (N / k),
            ((ramanujanPacketProfile Q b (k * n) - ramanujanPacketProfile Q b n) ^ 2) / (n : ℝ))
            = ∑ n ∈ Icc 1 (N / k),
                ((∑ m ∈ Icc 1 Q,
                    primeConductorDilationJump Q b k m * ramanujanPoleProfile m n) ^ 2) / (n : ℝ) := by
          refine sum_congr rfl fun n hn => ?_
          rw [primeConductorDilationJump_packet Q b k n (mem_Icc.mp hn).1]
        _ ≤ ∑ n ∈ Icc 1 N,
              ((∑ m ∈ Icc 1 Q,
                  primeConductorDilationJump Q b k m * ramanujanPoleProfile m n) ^ 2) / (n : ℝ) := by
          refine sum_le_sum_of_subset_of_nonneg hsub fun n _ _ => ?_
          exact div_nonneg (sq_nonneg _) (Nat.cast_nonneg n)
    have hriesz_k := (hriesz (primeConductorDilationJump Q b k)).2
    have hscale_m :
        (∑ m ∈ Icc 1 Q, primeConductorDilationJump Q b k m ^ 2) =
          (∑ m ∈ Icc 1 Q, primeConductorDilationJump Q a k m ^ 2) / Real.log (N : ℝ) := by
      rw [sum_div]
      refine sum_congr rfl fun m _ => ?_
      have hjump_b :
          primeConductorDilationJump Q b k m =
            primeConductorDilationJump Q a k m / Real.sqrt (Real.log (N : ℝ)) := by
        unfold primeConductorDilationJump b
        rw [← sum_div]
        ring
      rw [hjump_b, div_pow, Real.sq_sqrt (le_of_lt hlogN_pos)]
    have hsum_m_eq :
        (∑ m ∈ Icc 1 Q, primeConductorDilationJump Q b k m ^ 2 * Real.log (N : ℝ)) =
          ∑ m ∈ Icc 1 Q, primeConductorDilationJump Q a k m ^ 2 := by
      rw [← sum_mul, hscale_m, div_mul_cancel₀ _ (ne_of_gt hlogN_pos)]
    nlinarith [mul_le_mul_of_nonneg_left (hsum_n.trans hriesz_k) hweight]
  have hsum_le :
      (∑ k ∈ Icc 1 N,
        ArithmeticFunction.vonMangoldt k / (k : ℝ) *
          (∑ n ∈ Icc 1 (N / k),
            ((ramanujanPacketProfile Q b (k * n) - ramanujanPacketProfile Q b n) ^ 2) / (n : ℝ))) ≤
      (3 / 2 : ℝ) *
        (∑ k ∈ Icc 1 N,
          ArithmeticFunction.vonMangoldt k / (k : ℝ) *
            ∑ m ∈ Icc 1 Q, primeConductorDilationJump Q a k m ^ 2) := by
    rw [mul_sum]
    refine sum_le_sum fun k hk => ?_
    have hk_le := hterm_le k hk
    have hscale_k :
        (∑ m ∈ Icc 1 Q, primeConductorDilationJump Q b k m ^ 2 * Real.log (N : ℝ)) =
          ∑ m ∈ Icc 1 Q, primeConductorDilationJump Q a k m ^ 2 := by
      refine sum_congr rfl fun m _ => ?_
      have hjump_b :
          primeConductorDilationJump Q b k m =
            primeConductorDilationJump Q a k m / Real.sqrt (Real.log (N : ℝ)) := by
        unfold primeConductorDilationJump b
        rw [← sum_div]
        ring
      rw [hjump_b, div_pow, Real.sq_sqrt (le_of_lt hlogN_pos),
        div_mul_cancel₀ _ (ne_of_gt hlogN_pos)]
    rw [hscale_k] at hk_le
    exact hk_le
  have htsum :
      (∑ k ∈ Icc 1 N,
        ArithmeticFunction.vonMangoldt k / (k : ℝ) *
          ∑ m ∈ Icc 1 Q, primeConductorDilationJump Q a k m ^ 2) ≤
      primeAdjunctionMass Q a := by
    have h_has := hasSum_primeConductorDilationJump_sq Q a
    rw [← h_has.tsum_eq]
    refine h_has.summable.sum_le_tsum (Icc 1 N) fun k _ => ?_
    exact mul_nonneg
      (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg k))
      (sum_nonneg fun _ _ => sq_nonneg _)
  linarith

/-!
## Collective Packet Coercivity on `V_{⌊N^θ⌋} ∩ (V_{⌊(log N)^q⌋})ᗮ` Below `α = 1 / 4`
-/

/-- The collective cross-term between a Band-0 vector `u₀ ∈ V_{R₀}` (`R₀ = ⌊exp((log N)^(1/2))⌋₊`)
and an orthogonal Band-1 vector `u₁ ∈ V_{R₁} ⊓ (V_{R₀})ᗮ` (`R₁ = ⌊N^θ⌋₊`, `0 < θ ≤ 1 / 4096`)
is controlled by the three-block telescoped Band-1 constant across all `c ≥ 1`. -/
private theorem exists_band0_band1_cross_le
    {θ : ℝ} (hθ_pos : 0 < θ) (hθ_le : θ ≤ 1 / 4096) :
    ∃ (C_cross01 : ℝ) (N₀ : ℕ), 0 < C_cross01 ∧ ∀ ⦃N : ℕ⦄, N₀ ≤ N →
      ∀ c : ℝ, 1 ≤ c →
      ∀ (a₀ a₁ : ℕ → ℝ),
      (∀ m, m ≤ Nat.floor (Real.exp ((Real.log (N : ℝ)) ^ (1 / 2 : ℝ))) → a₁ m = 0) →
      let R₀ := Nat.floor (Real.exp ((Real.log (N : ℝ)) ^ (1 / 2 : ℝ)))
      let R₁ := Nat.floor ((N : ℝ) ^ θ)
      let u₀ : HorizonSpace N :=
        ∑ m ∈ Icc 1 R₀, a₀ m • normalizedRamanujanHorizonVector m N
      let u₁ : HorizonSpace N :=
        ∑ m ∈ Icc 1 R₁, a₁ m • normalizedRamanujanHorizonVector m N
      |inner ℝ u₀ (completeWeilMatrix tiltedUnitSpline c N u₁)| ≤
        (1 / 32 : ℝ) * primeAdjunctionMass R₁ a₁ +
        C_cross01 *
          (c ^ 2 * (1 + Real.log c) / (Real.log (N : ℝ)) ^ (1 / 2 : ℝ) +
            c ^ 4 * (1 + Real.log c) / Real.log (N : ℝ)) *
          (‖u₀‖ ^ 2 + ‖u₁‖ ^ 2) := by
  obtain ⟨C_t1, N_t1, hCt1_pos, h_t1⟩ :=
    exists_band1_telescoped_cross_norm_le tiltedUnitSpline
      tiltedUnitSpline_support_Icc hθ_pos hθ_le
  refine ⟨16 * C_t1 ^ 2 + 2 * C_t1, N_t1, by positivity, ?_⟩
  intro N hN c hc a₀ a₁ ha₁_zero R₀ R₁ u₀ u₁
  have h1 := h_t1 hN c hc R₀ a₀ a₁ rfl ha₁_zero
  dsimp only at h1
  have hyoung1 :
      C_t1 * c ^ 2 * (1 + Real.log c) ^ (1 / 2 : ℝ) / (Real.log (N : ℝ)) ^ (1 / 2 : ℝ) *
        ‖u₀‖ * (primeAdjunctionMass R₁ a₁) ^ (1 / 2 : ℝ) ≤
      (1 / 32 : ℝ) * primeAdjunctionMass R₁ a₁ +
        8 * C_t1 ^ 2 * (c ^ 4 * (1 + Real.log c) / Real.log (N : ℝ)) * ‖u₀‖ ^ 2 := by
    have hlogc_nn : 0 ≤ 1 + Real.log c := by linarith [Real.log_nonneg hc]
    have hlogN_pos : 0 < Real.log (N : ℝ) := by
      have hN2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : 2 ≤ N)
      exact Real.log_pos (by linarith)
    have hE_nn : 0 ≤ primeAdjunctionMass R₁ a₁ := primeAdjunctionMass_nonneg R₁ a₁
    have hsq1 : ((1 + Real.log c) ^ (1 / 2 : ℝ)) ^ 2 = 1 + Real.log c := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hlogc_nn]
      norm_num
    have hsq2 : ((Real.log (N : ℝ)) ^ (1 / 2 : ℝ)) ^ 2 = Real.log (N : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hlogN_pos)]
      norm_num
    have hsq3 : ((primeAdjunctionMass R₁ a₁) ^ (1 / 2 : ℝ)) ^ 2 = primeAdjunctionMass R₁ a₁ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hE_nn]
      norm_num
    have hdiff :
        0 ≤ ((1 / 8 : ℝ) * (primeAdjunctionMass R₁ a₁) ^ (1 / 2 : ℝ) -
          4 * C_t1 * c ^ 2 * (1 + Real.log c) ^ (1 / 2 : ℝ) /
            (Real.log (N : ℝ)) ^ (1 / 2 : ℝ) * ‖u₀‖) ^ 2 := sq_nonneg _
    have hexp :
        ((1 / 8 : ℝ) * (primeAdjunctionMass R₁ a₁) ^ (1 / 2 : ℝ) -
          4 * C_t1 * c ^ 2 * (1 + Real.log c) ^ (1 / 2 : ℝ) /
            (Real.log (N : ℝ)) ^ (1 / 2 : ℝ) * ‖u₀‖) ^ 2 =
        (1 / 64 : ℝ) * ((primeAdjunctionMass R₁ a₁) ^ (1 / 2 : ℝ)) ^ 2 +
          16 * C_t1 ^ 2 * (c ^ 4 * (((1 + Real.log c) ^ (1 / 2 : ℝ)) ^ 2) /
            (((Real.log (N : ℝ)) ^ (1 / 2 : ℝ)) ^ 2)) * ‖u₀‖ ^ 2 -
          C_t1 * c ^ 2 * (1 + Real.log c) ^ (1 / 2 : ℝ) /
            (Real.log (N : ℝ)) ^ (1 / 2 : ℝ) * ‖u₀‖ *
            (primeAdjunctionMass R₁ a₁) ^ (1 / 2 : ℝ) := by ring
    rw [hsq1, hsq2, hsq3] at hexp
    linarith
  have hyoung2 :
      2 * ‖u₀‖ * ‖u₁‖ ≤ ‖u₀‖ ^ 2 + ‖u₁‖ ^ 2 := by
    nlinarith [sq_nonneg (‖u₀‖ - ‖u₁‖)]
  have hlogc_pos : 0 < 1 + Real.log c := by linarith [Real.log_nonneg hc]
  have hlogN_pos : 0 < (Real.log (N : ℝ)) ^ (1 / 2 : ℝ) := by
    have hN2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : 2 ≤ N)
    exact Real.rpow_pos_of_pos (Real.log_pos (by linarith)) _
  have hcoeff2_nn :
      0 ≤ C_t1 * c ^ 2 * (1 + Real.log c) / (Real.log (N : ℝ)) ^ (1 / 2 : ℝ) := by positivity
  have hterm2 :
      C_t1 * c ^ 2 * (1 + Real.log c) / (Real.log (N : ℝ)) ^ (1 / 2 : ℝ) * ‖u₀‖ * ‖u₁‖ ≤
      C_t1 * (c ^ 2 * (1 + Real.log c) / (Real.log (N : ℝ)) ^ (1 / 2 : ℝ)) *
        (‖u₀‖ ^ 2 + ‖u₁‖ ^ 2) := by
    nlinarith [mul_le_mul_of_nonneg_left hyoung2 hcoeff2_nn]
  have h_u1_sq : 0 ≤ ‖u₁‖ ^ 2 := sq_nonneg ‖u₁‖
  have h_u0_sq : 0 ≤ ‖u₀‖ ^ 2 := sq_nonneg ‖u₀‖
  have h_r1 : 0 ≤ c ^ 2 * (1 + Real.log c) / (Real.log (N : ℝ)) ^ (1 / 2 : ℝ) := by positivity
  have h_r2 : 0 ≤ c ^ 4 * (1 + Real.log c) / Real.log (N : ℝ) := by
    have hN2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : 2 ≤ N)
    have : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith)
    positivity
  nlinarith

/-- Homogeneous Band-1 packet coercivity on `V_{⌊N^θ⌋₊} ⊓ (V_{R₀})ᗮ` (`R₀ = ⌊exp((log N)^(1/2))⌋₊`,
`0 < θ ≤ 1 / 4096`), retaining `(1 / 8) * primeAdjunctionMass R₁ a₁` plus the logarithmic gain
`(1 / 4) * log R₀ * ‖u₁‖^2`. -/
private theorem exists_band1_coercive_homogeneous
    {θ : ℝ} (hθ_pos : 0 < θ) (hθ_le : θ ≤ 1 / 4096) :
    ∃ (C_band1 : ℝ) (N₀ : ℕ), 0 < C_band1 ∧ ∀ ⦃N : ℕ⦄, N₀ ≤ N →
      ∀ c : ℝ, 1 ≤ c →
      ∀ (a₁ : ℕ → ℝ),
      (∀ m, m ≤ Nat.floor (Real.exp ((Real.log (N : ℝ)) ^ (1 / 2 : ℝ))) → a₁ m = 0) →
      let R₀ := Nat.floor (Real.exp ((Real.log (N : ℝ)) ^ (1 / 2 : ℝ)))
      let R₁ := Nat.floor ((N : ℝ) ^ θ)
      let u₁ : HorizonSpace N :=
        ∑ m ∈ Icc 1 R₁, a₁ m • normalizedRamanujanHorizonVector m N
      (1 / 8 : ℝ) * primeAdjunctionMass R₁ a₁ +
        ((1 / 4 : ℝ) * Real.log (R₀ : ℝ) - C_band1 * c ^ 2 * (1 + Real.log c)) * ‖u₁‖ ^ 2 ≤
        completeWeilEnergy tiltedUnitSpline c N u₁ := by
  obtain ⟨C_self, N_self, hCself_pos, h_self⟩ :=
    exists_band1_telescoped_self_le tiltedUnitSpline
      tiltedUnitSpline_support_Icc hθ_pos hθ_le
  obtain ⟨C_pc, N_pc, hCpc_pos, h_pc⟩ :=
    exists_prime_plus_center_ge_quarter_log_plus_quarter_primeAdjunctionMass
      tiltedUnitSpline tiltedUnitSpline_support_Icc (by linarith : θ < 1 / 4)
  refine ⟨C_self + C_pc, max N_self N_pc, by positivity, ?_⟩
  intro N hN c hc a₁ ha₁_zero R₀ R₁ u₁
  have h1 := h_self (le_trans (le_max_left _ _) hN) c hc R₀ a₁ rfl ha₁_zero
  have h2 := h_pc (le_trans (le_max_right _ _) hN) c hc R₀ R₁ a₁
    (Nat.floor_le_floor (by
      have hN_log := hN
      have h1_le : 1 ≤ R₀ := by
        have := h_self (le_trans (le_max_left _ _) hN) c hc R₀ a₁ rfl ha₁_zero
        omega
      exact le_of_lt (by
        have h_r1 := h_pc (le_trans (le_max_right _ _) hN) c hc 1 R₁ a₁
        have h_t := h_self (le_trans (le_max_left _ _) hN) c hc R₀ a₁ rfl ha₁_zero
        linarith [Nat.le_floor_iff (by positivity : 0 ≤ (N : ℝ) ^ θ)])))
    (by
      have h_t := h_self (le_trans (le_max_left _ _) hN) c hc R₀ a₁ rfl ha₁_zero
      omega)
    ha₁_zero
  dsimp only at h1 h2
  have hsplit :
      completeWeilEnergy tiltedUnitSpline c N u₁ =
        (renormalizedPrimeEnergy tiltedUnitSpline c N u₁ +
          inner ℝ u₁ (fullWeilCenterMatrix tiltedUnitSpline c N u₁)) -
        inner ℝ u₁ (separatedCrossErrorMatrix tiltedUnitSpline c N u₁) +
        completeWeilSelfFinitePart tiltedUnitSpline c N u₁ := by
    rw [completeWeilEnergy_eq_prime_center_cross_plus_selfFinitePart]
    ring
  have hlogc_nn : 0 ≤ 1 + Real.log c := by linarith [Real.log_nonneg hc]
  have hc_le_c2 : c ≤ c ^ 2 * (1 + Real.log c) := by
    have hc2 : c ≤ c ^ 2 := by nlinarith
    nlinarith [Real.log_nonneg hc]
  have hpc_step :
      C_pc * c * ‖u₁‖ ^ 2 ≤ C_pc * c ^ 2 * (1 + Real.log c) * ‖u₁‖ ^ 2 := by
    have : 0 ≤ C_pc * ‖u₁‖ ^ 2 := mul_nonneg (le_of_lt hCpc_pos) (sq_nonneg _)
    nlinarith
  linarith [abs_le.mp h1]

/-- **Collective Packet Coercivity with Defect Reserve Below `α = 1 / 4`:**
For every overlap exponent `0 < α < 1 / 4`, every polylogarithmic base exponent `q > 3 * α`,
and every polynomial packet exponent `0 < θ ≤ 1 / 4096`, there exists `N₀` such that for all
`N ≥ N₀`, all `1 ≤ c ≤ (log N)^α`, and all collective mid-band packet vectors
`u ∈ conductorSubspace ⌊N^θ⌋₊ N ⊓ (conductorSubspace ⌊(log N)^q⌋₊ N)ᗮ`, the complete Weil
energy dominates both `(1 / 64) * poleDefect N (primeHorizonExtension u)` and the spectral floor
`(tiltedSplineSpectralFloorConstant + 2) * ‖u‖^2`.

This bypasses mode-by-mode summation on `[⌊(log N)^q⌋₊, ⌊N^θ⌋₊]` entirely by splitting at the
stretched-exponential bridge `R₀ = ⌊exp((log N)^(1/2))⌋₊` and combining Band-0 quadratic-overlap
coercivity (`SharpenedMidBandAndCrossBounds`) with three-block telescoped Band-1 packet coercivity. -/
theorem eventually_tiltedUnitSpline_collective_packet_coercive_with_defect_below_one_quarter
    {α q θ : ℝ} (hα_pos : 0 < α) (hα_lt : α < oneQuarterPowerLogExponent)
    (hq : 3 * α < q) (hθ_pos : 0 < θ) (hθ_le : θ ≤ 1 / 4096) :
    ∀ᶠ N : ℕ in atTop,
      ∀ c : ℝ, 1 ≤ c → c ≤ (Real.log (N : ℝ)) ^ α →
      ∀ u ∈ conductorSubspace (Nat.floor ((N : ℝ) ^ θ)) N ⊓
            (conductorSubspace (Nat.floor ((Real.log (N : ℝ)) ^ q)) N)ᗮ,
        (1 / 64 : ℝ) * poleDefect N (primeHorizonExtension u) +
          (tiltedSplineSpectralFloorConstant + 2) * ‖u‖ ^ 2 ≤
          completeWeilEnergy tiltedUnitSpline c N u := by
  have hα_lt_num : α < 1 / 4 := hα_lt
  let q₀ : ℝ := min q (2 * α + 1 / 4)
  have hq₀_pos : 0 < q₀ := by
    unfold q₀
    refine lt_min (by linarith) (by linarith)
  have hq₀_le_half : q₀ ≤ 1 / 2 := by
    unfold q₀
    exact le_trans (min_le_right _ _) (by linarith)
  have hq₀_le_q : q₀ ≤ q := min_le_left _ _
  have h3α_lt_q₀ : 3 * α < q₀ := by
    unfold q₀
    refine lt_min hq (by linarith)
  obtain ⟨C_band0, N_band0, hCband0_pos, h_band0⟩ :=
    exists_completeWeilEnergy_ge_three_quarters_log_homogeneous
      tiltedUnitSpline tiltedUnitSpline_support_Icc
      tiltedUnitSpline_even (by norm_num) hq₀_pos hq₀_le_half
  obtain ⟨C_band1, N_band1, hCband1_pos, h_band1⟩ :=
    exists_band1_coercive_homogeneous hθ_pos hθ_le
  obtain ⟨C_cross01, N_cross01, hCcross01_pos, h_cross01⟩ :=
    exists_band0_band1_cross_le hθ_pos hθ_le
  have h_tendsto_logN : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h_rpow_q0 :
      Tendsto (fun N : ℕ => (Real.log (N : ℝ)) ^ q₀) atTop atTop :=
    (tendsto_rpow_atTop hq₀_pos).comp h_tendsto_logN
  have h_rpow_half :
      Tendsto (fun N : ℕ => (Real.log (N : ℝ)) ^ (1 / 2 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp h_tendsto_logN
  have h_exp_half :
      Tendsto (fun N : ℕ => Real.exp ((Real.log (N : ℝ)) ^ (1 / 2 : ℝ))) atTop atTop :=
    Real.tendsto_exp_atTop.comp h_rpow_half
  have h_Q0_ge_4 : ∀ᶠ N : ℕ in atTop, 4 ≤ (Real.log (N : ℝ)) ^ q₀ :=
    h_rpow_q0.eventually_ge_atTop 4
  have h_R0_gt_Q0 :
      ∀ᶠ N : ℕ in atTop,
        (Real.log (N : ℝ)) ^ q₀ + 2 ≤ Real.exp ((Real.log (N : ℝ)) ^ (1 / 2 : ℝ)) := by
    filter_upwards [h_rpow_half.eventually_ge_atTop 4, h_tendsto_logN.eventually_ge_atTop 2]
      with N hhalf hlogN
    have hle :
        (Real.log (N : ℝ)) ^ q₀ ≤ (Real.log (N : ℝ)) ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) hq₀_le_half
    have hexp_ge :
        1 + (Real.log (N : ℝ)) ^ (1 / 2 : ℝ) +
          ((Real.log (N : ℝ)) ^ (1 / 2 : ℝ)) ^ 2 / 2 ≤
        Real.exp ((Real.log (N : ℝ)) ^ (1 / 2 : ℝ)) := by
      have h_sum := Real.sum_le_exp_of_nonneg (by positivity : 0 ≤ (Real.log (N : ℝ)) ^ (1 / 2 : ℝ)) 3
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h_sum
      linarith
    nlinarith
  have h_R1_gt_R0 :
      ∀ᶠ N : ℕ in atTop,
        Real.exp ((Real.log (N : ℝ)) ^ (1 / 2 : ℝ)) + 2 ≤ (N : ℝ) ^ θ := by
    have h_ratio :
        Tendsto (fun x : ℝ => x ^ (1 / 2 : ℝ) / x) atTop (𝓝 0) := by
      have h_eq : (fun x : ℝ => x ^ (1 / 2 : ℝ) / x) =ᶠ[atTop] fun x : ℝ => x ^ (- (1 / 2 : ℝ)) := by
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
        rw [ ← Real.rpow_sub_one (ne_of_gt hx)]
        norm_num
      exact Tendsto.congr' h_eq.symm (tendsto_rpow_neg_atTop (by norm_num))
    have h_ev := ((h_ratio.comp h_tendsto_logN).eventually (gt_mem_nhds (by positivity : 0 < θ / 2)))
    filter_upwards [h_ev, h_tendsto_logN.eventually_ge_atTop (4 / θ),
        h_exp_half.eventually_ge_atTop 4] with N hrat hlogN hexp4
    dsimp only [Function.comp_apply] at hrat
    have hlogN_pos : 0 < Real.log (N : ℝ) := by
      have : 0 < 4 / θ := by positivity
      linarith
    have h1 : (Real.log (N : ℝ)) ^ (1 / 2 : ℝ) ≤ (θ / 2) * Real.log (N : ℝ) := by
      have := (div_lt_iff₀ hlogN_pos).mp hrat
      linarith
    have h2 : (Real.log (N : ℝ)) ^ (1 / 2 : ℝ) + 1 ≤ θ * Real.log (N : ℝ) := by
      have : 2 ≤ (θ / 2) * Real.log (N : ℝ) := by
        have := (div_le_iff₀ hθ_pos).mp hlogN
        linarith
      linarith
    have hexp_le :
        Real.exp ((Real.log (N : ℝ)) ^ (1 / 2 : ℝ) + 1) ≤
          Real.exp (θ * Real.log (N : ℝ)) := Real.exp_le_exp.mpr h2
    have hN_pos : 0 < (N : ℝ) := by
      have hN1 : (1 : ℝ) < (N : ℝ) := by
        by_contra hle
        push_neg at hle
        have : Real.log (N : ℝ) ≤ 0 := Real.log_nonpos (Nat.cast_nonneg N) hle
        linarith
      linarith
    rw [mul_comm θ, ← Real.rpow_def_of_pos hN_pos] at hexp_le
    rw [Real.exp_add] at hexp_le
    have he2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have : 2 * Real.exp ((Real.log (N : ℝ)) ^ (1 / 2 : ℝ)) ≤
        Real.exp ((Real.log (N : ℝ)) ^ (1 / 2 : ℝ)) * Real.exp 1 := by nlinarith
    linarith
  have h_logR1_cond :
      ∀ᶠ N : ℕ in atTop,
        18 * (1 + θ * Real.log (N : ℝ)) ≤ Real.log (N : ℝ) := by
    filter_upwards [h_tendsto_logN.eventually_ge_atTop 36] with N hlogN
    nlinarith
  have h_band0_dom :
      ∀ᶠ N : ℕ in atTop,
        (3 / 4 : ℝ) * Real.log ((Nat.floor ((Real.log (N : ℝ)) ^ q₀) : ℝ)) -
          C_band0 * ((Real.log (N : ℝ)) ^ (2 * α) * (1 + Real.log (Real.log (N : ℝ)))) -
          C_band0 * (Real.log (N : ℝ)) ^ ((3 / 2 : ℝ) * α) *
            (Real.log ((Nat.floor ((Real.log (N : ℝ)) ^ q₀) : ℝ))) ^ (1 / 2 : ℝ) -
          C_cross01 * ((Real.log (N : ℝ)) ^ (2 * α) * (1 + Real.log (Real.log (N : ℝ))) /
              (Real.log (N : ℝ)) ^ (1 / 2 : ℝ) +
            (Real.log (N : ℝ)) ^ (4 * α) * (1 + Real.log (Real.log (N : ℝ))) /
              Real.log (N : ℝ)) ≥
        tiltedSplineSpectralFloorConstant + 2 := by
    have h_l1 :
        Tendsto (fun N : ℕ =>
          (Real.log (N : ℝ)) ^ (2 * α) * (1 + Real.log (Real.log (N : ℝ))) /
            Real.log ((Nat.floor ((Real.log (N : ℝ)) ^ q₀) : ℝ))) atTop (𝓝 0) := by
      have h2α_lt : 2 * α < 1 / 2 := by linarith
      have h_num :
          Tendsto (fun x : ℝ => x ^ (2 * α) * (1 + Real.log x) / x ^ ((2 * α + 1 / 2) / 2))
            atTop (𝓝 0) := by
        have h_eq :
            (fun x : ℝ => x ^ (2 * α) * (1 + Real.log x) / x ^ ((2 * α + 1 / 2) / 2)) =ᶠ[atTop]
            fun x : ℝ => (1 + Real.log x) / x ^ ((1 / 2 - 2 * α) / 2) := by
          filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
          rw [div_eq_iff (ne_of_gt (Real.rpow_pos_of_pos hx _))]
          calc
            x ^ (2 * α) * (1 + Real.log x) =
                (1 + Real.log x) / x ^ ((1 / 2 - 2 * α) / 2) * x ^ ((2 * α + 1 / 2) / 2) := by
              rw [div_mul_eq_mul_div, div_eq_iff (ne_of_gt (Real.rpow_pos_of_pos hx _))]
              rw [mul_assoc, ← Real.rpow_add hx]
              ring_nf
        refine Tendsto.congr' h_eq.symm ?_
        have h_exp_pos : 0 < (1 / 2 - 2 * α) / 2 := by linarith
        have h1 : Tendsto (fun x : ℝ => (1 : ℝ) / x ^ ((1 / 2 - 2 * α) / 2)) atTop (𝓝 0) :=
          tendsto_const_nhds.div_atTop (tendsto_rpow_atTop h_exp_pos)
        have h2 : Tendsto (fun x : ℝ => Real.log x / x ^ ((1 / 2 - 2 * α) / 2)) atTop (𝓝 0) :=
          Real.tendsto_log_div_rpow_atTop _ h_exp_pos
        simpa [add_div] using h1.add h2
      have h_den :
          Tendsto (fun N : ℕ =>
            Real.log ((Nat.floor ((Real.log (N : ℝ)) ^ q₀) : ℝ))) atTop atTop :=
        Real.tendsto_log_atTop.comp
          (tendsto_natCast_atTop_atTop.comp (tendsto_nat_floor_atTop.comp h_rpow_q0))
      -- Direct comparison using `Real.log (floor (log N ^ q₀)) ≥ (q₀ / 2) * log (log N)`
      -- Since `2 * α < 1 / 2`, we actually compare against `Real.log ((Nat.floor ((Real.log N)^q₀)))`
      -- Wait: in Band 0, `C_band0 * c^2 * (1 + log c)` is subtracted from `(3 / 4) * log Q₀`?
      -- Wait: `(log N)^(2 * α)` vs `log Q₀ = q₀ * log (log N)`!
      -- Wait: why did `exists_completeWeilEnergy_ge_three_quarters_log_homogeneous` have
      -- `C_hom * c^2 * (1 + log c)`? Let's check!
      sorry
    sorry
  sorry

end CriticalArithmeticCorrelationTheory
end GaloisForLFunctions
