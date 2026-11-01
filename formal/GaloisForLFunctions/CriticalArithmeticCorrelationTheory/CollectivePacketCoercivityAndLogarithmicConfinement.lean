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

2. **Power-of-Logarithm Logarithmic Defect Reserve, `O(log c)` Sublevel Confinement, and `c⁻⁸`
   All-Vector Defect Reserve Below `α = 1 / 9`:**
   - Retaining half of the terminal prime-defect reserve `(a / (2 * c^7)) * poleDefect N (primeHorizonExtension w)`
     in the asymmetric two-region decomposition on `(V_{R₁})ᗮ` and combining it with the unused
     prime-adjunction mass on Bands 0 and 1 and with `completedConductorEnergy_ge_logarithmic_reserve`
     on `V_{Q₁}` yields a joint all-vector logarithmic defect reserve and spectral floor across
     `1 ≤ c ≤ (log N)^α` (`0 < α < 1 / 9`):
     `(a₀ / c^7) * (poleDefect N (primeHorizonExtension x) - C * log (2 * c) * ‖x‖^2) + (κ₀ / (2 * c^7)) * ‖x‖^2 ≤ completeWeilEnergy tiltedUnitSpline c N x`.
   - As immediate corollaries:
     * `exists_completeWeil_logarithmic_defect_reserve_iteratedLog` is lifted from iterated-log
       overlap `c ≤ (log log N)^α` (`α < 1 / 16`) to power-of-logarithm overlap `1 ≤ c ≤ (log N)^α`
       (`α < 1 / 9`);
     * every vector in the sublevel set
       `completeWeilEnergy tiltedUnitSpline c N x ≤ (κ₀ / (2 * c^7)) * ‖x‖^2` satisfies the
       logarithmic confinement bound `poleDefect N (primeHorizonExtension x) ≤ C * log (2 * c) * ‖x‖^2`
       (and `≤ C * c^2 * ‖x‖^2`), replacing `C * c^{16}` by `C * log (2 * c)`;
     * the all-vector positive defect reserve is sharpened from `c^{-23}` to `c^{-8}`.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Finset Filter Topology ArithmeticFunction
open scoped Classical BigOperators RealInnerProductSpace Matrix

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

open CompletedArithmeticForms RenormalizedArithmeticPotentialTheory
  RenormalizedArithmeticPotentialTheory.CompletedShell SpacingScaleHarmonicAnalysis
  ArithmeticElectrostatics CriticalScaleArithmeticRigidity
  SuccessorShellArithmetic ArithmeticIntersectionTheory

/-- The `1 / 4` power-of-logarithm overlap exponent threshold for collective packet coercivity. -/
def oneQuarterPowerLogExponent : ℝ := 1 / 4

theorem oneQuarterPowerLogExponent_pos :
    0 < oneQuarterPowerLogExponent := by
  norm_num [oneQuarterPowerLogExponent]

theorem oneEighthPowerLogExponent_lt_oneQuarterPowerLogExponent :
    oneEighthPowerLogExponent < oneQuarterPowerLogExponent := by
  norm_num [oneEighthPowerLogExponent, oneQuarterPowerLogExponent]

theorem oneNinthPowerLogExponent_lt_oneQuarterPowerLogExponent :
    oneNinthPowerLogExponent < oneQuarterPowerLogExponent := by
  norm_num [oneNinthPowerLogExponent, oneQuarterPowerLogExponent]

/-! ### 1. Quadratic subadditivity of `poleDefect` and two-sided Riesz sandwich on packets -/

theorem primeHorizonExtension_add {N : ℕ}
    (x y : EuclideanSpace ℝ (PrimeHorizonIndex N)) (n : ℕ) :
    primeHorizonExtension (x + y) n =
      primeHorizonExtension x n + primeHorizonExtension y n := by
  unfold primeHorizonExtension
  split_ifs with h
  · rfl
  · ring

/-- Cauchy–Schwarz triangle inequality for the quadratic prime-power dilation defect `poleDefect`:
`poleDefect N (x + y) ≤ 2 * poleDefect N x + 2 * poleDefect N y`. -/
theorem poleDefect_add_le (N : ℕ) (x y : ℕ → ℝ) :
    poleDefect N (fun n => x n + y n) ≤ 2 * poleDefect N x + 2 * poleDefect N y := by
  unfold poleDefect
  rw [← mul_sum, ← mul_sum, ← sum_add_distrib]
  refine sum_le_sum fun n _ => ?_
  rw [← mul_sum, ← mul_sum, ← sum_add_distrib]
  refine sum_le_sum fun k _ => ?_
  have hΛ : 0 ≤ vonMangoldt k := vonMangoldt_nonneg
  have hsq :
      ((x (n * k) + y (n * k)) - (x n + y n) / Real.sqrt k) ^ 2 ≤
        2 * (x (n * k) - x n / Real.sqrt k) ^ 2 +
          2 * (y (n * k) - y n / Real.sqrt k) ^ 2 := by
    have hsplit :
        (x (n * k) + y (n * k)) - (x n + y n) / Real.sqrt k =
          (x (n * k) - x n / Real.sqrt k) + (y (n * k) - y n / Real.sqrt k) := by ring
    rw [hsplit]
    have hdiff :
        0 ≤ ((x (n * k) - x n / Real.sqrt k) - (y (n * k) - y n / Real.sqrt k)) ^ 2 :=
      sq_nonneg _
    nlinarith only [hdiff]
  have hm := mul_le_mul_of_nonneg_left hsq hΛ
  linarith only [hm]

/-- Quadratic subadditivity of `poleDefect` composed with `primeHorizonExtension`. -/
theorem poleDefect_primeHorizonExtension_add_le
    (N : ℕ) (x y : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    poleDefect N (primeHorizonExtension (x + y)) ≤
      2 * poleDefect N (primeHorizonExtension x) +
        2 * poleDefect N (primeHorizonExtension y) := by
  have heq : primeHorizonExtension (x + y) =
      fun n => primeHorizonExtension x n + primeHorizonExtension y n :=
    funext (primeHorizonExtension_add x y)
  rw [heq]
  exact poleDefect_add_le N (primeHorizonExtension x) (primeHorizonExtension y)

/-- Three-term quadratic subadditivity of `poleDefect` composed with `primeHorizonExtension`. -/
theorem poleDefect_primeHorizonExtension_three_add_le
    (N : ℕ) (x y z : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    poleDefect N (primeHorizonExtension (x + y + z)) ≤
      4 * poleDefect N (primeHorizonExtension x) +
        4 * poleDefect N (primeHorizonExtension y) +
        2 * poleDefect N (primeHorizonExtension z) := by
  have h12 := poleDefect_primeHorizonExtension_add_le N (x + y) z
  have hxy := poleDefect_primeHorizonExtension_add_le N x y
  linarith only [h12, hxy]

/-- Upper Riesz bound for the prime-power dilation defect on normalized Ramanujan packets:
whenever `2 ≤ Q`, `Q * Q ≤ N`, and `18 * (1 + Real.log Q) ≤ Real.log N`, the finite-horizon
prime-power dilation defect is bounded above by `(3 / 2) * primeAdjunctionMass Q a`. -/
theorem poleDefect_normalizedRamanujanPacket_le_three_halves_primeAdjunctionMass
    {Q N : ℕ} (hQ : 2 ≤ Q) (hQN : Q * Q ≤ N)
    (hlog : 18 * (1 + Real.log (Q : ℝ)) ≤ Real.log (N : ℝ)) (a : ℕ → ℝ) :
    poleDefect N
        (primeHorizonExtension
          (∑ m ∈ Icc 1 Q, a m • normalizedRamanujanHorizonVector m N)) ≤
      (3 / 2 : ℝ) * primeAdjunctionMass Q a := by
  let b : ℕ → ℝ := fun m => a m / Real.sqrt (Real.log N)
  let y := ∑ m ∈ Icc 1 Q, a m • normalizedRamanujanHorizonVector m N
  have hL : 0 < Real.log (N : ℝ) := by
    have hlogQ : 0 ≤ Real.log (Q : ℝ) := Real.log_natCast_nonneg Q
    linarith only [hlog, hlogQ]
  have hsL : 0 < Real.sqrt (Real.log (N : ℝ)) := Real.sqrt_pos.mpr hL
  have hx (n : ℕ) (hn : n ∈ Icc 1 N) :
      primeHorizonExtension y n = ∑ m ∈ Icc 1 Q, b m * ramanujanPoleProfile m n := by
    rw [primeHorizonExtension_coe y ⟨n, hn⟩]
    change (PiLp.projₗ (𝕜 := ℝ) 2 (fun _ : PrimeHorizonIndex N => ℝ) ⟨n, hn⟩)
      (∑ m ∈ Icc 1 Q, a m • normalizedRamanujanHorizonVector m N) = _
    rw [map_sum]
    refine sum_congr rfl fun m _ => ?_
    change a m * ((Real.sqrt (Real.log N))⁻¹ * ramanujanPoleProfile m n) = _
    dsimp only [b]
    ring
  have hdef : poleDefect N (primeHorizonExtension y) =
      poleDefect N (fun n => ∑ m ∈ Icc 1 Q, b m * ramanujanPoleProfile m n) := by
    unfold poleDefect
    refine sum_congr rfl fun n hn => sum_congr rfl fun k hk => ?_
    have hnk : n * k ∈ Icc 1 N := by
      refine mem_Icc.mpr ⟨Nat.mul_pos (mem_Icc.mp hn).1 (mem_Icc.mp hk).1, ?_⟩
      simpa only [Nat.mul_comm] using
        (Nat.le_div_iff_mul_le (mem_Icc.mp hn).1).mp (mem_Icc.mp hk).2
    rw [hx n hn, hx (n * k) hnk]
  rw [hdef, poleDefect_ramanujanPacket_eq Q N b]
  have hriesz := half_and_three_halves_riesz_of_log_le hQ hQN hlog
  have hterm_le : ∀ k ∈ Icc 1 N,
      vonMangoldt k / (k : ℝ) *
        (∑ n ∈ Icc 1 (N / k),
          ((∑ m ∈ Icc 1 Q, b m * normalizedRamanujanMode m (k * n)) -
            ∑ m ∈ Icc 1 Q, b m * normalizedRamanujanMode m n) ^ 2 / (n : ℝ)) ≤
      (3 / 2 : ℝ) *
        (vonMangoldt k / (k : ℝ) *
          ∑ m ∈ Icc 1 Q, primeConductorDilationJump Q a k m ^ 2) := by
    intro k _
    have hweight : 0 ≤ vonMangoldt k / (k : ℝ) :=
      div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg k)
    let j_a := primeConductorDilationJump Q a k
    let v_k := ∑ m ∈ Icc 1 Q, j_a m • normalizedRamanujanHorizonVector m N
    have hjump_b : ∀ m, primeConductorDilationJump Q b k m =
        j_a m / Real.sqrt (Real.log N) := by
      intro m
      dsimp only [j_a, b]
      unfold primeConductorDilationJump
      rw [← sum_div]
      refine sum_congr rfl fun l _ => ?_
      ring
    have hrow_eq : ∀ n ∈ Icc 1 (N / k),
        ((∑ m ∈ Icc 1 Q, b m * normalizedRamanujanMode m (k * n)) -
          ∑ m ∈ Icc 1 Q, b m * normalizedRamanujanMode m n) ^ 2 / (n : ℝ) =
        primeHorizonExtension v_k n ^ 2 := by
      intro n hn
      have hnN : n ∈ Icc 1 N :=
        Icc_subset_Icc_right (Nat.div_le_self N k) hn
      have hn1 : 0 < n := (mem_Icc.mp hn).1
      rw [← primeConductorDilationJump_packet Q b k n]
      rw [primeHorizonExtension_coe v_k ⟨n, hnN⟩]
      have hv_n : v_k ⟨n, hnN⟩ =
          (∑ m ∈ Icc 1 Q, (j_a m / Real.sqrt (Real.log N)) * normalizedRamanujanMode m n) /
            Real.sqrt n := by
        change (PiLp.projₗ (𝕜 := ℝ) 2 (fun _ : PrimeHorizonIndex N => ℝ) ⟨n, hnN⟩)
          (∑ m ∈ Icc 1 Q, j_a m • normalizedRamanujanHorizonVector m N) = _
        rw [map_sum, sum_div]
        refine sum_congr rfl fun m _ => ?_
        change j_a m * ((Real.sqrt (Real.log N))⁻¹ * (normalizedRamanujanMode m n / Real.sqrt n)) = _
        ring
      rw [hv_n, div_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
      congr 2
      refine sum_congr rfl fun m _ => ?_
      rw [hjump_b m]
    have hsum_le_norm :
        (∑ n ∈ Icc 1 (N / k),
          ((∑ m ∈ Icc 1 Q, b m * normalizedRamanujanMode m (k * n)) -
            ∑ m ∈ Icc 1 Q, b m * normalizedRamanujanMode m n) ^ 2 / (n : ℝ)) ≤
        ‖v_k‖ ^ 2 := by
      rw [sum_congr rfl hrow_eq, ← sum_primeHorizonExtension_sq v_k]
      exact sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_right (Nat.div_le_self N k))
        fun _ _ _ => sq_nonneg _
    have hriesz_k : ‖v_k‖ ^ 2 ≤ (3 / 2 : ℝ) * ∑ m ∈ Icc 1 Q, j_a m ^ 2 := (hriesz j_a).2
    have hcomb := mul_le_mul_of_nonneg_left (hsum_le_norm.trans hriesz_k) hweight
    linarith only [hcomb]
  have hsum_le :
      (∑ k ∈ Icc 1 N, vonMangoldt k / (k : ℝ) *
        ∑ n ∈ Icc 1 (N / k),
          ((∑ m ∈ Icc 1 Q, b m * normalizedRamanujanMode m (k * n)) -
            ∑ m ∈ Icc 1 Q, b m * normalizedRamanujanMode m n) ^ 2 / (n : ℝ)) ≤
      (3 / 2 : ℝ) *
        ∑ k ∈ Icc 1 N, vonMangoldt k / (k : ℝ) *
          ∑ m ∈ Icc 1 Q, primeConductorDilationJump Q a k m ^ 2 := by
    rw [mul_sum]
    exact sum_le_sum hterm_le
  have htsum :
      (∑ k ∈ Icc 1 N, vonMangoldt k / (k : ℝ) *
        ∑ m ∈ Icc 1 Q, primeConductorDilationJump Q a k m ^ 2) ≤
      primeAdjunctionMass Q a := by
    have hs := hasSum_primeConductorDilationJump_sq Q a
    have h := hs.summable.sum_le_tsum (Icc 1 N) fun k _ =>
      mul_nonneg (div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg k))
        (sum_nonneg fun _ _ => sq_nonneg _)
    simpa only [hs.tsum_eq, primeAdjunctionMass] using h
  linarith only [hsum_le, htsum]

/-- Two-sided Riesz sandwich comparing the finite-horizon prime-power dilation defect
`poleDefect N (primeHorizonExtension u)` with `primeAdjunctionMass Q a`:
when `2 ≤ Q`, `Q * Q ≤ N`, and `18 * (1 + Real.log Q) ≤ Real.log N`,
`(3 / 4) * primeAdjunctionMass Q a ≤ poleDefect N (primeHorizonExtension u) ≤ (3 / 2) * primeAdjunctionMass Q a`. -/
theorem poleDefect_normalizedRamanujanPacket_sandwich_primeAdjunctionMass
    {Q N : ℕ} (hQ : 2 ≤ Q) (hQN : Q * Q ≤ N)
    (hlog : 18 * (1 + Real.log (Q : ℝ)) ≤ Real.log (N : ℝ)) (a : ℕ → ℝ) :
    (3 / 4 : ℝ) * primeAdjunctionMass Q a ≤
      poleDefect N
        (primeHorizonExtension
          (∑ m ∈ Icc 1 Q, a m • normalizedRamanujanHorizonVector m N)) ∧
    poleDefect N
        (primeHorizonExtension
          (∑ m ∈ Icc 1 Q, a m • normalizedRamanujanHorizonVector m N)) ≤
      (3 / 2 : ℝ) * primeAdjunctionMass Q a := by
  refine ⟨?_, poleDefect_normalizedRamanujanPacket_le_three_halves_primeAdjunctionMass hQ hQN hlog a⟩
  have hN2 : 2 ≤ N := (by norm_num : 2 ≤ 2 * 2).trans ((Nat.mul_le_mul hQ hQ).trans hQN)
  have hL : 0 < Real.log (N : ℝ) := by
    have := Real.log_natCast_nonneg Q; linarith only [hlog, this]
  have hraw := poleDefect_normalizedRamanujanPacket_ge_logarithmic hQ hN2 a
  change ((Real.log N - 3 * Real.log Q - 1) / Real.log N) * primeAdjunctionMass Q a ≤ _ at hraw
  have h34 : (3 / 4 : ℝ) ≤ (Real.log N - 3 * Real.log Q - 1) / Real.log N := by
    rw [le_div_iff₀ hL]
    have hlogQ : 0 ≤ Real.log (Q : ℝ) := Real.log_natCast_nonneg Q
    linarith only [hlog, hlogQ]
  exact (mul_le_mul_of_nonneg_right h34 (primeAdjunctionMass_nonneg Q a)).trans hraw

/-! ### 2. Collective Packet Coercivity on `V_{⌊N^θ⌋} ∩ (V_{⌊(log N)^q⌋})ᗮ` Below `α = 1 / 4` -/

/-- Orthogonal two-band split for a collective mid-band packet vector
`u ∈ conductorSubspace R₁ N ⊓ (conductorSubspace Q₁ N)ᗮ` at the intermediate cutoff `R₀`:
`u = u₀ + u₁` with `u₀ ∈ conductorSubspace R₀ N ⊓ (conductorSubspace Q₁ N)ᗮ`,
`u₁ ∈ conductorSubspace R₁ N ⊓ (conductorSubspace R₀ N)ᗮ`, and `‖u‖^2 = ‖u₀‖^2 + ‖u₁‖^2`. -/
private theorem collective_two_band_orthogonal_split {Q₁ R₀ R₁ N : ℕ}
    (hQR₀ : Q₁ ≤ R₀) (hR₀R₁ : R₀ ≤ R₁)
    {u : EuclideanSpace ℝ (PrimeHorizonIndex N)}
    (hu_mem : u ∈ conductorSubspace R₁ N)
    (hu_orth : u ∈ (conductorSubspace Q₁ N)ᗮ) :
    ∃ u₀ u₁ : EuclideanSpace ℝ (PrimeHorizonIndex N),
      u = u₀ + u₁ ∧
      u₀ ∈ conductorSubspace R₀ N ∧
      u₀ ∈ (conductorSubspace Q₁ N)ᗮ ∧
      u₁ ∈ conductorSubspace R₁ N ∧
      u₁ ∈ (conductorSubspace R₀ N)ᗮ ∧
      ‖u‖ ^ 2 = ‖u₀‖ ^ 2 + ‖u₁‖ ^ 2 := by
  let u₀ := (conductorSubspace R₀ N).starProjection u
  let u₁ := u - u₀
  have hu_eq : u = u₀ + u₁ := by dsimp only [u₁]; abel
  have hu₀_mem : u₀ ∈ conductorSubspace R₀ N :=
    (conductorSubspace R₀ N).starProjection_apply_mem u
  have hu₀_in_R₁ : u₀ ∈ conductorSubspace R₁ N :=
    conductorSubspace_mono hR₀R₁ N hu₀_mem
  have hu₁_mem : u₁ ∈ conductorSubspace R₁ N :=
    Submodule.sub_mem _ hu_mem hu₀_in_R₁
  have hu₁_orthR₀ : u₁ ∈ (conductorSubspace R₀ N)ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro v hv
    rw [real_inner_comm]
    exact (conductorSubspace R₀ N).starProjection_inner_eq_zero u v hv
  have hu₀_orthQ : u₀ ∈ (conductorSubspace Q₁ N)ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro v hv
    have hvR₀ : v ∈ conductorSubspace R₀ N := conductorSubspace_mono hQR₀ N hv
    have huv : ⟪v, u⟫ = 0 := Submodule.inner_right_of_mem_orthogonal hv hu_orth
    have hdiff : ⟪v, u₁⟫ = 0 := Submodule.inner_right_of_mem_orthogonal hvR₀ hu₁_orthR₀
    have hu₀_id : u₀ = u - u₁ := by dsimp only [u₁]; abel
    rw [hu₀_id, inner_sub_right, huv, hdiff, sub_zero]
  have horth01 : ⟪u₀, u₁⟫ = 0 :=
    Submodule.inner_right_of_mem_orthogonal hu₀_mem hu₁_orthR₀
  have hnorm : ‖u‖ ^ 2 = ‖u₀‖ ^ 2 + ‖u₁‖ ^ 2 := by
    have h1 := norm_add_sq_real u₀ u₁
    rw [← hu_eq, horth01, mul_zero, add_zero] at h1
    exact h1
  exact ⟨u₀, u₁, hu_eq, hu₀_mem, hu₀_orthQ, hu₁_mem, hu₁_orthR₀, hnorm⟩

/-- Cross payment between `u₀ ∈ V_{R₀} ∩ (V_1)ᗮ` and `u₁ ∈ (V_{R₀})ᗮ` at `M = N`, spending
`(1 / 16) * (log N)^(1/2) * ‖u₁‖^2` from Band 1's subpolynomial logarithmic reserve. -/
private theorem exists_band0_band1_cross_le :
    ∃ C_cross01 : ℝ, 0 < C_cross01 ∧
      ∀ {R₀ N : ℕ} {c : ℝ},
        2 ≤ R₀ → R₀ ^ 6 ≤ N → 18 * (1 + Real.log R₀) ≤ Real.log N →
        1 ≤ c → c / N ≤ 1 / 3 →
        ((R₀ * R₀ : ℕ) + 1 : ℝ) * (linearNearRowRadius c + 1) ≤ N →
        ((R₀ * R₀ : ℕ) + 1 : ℝ) * (c * Real.exp 1 + 1) ≤ N →
        1 + Real.log R₀ ≤ 2 * Real.log N ^ (1 / 2 : ℝ) →
        C_cross01 * (1 / Real.log N ^ (1 / 2 : ℝ) +
          c ^ 2 * (1 + Real.log c) / Real.log N ^ (1 / 2 : ℝ) +
          c ^ 4 * (1 + Real.log c) / Real.log N +
          c ^ 3 * (R₀ : ℝ) ^ 2 * (Real.log N / N)) ≤ 1 →
      ∀ a₀ : ℕ → ℝ,
        (∑ m ∈ Icc 1 R₀, a₀ m • normalizedRamanujanHorizonVector m N) ∈
          (conductorSubspace 1 N)ᗮ →
      ∀ {u₁ : EuclideanSpace ℝ (PrimeHorizonIndex N)}, u₁ ∈ (conductorSubspace R₀ N)ᗮ →
        2 * |⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
            (∑ m ∈ Icc 1 R₀, a₀ m • normalizedRamanujanHorizonVector m N), u₁⟫| ≤
          (1 / 32 : ℝ) * primeAdjunctionMass R₀ a₀ +
            (1 / 4 : ℝ) * ‖∑ m ∈ Icc 1 R₀, a₀ m • normalizedRamanujanHorizonVector m N‖ ^ 2 +
            (1 / 16 : ℝ) * Real.log N ^ (1 / 2 : ℝ) * ‖u₁‖ ^ 2 := by
  obtain ⟨C_pr, C_np, hC_pr, hC_np, hcross⟩ := exists_completeWeil_cross_le_c9_split_reserves
  let C_cross01 := 32768 * (C_pr + C_np + 1)
  refine ⟨C_cross01, by dsimp only [C_cross01]; positivity, ?_⟩
  intro R₀ N c hR₀ hR₀6 hlog hc1 hw1 hsize_near hsize_up hH₀_ub hsmall a₀ hu₀_1 u₁ hu₁
  let L := Real.log (N : ℝ)
  let Lh := L ^ (1 / 2 : ℝ)
  let s := (1 / 32 : ℝ) * Lh
  let u₀ := ∑ m ∈ Icc 1 R₀, a₀ m • normalizedRamanujanHorizonVector m N
  let H₀ := 1 + Real.log (R₀ : ℝ)
  let A₀ := ∑ m ∈ Icc 1 R₀, a₀ m ^ 2
  let E₀ := primeAdjunctionMass R₀ a₀
  let G₀ := ∑ m ∈ Icc 1 R₀, (1 + Real.log m) * a₀ m ^ 2
  have hRR₀ : R₀ * R₀ ≤ N := by
    have hh := (Nat.pow_le_pow_right (by omega : 0 < R₀) (by norm_num : 2 ≤ 6)).trans hR₀6
    simpa only [sq] using hh
  have hL1 : 1 ≤ L := by dsimp only [L]; linarith only [hlog, Real.log_natCast_nonneg R₀]
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have hLh1 : 1 ≤ Lh := Real.one_le_rpow hL1 (by norm_num)
  have hLh0 : 0 < Lh := zero_lt_one.trans_le hLh1
  have hLh_sq : Lh * Lh = L := by
    dsimp only [Lh]
    rw [← Real.rpow_add hL0]
    norm_num [Real.rpow_one]
  have hs0 : 0 < s := by dsimp only [s]; positivity
  have hraw := hcross hR₀ hR₀6 (le_rfl : N ≤ N) hlog hc1 hw1 hsize_near hsize_up a₀ hu₀_1 hu₁
    s s s hs0 hs0 hs0
  rw [sum_primeHorizonExtension_sq u₁, Finset.Ioc_self, sum_empty, mul_zero, add_zero] at hraw
  have hterm_N : terminalPacketCost R₀ N N ≤ 2 := by
    unfold terminalPacketCost
    rw [sub_self, zero_add]
    have hRsq : (R₀ : ℝ) ^ 2 ≤ (N : ℝ) + 1 := by
      have hcast : (R₀ : ℝ) ^ 2 ≤ (N : ℝ) := by
        simpa only [sq, Nat.cast_mul] using (Nat.cast_le (α := ℝ).mpr hRR₀)
      linarith only [hcast]
    exact (div_le_iff₀ (by positivity : (0 : ℝ) < (N : ℝ) + 1)).mpr (by linarith only [hRsq])
  have hA₀ : 0 ≤ A₀ := sum_nonneg fun _ _ => sq_nonneg _
  have hE₀ : 0 ≤ E₀ := primeAdjunctionMass_nonneg R₀ a₀
  have hG₀ : 0 ≤ G₀ := sum_nonneg fun m _ => by have := Real.log_natCast_nonneg m; positivity
  have hAU : A₀ ≤ 2 * ‖u₀‖ ^ 2 := by
    have hh := (half_and_three_halves_riesz_of_log_le hR₀ hRR₀ hlog a₀).1
    linarith only [hh]
  have hG_le : G₀ ≤ 2 * ‖u₀‖ ^ 2 + E₀ := by
    have hGE : G₀ ≤ A₀ + E₀ := by
      dsimp only [G₀, A₀, E₀, primeAdjunctionMass]
      rw [← sum_add_distrib]
      refine sum_le_sum fun m _ => ?_
      nlinarith only [mul_nonneg (tameDifferent_nonneg m) (sq_nonneg (a₀ m))]
    linarith only [hGE, hAU]
  let e := 1 / Lh + c ^ 2 * (1 + Real.log c) / Lh +
    c ^ 4 * (1 + Real.log c) / L + c ^ 3 * (R₀ : ℝ) ^ 2 * (L / (N : ℝ))
  have hlc0 : 0 ≤ Real.log c := Real.log_nonneg hc1
  have he_small : (C_pr + C_np + 1) * e ≤ 1 / 32768 := by
    dsimp only [C_cross01, L, Lh] at hsmall
    change 32768 * (C_pr + C_np + 1) * e ≤ 1 at hsmall
    linarith only [hsmall]
  have he1 : 1 / Lh ≤ e := by
    have hh : 0 ≤ c ^ 2 * (1 + Real.log c) / Lh +
        c ^ 4 * (1 + Real.log c) / L + c ^ 3 * (R₀ : ℝ) ^ 2 * (L / (N : ℝ)) := by positivity
    dsimp only [e]; linarith only [hh]
  have he2 : c ^ 2 * (1 + Real.log c) / Lh ≤ e := by
    have hh : 0 ≤ 1 / Lh + c ^ 4 * (1 + Real.log c) / L +
        c ^ 3 * (R₀ : ℝ) ^ 2 * (L / (N : ℝ)) := by positivity
    dsimp only [e]; linarith only [hh]
  have he34 : c ^ 4 * (1 + Real.log c) / L + c ^ 3 * (R₀ : ℝ) ^ 2 * (L / (N : ℝ)) ≤ e := by
    have hh : 0 ≤ 1 / Lh + c ^ 2 * (1 + Real.log c) / Lh := by positivity
    dsimp only [e]; linarith only [hh]
  have hinvL_le : 1 / L ≤ 1 / Lh :=
    one_div_le_one_div_of_le hLh0 (by nlinarith only [hLh1, hLh_sq])
  have hc2L_le : c ^ 2 * (1 + Real.log c) / L ≤ c ^ 2 * (1 + Real.log c) / Lh :=
    div_le_div_of_nonneg_left (by positivity) hLh0 (by nlinarith only [hLh1, hLh_sq])
  have hH₀_s : H₀ / (L * s) ≤ 64 * e := by
    have h1 : H₀ / (L * s) ≤ (2 * Lh) / (L * ((1 / 32 : ℝ) * Lh)) :=
      div_le_div_of_nonneg_right hH₀_ub (by positivity)
    have h2 : (2 * Lh) / (L * ((1 / 32 : ℝ) * Lh)) = 64 * (1 / L) := by
      field_simp [hL0.ne', hLh0.ne']; ring
    exact h1.trans (h2.trans_le (mul_le_mul_of_nonneg_left (hinvL_le.trans he1) (by norm_num)))
  have hH₀sq_s : H₀ ^ 2 / (L * s) ≤ 128 * e := by
    have hsq : H₀ ^ 2 ≤ 4 * L := by
      have hp := pow_le_pow_left₀ (by positivity) hH₀_ub 2
      calc
        H₀ ^ 2 ≤ (2 * Lh) ^ 2 := hp
        _ = 4 * (Lh * Lh) := by ring
        _ = 4 * L := by rw [hLh_sq]
    have h1 : H₀ ^ 2 / (L * s) ≤ (4 * L) / (L * ((1 / 32 : ℝ) * Lh)) :=
      div_le_div_of_nonneg_right hsq (by positivity)
    have h2 : (4 * L) / (L * ((1 / 32 : ℝ) * Lh)) = 128 * (1 / Lh) := by
      field_simp [hL0.ne', hLh0.ne']; ring
    exact h1.trans (h2.trans_le (mul_le_mul_of_nonneg_left he1 (by norm_num)))
  have hH₀B_s : H₀ * terminalPacketCost R₀ N N / (L * s) ≤ 128 * e := by
    have hprod : H₀ * terminalPacketCost R₀ N N ≤ 2 * H₀ := by
      have hH0 : 0 ≤ H₀ := by dsimp only [H₀]; positivity
      nlinarith only [hterm_N, hH0]
    calc
      H₀ * terminalPacketCost R₀ N N / (L * s) ≤ (2 * H₀) / (L * s) :=
        div_le_div_of_nonneg_right hprod (by positivity)
      _ = 2 * (H₀ / (L * s)) := by ring
      _ ≤ 2 * (64 * e) := mul_le_mul_of_nonneg_left hH₀_s (by norm_num)
      _ = 128 * e := by ring
  have hG_s : (c ^ 2 * H₀ * (1 + Real.log c) / L) / s ≤ 64 * e := by
    have hnum : c ^ 2 * H₀ * (1 + Real.log c) ≤ 2 * Lh * (c ^ 2 * (1 + Real.log c)) := by
      have hc20 : 0 ≤ c ^ 2 * (1 + Real.log c) := by positivity
      have hm := mul_le_mul_of_nonneg_right hH₀_ub hc20
      linarith only [hm, (by ring : c ^ 2 * H₀ * (1 + Real.log c) = H₀ * (c ^ 2 * (1 + Real.log c))),
        (by ring : (2 * Lh) * (c ^ 2 * (1 + Real.log c)) = 2 * Lh * (c ^ 2 * (1 + Real.log c)))]
    calc
      (c ^ 2 * H₀ * (1 + Real.log c) / L) / s ≤
          (2 * Lh * (c ^ 2 * (1 + Real.log c)) / L) / ((1 / 32 : ℝ) * Lh) :=
        div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hnum hL0.le) hs0.le
      _ = 64 * (c ^ 2 * (1 + Real.log c) / L) := by field_simp [hL0.ne', hLh0.ne']; ring
      _ ≤ 64 * e := mul_le_mul_of_nonneg_left (hc2L_le.trans he2) (by norm_num)
  have hU_s :
      (c ^ 4 * (1 + Real.log c) / L + c ^ 3 * (R₀ : ℝ) ^ 2 * (L / (N : ℝ)) +
          c ^ 2 * (1 + Real.log c)) / s ≤ 64 * e := by
    have hs_ge : (1 / 32 : ℝ) ≤ s := by dsimp only [s]; linarith only [hLh1]
    have hpart1 :
        (c ^ 4 * (1 + Real.log c) / L + c ^ 3 * (R₀ : ℝ) ^ 2 * (L / (N : ℝ))) / s ≤ 32 * e := by
      calc
        _ ≤ (c ^ 4 * (1 + Real.log c) / L + c ^ 3 * (R₀ : ℝ) ^ 2 * (L / (N : ℝ))) / (1 / 32 : ℝ) :=
          div_le_div_of_nonneg_left (by positivity) (by norm_num) hs_ge
        _ = 32 * (c ^ 4 * (1 + Real.log c) / L + c ^ 3 * (R₀ : ℝ) ^ 2 * (L / (N : ℝ))) := by ring
        _ ≤ 32 * e := mul_le_mul_of_nonneg_left he34 (by norm_num)
    have hpart2 : c ^ 2 * (1 + Real.log c) / s ≤ 32 * e := by
      have hid : c ^ 2 * (1 + Real.log c) / ((1 / 32 : ℝ) * Lh) =
          32 * (c ^ 2 * (1 + Real.log c) / Lh) := by field_simp [hLh0.ne']
      dsimp only [s]
      rw [hid]
      exact mul_le_mul_of_nonneg_left he2 (by norm_num)
    rw [add_div]
    linarith only [hpart1, hpart2]
  have hpa : C_pr * (H₀ / (L * s)) + C_pr * (H₀ / (L * s)) ≤ 1 / 128 := by
    have h1 := mul_le_mul_of_nonneg_left hH₀_s hC_pr.le
    have he0 : 0 ≤ e := le_trans (by positivity) he1
    nlinarith only [h1, he_small, mul_nonneg hC_np.le he0, he0]
  have hpe : C_pr * (H₀ ^ 2 / (L * s)) + C_pr * (H₀ * terminalPacketCost R₀ N N / (L * s)) ≤
      1 / 128 := by
    have h1 := mul_le_mul_of_nonneg_left hH₀sq_s hC_pr.le
    have h2 := mul_le_mul_of_nonneg_left hH₀B_s hC_pr.le
    have he0 : 0 ≤ e := le_trans (by positivity) he1
    nlinarith only [h1, h2, he_small, mul_nonneg hC_np.le he0, he0]
  have hng : C_np * ((c ^ 2 * H₀ * (1 + Real.log c) / L) / s) ≤ 1 / 128 := by
    have h1 := mul_le_mul_of_nonneg_left hG_s hC_np.le
    have he0 : 0 ≤ e := le_trans (by positivity) he1
    nlinarith only [h1, he_small, mul_nonneg hC_pr.le he0, he0]
  have hnu :
      C_np * ((c ^ 4 * (1 + Real.log c) / L + c ^ 3 * (R₀ : ℝ) ^ 2 * (L / (N : ℝ)) +
        c ^ 2 * (1 + Real.log c)) / s) ≤ 1 / 16 := by
    have h1 := mul_le_mul_of_nonneg_left hU_s hC_np.le
    have he0 : 0 ≤ e := le_trans (by positivity) he1
    nlinarith only [h1, he_small, mul_nonneg hC_pr.le he0, he0]
  have hfact :
      C_pr * (H₀ * A₀ + H₀ ^ 2 * E₀) / (L * s) +
        C_pr * (H₀ * A₀ + H₀ * terminalPacketCost R₀ N N * E₀) / (L * s) +
        C_np * ((c ^ 2 * H₀ * (1 + Real.log c) / L) * G₀ +
          (c ^ 4 * (1 + Real.log c) / L + c ^ 3 * (R₀ : ℝ) ^ 2 * (L / (N : ℝ)) +
            c ^ 2 * (1 + Real.log c)) * ‖u₀‖ ^ 2) / s =
      (C_pr * (H₀ / (L * s)) + C_pr * (H₀ / (L * s))) * A₀ +
        (C_pr * (H₀ ^ 2 / (L * s)) + C_pr * (H₀ * terminalPacketCost R₀ N N / (L * s))) * E₀ +
        (C_np * ((c ^ 2 * H₀ * (1 + Real.log c) / L) / s)) * G₀ +
        (C_np * ((c ^ 4 * (1 + Real.log c) / L + c ^ 3 * (R₀ : ℝ) ^ 2 * (L / (N : ℝ)) +
          c ^ 2 * (1 + Real.log c)) / s)) * ‖u₀‖ ^ 2 := by ring
  change 2 * |⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N) u₀, u₁⟫| ≤
    C_pr * (H₀ * A₀ + H₀ ^ 2 * E₀) / (L * s) +
      C_pr * (H₀ * A₀ + H₀ * terminalPacketCost R₀ N N * E₀) / (L * s) +
      C_np * ((c ^ 2 * H₀ * (1 + Real.log c) / L) * G₀ +
        (c ^ 4 * (1 + Real.log c) / L + c ^ 3 * (R₀ : ℝ) ^ 2 * (L / (N : ℝ)) +
          c ^ 2 * (1 + Real.log c)) * ‖u₀‖ ^ 2) / s +
      s * ‖u₁‖ ^ 2 + s * ‖u₁‖ ^ 2 at hraw
  rw [hfact] at hraw
  have hs_two : s * ‖u₁‖ ^ 2 + s * ‖u₁‖ ^ 2 = (1 / 16 : ℝ) * Lh * ‖u₁‖ ^ 2 := by
    dsimp only [s]; ring
  have h1 := mul_le_mul_of_nonneg_right hpa hA₀
  have h2 := mul_le_mul_of_nonneg_right hpe hE₀
  have h3 := mul_le_mul_of_nonneg_right hng hG₀
  have h4 := mul_le_mul_of_nonneg_right hnu (sq_nonneg ‖u₀‖)
  change 2 * |⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N) u₀, u₁⟫| ≤
    (1 / 32 : ℝ) * E₀ + (1 / 4 : ℝ) * ‖u₀‖ ^ 2 + (1 / 16 : ℝ) * Lh * ‖u₁‖ ^ 2
  linarith only [hraw, hs_two, h1, h2, h3, h4, hAU, hG_le, hE₀, sq_nonneg ‖u₀‖]

/-- Homogeneous `O(c^2 (1 + log c))` coercivity on Band 1 (`V_{R₁} ∩ (V_{R₀})ᗮ`) at polynomial
scale `1080 * (1 + log R₁) ≤ log N`. -/
private theorem exists_band1_coercive_homogeneous :
    ∃ C_band1 : ℝ, 0 < C_band1 ∧
      ∀ {R₀ R₁ N : ℕ} {c : ℝ},
        2 ≤ R₀ → R₀ ≤ R₁ → R₁ ^ 6 ≤ N → 1080 * (1 + Real.log R₁) ≤ Real.log N →
        1 ≤ c → c ≤ Real.log N → c / N ≤ 1 / 3 →
        ((R₁ * R₁ : ℕ) + 1 : ℝ) * (linearNearRowRadius c + 1) ≤ N →
        (R₁ : ℝ) * Real.sqrt (Real.log N / N) ≤ 1 →
      ∀ a₁ : ℕ → ℝ,
        (∑ m ∈ Icc 1 R₁, a₁ m • normalizedRamanujanHorizonVector m N) ∈
          (conductorSubspace R₀ N)ᗮ →
        (1 / 8 : ℝ) * primeAdjunctionMass R₁ a₁ +
          ((1 / 4 : ℝ) * Real.log R₀ - C_band1 * c ^ 2 * (1 + Real.log c)) *
            ‖∑ m ∈ Icc 1 R₁, a₁ m • normalizedRamanujanHorizonVector m N‖ ^ 2 ≤
        completeWeilEnergy tiltedUnitSpline c N
          (∑ m ∈ Icc 1 R₁, a₁ m • normalizedRamanujanHorizonVector m N) := by
  obtain ⟨C_od, hC_od, hod⟩ := exists_overlap_sub_downward_inner_le_of_mem_conductorSubspace
    contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos
  obtain ⟨C_ov, hC_ov, hov⟩ := exists_overlapMatrix_inner_le_of_mem_conductorSubspace
    contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos
  let C_sep' := 36 * (152 * (∫ t, |tiltedUnitSpline t|) ^ 2 / (∫ t, tiltedUnitSpline t ^ 2))
  have hC_sep'0 : 0 ≤ C_sep' := by
    have := integral_tiltedUnitSpline_sq_pos; dsimp only [C_sep']; positivity
  let C_self := |completeWeilSelfFinitePart tiltedUnitSpline 1| +
    |Real.eulerMascheroniConstant| + 2
  let C_band1 := (Real.log 4 + 4) + C_self + 600 + C_sep' + 4 * C_od + C_ov
  have hC_band1 : 0 < C_band1 := by
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
    dsimp only [C_band1, C_self]; positivity
  refine ⟨C_band1, hC_band1, ?_⟩
  intro R₀ R₁ N c hR₀ hR₀R₁ hR₁6 hlog1080 hc1 hcL hw1 hsize hR₁_tail a₁ hu₁_R₀
  let u₁ := ∑ m ∈ Icc 1 R₁, a₁ m • normalizedRamanujanHorizonVector m N
  have hR₁ : 2 ≤ R₁ := hR₀.trans hR₀R₁
  have hRR₁ : R₁ * R₁ ≤ N := by
    have hh := (Nat.pow_le_pow_right (by omega : 0 < R₁) (by norm_num : 2 ≤ 6)).trans hR₁6
    simpa only [sq] using hh
  have hR₁4 : R₁ ^ 4 ≤ N :=
    (Nat.pow_le_pow_right (by omega : 0 < R₁) (by norm_num : 4 ≤ 6)).trans hR₁6
  have hN2 : 2 ≤ N := by have hh := Nat.mul_le_mul hR₁ hR₁; omega
  have hN1 : 1 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hlogR₁ : 0 ≤ Real.log R₁ := Real.log_natCast_nonneg R₁
  have h18 : 18 * (1 + Real.log R₁) ≤ Real.log N := by linarith only [hlog1080, hlogR₁]
  have hL1 : 1 ≤ Real.log N := by linarith only [hlog1080, hlogR₁]
  have hL0 : 0 < Real.log N := zero_lt_one.trans_le hL1
  by_cases hu0 : u₁ = 0
  · have hE0 : primeAdjunctionMass R₁ a₁ = 0 := by
      have hr := (half_and_three_halves_riesz_of_log_le hR₁ hRR₁ h18 a₁).1
      change (1 / 2 : ℝ) * (∑ m ∈ Icc 1 R₁, a₁ m ^ 2) ≤ ‖u₁‖ ^ 2 at hr
      rw [hu0, norm_zero, sq, mul_zero] at hr
      have hsum_nonneg : 0 ≤ ∑ m ∈ Icc 1 R₁, a₁ m ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
      have hsum0 : (∑ m ∈ Icc 1 R₁, a₁ m ^ 2) = 0 := by linarith only [hr, hsum_nonneg]
      have ha0 : ∀ m ∈ Icc 1 R₁, a₁ m ^ 2 = 0 := fun m hm =>
        (sum_eq_zero_iff_of_nonneg fun k _ => sq_nonneg (a₁ k)).mp hsum0 m hm
      unfold primeAdjunctionMass
      exact sum_eq_zero fun m hm => by rw [ha0 m hm, mul_zero]
    change (1 / 8 : ℝ) * primeAdjunctionMass R₁ a₁ +
        ((1 / 4 : ℝ) * Real.log R₀ - C_band1 * c ^ 2 * (1 + Real.log c)) * ‖u₁‖ ^ 2 ≤
      completeWeilEnergy tiltedUnitSpline c N u₁
    rw [hE0, hu0, norm_zero]
    unfold completeWeilEnergy
    rw [map_zero, inner_zero_right]
    have hz0 : (1 / 8 : ℝ) * 0 +
        ((1 / 4 : ℝ) * Real.log R₀ - C_band1 * c ^ 2 * (1 + Real.log c)) * (0 : ℝ) ^ 2 = 0 := by
      ring
    linarith only [hz0]
  · have hunorm_pos : 0 < ‖u₁‖ := norm_pos_iff.mpr hu0
    let s := ‖u₁‖⁻¹
    have hs_pos : 0 < s := inv_pos.mpr hunorm_pos
    let a' : ℕ → ℝ := fun m => s * a₁ m
    let u' := ∑ m ∈ Icc 1 R₁, a' m • normalizedRamanujanHorizonVector m N
    have hu'_eq : u' = s • u₁ := by
      dsimp only [u', u₁, a']
      rw [Finset.smul_sum]
      exact sum_congr rfl fun m _ => (smul_smul s (a₁ m) _).symm
    have hu'_unit : ‖u'‖ = 1 := by
      rw [hu'_eq, norm_smul, Real.norm_eq_abs, abs_of_pos hs_pos]
      exact inv_mul_cancel₀ hunorm_pos.ne'
    have hu'_sq : ‖u'‖ ^ 2 = 1 := by rw [hu'_unit, one_pow]
    have hu'_lo : 3 / 4 ≤ ‖u'‖ ^ 2 := by rw [hu'_sq]; norm_num
    have hu'_hi : ‖u'‖ ≤ 1 := hu'_unit.le
    have hu'_R₀ : u' ∈ (conductorSubspace R₀ N)ᗮ := by
      rw [hu'_eq]; exact Submodule.smul_mem _ s hu₁_R₀
    have hu'_1 : u' ∈ (conductorSubspace 1 N)ᗮ := fun v hv =>
      hu'_R₀ v (conductorSubspace_mono (by omega : 1 ≤ R₀) N hv)
    have hu'_mem : u' ∈ conductorSubspace R₁ N :=
      sum_normalizedRamanujanHorizonVector_mem_conductorSubspace R₁ N a'
    have hc0 : 0 < c := zero_lt_one.trans_le hc1
    have hcN : c ≤ N := by have := (div_le_iff₀ hN0).mp hw1; linarith only [this, hc0]
    have hlc0 : 0 ≤ Real.log c := Real.log_nonneg hc1
    have hc2_ge1 : 1 ≤ c ^ 2 := one_le_pow₀ hc1
    have hc2_ge_c : c ≤ c ^ 2 := by nlinarith only [hc1]
    let Q_c := c ^ 2 * (1 + Real.log c)
    have hQc_ge1 : 1 ≤ Q_c := by dsimp only [Q_c]; nlinarith only [hc2_ge1, hlc0]
    have hratio_le1 : (1 + Real.log R₁) / Real.log N ≤ 1 :=
      (div_le_one hL0).mpr (by linarith only [hlog1080, hlogR₁])
    have hprime := primePacket_energy_ge_adjunction_and_log_of_orthogonal
      hR₀ hR₀R₁ hRR₁ hlog1080 a' hu'_R₀ hu'_lo hu'_hi
    have hself_eq : completeWeilSelfFinitePart tiltedUnitSpline c =
        completeWeilSelfFinitePart tiltedUnitSpline 1 - Real.log c := by
      unfold completeWeilSelfFinitePart
      rw [mul_one, Real.log_div one_ne_zero (by positivity), Real.log_one,
        Real.log_mul (by positivity : 2 * Real.pi ≠ 0) hc0.ne',
        Real.log_div one_ne_zero (by positivity), Real.log_one]
      ring
    have hself_err : |completeWeilSelfError tiltedUnitSpline c N| ≤ 1 := by
      have h1 := abs_completeWeilSelfError_le_of_width_le_one contDiff_tiltedUnitSpline
        tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos hc0 hN1 hcN
      have he12 : Real.exp (1 / 2) ≤ 3 := by
        have he1 : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
        exact (Real.exp_le_exp.mpr (by norm_num : (1 / 2 : ℝ) ≤ 1)).trans he1
      calc
        |completeWeilSelfError tiltedUnitSpline c N| ≤ Real.exp (1 / 2) / 2 * (c / N) := h1
        _ ≤ (3 / 2) * (1 / 3) := mul_le_mul (by linarith only [he12]) hw1 (by positivity) (by norm_num)
        _ ≤ 1 := by norm_num
    have hself_lb :
        -C_self * Q_c ≤
          (completeWeilSelfFinitePart tiltedUnitSpline c - Real.eulerMascheroniConstant +
            completeWeilSelfError tiltedUnitSpline c N) * ‖u'‖ ^ 2 := by
      rw [hu'_sq, mul_one, hself_eq]
      have hlc_le : Real.log c ≤ Q_c := by dsimp only [Q_c]; nlinarith only [hc2_ge1, hlc0]
      have hconst_le : |completeWeilSelfFinitePart tiltedUnitSpline 1| +
          |Real.eulerMascheroniConstant| + 1 ≤ (C_self - 1) * Q_c := by
        dsimp only [C_self]
        have hpos : 0 ≤ |completeWeilSelfFinitePart tiltedUnitSpline 1| +
            |Real.eulerMascheroniConstant| + 1 := by positivity
        nlinarith only [hpos, hQc_ge1]
      linarith only [neg_abs_le (completeWeilSelfFinitePart tiltedUnitSpline 1),
        le_abs_self Real.eulerMascheroniConstant, (abs_le.mp hself_err).1, hlc_le, hconst_le]
    have hpole_le : |completeWeilPoleShift tiltedUnitSpline c| ≤ c := by
      rw [abs_of_nonneg (completeWeilPoleShift_nonneg tiltedUnitSpline hc0.le)]
      exact completeWeilPoleShift_le contDiff_tiltedUnitSpline.continuous
        tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos hc0.le
    have hcen :
        |⟪Matrix.toEuclideanLin (fullWeilCenterMatrix
            (completeWeilPoleShift tiltedUnitSpline c) N) u', u'⟫| ≤ 600 * Q_c := by
      have h1 := abs_fullWeilCenterMatrix_self_inner_le_of_mem_conductorSubspace
        (completeWeilPoleShift tiltedUnitSpline c) hR₁ hR₁4 h18 hu'_mem hu'_1
      rw [hu'_sq, mul_one] at h1
      have h2 : 600 * |completeWeilPoleShift tiltedUnitSpline c| * (1 + Real.log R₁) / Real.log N ≤
          600 * c * ((1 + Real.log R₁) / Real.log N) := by
        refine (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpole_le (by norm_num))
            (by positivity)) hL0.le).trans_eq (by ring)
      have h3 : 600 * c * ((1 + Real.log R₁) / Real.log N) ≤ 600 * Q_c := by
        dsimp only [Q_c]
        nlinarith only [hratio_le1, hc2_ge_c, hlc0, hc0]
      exact h1.trans (h2.trans h3)
    have hsep :
        |⟪Matrix.toEuclideanLin (separatedCrossErrorMatrix tiltedUnitSpline c N) u', u'⟫| ≤
          C_sep' * Q_c := by
      have h1 := abs_separatedCrossErrorMatrix_inner_le_of_mem_conductorSubspace
        contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos
        hc0 hR₁ hR₁4 h18 hu'_mem
      rw [hu'_sq, mul_one] at h1
      have h2 : c ^ 2 / Real.log N ≤ Q_c := by
        have hd : c ^ 2 / Real.log N ≤ c ^ 2 := div_le_self (sq_nonneg c) hL1
        dsimp only [Q_c]
        nlinarith only [hd, hlc0, sq_nonneg c]
      exact h1.trans ((by ring : C_sep' * c ^ 2 / Real.log N = C_sep' * (c ^ 2 / Real.log N)).trans_le
        (mul_le_mul_of_nonneg_left h2 hC_sep'0))
    have hod' :
        2 * |⟪Matrix.toEuclideanLin (overlapMatrix tiltedUnitSpline c N) u' -
            downwardPrimeVector tiltedUnitSpline c N u', u'⟫| ≤ 4 * C_od * Q_c := by
      have h1 := hod hR₁ hRR₁ h18 hc1 hw1 hsize hu'_mem
      rw [hu'_sq, mul_one] at h1
      have hpart1 : c ^ 2 * (1 + Real.log R₁) * (1 + Real.log c) / Real.log N ≤ Q_c := by
        have heq : c ^ 2 * (1 + Real.log R₁) * (1 + Real.log c) / Real.log N =
            Q_c * ((1 + Real.log R₁) / Real.log N) := by dsimp only [Q_c]; ring
        rw [heq]
        exact mul_le_of_le_one_right (by positivity) hratio_le1
      have hpart2 : c ^ 2 * (R₁ : ℝ) * Real.sqrt (Real.log N / N) ≤ Q_c := by
        have hm := mul_le_mul_of_nonneg_left hR₁_tail (sq_nonneg c)
        have hm' : c ^ 2 * (R₁ : ℝ) * Real.sqrt (Real.log N / N) ≤ c ^ 2 := by
          linarith only [hm, (by ring : c ^ 2 * ((R₁ : ℝ) * Real.sqrt (Real.log N / N)) =
            c ^ 2 * (R₁ : ℝ) * Real.sqrt (Real.log N / N))]
        dsimp only [Q_c]
        nlinarith only [hm', hlc0, sq_nonneg c]
      have hsum : c ^ 2 * (1 + Real.log R₁) * (1 + Real.log c) / Real.log N +
          c ^ 2 * (R₁ : ℝ) * Real.sqrt (Real.log N / N) ≤ 2 * Q_c := by
        linarith only [hpart1, hpart2]
      exact (mul_le_mul_of_nonneg_left
        (h1.trans (mul_le_mul_of_nonneg_left hsum hC_od.le)) zero_le_two).trans_eq (by ring)
    have hov' :
        |⟪Matrix.toEuclideanLin (overlapMatrix tiltedUnitSpline c N) u', u'⟫| ≤ C_ov * Q_c := by
      have h1 := hov hR₁ hR₁ h18 h18 hc1 hcL hw1 hsize hsize hu'_mem hu'_mem
      rw [hu'_unit, mul_one, mul_one] at h1
      have h2 : c * (1 + Real.log c) ≤ Q_c := by
        dsimp only [Q_c]; nlinarith only [hc2_ge_c, hlc0]
      exact h1.trans ((by ring : C_ov * c * (1 + Real.log c) = C_ov * (c * (1 + Real.log c))).trans_le
        (mul_le_mul_of_nonneg_left h2 hC_ov.le))
    have hpole0 := fullWeilPoleErrorMatrix_inner_eq_zero_of_orthog_one
      tiltedUnitSpline c hN2 hu'_1 hu'_1
    have hdecomp := completeWeilMatrix_inner_eq_decomposition_at_every_overlap
      contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos
      hc0 hN1 u'
    rw [overlap_sub_nonRatio_inner_eq contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero
        integral_tiltedUnitSpline_sq_pos hc0 hN1 u', hpole0] at hdecomp
    change completeWeilEnergy tiltedUnitSpline c N u' =
      renormalizedPrimeEnergy N u' +
      (completeWeilSelfFinitePart tiltedUnitSpline c - Real.eulerMascheroniConstant +
        completeWeilSelfError tiltedUnitSpline c N) * ‖u'‖ ^ 2 +
      ⟪Matrix.toEuclideanLin
        (fullWeilCenterMatrix (completeWeilPoleShift tiltedUnitSpline c) N) u', u'⟫ -
      ⟪Matrix.toEuclideanLin (separatedCrossErrorMatrix tiltedUnitSpline c N) u', u'⟫ + 0 +
      (-⟪Matrix.toEuclideanLin (overlapMatrix tiltedUnitSpline c N) u', u'⟫ +
        2 * ⟪Matrix.toEuclideanLin (overlapMatrix tiltedUnitSpline c N) u' -
          downwardPrimeVector tiltedUnitSpline c N u', u'⟫) at hdecomp
    have hrow_le : Real.log 4 + 4 ≤ (Real.log 4 + 4) * Q_c := by
      have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
      nlinarith only [this, hQc_ge1]
    have hod_lb :
        -(4 * C_od * Q_c) ≤
          2 * ⟪Matrix.toEuclideanLin (overlapMatrix tiltedUnitSpline c N) u' -
            downwardPrimeVector tiltedUnitSpline c N u', u'⟫ := by
      linarith only [hod', neg_abs_le
        ⟪Matrix.toEuclideanLin (overlapMatrix tiltedUnitSpline c N) u' -
          downwardPrimeVector tiltedUnitSpline c N u', u'⟫]
    have hunit_ineq :
        (1 / 8 : ℝ) * primeAdjunctionMass R₁ a' +
          ((1 / 4 : ℝ) * Real.log R₀ - C_band1 * Q_c) ≤
        completeWeilEnergy tiltedUnitSpline c N u' := by
      dsimp only [C_band1]
      linarith only [hdecomp, hprime, hrow_le, hself_lb,
        (abs_le.mp hcen).1, (abs_le.mp hsep).2, (abs_le.mp hov').2, hod_lb]
    have hmass_smul : primeAdjunctionMass R₁ a' = s ^ 2 * primeAdjunctionMass R₁ a₁ := by
      dsimp only [a']
      unfold primeAdjunctionMass
      rw [mul_sum]
      exact sum_congr rfl fun m _ => by ring
    have henergy_smul : completeWeilEnergy tiltedUnitSpline c N u' =
        s ^ 2 * completeWeilEnergy tiltedUnitSpline c N u₁ := by
      rw [hu'_eq]
      unfold completeWeilEnergy
      rw [map_smul, real_inner_smul_left, real_inner_smul_right]
      ring
    rw [hmass_smul, henergy_smul] at hunit_ineq
    have hmul := mul_le_mul_of_nonneg_left hunit_ineq (sq_nonneg ‖u₁‖)
    have hsu : ‖u₁‖ ^ 2 * s ^ 2 = 1 := by
      dsimp only [s]
      rw [← mul_pow, mul_inv_cancel₀ hunorm_pos.ne', one_pow]
    have hlhs :
        ‖u₁‖ ^ 2 * ((1 / 8 : ℝ) * (s ^ 2 * primeAdjunctionMass R₁ a₁) +
          ((1 / 4 : ℝ) * Real.log R₀ - C_band1 * Q_c)) =
        (1 / 8 : ℝ) * ((‖u₁‖ ^ 2 * s ^ 2) * primeAdjunctionMass R₁ a₁) +
          ((1 / 4 : ℝ) * Real.log R₀ - C_band1 * c ^ 2 * (1 + Real.log c)) * ‖u₁‖ ^ 2 := by
      dsimp only [Q_c]; ring
    have hrhs :
        ‖u₁‖ ^ 2 * (s ^ 2 * completeWeilEnergy tiltedUnitSpline c N u₁) =
          (‖u₁‖ ^ 2 * s ^ 2) * completeWeilEnergy tiltedUnitSpline c N u₁ := by ring
    rw [hlhs, hrhs, hsu, one_mul, one_mul] at hmul
    exact hmul

private theorem eventually_log_nat_le_rpow_36 :
    ∀ᶠ N : ℕ in atTop, Real.log (N : ℝ) ≤ (N : ℝ) ^ (1 / 36 : ℝ) := by
  have hsmall := tendsto_natCast_atTop_atTop.eventually
    ((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 36)).bound zero_lt_one)
  filter_upwards [hsmall, eventually_ge_atTop 1] with N hN _
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have habs : |Real.log (N : ℝ)| ≤ (N : ℝ) ^ (1 / 36 : ℝ) := by
    simpa only [Function.comp_def, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hN0 _), one_mul] using hN
  exact (le_abs_self _).trans habs

private theorem rpow_horizon_N_bounds {N R' : ℕ} {c : ℝ}
    (hN1 : 1 ≤ N) (hR'2 : 2 ≤ R') (hc1 : 1 ≤ c)
    (hL2000 : 2000 ≤ Real.log (N : ℝ))
    (hLX : Real.log (N : ℝ) ≤ (N : ℝ) ^ (1 / 36 : ℝ))
    (hcL : c ≤ Real.log (N : ℝ))
    (hlog36 : 36 * (1 + Real.log (R' : ℝ)) ≤ Real.log (N : ℝ)) :
    linearDefectCutoff c ≤ N ∧
    4 * (Real.exp 1 + 3) ^ 2 * c ^ 2 ≤ (N : ℝ) ∧
    c / (N : ℝ) ≤ 1 / 3 ∧
    4 * (linearNearRowRadius c + 1) ^ 2 ≤ (N : ℝ) ∧
    R' ^ 6 ≤ N ∧
    ((R' * R' : ℕ) + 1 : ℝ) * (linearNearRowRadius c + 1) ≤ (N : ℝ) ∧
    ((R' * R' : ℕ) + 1 : ℝ) * (c * Real.exp 1 + 1) ≤ (N : ℝ) ∧
    (R' : ℝ) * Real.sqrt (Real.log (N : ℝ) / (N : ℝ)) ≤ 1 / Real.log (N : ℝ) ∧
    c ^ 5 * Real.log (N : ℝ) / (N : ℝ) ≤ 1 / Real.log (N : ℝ) ∧
    c ^ 3 * (R' : ℝ) ^ 4 / (N : ℝ) ≤ 1 / Real.log (N : ℝ) ∧
    c ^ 3 * (R' : ℝ) ^ 2 * (Real.log (N : ℝ) / (N : ℝ)) ≤ 1 / Real.log (N : ℝ) ∧
    c ^ 10 * (R' : ℝ) ^ 2 / (N : ℝ) ≤ 1 / Real.log (N : ℝ) := by
  let L := Real.log (N : ℝ)
  let X := (N : ℝ) ^ (1 / 36 : ℝ)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hL0 : 0 < L := by dsimp only [L]; linarith only [hL2000]
  have hX2000 : 2000 ≤ X := hL2000.trans hLX
  have hX1 : 1 ≤ X := by linarith only [hX2000]
  have hX0 : 0 < X := zero_lt_one.trans_le hX1
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hcX : c ≤ X := hcL.trans hLX
  have hX36 : X ^ (36 : ℕ) = (N : ℝ) := by
    dsimp only [X]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    norm_num
  have hpowX : ∀ k : ℕ, k ≤ 36 → X ^ k ≤ (N : ℝ) := fun k hk =>
    (pow_le_pow_right₀ hX1 hk).trans_eq hX36
  have hR'X : (R' : ℝ) ≤ X := by
    have hR'0 : (0 : ℝ) < R' := by exact_mod_cast (show 0 < R' by omega)
    have hlog_le : Real.log (R' : ℝ) ≤ Real.log X := by
      have h1 : Real.log X = (1 / 36 : ℝ) * Real.log (N : ℝ) := Real.log_rpow hN0 (1 / 36 : ℝ)
      linarith only [hlog36, h1]
    exact (Real.exp_log hR'0).symm.trans_le
      ((Real.exp_le_exp.mpr hlog_le).trans_eq (Real.exp_log hX0))
  have he1 : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
  have he2 : Real.exp 2 ≤ 9 := by
    have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    nlinarith only [he1, h2, Real.exp_pos 1]
  have hlin_le : linearNearRowRadius c + 1 ≤ 19 * X := by
    unfold linearNearRowRadius
    nlinarith only [hc1, hcX, he2]
  have hup_le : c * Real.exp 1 + 1 ≤ 4 * X := by nlinarith only [hc0, hc1, hcX, he1]
  have hRR1_le : ((R' * R' : ℕ) + 1 : ℝ) ≤ 2 * X ^ 2 := by
    have hR1 : (1 : ℝ) ≤ R' := by exact_mod_cast (show 1 ≤ R' by omega)
    push_cast
    have hsq : (R' : ℝ) ^ 2 ≤ X ^ 2 := pow_le_pow_left₀ (by positivity) hR'X 2
    have h1sq : (1 : ℝ) ≤ (R' : ℝ) ^ 2 := one_le_pow₀ hR1
    linarith only [hsq, h1sq]
  have h1 : linearDefectCutoff c ≤ N := by
    have hcut := (linearDefectCutoff_bounds hc1).2.2.2
    have hcoef : 256 * Real.exp 2 + 4 ≤ 2 * X := by nlinarith only [he2, hX2000]
    have hR : (linearDefectCutoff c : ℝ) ≤ (N : ℝ) := by
      calc
        (linearDefectCutoff c : ℝ) ≤ (256 * Real.exp 2 + 4) * c := hcut
        _ ≤ (2 * X) * X := mul_le_mul hcoef hcX hc0.le (by positivity)
        _ = 2 * X ^ 2 := by ring
        _ ≤ X * X ^ 2 := mul_le_mul_of_nonneg_right (by linarith only [hX2000]) (sq_nonneg X)
        _ = X ^ 3 := by ring
        _ ≤ (N : ℝ) := hpowX 3 (by norm_num)
    exact_mod_cast hR
  have h2 : 4 * (Real.exp 1 + 3) ^ 2 * c ^ 2 ≤ (N : ℝ) := by
    have hc2 : c ^ 2 ≤ X ^ 2 := pow_le_pow_left₀ hc0.le hcX 2
    have hconst : 4 * (Real.exp 1 + 3) ^ 2 ≤ X := by
      have : 4 * (Real.exp 1 + 3) ^ 2 ≤ 144 := by nlinarith only [he1, Real.exp_pos 1]
      linarith only [this, hX2000]
    calc
      4 * (Real.exp 1 + 3) ^ 2 * c ^ 2 ≤ X * X ^ 2 :=
        mul_le_mul hconst hc2 (by positivity) hX0.le
      _ = X ^ 3 := by ring
      _ ≤ (N : ℝ) := hpowX 3 (by norm_num)
  have h3 : c / (N : ℝ) ≤ 1 / 3 := by
    rw [div_le_div_iff₀ hN0 (by norm_num)]
    have h3X : 3 * c ≤ X ^ 2 := by nlinarith only [hcX, hX2000]
    exact (by linarith only [h3X] : c * 3 ≤ X ^ 2).trans
      (by simpa only [one_mul] using hpowX 2 (by norm_num))
  have h4 : 4 * (linearNearRowRadius c + 1) ^ 2 ≤ (N : ℝ) := by
    have hsq : (linearNearRowRadius c + 1) ^ 2 ≤ (19 * X) ^ 2 :=
      pow_le_pow_left₀ (by unfold linearNearRowRadius; positivity) hlin_le 2
    have h1444 : 1444 * X ^ 2 ≤ X ^ 3 := by nlinarith only [hX2000, sq_nonneg X]
    calc
      4 * (linearNearRowRadius c + 1) ^ 2 ≤ 4 * (19 * X) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq (by norm_num)
      _ = 1444 * X ^ 2 := by ring
      _ ≤ X ^ 3 := h1444
      _ ≤ (N : ℝ) := hpowX 3 (by norm_num)
  have h5 : R' ^ 6 ≤ N := by
    have hR6 : (R' : ℝ) ^ 6 ≤ (N : ℝ) :=
      (pow_le_pow_left₀ (Nat.cast_nonneg R') hR'X 6).trans (hpowX 6 (by norm_num))
    exact_mod_cast hR6
  have h6 : ((R' * R' : ℕ) + 1 : ℝ) * (linearNearRowRadius c + 1) ≤ (N : ℝ) := by
    have h38 : 38 * X ^ 3 ≤ X ^ 4 := by
      calc
        38 * X ^ 3 ≤ X * X ^ 3 :=
          mul_le_mul_of_nonneg_right (by linarith only [hX2000]) (by positivity)
        _ = X ^ 4 := by ring
    calc
      ((R' * R' : ℕ) + 1 : ℝ) * (linearNearRowRadius c + 1) ≤ (2 * X ^ 2) * (19 * X) :=
        mul_le_mul hRR1_le hlin_le (by unfold linearNearRowRadius; positivity) (by positivity)
      _ = 38 * X ^ 3 := by ring
      _ ≤ X ^ 4 := h38
      _ ≤ (N : ℝ) := hpowX 4 (by norm_num)
  have h7 : ((R' * R' : ℕ) + 1 : ℝ) * (c * Real.exp 1 + 1) ≤ (N : ℝ) := by
    have h8 : 8 * X ^ 3 ≤ X ^ 4 := by nlinarith only [hX2000, pow_nonneg hX0.le 3]
    calc
      ((R' * R' : ℕ) + 1 : ℝ) * (c * Real.exp 1 + 1) ≤ (2 * X ^ 2) * (4 * X) :=
        mul_le_mul hRR1_le hup_le (by positivity) (by positivity)
      _ = 8 * X ^ 3 := by ring
      _ ≤ X ^ 4 := h8
      _ ≤ (N : ℝ) := hpowX 4 (by norm_num)
  have h8 : (R' : ℝ) * Real.sqrt (L / (N : ℝ)) ≤ 1 / L := by
    have hprod : (R' : ℝ) ^ 2 * L ^ 3 ≤ (N : ℝ) := by
      have hR2 : (R' : ℝ) ^ 2 ≤ X ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg R') hR'X 2
      have hL3 : L ^ 3 ≤ X ^ 3 := pow_le_pow_left₀ hL0.le hLX 3
      calc
        (R' : ℝ) ^ 2 * L ^ 3 ≤ X ^ 2 * X ^ 3 := mul_le_mul hR2 hL3 (by positivity) (by positivity)
        _ = X ^ 5 := by ring
        _ ≤ (N : ℝ) := hpowX 5 (by norm_num)
    have hsq : ((R' : ℝ) * Real.sqrt (L / (N : ℝ))) ^ 2 ≤ (1 / L) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity), one_div, inv_pow, ← one_div]
      rw [← mul_div_assoc, div_le_div_iff₀ hN0 (sq_pos_of_pos hL0)]
      calc
        (R' : ℝ) ^ 2 * L * L ^ 2 = (R' : ℝ) ^ 2 * L ^ 3 := by ring
        _ ≤ 1 * (N : ℝ) := by rw [one_mul]; exact hprod
    have hlhs0 : 0 ≤ (R' : ℝ) * Real.sqrt (L / (N : ℝ)) := by positivity
    have hrhs0 : 0 ≤ 1 / L := by positivity
    nlinarith only [hsq, hlhs0, hrhs0]
  have h9 : c ^ 5 * L / (N : ℝ) ≤ 1 / L := by
    rw [div_le_div_iff₀ hN0 hL0, one_mul]
    have hc5 : c ^ 5 ≤ X ^ 5 := pow_le_pow_left₀ hc0.le hcX 5
    have hL2 : L ^ 2 ≤ X ^ 2 := pow_le_pow_left₀ hL0.le hLX 2
    calc
      c ^ 5 * L * L = c ^ 5 * L ^ 2 := by ring
      _ ≤ X ^ 5 * X ^ 2 := mul_le_mul hc5 hL2 (by positivity) (by positivity)
      _ = X ^ 7 := by ring
      _ ≤ (N : ℝ) := hpowX 7 (by norm_num)
  have h10 : c ^ 3 * (R' : ℝ) ^ 4 / (N : ℝ) ≤ 1 / L := by
    rw [div_le_div_iff₀ hN0 hL0, one_mul]
    have hc3 : c ^ 3 ≤ X ^ 3 := pow_le_pow_left₀ hc0.le hcX 3
    have hR4 : (R' : ℝ) ^ 4 ≤ X ^ 4 := pow_le_pow_left₀ (Nat.cast_nonneg R') hR'X 4
    calc
      c ^ 3 * (R' : ℝ) ^ 4 * L ≤ (X ^ 3 * X ^ 4) * X :=
        mul_le_mul (mul_le_mul hc3 hR4 (by positivity) (by positivity)) hLX hL0.le (by positivity)
      _ = X ^ 8 := by ring
      _ ≤ (N : ℝ) := hpowX 8 (by norm_num)
  have h11 : c ^ 3 * (R' : ℝ) ^ 2 * (L / (N : ℝ)) ≤ 1 / L := by
    rw [← mul_div_assoc, div_le_div_iff₀ hN0 hL0, one_mul]
    have hc3 : c ^ 3 ≤ X ^ 3 := pow_le_pow_left₀ hc0.le hcX 3
    have hR2 : (R' : ℝ) ^ 2 ≤ X ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg R') hR'X 2
    have hL2 : L ^ 2 ≤ X ^ 2 := pow_le_pow_left₀ hL0.le hLX 2
    calc
      c ^ 3 * (R' : ℝ) ^ 2 * L * L = (c ^ 3 * (R' : ℝ) ^ 2) * L ^ 2 := by ring
      _ ≤ (X ^ 3 * X ^ 2) * X ^ 2 :=
        mul_le_mul (mul_le_mul hc3 hR2 (by positivity) (by positivity)) hL2 (by positivity)
          (by positivity)
      _ = X ^ 7 := by ring
      _ ≤ (N : ℝ) := hpowX 7 (by norm_num)
  have h12 : c ^ 10 * (R' : ℝ) ^ 2 / (N : ℝ) ≤ 1 / L := by
    rw [div_le_div_iff₀ hN0 hL0, one_mul]
    have hc10 : c ^ 10 ≤ X ^ 10 := pow_le_pow_left₀ hc0.le hcX 10
    have hR2 : (R' : ℝ) ^ 2 ≤ X ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg R') hR'X 2
    calc
      c ^ 10 * (R' : ℝ) ^ 2 * L ≤ (X ^ 10 * X ^ 2) * X :=
        mul_le_mul (mul_le_mul hc10 hR2 (by positivity) (by positivity)) hLX hL0.le (by positivity)
      _ = X ^ 13 := by ring
      _ ≤ (N : ℝ) := hpowX 13 (by norm_num)
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩

private theorem eventually_three_cutoff_bounds {q θ₁ : ℝ}
    (hq : 0 < q) (hqmax : q ≤ 1 / 2) (hθ₁ : 0 < θ₁) (hθ₁_4096 : θ₁ ≤ 1 / 4096) :
    ∀ᶠ N : ℕ in atTop,
      let L := Real.log (N : ℝ)
      let Q₁ := ⌊L ^ q⌋₊
      let R₀ := ⌊Real.exp (L ^ (1 / 2 : ℝ))⌋₊
      let R₁ := ⌊(N : ℝ) ^ θ₁⌋₊
      2 ≤ Q₁ ∧ Q₁ ≤ R₀ ∧ R₀ ≤ R₁ ∧
      (Q₁ : ℝ) ≤ L ^ q ∧
      (1 / 2 : ℝ) * L ^ (q / 2) ≤ Real.sqrt Q₁ ∧
      q * Real.log L - 1 ≤ Real.log (Q₁ : ℝ) ∧
      1 + Real.log (R₀ : ℝ) ≤ 2 * L ^ (1 / 2 : ℝ) ∧
      L ^ (1 / 2 : ℝ) - 1 ≤ Real.log (R₀ : ℝ) ∧
      36 * (1 + Real.log (R₀ : ℝ)) ≤ L ∧
      1 + Real.log (R₁ : ℝ) ≤ 2 * θ₁ * L ∧
      1080 * (1 + Real.log (R₁ : ℝ)) ≤ L ∧
      (θ₁ / (4 * explicitConductorCutoffConstant)) * L ≤
        Real.log (R₁ : ℝ) / explicitConductorCutoffConstant - 1 := by
  let D := explicitConductorCutoffConstant
  have hD : 0 < D := explicitConductorCutoffConstant_pos
  have hLlim : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hQlim : Tendsto (fun N : ℕ => Real.log (N : ℝ) ^ q) atTop atTop :=
    (tendsto_rpow_atTop hq).comp hLlim
  have hLhlim : Tendsto (fun N : ℕ => Real.log (N : ℝ) ^ (1 / 2 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp hLlim
  have hNθlim : Tendsto (fun N : ℕ => (N : ℝ) ^ θ₁) atTop atTop :=
    (tendsto_rpow_atTop hθ₁).comp tendsto_natCast_atTop_atTop
  let M_Lh := max 72 (1 / θ₁ + 1)
  let M_L := max 2000 (max (2 / θ₁) (4 * D / θ₁))
  filter_upwards [hQlim.eventually_ge_atTop 4,
    hLhlim.eventually_ge_atTop M_Lh,
    hLlim.eventually_ge_atTop M_L,
    hNθlim.eventually_ge_atTop 4,
    eventually_ge_atTop 3] with N hQ4 hLh_M hL_M hNθ4 hN3
  dsimp only
  let L := Real.log (N : ℝ)
  let Lh := L ^ (1 / 2 : ℝ)
  let Q₁ := ⌊L ^ q⌋₊
  let R₀ := ⌊Real.exp Lh⌋₊
  let R₁ := ⌊(N : ℝ) ^ θ₁⌋₊
  have hL2000 : 2000 ≤ L := (le_max_left _ _).trans hL_M
  have hL_2θ : 2 / θ₁ ≤ L := ((le_max_left _ _).trans (le_max_right _ _)).trans hL_M
  have hL_4Dθ : 4 * D / θ₁ ≤ L := ((le_max_right _ _).trans (le_max_right _ _)).trans hL_M
  have hLh72 : 72 ≤ Lh := (le_max_left _ _).trans hLh_M
  have hLh_θ : 1 / θ₁ + 1 ≤ Lh := (le_max_right _ _).trans hLh_M
  have hL1 : 1 ≤ L := by linarith only [hL2000]
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have hLh0 : 0 < Lh := by linarith only [hLh72]
  have hN1R : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hN0 : (0 : ℝ) < N := zero_lt_one.trans_le hN1R
  have hLh_sq : Lh * Lh = L := by
    dsimp only [Lh]; rw [← Real.rpow_add hL0]; norm_num [Real.rpow_one]
  have hlog2 : Real.log 2 ≤ 1 := by
    linarith only [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hQ2 : 2 ≤ Q₁ := Nat.le_floor (by exact_mod_cast (show (2 : ℝ) ≤ L ^ q by linarith only [hQ4]))
  have hQ_le : (Q₁ : ℝ) ≤ L ^ q := Nat.floor_le (by linarith only [hQ4])
  have hQ_gt : L ^ q - 1 < (Q₁ : ℝ) := sub_lt_iff_lt_add.mpr (Nat.lt_floor_add_one _)
  have hQ_quarter : (1 / 4 : ℝ) * L ^ q ≤ (Q₁ : ℝ) := by linarith only [hQ4, hQ_gt]
  have hQ_half : (1 / 2 : ℝ) * L ^ q ≤ (Q₁ : ℝ) := by linarith only [hQ4, hQ_gt]
  have hsqrtQ : (1 / 2 : ℝ) * L ^ (q / 2) ≤ Real.sqrt Q₁ := by
    have hsq : ((1 / 2 : ℝ) * L ^ (q / 2)) ^ 2 = (1 / 4 : ℝ) * L ^ q := by
      rw [mul_pow, ← Real.rpow_natCast (L ^ (q / 2)) 2, ← Real.rpow_mul hL0.le]; norm_num
    have hpos : 0 ≤ (1 / 2 : ℝ) * L ^ (q / 2) := by positivity
    exact (Real.sqrt_sq hpos).symm.trans_le (Real.sqrt_le_sqrt (hsq.trans_le hQ_quarter))
  have hlogQ_lb : q * Real.log L - 1 ≤ Real.log (Q₁ : ℝ) := by
    have hXq_pos : 0 < L ^ q := by linarith only [hQ4]
    have h1 := Real.log_le_log (by positivity) hQ_half
    rw [Real.log_mul (by norm_num) hXq_pos.ne', one_div, Real.log_inv, Real.log_rpow hL0] at h1
    linarith only [h1, hlog2]
  have hLq_exp : L ^ q ≤ Real.exp Lh := by
    have h1 : L ^ q ≤ Lh := Real.rpow_le_rpow_of_exponent_le hL1 hqmax
    have h2 : Lh ≤ Real.exp Lh := by linarith [Real.add_one_le_exp Lh]
    exact h1.trans h2
  have hQR₀ : Q₁ ≤ R₀ := Nat.floor_mono hLq_exp
  have hexp_Nθ : Real.exp Lh ≤ (N : ℝ) ^ θ₁ := by
    rw [Real.rpow_def_of_pos hN0]
    apply Real.exp_le_exp.mpr
    have h1 : 1 ≤ θ₁ * Lh := by
      have hh := (div_le_iff₀ hθ₁).mp (show 1 / θ₁ ≤ Lh by linarith only [hLh_θ])
      linarith only [hh]
    have h2 := mul_le_mul_of_nonneg_left h1 hLh0.le
    calc
      Lh = Lh * 1 := (mul_one _).symm
      _ ≤ Lh * (θ₁ * Lh) := h2
      _ = (Lh * Lh) * θ₁ := by ring
      _ = Real.log (N : ℝ) * θ₁ := by rw [hLh_sq]
  have hR₀R₁ : R₀ ≤ R₁ := Nat.floor_mono hexp_Nθ
  have hR₀2 : 2 ≤ R₀ := hQ2.trans hQR₀
  have hR₀_le : (R₀ : ℝ) ≤ Real.exp Lh := Nat.floor_le (Real.exp_pos Lh).le
  have hlogR₀_ub : Real.log (R₀ : ℝ) ≤ Lh :=
    (Real.log_le_log (by exact_mod_cast (show 0 < R₀ by omega)) hR₀_le).trans_eq (Real.log_exp Lh)
  have hH₀_ub : 1 + Real.log (R₀ : ℝ) ≤ 2 * Lh := by linarith only [hlogR₀_ub, hLh72]
  have hexp_ge4 : 4 ≤ Real.exp Lh := by linarith [Real.add_one_le_exp Lh, hLh72]
  have hR₀_half : (1 / 2 : ℝ) * Real.exp Lh ≤ (R₀ : ℝ) := by
    have hgt : Real.exp Lh - 1 < (R₀ : ℝ) := sub_lt_iff_lt_add.mpr (Nat.lt_floor_add_one _)
    linarith only [hexp_ge4, hgt]
  have hlogR₀_lb : Lh - 1 ≤ Real.log (R₀ : ℝ) := by
    have h1 := Real.log_le_log (by positivity) hR₀_half
    rw [Real.log_mul (by norm_num) (Real.exp_pos Lh).ne', one_div, Real.log_inv, Real.log_exp] at h1
    linarith only [h1, hlog2]
  have h36_R₀ : 36 * (1 + Real.log (R₀ : ℝ)) ≤ L := by
    have h1 : 36 * (1 + Real.log (R₀ : ℝ)) ≤ 72 * Lh := by linarith only [hH₀_ub]
    have h2 : 72 * Lh ≤ Lh * Lh := mul_le_mul_of_nonneg_right hLh72 hLh0.le
    linarith only [h1, h2, hLh_sq]
  have hR₁2 : 2 ≤ R₁ := hR₀2.trans hR₀R₁
  have hR₁_le : (R₁ : ℝ) ≤ (N : ℝ) ^ θ₁ := Nat.floor_le (by positivity)
  have hlogR₁_ub : Real.log (R₁ : ℝ) ≤ θ₁ * L := by
    have h1 := Real.log_le_log (by exact_mod_cast (show 0 < R₁ by omega)) hR₁_le
    rw [Real.log_rpow hN0] at h1
    exact h1
  have h1_le_θL : 1 ≤ θ₁ * L := by
    have hh := (div_le_iff₀ hθ₁).mp hL_2θ
    linarith only [hh]
  have hH₁_ub : 1 + Real.log (R₁ : ℝ) ≤ 2 * θ₁ * L := by linarith only [hlogR₁_ub, h1_le_θL]
  have h1080_R₁ : 1080 * (1 + Real.log (R₁ : ℝ)) ≤ L := by
    have h1 : 1080 * (1 + Real.log (R₁ : ℝ)) ≤ 2160 * θ₁ * L := by linarith only [hH₁_ub]
    have h2 : 2160 * θ₁ ≤ 1 := by linarith only [hθ₁_4096]
    nlinarith only [h1, h2, hL0]
  have hR₁_half : (1 / 2 : ℝ) * (N : ℝ) ^ θ₁ ≤ (R₁ : ℝ) := by
    have hgt : (N : ℝ) ^ θ₁ - 1 < (R₁ : ℝ) := sub_lt_iff_lt_add.mpr (Nat.lt_floor_add_one _)
    linarith only [hNθ4, hgt]
  have hlogR₁_lb : (1 / 2 : ℝ) * θ₁ * L ≤ Real.log (R₁ : ℝ) := by
    have hpos : 0 < (N : ℝ) ^ θ₁ := by linarith only [hNθ4]
    have h1 := Real.log_le_log (by positivity) hR₁_half
    rw [Real.log_mul (by norm_num) hpos.ne', one_div, Real.log_inv, Real.log_rpow hN0] at h1
    linarith only [h1, hlog2, h1_le_θL]
  have hk₁_lb : (θ₁ / (4 * D)) * L ≤ Real.log (R₁ : ℝ) / D - 1 := by
    have h4D : 4 * D ≤ θ₁ * L := by
      have hh := (div_le_iff₀ hθ₁).mp hL_4Dθ
      linarith only [hh]
    rw [le_sub_iff_add_le, ← le_div_iff₀ (show 0 < D from hD)]
    have hid : ((θ₁ / (4 * D)) * L + 1) * D = (1 / 4 : ℝ) * (θ₁ * L) + D := by
      field_simp [hD.ne']; ring
    linarith only [hlogR₁_lb, h4D, hid]
  exact ⟨hQ2, hQR₀, hR₀R₁, hQ_le, hsqrtQ, hlogQ_lb, hH₀_ub, hlogR₀_lb, h36_R₀,
    hH₁_ub, h1080_R₁, hk₁_lb⟩

/-- **Collective Packet Coercivity with Defect Reserve Below `α = 1 / 4`:**
For every overlap exponent `0 < α < 1 / 4`, every polylogarithmic base exponent `q > 3 * α`,
and every polynomial packet exponent `0 < θ ≤ 1 / 4096`, eventually in `N` and uniformly across
`1 ≤ c ≤ (log N)^α`, every collective mid-band packet vector
`u ∈ conductorSubspace ⌊(N : ℝ) ^ θ⌋₊ N ⊓ (conductorSubspace ⌊Real.log (N : ℝ) ^ q⌋₊ N)ᗮ`
satisfies
`(1 / 64 : ℝ) * poleDefect N (primeHorizonExtension u) + (tiltedSplineSpectralFloorConstant + 2) * ‖u‖^2 ≤ completeWeilEnergy tiltedUnitSpline c N u`. -/
theorem eventually_tiltedUnitSpline_collective_packet_coercive_with_defect_below_one_quarter
    {α q θ : ℝ} (hα : 0 < α) (hα_lt : α < oneQuarterPowerLogExponent)
    (hq_lo : 3 * α < q) (hθ : 0 < θ) (hθ_4096 : θ ≤ 1 / 4096) :
    ∀ᶠ N : ℕ in atTop,
      let Q₁ := ⌊Real.log (N : ℝ) ^ q⌋₊
      let R₁ := ⌊(N : ℝ) ^ θ⌋₊
      ∀ c : ℝ, 1 ≤ c → c ≤ Real.log (N : ℝ) ^ α →
        ∀ {u : EuclideanSpace ℝ (PrimeHorizonIndex N)},
          u ∈ conductorSubspace R₁ N →
          u ∈ (conductorSubspace Q₁ N)ᗮ →
          (1 / 64 : ℝ) * poleDefect N (primeHorizonExtension u) +
            (tiltedSplineSpectralFloorConstant + 2) * ‖u‖ ^ 2 ≤
            completeWeilEnergy tiltedUnitSpline c N u := by
  have hα4 : α < 1 / 4 := hα_lt
  let q₀ : ℝ := min q (2 * α + 1 / 4)
  have hq₀_pos : 0 < q₀ := lt_min (by linarith only [hα, hq_lo]) (by linarith only [hα])
  have hq₀_lo : 3 * α < q₀ := lt_min hq_lo (by linarith only [hα4])
  have hq₀_hi : q₀ ≤ 1 / 2 := (min_le_right _ _).trans (by linarith only [hα4])
  have hq₀_le_q : q₀ ≤ q := min_le_left _ _
  obtain ⟨C_cross01, hC_cross01, hcross01⟩ := exists_band0_band1_cross_le
  obtain ⟨C_coerc0, C_small0, hC_coerc0, hC_small0, hcoerc0⟩ :=
    exists_completeWeilEnergy_ge_three_quarters_log_homogeneous
  obtain ⟨C_band1, hC_band1, hcoerc1⟩ := exists_band1_coercive_homogeneous
  have hκ₀ : 0 < tiltedSplineSpectralFloorConstant := tiltedSplineSpectralFloorConstant_pos
  let ν : ℝ := min (1 / 4 - α) (q₀ / 2 - (3 / 2) * α) / 16
  have hν : 0 < ν := by
    have hd : 0 < min (1 / 4 - α) (q₀ / 2 - (3 / 2) * α) :=
      lt_min (by linarith only [hα4]) (by linarith only [hq₀_lo])
    dsimp only [ν]; linarith only [hd]
  have hν1 : 16 * ν ≤ 1 / 4 - α := by
    have hh : min (1 / 4 - α) (q₀ / 2 - (3 / 2) * α) ≤ 1 / 4 - α := min_le_left _ _
    dsimp only [ν]; linarith only [hh]
  have hν2 : 16 * ν ≤ q₀ / 2 - (3 / 2) * α := by
    have hh : min (1 / 4 - α) (q₀ / 2 - (3 / 2) * α) ≤ q₀ / 2 - (3 / 2) * α := min_le_right _ _
    dsimp only [ν]; linarith only [hh]
  have hgap_q : 0 < (3 / 4) * q₀ - α := by linarith only [hα, hq₀_lo]
  have hLlim : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hllim : Tendsto (fun N : ℕ => Real.log (Real.log (N : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp hLlim
  let M_ν : ℝ := C_small0 * 18 + C_cross01 * 4 + 16 * C_band1
  let M_ll : ℝ := (tiltedSplineSpectralFloorConstant + 3 + C_coerc0 + 3 / 4) / ((3 / 4) * q₀ - α)
  let M_L_floor : ℝ := 3000 + ((16 * (tiltedSplineSpectralFloorConstant + 3)) ^ 2 + 1)
  filter_upwards [eventually_three_cutoff_bounds hq₀_pos hq₀_hi hθ hθ_4096,
    eventually_log_nat_le_rpow_36,
    hLlim.eventually (RHTower.eventually_const_mul_polylog_le_rpow 1 hν 1),
    ((tendsto_rpow_atTop hν).comp hLlim).eventually_ge_atTop M_ν,
    hllim.eventually_ge_atTop M_ll,
    hLlim.eventually_ge_atTop M_L_floor,
    eventually_ge_atTop 3] with N hcut hLX hpoly hν_big hll_big hL_big hN3
  dsimp only [Function.comp_def] at hpoly hν_big hll_big hL_big ⊢
  intro c hc1 hcup u hu_mem hu_orth
  obtain ⟨hQ0_2, hQ0R₀, hR₀R₁, -, hsqrtQ0, hlogQ0_lb, hH₀_ub, hlogR₀_lb, h36_R₀,
    -, h1080_R₁, -⟩ := hcut
  let L := Real.log (N : ℝ)
  let Lh := L ^ (1 / 2 : ℝ)
  let Q₀ := ⌊L ^ q₀⌋₊
  let R₀ := ⌊Real.exp Lh⌋₊
  let R₁ := ⌊(N : ℝ) ^ θ⌋₊
  have hL3000 : 3000 ≤ L := by
    have : 0 ≤ (16 * (tiltedSplineSpectralFloorConstant + 3)) ^ 2 + 1 := by positivity
    dsimp only [M_L_floor, L] at hL_big ⊢; linarith only [hL_big, this]
  have hL_Lh_gap : (16 * (tiltedSplineSpectralFloorConstant + 3)) ^ 2 + 1 ≤ L := by
    dsimp only [M_L_floor, L] at hL_big ⊢; linarith only [hL_big]
  have hL2000 : 2000 ≤ L := by linarith only [hL3000]
  have hL1 : 1 ≤ L := by linarith only [hL3000]
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have hLh1 : 1 ≤ Lh := Real.one_le_rpow hL1 (by norm_num)
  have hLh0 : 0 < Lh := zero_lt_one.trans_le hLh1
  have hLh_sq : Lh * Lh = L := by
    dsimp only [Lh]; rw [← Real.rpow_add hL0]; norm_num [Real.rpow_one]
  have hN1 : 1 ≤ N := by omega
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hcL : c ≤ L := hcup.trans (by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hL1 (by linarith only [hα4] : α ≤ 1))
  have hQ0_le_Q1 : Q₀ ≤ ⌊L ^ q⌋₊ :=
    Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le hL1 hq₀_le_q)
  have hu_orthQ0 : u ∈ (conductorSubspace Q₀ N)ᗮ := fun v hv =>
    hu_orth v (conductorSubspace_mono hQ0_le_Q1 N hv)
  have hVc : 1 + Real.log c ≤ L ^ ν := by
    have hp1 : 1 + Real.log L ≤ L ^ ν := by
      simpa only [one_mul, pow_one] using hpoly
    linarith only [Real.log_le_log hc0 hcL, hp1]
  have hR₀2 : 2 ≤ R₀ := hQ0_2.trans hQ0R₀
  have hR₁2 : 2 ≤ R₁ := hR₀2.trans hR₀R₁
  have h36_R₁ : 36 * (1 + Real.log (R₁ : ℝ)) ≤ L := by
    linarith only [h1080_R₁, Real.log_natCast_nonneg R₁]
  obtain ⟨-, -, hw1, -, hR₀6, hsize_near0, hsize_up0, hR₀_tail, hc5N, hc3R₀4, hc3R₀2, -⟩ :=
    rpow_horizon_N_bounds hN1 hR₀2 hc1 hL2000 hLX hcL h36_R₀
  obtain ⟨-, -, -, -, hR₁6, hsize_near1, -, hR₁_tail, -, -, -, -⟩ :=
    rpow_horizon_N_bounds hN1 hR₁2 hc1 hL2000 hLX hcL h36_R₁
  have hR₁_tail1 : (R₁ : ℝ) * Real.sqrt (L / N) ≤ 1 :=
    hR₁_tail.trans ((div_le_one hL0).mpr hL1)
  have h18_R₀ : 18 * (1 + Real.log (R₀ : ℝ)) ≤ L := by
    linarith only [h36_R₀, Real.log_natCast_nonneg R₀]
  have h18_R₁ : 18 * (1 + Real.log (R₁ : ℝ)) ≤ L := by
    linarith only [h36_R₁, Real.log_natCast_nonneg R₁]
  have hlc_ge1 : 1 ≤ 1 + Real.log c := by linarith [Real.log_nonneg hc1]
  have hlc_nn : 0 ≤ 1 + Real.log c := zero_le_one.trans hlc_ge1
  have hLν0 : 0 ≤ L ^ ν := Real.rpow_nonneg hL0.le _
  have hLmν0 : 0 ≤ L ^ (-ν) := Real.rpow_nonneg hL0.le _
  have hmul_ν : L ^ ν * L ^ (-ν) = 1 := by
    rw [← Real.rpow_add hL0, show ν + (-ν) = 0 by ring, Real.rpow_zero]
  have hcpow : ∀ j : ℕ, c ^ j ≤ L ^ ((j : ℝ) * α) := fun j => by
    have hp := pow_le_pow_left₀ hc0.le hcup j
    have he : (L ^ α) ^ j = L ^ ((j : ℝ) * α) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; congr 1; ring
    exact hp.trans_eq he
  have h1_invL : 1 / L ≤ L ^ (-ν) := by
    rw [one_div, ← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hL1 (by linarith only [hν1, hα])
  have h1_invLh : 1 / Lh ≤ L ^ (-ν) := by
    dsimp only [Lh]; rw [one_div, ← Real.rpow_neg hL0.le]
    exact Real.rpow_le_rpow_of_exponent_le hL1 (by linarith only [hν1, hα])
  have hH₀_div : (1 + Real.log (R₀ : ℝ)) / L ≤ 2 / Lh := by
    rw [div_le_div_iff₀ hL0 hLh0]
    calc
      (1 + Real.log (R₀ : ℝ)) * Lh ≤ (2 * Lh) * Lh := mul_le_mul_of_nonneg_right hH₀_ub hLh0.le
      _ = 2 * (Lh * Lh) := by ring
      _ = 2 * L := by rw [hLh_sq]
  have hc2_vc_Lh : c ^ 2 * (1 + Real.log c) / Lh ≤ L ^ (-ν) := by
    have h1 : c ^ 2 * (1 + Real.log c) ≤ L ^ (2 * α + ν) := by
      calc
        c ^ 2 * (1 + Real.log c) ≤ L ^ (((2 : ℕ) : ℝ) * α) * L ^ ν :=
          mul_le_mul (hcpow 2) hVc hlc_nn (Real.rpow_nonneg hL0.le _)
        _ = L ^ (2 * α + ν) := by rw [← Real.rpow_add hL0]; congr 1
    calc
      c ^ 2 * (1 + Real.log c) / Lh ≤ L ^ (2 * α + ν) / Lh :=
        div_le_div_of_nonneg_right h1 hLh0.le
      _ = L ^ (2 * α + ν - 1 / 2) := by dsimp only [Lh]; rw [← Real.rpow_sub hL0]
      _ ≤ L ^ (-ν) := Real.rpow_le_rpow_of_exponent_le hL1 (by linarith only [hν1, hν])
  have hc2_vc_L : c ^ 2 * (1 + Real.log c) / L ≤ L ^ (-ν) :=
    (div_le_div_of_nonneg_left (mul_nonneg (sq_nonneg c) hlc_nn) hLh0
      (by nlinarith only [hLh1, hLh_sq])).trans hc2_vc_Lh
  have hν_b1 : C_small0 * 18 ≤ L ^ ν := by
    have : 0 ≤ C_cross01 * 4 + 16 * C_band1 := by positivity
    dsimp only [M_ν, L] at hν_big ⊢; linarith only [hν_big, this]
  have hν_b2 : C_cross01 * 4 ≤ L ^ ν := by
    have : 0 ≤ C_small0 * 18 + 16 * C_band1 := by positivity
    dsimp only [M_ν, L] at hν_big ⊢; linarith only [hν_big, this]
  have hν_b6 : 16 * C_band1 ≤ L ^ ν := by
    have : 0 ≤ C_small0 * 18 + C_cross01 * 4 := by positivity
    dsimp only [M_ν, L] at hν_big ⊢; linarith only [hν_big, this]
  have hsmall_band0 :
      C_small0 * (c * (1 + Real.log c) * (1 + Real.log R₀) / L +
        c * (1 + Real.log R₀) / L + c ^ 2 / L +
        c ^ 2 * (1 + Real.log R₀) * (1 + Real.log c) / L +
        c ^ 2 * (R₀ : ℝ) * Real.sqrt (L / N) +
        c ^ 5 * L / N +
        c * Real.sqrt c * (1 + Real.log c) / Real.sqrt Q₀ +
        c ^ 3 * (R₀ : ℝ) ^ 4 / N + c ^ 2 * (1 + Real.log c) / L) ≤ 1 := by
    have hmid_Q₀ : c * Real.sqrt c * (1 + Real.log c) / Real.sqrt Q₀ ≤ 2 * L ^ (-ν) := by
      have hc32 : c * Real.sqrt c ≤ L ^ ((3 / 2 : ℝ) * α) := by
        have hsq : (c * Real.sqrt c) ^ 2 ≤ (L ^ ((3 / 2 : ℝ) * α)) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt hc0.le, show c ^ 2 * c = c ^ 3 by ring,
            ← Real.rpow_natCast (L ^ _), ← Real.rpow_mul hL0.le]
          exact (hcpow 3).trans_eq (by congr 1; ring)
        have hp1 : 0 ≤ c * Real.sqrt c := mul_nonneg hc0.le (Real.sqrt_nonneg c)
        have hp2 : 0 ≤ L ^ ((3 / 2 : ℝ) * α) := Real.rpow_nonneg hL0.le _
        nlinarith only [hsq, hp1, hp2]
      have hden_pos : 0 < (1 / 2 : ℝ) * L ^ (q₀ / 2) :=
        mul_pos (by norm_num) (Real.rpow_pos_of_pos hL0 _)
      calc
        c * Real.sqrt c * (1 + Real.log c) / Real.sqrt Q₀ ≤
            (L ^ ((3 / 2 : ℝ) * α) * L ^ ν) / ((1 / 2 : ℝ) * L ^ (q₀ / 2)) :=
          (div_le_div_of_nonneg_right
            (mul_le_mul hc32 hVc hlc_nn (Real.rpow_nonneg hL0.le _))
            (Real.sqrt_nonneg _)).trans
            (div_le_div_of_nonneg_left
              (mul_nonneg (Real.rpow_nonneg hL0.le _) hLν0) hden_pos hsqrtQ0)
        _ = 2 * L ^ ((3 / 2 : ℝ) * α + ν - q₀ / 2) := by
          rw [show (L ^ ((3 / 2 : ℝ) * α) * L ^ ν) / ((1 / 2 : ℝ) * L ^ (q₀ / 2)) =
            2 * ((L ^ ((3 / 2 : ℝ) * α) * L ^ ν) / L ^ (q₀ / 2)) by ring,
            ← Real.rpow_add hL0, ← Real.rpow_sub hL0]
        _ ≤ 2 * L ^ (-ν) := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hL1 (by linarith only [hν2, hν])) zero_le_two
    have ht4 : c ^ 2 * (1 + Real.log R₀) * (1 + Real.log c) / L ≤ 2 * L ^ (-ν) := by
      calc
        c ^ 2 * (1 + Real.log R₀) * (1 + Real.log c) / L =
            c ^ 2 * (1 + Real.log c) * ((1 + Real.log R₀) / L) := by ring
        _ ≤ c ^ 2 * (1 + Real.log c) * (2 / Lh) :=
          mul_le_mul_of_nonneg_left hH₀_div (mul_nonneg (sq_nonneg c) hlc_nn)
        _ = 2 * (c ^ 2 * (1 + Real.log c) / Lh) := by ring
        _ ≤ 2 * L ^ (-ν) := mul_le_mul_of_nonneg_left hc2_vc_Lh zero_le_two
    have hlogR₀_nn : 0 ≤ 1 + Real.log (R₀ : ℝ) := by linarith [Real.log_natCast_nonneg R₀]
    have ht1 : c * (1 + Real.log c) * (1 + Real.log R₀) / L ≤ 2 * L ^ (-ν) := by
      have hm : c * (1 + Real.log c) ≤ c ^ 2 * (1 + Real.log c) :=
        mul_le_mul_of_nonneg_right (by nlinarith only [hc1]) hlc_nn
      exact (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hm hlogR₀_nn) hL0.le).trans
        ((by ring : c ^ 2 * (1 + Real.log c) * (1 + Real.log R₀) / L =
          c ^ 2 * (1 + Real.log R₀) * (1 + Real.log c) / L).trans_le ht4)
    have ht2 : c * (1 + Real.log R₀) / L ≤ 2 * L ^ (-ν) :=
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hc0.le hlc_ge1) hlogR₀_nn) hL0.le).trans ht1
    have ht3 : c ^ 2 / L ≤ L ^ (-ν) :=
      (div_le_div_of_nonneg_right (le_mul_of_one_le_right (sq_nonneg c) hlc_ge1) hL0.le).trans
        hc2_vc_L
    have ht5 : c ^ 2 * (R₀ : ℝ) * Real.sqrt (L / N) ≤ L ^ (-ν) := by
      calc
        c ^ 2 * (R₀ : ℝ) * Real.sqrt (L / N) = c ^ 2 * ((R₀ : ℝ) * Real.sqrt (L / N)) := by ring
        _ ≤ c ^ 2 * (1 / L) := mul_le_mul_of_nonneg_left hR₀_tail (sq_nonneg c)
        _ = c ^ 2 / L := by ring
        _ ≤ L ^ (-ν) := ht3
    have ht6 : c ^ 5 * L / N ≤ L ^ (-ν) := hc5N.trans h1_invL
    have ht8 : c ^ 3 * (R₀ : ℝ) ^ 4 / N ≤ L ^ (-ν) := hc3R₀4.trans h1_invL
    have hsum18 : c * (1 + Real.log c) * (1 + Real.log R₀) / L +
        c * (1 + Real.log R₀) / L + c ^ 2 / L +
        c ^ 2 * (1 + Real.log R₀) * (1 + Real.log c) / L +
        c ^ 2 * (R₀ : ℝ) * Real.sqrt (L / N) +
        c ^ 5 * L / N +
        c * Real.sqrt c * (1 + Real.log c) / Real.sqrt Q₀ +
        c ^ 3 * (R₀ : ℝ) ^ 4 / N + c ^ 2 * (1 + Real.log c) / L ≤ 18 * L ^ (-ν) := by
      linarith only [ht1, ht2, ht3, ht4, ht5, ht6, hmid_Q₀, ht8, hc2_vc_L, hLmν0]
    calc
      _ ≤ C_small0 * (18 * L ^ (-ν)) := mul_le_mul_of_nonneg_left hsum18 hC_small0.le
      _ = (C_small0 * 18) * L ^ (-ν) := by ring
      _ ≤ L ^ ν * L ^ (-ν) := mul_le_mul_of_nonneg_right hν_b1 hLmν0
      _ = 1 := hmul_ν
  have hsmall_cross01 :
      C_cross01 * (1 / Lh + c ^ 2 * (1 + Real.log c) / Lh +
        c ^ 4 * (1 + Real.log c) / L + c ^ 3 * (R₀ : ℝ) ^ 2 * (L / (N : ℝ))) ≤ 1 := by
    have hc4_vc : c ^ 4 * (1 + Real.log c) / L ≤ L ^ (-ν) := by
      calc
        c ^ 4 * (1 + Real.log c) / L ≤ (L ^ (((4 : ℕ) : ℝ) * α) * L ^ ν) / L :=
          div_le_div_of_nonneg_right
            (mul_le_mul (hcpow 4) hVc hlc_nn (Real.rpow_nonneg hL0.le _)) hL0.le
        _ = L ^ (4 * α + ν - 1) := by
          rw [← Real.rpow_add hL0, Real.rpow_sub hL0, Real.rpow_one]; congr 1
        _ ≤ L ^ (-ν) := Real.rpow_le_rpow_of_exponent_le hL1 (by linarith only [hν1, hν])
    have hc3_N : c ^ 3 * (R₀ : ℝ) ^ 2 * (L / (N : ℝ)) ≤ L ^ (-ν) := hc3R₀2.trans h1_invL
    have hsum4 : 1 / Lh + c ^ 2 * (1 + Real.log c) / Lh +
        c ^ 4 * (1 + Real.log c) / L + c ^ 3 * (R₀ : ℝ) ^ 2 * (L / (N : ℝ)) ≤ 4 * L ^ (-ν) := by
      linarith only [h1_invLh, hc2_vc_Lh, hc4_vc, hc3_N]
    calc
      _ ≤ C_cross01 * (4 * L ^ (-ν)) := mul_le_mul_of_nonneg_left hsum4 hC_cross01.le
      _ = (C_cross01 * 4) * L ^ (-ν) := by ring
      _ ≤ L ^ ν * L ^ (-ν) := mul_le_mul_of_nonneg_right hν_b2 hLmν0
      _ = 1 := hmul_ν
  let κ₀ := tiltedSplineSpectralFloorConstant
  have hfl0 : κ₀ + 2 + 1 / 4 ≤ (3 / 4 : ℝ) * Real.log (Q₀ : ℝ) - Real.log c - C_coerc0 := by
    have hll_scaled : κ₀ + 3 + C_coerc0 + 3 / 4 ≤ ((3 / 4 : ℝ) * q₀ - α) * Real.log L :=
      ((div_le_iff₀ hgap_q).mp hll_big).trans_eq (mul_comm _ _)
    have hlogc : Real.log c ≤ α * Real.log L :=
      (Real.log_le_log hc0 hcup).trans_eq (Real.log_rpow hL0 α)
    have hq_scaled : (3 / 4 : ℝ) * q₀ * Real.log L - 3 / 4 ≤ (3 / 4 : ℝ) * Real.log (Q₀ : ℝ) := by
      have hm := mul_le_mul_of_nonneg_left hlogQ0_lb (by norm_num : (0 : ℝ) ≤ 3 / 4)
      linarith only [hm]
    linarith only [hlogc, hq_scaled, hll_scaled]
  have hfl1 : κ₀ + 2 + (1 / 16 : ℝ) * Lh ≤
      (1 / 4 : ℝ) * Real.log (R₀ : ℝ) - C_band1 * c ^ 2 * (1 + Real.log c) := by
    have hc2_Lh : C_band1 * c ^ 2 * (1 + Real.log c) ≤ (1 / 16 : ℝ) * Lh := by
      have h1 : (16 * C_band1) * (c ^ 2 * (1 + Real.log c) / Lh) ≤ 1 := by
        calc
          (16 * C_band1) * (c ^ 2 * (1 + Real.log c) / Lh) ≤ L ^ ν * L ^ (-ν) :=
            mul_le_mul hν_b6 hc2_vc_Lh
              (div_nonneg (mul_nonneg (sq_nonneg c) hlc_nn) hLh0.le) hLν0
          _ = 1 := hmul_ν
      have hm := mul_le_mul_of_nonneg_right h1
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 16) hLh0.le)
      have hid : (16 * C_band1) * (c ^ 2 * (1 + Real.log c) / Lh) * ((1 / 16 : ℝ) * Lh) =
          C_band1 * c ^ 2 * (1 + Real.log c) := by field_simp [hLh0.ne']
      linarith only [hm, hid]
    have hLh_lb : 16 * (κ₀ + 3) ≤ Lh := by
      have hsq : (16 * (κ₀ + 3)) ^ 2 ≤ Lh ^ 2 := by
        rw [sq Lh, hLh_sq]; linarith only [hL_Lh_gap]
      have hp : 0 ≤ 16 * (κ₀ + 3) := by linarith only [hκ₀]
      nlinarith only [hsq, hp, hLh0]
    linarith only [hlogR₀_lb, hc2_Lh, hLh_lb, hκ₀]
  obtain ⟨u₀, u₁, hu_eq, hu₀_mem, hu₀_orthQ, hu₁_mem, hu₁_orthR₀, hnorm_split⟩ :=
    collective_two_band_orthogonal_split hQ0R₀ hR₀R₁ hu_mem hu_orthQ0
  obtain ⟨a₀, -, ha₀⟩ := (mem_conductorSubspace_iff (M := R₀) (N := N) (x := u₀)).mp hu₀_mem
  obtain ⟨a₁, -, ha₁⟩ := (mem_conductorSubspace_iff (M := R₁) (N := N) (x := u₁)).mp hu₁_mem
  have hu₀_1 : u₀ ∈ (conductorSubspace 1 N)ᗮ := fun v hv =>
    hu₀_orthQ v (conductorSubspace_mono ((by norm_num : 1 ≤ 2).trans hQ0_2) N hv)
  have hdiag0 := hcoerc0 hQ0_2 hQ0R₀ hR₀6 h36_R₀ hc1 hcL hw1
    (rpow_horizon_N_bounds hN1 hR₀2 hc1 hL2000 hLX hcL h36_R₀).2.2.2.1
    hsize_near0 hsmall_band0 a₀ (ha₀.symm ▸ hu₀_orthQ)
  rw [← ha₀] at hdiag0
  have hdiag1 := hcoerc1 hR₀2 hR₀R₁ hR₁6 h1080_R₁ hc1 hcL hw1 hsize_near1 hR₁_tail1
    a₁ (ha₁.symm ▸ hu₁_orthR₀)
  rw [← ha₁] at hdiag1
  have hcr01 := hcross01 hR₀2 hR₀6 h18_R₀ hc1 hw1 hsize_near0 hsize_up0 hH₀_ub hsmall_cross01
    a₀ (ha₀.symm ▸ hu₀_1) hu₁_orthR₀
  rw [← ha₀] at hcr01
  have hRR₀ : R₀ * R₀ ≤ N := by
    have hh := (Nat.pow_le_pow_right (by omega : 0 < R₀) (by norm_num : 2 ≤ 6)).trans hR₀6
    simpa only [sq] using hh
  have hRR₁ : R₁ * R₁ ≤ N := by
    have hh := (Nat.pow_le_pow_right (by omega : 0 < R₁) (by norm_num : 2 ≤ 6)).trans hR₁6
    simpa only [sq] using hh
  have hdef0 := poleDefect_normalizedRamanujanPacket_le_three_halves_primeAdjunctionMass
    hR₀2 hRR₀ h18_R₀ a₀
  rw [← ha₀] at hdef0
  have hdef1 := poleDefect_normalizedRamanujanPacket_le_three_halves_primeAdjunctionMass
    hR₁2 hRR₁ h18_R₁ a₁
  rw [← ha₁] at hdef1
  have hdef_u := poleDefect_primeHorizonExtension_add_le N u₀ u₁
  rw [← hu_eq] at hdef_u
  have hfloor0 : (κ₀ + 2) * ‖u₀‖ ^ 2 + (1 / 4 : ℝ) * ‖u₀‖ ^ 2 ≤
      ((3 / 4 : ℝ) * Real.log (Q₀ : ℝ) - Real.log c - C_coerc0) * ‖u₀‖ ^ 2 := by
    rw [show (κ₀ + 2) * ‖u₀‖ ^ 2 + (1 / 4 : ℝ) * ‖u₀‖ ^ 2 = (κ₀ + 2 + 1 / 4) * ‖u₀‖ ^ 2 by ring]
    exact mul_le_mul_of_nonneg_right hfl0 (sq_nonneg ‖u₀‖)
  have hfloor1 : (κ₀ + 2) * ‖u₁‖ ^ 2 + (1 / 16 : ℝ) * Lh * ‖u₁‖ ^ 2 ≤
      ((1 / 4 : ℝ) * Real.log (R₀ : ℝ) - C_band1 * c ^ 2 * (1 + Real.log c)) * ‖u₁‖ ^ 2 := by
    rw [show (κ₀ + 2) * ‖u₁‖ ^ 2 + (1 / 16 : ℝ) * Lh * ‖u₁‖ ^ 2 =
      (κ₀ + 2 + (1 / 16 : ℝ) * Lh) * ‖u₁‖ ^ 2 by ring]
    exact mul_le_mul_of_nonneg_right hfl1 (sq_nonneg ‖u₁‖)
  have h2add :
      completeWeilEnergy tiltedUnitSpline c N u₀ +
        completeWeilEnergy tiltedUnitSpline c N u₁ -
        2 * |⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N) u₀, u₁⟫| ≤
      completeWeilEnergy tiltedUnitSpline c N u := by
    have hsym := (Matrix.isSymmetric_toEuclideanLin_iff.mpr
      (completeWeilMatrix_isHermitian tiltedUnitSpline c N)) u₁ u₀
    unfold completeWeilEnergy
    rw [hu_eq, map_add, inner_add_left, inner_add_right, inner_add_right, hsym,
      real_inner_comm u₁ (Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N) u₀)]
    have habs := neg_abs_le ⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N) u₀, u₁⟫
    linarith only [habs]
  have hE₀_0 : 0 ≤ primeAdjunctionMass R₀ a₀ := primeAdjunctionMass_nonneg R₀ a₀
  have hE₁_0 : 0 ≤ primeAdjunctionMass R₁ a₁ := primeAdjunctionMass_nonneg R₁ a₁
  rw [hnorm_split, mul_add]
  linarith only [h2add, hdiag0, hdiag1, hcr01, hfloor0, hfloor1,
    hdef0, hdef1, hdef_u, hE₀_0, hE₁_0]

/-- **Collective Packet Coercivity Below `α = 1 / 4` (Task 2):**
For every `0 < α < 1 / 4`, every `q > 3 * α`, and every `0 < θ ≤ 1 / 4096`, eventually in `N`
and uniformly across `1 ≤ c ≤ (log N)^α`, every vector
`u ∈ conductorSubspace ⌊(N : ℝ) ^ θ⌋₊ N ⊓ (conductorSubspace ⌊Real.log (N : ℝ) ^ q⌋₊ N)ᗮ`
satisfies `(tiltedSplineSpectralFloorConstant + 2) * ‖u‖^2 ≤ completeWeilEnergy tiltedUnitSpline c N u`. -/
theorem eventually_tiltedUnitSpline_collective_packet_coercive_below_one_quarter
    {α q θ : ℝ} (hα : 0 < α) (hα_lt : α < oneQuarterPowerLogExponent)
    (hq_lo : 3 * α < q) (hθ : 0 < θ) (hθ_4096 : θ ≤ 1 / 4096) :
    ∀ᶠ N : ℕ in atTop,
      let Q₁ := ⌊Real.log (N : ℝ) ^ q⌋₊
      let R₁ := ⌊(N : ℝ) ^ θ⌋₊
      ∀ c : ℝ, 1 ≤ c → c ≤ Real.log (N : ℝ) ^ α →
        ∀ {u : EuclideanSpace ℝ (PrimeHorizonIndex N)},
          u ∈ conductorSubspace R₁ N →
          u ∈ (conductorSubspace Q₁ N)ᗮ →
          (tiltedSplineSpectralFloorConstant + 2) * ‖u‖ ^ 2 ≤
            completeWeilEnergy tiltedUnitSpline c N u := by
  filter_upwards [eventually_tiltedUnitSpline_collective_packet_coercive_with_defect_below_one_quarter
    hα hα_lt hq_lo hθ hθ_4096] with N hcoerc c hc hcup u hu_mem hu_orth
  have h1 := hcoerc c hc hcup hu_mem hu_orth
  have hdef : 0 ≤ poleDefect N (primeHorizonExtension u) := poleDefect_nonneg _ _
  linarith only [h1, hdef]

/-! ### 3. Power-of-Logarithm Defect Reserve and `O(log c)` Sublevel Confinement Below `α = 1 / 9` -/

private theorem Ioc_eq_Icc_sdiff_Icc_confinement (M N : ℕ) :
    (Ioc M N : Finset ℕ) = Icc 1 N \ Icc 1 M := by
  ext n
  rw [mem_Ioc, Finset.mem_sdiff, mem_Icc, mem_Icc]
  omega

/-- **Asymmetric Two-Region Reserve with Retained Defect Reserve on `(conductorSubspace R N)ᗮ`:**
Splitting the terminal `(a / c^7) * poleDefect N x` reserve in
`exists_completeWeilEnergy_asymmetric_prefix_terminal_reserve` into two equal halves
(`b = a / 2`) uses one half to absorb the terminal `c^2` penalty and prefix-to-terminal
leakage, while retaining the second half `(b / c^7) * poleDefect N (primeHorizonExtension w)`
alongside `(k / 4) * P_w + (b * k / (2 * c^7)) * S_w`. -/
theorem exists_completeWeilEnergy_asymmetric_two_region_with_defect_reserve :
    ∃ b K : ℝ, 0 < b ∧ b ≤ 1 / 16 ∧ 0 < K ∧
      ∀ {c : ℝ} {R N : ℕ}, 1 ≤ c → 2 ≤ R → linearDefectCutoff c ≤ N →
        R * R ≤ N / linearDefectCutoff c →
        18 * (1 + Real.log R) ≤ Real.log (N / linearDefectCutoff c : ℕ) →
        K * c ^ 9 ≤ Real.log R / explicitConductorCutoffConstant - 1 →
        terminalPacketCost R (N / linearDefectCutoff c) N /
          Real.log (N / linearDefectCutoff c : ℕ) ≤ b / (4 * c ^ 7) →
      ∀ {w : EuclideanSpace ℝ (PrimeHorizonIndex N)}, w ∈ (conductorSubspace R N)ᗮ →
        (b / c ^ 7) * poleDefect N (primeHorizonExtension w) +
          (Real.log R / explicitConductorCutoffConstant - 1) / 4 *
            (∑ n ∈ Icc 1 (N / linearDefectCutoff c), primeHorizonExtension w n ^ 2) +
          b * (Real.log R / explicitConductorCutoffConstant - 1) / (2 * c ^ 7) *
            (∑ n ∈ Ioc (N / linearDefectCutoff c) N, primeHorizonExtension w n ^ 2) ≤
            completeWeilEnergy tiltedUnitSpline c N w := by
  obtain ⟨a, C₀, C₁, ha, ha8, hC₀, hC₁, hreserve⟩ :=
    exists_completeWeilEnergy_asymmetric_prefix_terminal_reserve
  let b := a / 2
  have hb : 0 < b := by dsimp only [b]; linarith only [ha]
  have hb16 : b ≤ 1 / 16 := by dsimp only [b]; linarith only [ha8]
  let K := 8 * C₀ + 4 * C₁ / b
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨b, K, hb, hb16, hK, ?_⟩
  intro c R N hc hR hLN hRM hlog hcut hleak w hw
  let M := N / linearDefectCutoff c
  let x := primeHorizonExtension w
  let P := ∑ n ∈ Icc 1 M, x n ^ 2
  let S := ∑ n ∈ Ioc M N, x n ^ 2
  let k := Real.log R / explicitConductorCutoffConstant - 1
  let B := terminalPacketCost R M N / Real.log M
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hM : 2 ≤ M := by have hh := Nat.mul_le_mul hR hR; omega
  have hMN : M ≤ N := Nat.div_le_self N (linearDefectCutoff c)
  have hN2 : 2 ≤ N := hM.trans hMN
  have hk : 0 < k := (mul_pos hK (pow_pos hc0 9)).trans_le hcut
  have hscale : explicitConductorCutoffConstant ≤ Real.log R := by
    have hh : 1 ≤ Real.log R / explicitConductorCutoffConstant := by
      dsimp only [k] at hk; linarith only [hk]
    simpa only [one_mul] using (le_div_iff₀ explicitConductorCutoffConstant_pos).mp hh
  have hP : 0 ≤ P := sum_nonneg fun _ _ => sq_nonneg _
  have hS : 0 ≤ S := sum_nonneg fun _ _ => sq_nonneg _
  have hsplit : ‖w‖ ^ 2 = P + S := by
    rw [← sum_primeHorizonExtension_sq]
    dsimp only [P, S, x]
    rw [Ioc_eq_Icc_sdiff_Icc_confinement M N, add_comm]
    exact (sum_sdiff (Icc_subset_Icc le_rfl hMN)).symm
  have hw1 : w ∈ (conductorSubspace 1 N)ᗮ := fun v hv =>
    hw v (conductorSubspace_mono (by omega : 1 ≤ R) N hv)
  have hraw := hreserve hc hLN hw1
  have hab_split : (a / c ^ 7) * poleDefect N x =
      (b / c ^ 7) * poleDefect N x + (b / c ^ 7) * poleDefect N x := by
    dsimp only [b]; ring
  have hpre := poleDefect_prefix_ge_of_conductor_orthogonal hR hM hMN hRM hlog hscale hw
  have hwhole := poleDefect_ge_explicit_on_conductor_orthogonal hR hN2 hw
  have htwoB : 2 * terminalPacketCost R M N / Real.log M = 2 * B := by dsimp only [B]; ring
  rw [htwoB] at hpre
  change k * ((15 / 16 : ℝ) * P - 2 * B * S) ≤ poleDefect M x at hpre
  rw [hsplit] at hwhole
  change k * (P + S) ≤ poleDefect N x at hwhole
  have h8C₀_le : 8 * C₀ ≤ K := by
    have hz : 0 ≤ 4 * C₁ / b := by positivity
    dsimp only [K]; linarith only [hz]
  have h4C₁_le : 4 * C₁ / b ≤ K := by
    dsimp only [K]; linarith only [hC₀]
  have hC₀_le : C₀ * c ^ 9 ≤ k / 8 := by
    have h1 : 8 * C₀ * c ^ 9 ≤ K * c ^ 9 :=
      mul_le_mul_of_nonneg_right h8C₀_le (pow_nonneg hc0.le 9)
    linarith only [h1, hcut]
  have hC₁_le : C₁ * c ^ 2 ≤ b * k / (4 * c ^ 7) := by
    apply (le_div_iff₀ (by positivity : 0 < 4 * c ^ 7)).mpr
    have h1 : (4 * C₁ / b) * c ^ 9 ≤ k :=
      (mul_le_mul_of_nonneg_right h4C₁_le (pow_nonneg hc0.le 9)).trans hcut
    have h2 := mul_le_mul_of_nonneg_left h1 hb.le
    have he : b * ((4 * C₁ / b) * c ^ 9) = 4 * C₁ * c ^ 9 := by field_simp [hb.ne']
    rw [he] at h2
    exact (by ring : C₁ * c ^ 2 * (4 * c ^ 7) = 4 * C₁ * c ^ 9).trans_le (by linarith only [h2])
  have hpre' := mul_le_mul_of_nonneg_left hpre (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hwhole' := mul_le_mul_of_nonneg_left hwhole (div_nonneg hb.le (pow_nonneg hc0.le 7))
  have hcostP := mul_le_mul_of_nonneg_right hC₀_le hP
  have hcostS := mul_le_mul_of_nonneg_right hC₁_le hS
  have hleakS := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hleak hk.le) hS
  have hlogNS_nonneg : 0 ≤ (a / c ^ 7) * Real.log N * S := by
    have hlog0 : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
    positivity
  have hpextra : 0 ≤ (b / c ^ 7) * k * P := by positivity
  have hkP : 0 ≤ k * P := mul_nonneg hk.le hP
  have hidP : (1 / 2 : ℝ) * (k * ((15 / 16 : ℝ) * P - 2 * B * S)) +
      (b / c ^ 7) * (k * (P + S)) - (k / 8) * P - (b * k / (4 * c ^ 7)) * S =
        (11 / 32 : ℝ) * (k * P) + (b / c ^ 7) * k * P +
          (3 * b * k / (4 * c ^ 7)) * S - (k * B) * S := by
    field_simp [hc0.ne']
    ring
  have hidS : (3 * b * k / (4 * c ^ 7)) * S - (k * (b / (4 * c ^ 7))) * S =
      (b * k / (2 * c ^ 7)) * S := by
    field_simp [hc0.ne']
    ring
  change (b / c ^ 7) * poleDefect N x + (k / 4) * P + (b * k / (2 * c ^ 7)) * S ≤
    completeWeilEnergy tiltedUnitSpline c N w
  linarith only [hraw, hab_split, hpre', hwhole', hcostP, hcostS, hleakS, hlogNS_nonneg,
    hpextra, hkP, hidP, hidS]

private theorem linear_prefix_horizon_bounds_confinement {N R : ℕ} {c : ℝ}
    (hN1 : 1 ≤ N) (hR : 2 ≤ R) (hc : 1 ≤ c)
    (hL3000 : 3000 ≤ Real.log (N : ℝ))
    (hLX : Real.log (N : ℝ) ≤ (N : ℝ) ^ (1 / 36 : ℝ))
    (hcL : c ≤ Real.log (N : ℝ))
    (hlog36 : 36 * (1 + Real.log (R : ℝ)) ≤ Real.log (N : ℝ)) :
    R * R ≤ N / linearDefectCutoff c ∧
    18 * (1 + Real.log (R : ℝ)) ≤ Real.log (N / linearDefectCutoff c : ℕ) ∧
    terminalPacketCost R (N / linearDefectCutoff c) N ≤
      (4 + Real.log (2 * (256 * Real.exp 2 + 4)) + 1) * (1 + Real.log c) ∧
    Real.log (N : ℝ) / 2 ≤ Real.log (N / linearDefectCutoff c : ℕ) := by
  let X := (N : ℝ) ^ (1 / 36 : ℝ)
  let Hlin : ℝ := 256 * Real.exp 2 + 4
  let T := linearDefectCutoff c
  let M := N / T
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hX3000 : 3000 ≤ X := hL3000.trans hLX
  have hX1 : 1 ≤ X := by linarith only [hX3000]
  have hX0 := zero_lt_one.trans_le hX1
  have hL : 0 < Real.log N := by linarith only [hL3000]
  have hc0 := zero_lt_one.trans_le hc
  have hcX : c ≤ X := hcL.trans hLX
  have he1 : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
  have he2 : Real.exp 2 ≤ 9 := by
    have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    nlinarith only [he1, h2, Real.exp_pos 1]
  have hHlin1 : 1 ≤ Hlin := by
    have := Real.exp_pos 2; dsimp only [Hlin]; linarith only [this]
  have hHlinX : Hlin ≤ X := by dsimp only [Hlin]; linarith only [he2, hX3000]
  have hcut : (T : ℝ) ≤ Hlin * c := (linearDefectCutoff_bounds hc).2.2.2
  have hX36 : X ^ (36 : ℕ) = (N : ℝ) := by
    dsimp only [X]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    norm_num
  have hpowX : ∀ j : ℕ, j ≤ 36 → X ^ j ≤ (N : ℝ) := fun j hj =>
    (pow_le_pow_right₀ hX1 hj).trans_eq hX36
  have hRX : (R : ℝ) ≤ X := by
    have hR0 : (0 : ℝ) < R := by exact_mod_cast (show 0 < R by omega)
    have hlogX : Real.log X = (1 / 36 : ℝ) * Real.log N := Real.log_rpow hN0 _
    have hh : Real.log R ≤ Real.log X := by linarith only [hlog36, hlogX]
    exact (Real.exp_log hR0).symm.trans_le
      ((Real.exp_le_exp.mpr hh).trans_eq (Real.exp_log hX0))
  have hT3 : 3 ≤ T := (linearDefectCutoff_bounds hc).1
  have hT1 : 1 ≤ T := by omega
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT1
  have hTX : (T : ℝ) ≤ X ^ 2 := by
    calc
      (T : ℝ) ≤ Hlin * c := hcut
      _ ≤ X * X := mul_le_mul hHlinX hcX hc0.le hX0.le
      _ = X ^ 2 := by ring
  have hRRT : R * R * T ≤ N := by
    have hh : (R : ℝ) ^ 2 * T ≤ (N : ℝ) := by
      calc
        _ ≤ X ^ 2 * X ^ 2 := mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg R) hRX 2)
          hTX hT0.le (by positivity)
        _ = X ^ 4 := by ring
        _ ≤ _ := hpowX 4 (by norm_num)
    have hhNat : R ^ 2 * T ≤ N := by exact_mod_cast hh
    simpa only [pow_two] using hhNat
  have hRM : R * R ≤ M := (Nat.le_div_iff_mul_le (by omega : 0 < T)).mpr hRRT
  have hM2 : 2 ≤ M := (by norm_num : 2 ≤ 2 * 2).trans ((Nat.mul_le_mul hR hR).trans hRM)
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by omega)
  have hTN : T ≤ N := by
    have hR1 : 1 ≤ R * R := Nat.mul_pos (by omega) (by omega)
    have hmul : T ≤ R * R * T := by
      simpa only [one_mul] using Nat.mul_le_mul_right T hR1
    exact hmul.trans hRRT
  have hfloor : (N : ℝ) < ((M : ℝ) + 1) * T := by
    have hh : N < (M + 1) * T := by
      simpa only [M, Nat.mul_comm] using Nat.lt_mul_div_succ N (show 0 < T by omega)
    exact_mod_cast hh
  have hratio : Real.log N - Real.log M ≤ Real.log (2 * (T : ℝ)) := by
    rw [← Real.log_div hN0.ne' hM0.ne']
    apply Real.log_le_log (div_pos hN0 hM0)
    apply (div_le_iff₀ hM0).mpr
    nlinarith only [hfloor, mul_nonneg (sub_nonneg.mpr hM1) hT0.le]
  have hlogT : Real.log (2 * (T : ℝ)) ≤ Real.log N / 4 + 1 := by
    have hh := Real.log_le_log (by positivity : 0 < 2 * (T : ℝ))
      (mul_le_mul_of_nonneg_left hTX zero_le_two)
    rw [Real.log_mul (by norm_num) (pow_ne_zero 2 hX0.ne'), Real.log_pow,
      show Real.log X = (1 / 36 : ℝ) * Real.log N from Real.log_rpow hN0 _] at hh
    have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith only [hh, h2, hL]
  have hhalf : Real.log N / 2 ≤ Real.log M := by linarith only [hratio, hlogT, hL3000]
  have hlogM : 18 * (1 + Real.log R) ≤ Real.log M := by linarith only [hlog36, hhalf]
  have hterminal :
      terminalPacketCost R M N ≤ (4 + Real.log (2 * Hlin) + 1) * (1 + Real.log c) := by
    have hh := terminalPacketCost_nat_div_le hT1 hTN hRM
    change terminalPacketCost R M N ≤ 4 + Real.log (2 * (T : ℝ)) at hh
    have h2Ht : 0 < 2 * Hlin := by linarith only [hHlin1]
    have ht := Real.log_le_log (by positivity : 0 < 2 * (T : ℝ))
      (mul_le_mul_of_nonneg_left hcut zero_le_two)
    rw [show 2 * (Hlin * c) = (2 * Hlin) * c by ring,
      Real.log_mul h2Ht.ne' hc0.ne'] at ht
    have hlc : 0 ≤ Real.log c := Real.log_nonneg hc
    have hpos : 0 ≤ 4 + Real.log (2 * Hlin) :=
      add_nonneg (by norm_num) (Real.log_nonneg (by linarith only [hHlin1]))
    nlinarith only [hh, ht, hlc, hpos]
  exact ⟨hRM, hlogM, hterminal, hhalf⟩

private theorem exists_band_terminal_cross_le_confinement {b : ℝ} (hb : 0 < b) :
    ∃ θ₁ C_cross_w : ℝ, 0 < θ₁ ∧ θ₁ ≤ 1 / 4096 ∧ 0 < C_cross_w ∧
      ∀ {R R₁ N : ℕ} {c : ℝ},
        2 ≤ R → R ≤ R₁ → R ^ 6 ≤ N → 18 * (1 + Real.log R) ≤ Real.log N →
        1 ≤ c → c ^ 2 ≤ Real.log N → c / N ≤ 1 / 3 →
        ((R * R : ℕ) + 1 : ℝ) * (linearNearRowRadius c + 1) ≤ N →
        ((R * R : ℕ) + 1 : ℝ) * (c * Real.exp 1 + 1) ≤ N →
        1 + Real.log R₁ ≤ 2 * θ₁ * Real.log N →
        (θ₁ / (4 * explicitConductorCutoffConstant)) * Real.log N ≤
          Real.log R₁ / explicitConductorCutoffConstant - 1 →
        C_cross_w * (c ^ 7 * (1 + terminalPacketCost R (N / linearDefectCutoff c) N) / Real.log N +
          c ^ 9 * (1 + Real.log c) / Real.log N +
          c ^ 10 * (R : ℝ) ^ 2 / N) ≤ 1 →
      ∀ a : ℕ → ℝ,
        (∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N) ∈
          (conductorSubspace 1 N)ᗮ →
      ∀ {w : EuclideanSpace ℝ (PrimeHorizonIndex N)}, w ∈ (conductorSubspace R₁ N)ᗮ →
        2 * |⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
            (∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N), w⟫| ≤
          (1 / 32 : ℝ) * primeAdjunctionMass R a +
            (1 / 4 : ℝ) * ‖∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 +
            ((Real.log R₁ / explicitConductorCutoffConstant - 1) / 32) *
              (∑ n ∈ Icc 1 (N / linearDefectCutoff c), primeHorizonExtension w n ^ 2) +
            (b * (Real.log R₁ / explicitConductorCutoffConstant - 1) / (32 * c ^ 7)) *
              (∑ n ∈ Ioc (N / linearDefectCutoff c) N, primeHorizonExtension w n ^ 2) +
            (b * (Real.log R₁ / explicitConductorCutoffConstant - 1) / (32 * c ^ 7)) * ‖w‖ ^ 2 := by
  obtain ⟨C_pr, C_np, hC_pr, hC_np, hcross⟩ := exists_completeWeil_cross_le_c9_split_reserves
  let D := explicitConductorCutoffConstant
  have hD : 0 < D := explicitConductorCutoffConstant_pos
  let θ₁ := min (1 / 4096) (1 / (131072 * C_pr * D + 1))
  have hθ₁ : 0 < θ₁ := lt_min (by norm_num) (by positivity)
  have hθ₁_4096 : θ₁ ≤ 1 / 4096 := min_le_left _ _
  have hθ₁_pr : 512 * C_pr * D * θ₁ ≤ 1 / 256 := by
    have hle : θ₁ ≤ 1 / (131072 * C_pr * D + 1) := min_le_right _ _
    have hpos : 0 < 131072 * C_pr * D + 1 := by positivity
    have hm := (le_div_iff₀ hpos).mp hle
    nlinarith only [hm, hθ₁]
  let K_fac := 256 * D + 256 * D / b + 256 * D / (b * θ₁) + 1
  have hK_fac : 0 < K_fac := by dsimp only [K_fac]; positivity
  let C_cross_w := 256 * (2 * C_pr + C_np + 1) * K_fac
  refine ⟨θ₁, C_cross_w, hθ₁, hθ₁_4096, by dsimp only [C_cross_w]; positivity, ?_⟩
  intro R R₁ N c hR hRR₁ hR6 hlog hc1 hc2L hw1 hsize_near hsize_up hH₁_ub hk₁_lb hsmall a hu_1 w hw_R₁
  let L := Real.log (N : ℝ)
  let M := N / linearDefectCutoff c
  let k₁ := Real.log (R₁ : ℝ) / D - 1
  let s_w := k₁ / 32
  let t_w := b * k₁ / (32 * c ^ 7)
  let u := ∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N
  let H := 1 + Real.log (R : ℝ)
  let A := ∑ m ∈ Icc 1 R, a m ^ 2
  let E := primeAdjunctionMass R a
  let G := ∑ m ∈ Icc 1 R, (1 + Real.log m) * a m ^ 2
  let B := terminalPacketCost R M N
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hMN : M ≤ N := Nat.div_le_self N (linearDefectCutoff c)
  have hRR : R * R ≤ N := by
    have hh := (Nat.pow_le_pow_right (by omega : 0 < R) (by norm_num : 2 ≤ 6)).trans hR6
    simpa only [sq] using hh
  have hL1 : 1 ≤ L := by dsimp only [L]; linarith only [hlog, Real.log_natCast_nonneg R]
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have hN0 : (0 : ℝ) < N := by
    have hN2 : 2 ≤ N := by have hh := Nat.mul_le_mul hR hR; omega
    exact_mod_cast (show 0 < N by omega)
  have hk₁_pos : 0 < k₁ := (mul_pos (div_pos hθ₁ (by positivity)) hL0).trans_le hk₁_lb
  have hs_pos : 0 < s_w := by dsimp only [s_w]; positivity
  have ht_pos : 0 < t_w := by dsimp only [t_w]; positivity
  have hw_R : w ∈ (conductorSubspace R N)ᗮ := fun v hv =>
    hw_R₁ v (conductorSubspace_mono hRR₁ N hv)
  have hraw := hcross hR hR6 hMN hlog hc1 hw1 hsize_near hsize_up a hu_1 hw_R
    s_w t_w t_w hs_pos ht_pos ht_pos
  have hH_ub : H ≤ 2 * θ₁ * L := by
    have hlogR : Real.log (R : ℝ) ≤ Real.log (R₁ : ℝ) :=
      Real.log_le_log (by exact_mod_cast (show 0 < R by omega)) (by exact_mod_cast hRR₁)
    dsimp only [H, L] at hH₁_ub ⊢
    linarith only [hlogR, hH₁_ub]
  have hH0 : 0 ≤ H := by dsimp only [H]; positivity
  have hB0 : 0 ≤ B := terminalPacketCost_nonneg R hMN
  have hlc0 : 0 ≤ Real.log c := Real.log_nonneg hc1
  have hA0 : 0 ≤ A := sum_nonneg fun _ _ => sq_nonneg _
  have hE0 : 0 ≤ E := primeAdjunctionMass_nonneg R a
  have hG0 : 0 ≤ G := sum_nonneg fun m _ => by have := Real.log_natCast_nonneg m; positivity
  have hAU : A ≤ 2 * ‖u‖ ^ 2 := by
    have hh := (half_and_three_halves_riesz_of_log_le hR hRR hlog a).1
    linarith only [hh]
  have hG_le : G ≤ 2 * ‖u‖ ^ 2 + E := by
    have hGE : G ≤ A + E := by
      dsimp only [G, A, E, primeAdjunctionMass]
      rw [← sum_add_distrib]
      refine sum_le_sum fun m _ => ?_
      nlinarith only [mul_nonneg (tameDifferent_nonneg m) (sq_nonneg (a m))]
    linarith only [hGE, hAU]
  let e := c ^ 7 * (1 + B) / L + c ^ 9 * (1 + Real.log c) / L + c ^ 10 * (R : ℝ) ^ 2 / (N : ℝ)
  have he_small : (2 * C_pr + C_np + 1) * K_fac * e ≤ 1 / 256 := by
    dsimp only [C_cross_w, L, M, B] at hsmall
    change 256 * (2 * C_pr + C_np + 1) * K_fac * e ≤ 1 at hsmall
    linarith only [hsmall]
  have hc7_ge1 : (1 : ℝ) ≤ c ^ 7 := one_le_pow₀ hc1
  have he_B : c ^ 7 * (1 + B) / L ≤ e := by
    have hh : 0 ≤ c ^ 9 * (1 + Real.log c) / L + c ^ 10 * (R : ℝ) ^ 2 / (N : ℝ) := by positivity
    dsimp only [e]; linarith only [hh]
  have he_1L : 1 / L ≤ e := by
    have h1 : 1 / L ≤ c ^ 7 * (1 + B) / L :=
      div_le_div_of_nonneg_right (by nlinarith only [hc7_ge1, mul_nonneg (pow_nonneg hc0.le 7) hB0])
        hL0.le
    exact h1.trans he_B
  have he_c7 : c ^ 7 / L ≤ e := by
    have h1 : c ^ 7 / L ≤ c ^ 7 * (1 + B) / L :=
      div_le_div_of_nonneg_right (by nlinarith only [mul_nonneg (pow_nonneg hc0.le 7) hB0]) hL0.le
    exact h1.trans he_B
  have he_c7B : c ^ 7 * B / L ≤ e := by
    have h1 : c ^ 7 * B / L ≤ c ^ 7 * (1 + B) / L :=
      div_le_div_of_nonneg_right (by nlinarith only [pow_nonneg hc0.le 7]) hL0.le
    exact h1.trans he_B
  have he_c9 : c ^ 9 * (1 + Real.log c) / L ≤ e := by
    have hh : 0 ≤ c ^ 7 * (1 + B) / L + c ^ 10 * (R : ℝ) ^ 2 / (N : ℝ) := by positivity
    dsimp only [e]; linarith only [hh]
  have he_c10 : c ^ 10 * (R : ℝ) ^ 2 / (N : ℝ) ≤ e := by
    have hh : 0 ≤ c ^ 7 * (1 + B) / L + c ^ 9 * (1 + Real.log c) / L := by positivity
    dsimp only [e]; linarith only [hh]
  have he0 : 0 ≤ e := le_trans (by positivity) he_1L
  have hs_lb : (θ₁ / (128 * D)) * L ≤ s_w := by
    dsimp only [s_w]
    have hh := div_le_div_of_nonneg_right hk₁_lb (by norm_num : (0 : ℝ) ≤ 32)
    exact (by ring : (θ₁ / (128 * D)) * L = ((θ₁ / (4 * D)) * L) / 32).trans_le hh
  have ht_lb : (b * θ₁ / (128 * D)) * (L / c ^ 7) ≤ t_w := by
    dsimp only [t_w]
    have hh := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hk₁_lb hb.le)
      (by positivity : 0 ≤ 32 * c ^ 7)
    refine (?_ : (b * θ₁ / (128 * D)) * (L / c ^ 7) =
        b * ((θ₁ / (4 * D)) * L) / (32 * c ^ 7)).trans_le hh
    field_simp [hD.ne', hc0.ne']; ring
  have hs_lb_pos : 0 < (θ₁ / (128 * D)) * L := by positivity
  have ht_lb_pos : 0 < (b * θ₁ / (128 * D)) * (L / c ^ 7) := by positivity
  have hr_Hs : H / (L * s_w) ≤ K_fac * e := by
    calc
      H / (L * s_w) ≤ (2 * θ₁ * L) / (L * ((θ₁ / (128 * D)) * L)) :=
        (div_le_div_of_nonneg_right hH_ub (by positivity)).trans
          (div_le_div_of_nonneg_left (by positivity) (by positivity)
            (mul_le_mul_of_nonneg_left hs_lb hL0.le))
      _ = 256 * D * (1 / L) := by field_simp [hL0.ne', hθ₁.ne', hD.ne']; ring
      _ ≤ 256 * D * e := mul_le_mul_of_nonneg_left he_1L (by positivity)
      _ ≤ K_fac * e := mul_le_mul_of_nonneg_right
        (by dsimp only [K_fac]; have : 0 ≤ 256 * D / b + 256 * D / (b * θ₁) + 1 := by positivity
            linarith only [this]) he0
  have hr_Ht : H / (L * t_w) ≤ K_fac * e := by
    calc
      H / (L * t_w) ≤ (2 * θ₁ * L) / (L * ((b * θ₁ / (128 * D)) * (L / c ^ 7))) :=
        (div_le_div_of_nonneg_right hH_ub (by positivity)).trans
          (div_le_div_of_nonneg_left (by positivity) (by positivity)
            (mul_le_mul_of_nonneg_left ht_lb hL0.le))
      _ = (256 * D / b) * (c ^ 7 / L) := by
        field_simp [hL0.ne', hθ₁.ne', hD.ne', hb.ne', hc0.ne']; ring
      _ ≤ (256 * D / b) * e := mul_le_mul_of_nonneg_left he_c7 (by positivity)
      _ ≤ K_fac * e := mul_le_mul_of_nonneg_right
        (by dsimp only [K_fac]; have : 0 ≤ 256 * D + 256 * D / (b * θ₁) + 1 := by positivity
            linarith only [this]) he0
  have hr_H2s : C_pr * (H ^ 2 / (L * s_w)) ≤ 1 / 256 := by
    have hH2 : H ^ 2 ≤ (2 * θ₁ * L) ^ 2 := pow_le_pow_left₀ hH0 hH_ub 2
    have hdiv : H ^ 2 / (L * s_w) ≤ 512 * D * θ₁ := by
      calc
        H ^ 2 / (L * s_w) ≤ (2 * θ₁ * L) ^ 2 / (L * ((θ₁ / (128 * D)) * L)) :=
          (div_le_div_of_nonneg_right hH2 (by positivity)).trans
            (div_le_div_of_nonneg_left (by positivity) (by positivity)
              (mul_le_mul_of_nonneg_left hs_lb hL0.le))
        _ = 512 * D * θ₁ := by field_simp [hL0.ne', hθ₁.ne', hD.ne']; ring
    exact (mul_le_mul_of_nonneg_left hdiv hC_pr.le).trans
      ((by ring : C_pr * (512 * D * θ₁) = 512 * C_pr * D * θ₁).trans_le hθ₁_pr)
  have hr_HBt : H * B / (L * t_w) ≤ K_fac * e := by
    have hHB : H * B ≤ 2 * θ₁ * L * B := mul_le_mul_of_nonneg_right hH_ub hB0
    calc
      H * B / (L * t_w) ≤ (2 * θ₁ * L * B) / (L * ((b * θ₁ / (128 * D)) * (L / c ^ 7))) :=
        (div_le_div_of_nonneg_right hHB (by positivity)).trans
          (div_le_div_of_nonneg_left (by positivity) (by positivity)
            (mul_le_mul_of_nonneg_left ht_lb hL0.le))
      _ = (256 * D / b) * (c ^ 7 * B / L) := by
        field_simp [hL0.ne', hθ₁.ne', hD.ne', hb.ne', hc0.ne']; ring
      _ ≤ (256 * D / b) * e := mul_le_mul_of_nonneg_left he_c7B (by positivity)
      _ ≤ K_fac * e := mul_le_mul_of_nonneg_right
        (by dsimp only [K_fac]; have : 0 ≤ 256 * D + 256 * D / (b * θ₁) + 1 := by positivity
            linarith only [this]) he0
  have hr_G : (c ^ 2 * H * (1 + Real.log c) / L) / t_w ≤ K_fac * e := by
    have hnum : c ^ 2 * H * (1 + Real.log c) ≤ 2 * θ₁ * L * c ^ 2 * (1 + Real.log c) := by
      have hm := mul_le_mul_of_nonneg_left hH_ub (sq_nonneg c)
      exact (mul_le_mul_of_nonneg_right hm (by positivity)).trans_eq (by ring)
    have hc29 : c ^ 2 ≤ c ^ 9 := pow_le_pow_right₀ hc1 (by norm_num)
    have hc29_e : c ^ 2 * (1 + Real.log c) / L ≤ c ^ 9 * (1 + Real.log c) / L :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hc29 (by positivity)) hL0.le
    calc
      (c ^ 2 * H * (1 + Real.log c) / L) / t_w ≤
          (2 * θ₁ * L * c ^ 2 * (1 + Real.log c) / L) / ((b * θ₁ / (128 * D)) * (L / c ^ 7)) :=
        (div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hnum hL0.le) ht_pos.le).trans
          (div_le_div_of_nonneg_left (by positivity) ht_lb_pos ht_lb)
      _ = (256 * D / b) * (c ^ 9 * (1 + Real.log c) / L) := by
        field_simp [hL0.ne', hθ₁.ne', hD.ne', hb.ne', hc0.ne']; ring
      _ ≤ (256 * D / b) * e := mul_le_mul_of_nonneg_left he_c9 (by positivity)
      _ ≤ K_fac * e := mul_le_mul_of_nonneg_right
        (by dsimp only [K_fac]; have : 0 ≤ 256 * D + 256 * D / (b * θ₁) + 1 := by positivity
            linarith only [this]) he0
  have hr_U :
      (c ^ 4 * (1 + Real.log c) / L + c ^ 3 * (R : ℝ) ^ 2 * (L / (N : ℝ)) +
          c ^ 2 * (1 + Real.log c)) / t_w ≤ 2 * K_fac * e := by
    have hc42 : c ^ 4 * (1 + Real.log c) / L ≤ c ^ 2 * (1 + Real.log c) := by
      have h1 : c ^ 2 / L ≤ 1 := (div_le_one hL0).mpr hc2L
      have h2 := mul_le_mul_of_nonneg_right h1
        (mul_nonneg (sq_nonneg c) (by positivity : 0 ≤ 1 + Real.log c))
      exact (by ring : c ^ 4 * (1 + Real.log c) / L =
        (c ^ 2 / L) * (c ^ 2 * (1 + Real.log c))).trans_le (h2.trans_eq (one_mul _))
    have hmain :
        (c ^ 4 * (1 + Real.log c) / L + c ^ 2 * (1 + Real.log c)) / t_w ≤ K_fac * e := by
      have hsum : c ^ 4 * (1 + Real.log c) / L + c ^ 2 * (1 + Real.log c) ≤
          2 * c ^ 2 * (1 + Real.log c) := by linarith only [hc42]
      calc
        _ ≤ (2 * c ^ 2 * (1 + Real.log c)) / ((b * θ₁ / (128 * D)) * (L / c ^ 7)) :=
          (div_le_div_of_nonneg_right hsum ht_pos.le).trans
            (div_le_div_of_nonneg_left (by positivity) ht_lb_pos ht_lb)
        _ = (256 * D / (b * θ₁)) * (c ^ 9 * (1 + Real.log c) / L) := by
          field_simp [hL0.ne', hθ₁.ne', hD.ne', hb.ne', hc0.ne']; ring
        _ ≤ (256 * D / (b * θ₁)) * e := mul_le_mul_of_nonneg_left he_c9 (by positivity)
        _ ≤ K_fac * e := mul_le_mul_of_nonneg_right
          (by dsimp only [K_fac]; have : 0 ≤ 256 * D + 256 * D / b + 1 := by positivity
              linarith only [this]) he0
    have htail : (c ^ 3 * (R : ℝ) ^ 2 * (L / (N : ℝ))) / t_w ≤ K_fac * e := by
      calc
        (c ^ 3 * (R : ℝ) ^ 2 * (L / (N : ℝ))) / t_w ≤
            (c ^ 3 * (R : ℝ) ^ 2 * (L / (N : ℝ))) / ((b * θ₁ / (128 * D)) * (L / c ^ 7)) :=
          div_le_div_of_nonneg_left (by positivity) ht_lb_pos ht_lb
        _ = (128 * D / (b * θ₁)) * (c ^ 10 * (R : ℝ) ^ 2 / (N : ℝ)) := by
          field_simp [hL0.ne', hN0.ne', hθ₁.ne', hD.ne', hb.ne', hc0.ne']; ring
        _ ≤ (128 * D / (b * θ₁)) * e := mul_le_mul_of_nonneg_left he_c10 (by positivity)
        _ ≤ K_fac * e := mul_le_mul_of_nonneg_right
          (by dsimp only [K_fac]
              have h1 : 0 ≤ 256 * D + 256 * D / b + 1 := by positivity
              have h2 : 0 ≤ 128 * D / (b * θ₁) := by positivity
              linarith only [h1, h2]) he0
    have hsplit_u :
        (c ^ 4 * (1 + Real.log c) / L + c ^ 3 * (R : ℝ) ^ 2 * (L / (N : ℝ)) +
            c ^ 2 * (1 + Real.log c)) / t_w =
          (c ^ 4 * (1 + Real.log c) / L + c ^ 2 * (1 + Real.log c)) / t_w +
            (c ^ 3 * (R : ℝ) ^ 2 * (L / (N : ℝ))) / t_w := by ring
    rw [hsplit_u]
    linarith only [hmain, htail]
  have hpa : C_pr * (H / (L * s_w)) + C_pr * (H / (L * t_w)) ≤ 1 / 128 := by
    have h1 := mul_le_mul_of_nonneg_left hr_Hs hC_pr.le
    have h2 := mul_le_mul_of_nonneg_left hr_Ht hC_pr.le
    nlinarith only [h1, h2, he_small, mul_nonneg hC_np.le (mul_nonneg hK_fac.le he0),
      mul_nonneg hK_fac.le he0]
  have hpe : C_pr * (H ^ 2 / (L * s_w)) + C_pr * (H * B / (L * t_w)) ≤ 1 / 128 := by
    have h2 := mul_le_mul_of_nonneg_left hr_HBt hC_pr.le
    nlinarith only [hr_H2s, h2, he_small, mul_nonneg hC_np.le (mul_nonneg hK_fac.le he0),
      mul_nonneg hK_fac.le he0]
  have hng : C_np * ((c ^ 2 * H * (1 + Real.log c) / L) / t_w) ≤ 1 / 128 := by
    have h1 := mul_le_mul_of_nonneg_left hr_G hC_np.le
    nlinarith only [h1, he_small, mul_nonneg hC_pr.le (mul_nonneg hK_fac.le he0),
      mul_nonneg hK_fac.le he0]
  have hnu :
      C_np * ((c ^ 4 * (1 + Real.log c) / L + c ^ 3 * (R : ℝ) ^ 2 * (L / (N : ℝ)) +
          c ^ 2 * (1 + Real.log c)) / t_w) ≤ 1 / 16 := by
    have h1 := mul_le_mul_of_nonneg_left hr_U hC_np.le
    nlinarith only [h1, he_small, mul_nonneg hC_pr.le (mul_nonneg hK_fac.le he0),
      mul_nonneg hK_fac.le he0]
  have hfact :
      C_pr * (H * A + H ^ 2 * E) / (L * s_w) +
        C_pr * (H * A + H * B * E) / (L * t_w) +
        C_np * ((c ^ 2 * H * (1 + Real.log c) / L) * G +
          (c ^ 4 * (1 + Real.log c) / L + c ^ 3 * (R : ℝ) ^ 2 * (L / (N : ℝ)) +
            c ^ 2 * (1 + Real.log c)) * ‖u‖ ^ 2) / t_w =
      (C_pr * (H / (L * s_w)) + C_pr * (H / (L * t_w))) * A +
        (C_pr * (H ^ 2 / (L * s_w)) + C_pr * (H * B / (L * t_w))) * E +
        (C_np * ((c ^ 2 * H * (1 + Real.log c) / L) / t_w)) * G +
        (C_np * ((c ^ 4 * (1 + Real.log c) / L + c ^ 3 * (R : ℝ) ^ 2 * (L / (N : ℝ)) +
          c ^ 2 * (1 + Real.log c)) / t_w)) * ‖u‖ ^ 2 := by ring
  change 2 * |⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N) u, w⟫| ≤
    C_pr * (H * A + H ^ 2 * E) / (L * s_w) +
      C_pr * (H * A + H * B * E) / (L * t_w) +
      C_np * ((c ^ 2 * H * (1 + Real.log c) / L) * G +
        (c ^ 4 * (1 + Real.log c) / L + c ^ 3 * (R : ℝ) ^ 2 * (L / (N : ℝ)) +
          c ^ 2 * (1 + Real.log c)) * ‖u‖ ^ 2) / t_w +
      s_w * (∑ n ∈ Icc 1 M, primeHorizonExtension w n ^ 2) +
      t_w * (∑ n ∈ Ioc M N, primeHorizonExtension w n ^ 2) +
      t_w * ‖w‖ ^ 2 at hraw
  rw [hfact] at hraw
  have h1 := mul_le_mul_of_nonneg_right hpa hA0
  have h2 := mul_le_mul_of_nonneg_right hpe hE0
  have h3 := mul_le_mul_of_nonneg_right hng hG0
  have h4 := mul_le_mul_of_nonneg_right hnu (sq_nonneg ‖u‖)
  change 2 * |⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N) u, w⟫| ≤
    (1 / 32 : ℝ) * E + (1 / 4 : ℝ) * ‖u‖ ^ 2 +
      s_w * (∑ n ∈ Icc 1 M, primeHorizonExtension w n ^ 2) +
      t_w * (∑ n ∈ Ioc M N, primeHorizonExtension w n ^ 2) +
      t_w * ‖w‖ ^ 2
  linarith only [hraw, h1, h2, h3, h4, hAU, hG_le, hE0, sq_nonneg ‖u‖]

private theorem telescoped_three_band_orthogonal_split_confinement {Q₁ R₀ R₁ N : ℕ}
    (hQR₀ : Q₁ ≤ R₀) (hR₀R₁ : R₀ ≤ R₁)
    {z : EuclideanSpace ℝ (PrimeHorizonIndex N)}
    (hz : z ∈ (conductorSubspace Q₁ N)ᗮ) :
    ∃ u₀ u₁ w : EuclideanSpace ℝ (PrimeHorizonIndex N),
      z = u₀ + u₁ + w ∧
      u₀ ∈ conductorSubspace R₀ N ∧
      u₀ ∈ (conductorSubspace Q₁ N)ᗮ ∧
      u₁ ∈ conductorSubspace R₁ N ∧
      u₁ ∈ (conductorSubspace R₀ N)ᗮ ∧
      w ∈ (conductorSubspace R₁ N)ᗮ ∧
      ‖z‖ ^ 2 = ‖u₀‖ ^ 2 + ‖u₁‖ ^ 2 + ‖w‖ ^ 2 := by
  let p₁ := (conductorSubspace R₁ N).starProjection z
  let w := z - p₁
  let u₀ := (conductorSubspace R₀ N).starProjection p₁
  let u₁ := p₁ - u₀
  have hp₁_mem : p₁ ∈ conductorSubspace R₁ N :=
    (conductorSubspace R₁ N).starProjection_apply_mem z
  have hw_orth : w ∈ (conductorSubspace R₁ N)ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro v hv
    rw [real_inner_comm]
    exact (conductorSubspace R₁ N).starProjection_inner_eq_zero z v hv
  have hp₁_orthQ : p₁ ∈ (conductorSubspace Q₁ N)ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro v hv
    have hvR₁ : v ∈ conductorSubspace R₁ N :=
      conductorSubspace_mono (hQR₀.trans hR₀R₁) N hv
    have hzv : ⟪v, z⟫ = 0 := Submodule.inner_right_of_mem_orthogonal hv hz
    have hvw : ⟪v, w⟫ = 0 := Submodule.inner_right_of_mem_orthogonal hvR₁ hw_orth
    have hp₁_id : p₁ = z - w := by dsimp only [w]; abel
    rw [hp₁_id, inner_sub_right, hzv, hvw, sub_zero]
  obtain ⟨u₀', u₁', hp₁_eq, hu₀'_mem, hu₀'_orthQ, hu₁'_mem, hu₁'_orthR₀, hp₁_norm⟩ :=
    collective_two_band_orthogonal_split hQR₀ hR₀R₁ hp₁_mem hp₁_orthQ
  have hz_eq : z = u₀' + u₁' + w := by
    have : z = p₁ + w := by dsimp only [w]; abel
    rw [this, hp₁_eq]
  have horth_p₁w : ⟪p₁, w⟫ = 0 :=
    Submodule.inner_right_of_mem_orthogonal hp₁_mem hw_orth
  have hz_norm : ‖z‖ ^ 2 = ‖u₀'‖ ^ 2 + ‖u₁'‖ ^ 2 + ‖w‖ ^ 2 := by
    have hzw : z = p₁ + w := by dsimp only [w]; abel
    have h1 := norm_add_sq_real p₁ w
    rw [← hzw, horth_p₁w, mul_zero, add_zero, hp₁_norm] at h1
    exact h1
  exact ⟨u₀', u₁', w, hz_eq, hu₀'_mem, hu₀'_orthQ, hu₁'_mem, hu₁'_orthR₀, hw_orth, hz_norm⟩

private theorem completeWeilEnergy_three_add_ge_confinement (φ : ℝ → ℝ) (c : ℝ) {N : ℕ}
    (u₀ u₁ w : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    completeWeilEnergy φ c N u₀ +
      completeWeilEnergy φ c N u₁ +
      completeWeilEnergy φ c N w -
      2 * |⟪Matrix.toEuclideanLin (completeWeilMatrix φ c N) u₀, u₁⟫| -
      2 * |⟪Matrix.toEuclideanLin (completeWeilMatrix φ c N) u₀, w⟫| -
      2 * |⟪Matrix.toEuclideanLin (completeWeilMatrix φ c N) u₁, w⟫| ≤
      completeWeilEnergy φ c N (u₀ + u₁ + w) := by
  let A := Matrix.toEuclideanLin (completeWeilMatrix φ c N)
  have hsym : ∀ x y : EuclideanSpace ℝ (PrimeHorizonIndex N), ⟪A x, y⟫ = ⟪x, A y⟫ :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr (completeWeilMatrix_isHermitian φ c N)
  have h01 : ⟪A u₁, u₀⟫ = ⟪A u₀, u₁⟫ := by rw [hsym u₁ u₀, real_inner_comm]
  have h0w : ⟪A w, u₀⟫ = ⟪A u₀, w⟫ := by rw [hsym w u₀, real_inner_comm]
  have h1w : ⟪A w, u₁⟫ = ⟪A u₁, w⟫ := by rw [hsym w u₁, real_inner_comm]
  have hexp : completeWeilEnergy φ c N (u₀ + u₁ + w) =
      completeWeilEnergy φ c N u₀ + completeWeilEnergy φ c N u₁ + completeWeilEnergy φ c N w +
        2 * ⟪A u₀, u₁⟫ + 2 * ⟪A u₀, w⟫ + 2 * ⟪A u₁, w⟫ := by
    unfold completeWeilEnergy
    change ⟪A (u₀ + u₁ + w), u₀ + u₁ + w⟫ =
      ⟪A u₀, u₀⟫ + ⟪A u₁, u₁⟫ + ⟪A w, w⟫ + 2 * ⟪A u₀, u₁⟫ + 2 * ⟪A u₀, w⟫ + 2 * ⟪A u₁, w⟫
    rw [map_add, map_add, inner_add_left, inner_add_left,
      inner_add_right, inner_add_right, inner_add_right, inner_add_right,
      inner_add_right, inner_add_right, h01, h0w, h1w]
    ring
  rw [hexp]
  have habs01 := neg_abs_le ⟪A u₀, u₁⟫
  have habs0w := neg_abs_le ⟪A u₀, w⟫
  have habs1w := neg_abs_le ⟪A u₁, w⟫
  linarith only [habs01, habs0w, habs1w]

private theorem complement_three_band_vector_assembly_with_defect_one_ninth
    {Q₁ R₀ R₁ N : ℕ} {c b k₁ Lh κ₀ C_coerc0 C_band1 : ℝ}
    (hQ2 : 2 ≤ Q₁) (hQR₀ : Q₁ ≤ R₀) (hR₀R₁ : R₀ ≤ R₁)
    (hRR₀ : R₀ * R₀ ≤ N) (hRR₁ : R₁ * R₁ ≤ N)
    (h18_R₀ : 18 * (1 + Real.log (R₀ : ℝ)) ≤ Real.log (N : ℝ))
    (h18_R₁ : 18 * (1 + Real.log (R₁ : ℝ)) ≤ Real.log (N : ℝ))
    (hc1 : 1 ≤ c) (hb : 0 < b) (hb16 : b ≤ 1 / 16) (hk₁_pos : 0 < k₁)
    (hband0 : ∀ a₀ : ℕ → ℝ,
      (∑ m ∈ Icc 1 R₀, a₀ m • normalizedRamanujanHorizonVector m N) ∈
        (conductorSubspace Q₁ N)ᗮ →
      (1 / 8 : ℝ) * primeAdjunctionMass R₀ a₀ +
        ((3 / 4 : ℝ) * Real.log (Q₁ : ℝ) - Real.log c - C_coerc0) *
          ‖∑ m ∈ Icc 1 R₀, a₀ m • normalizedRamanujanHorizonVector m N‖ ^ 2 ≤
        completeWeilEnergy tiltedUnitSpline c N
          (∑ m ∈ Icc 1 R₀, a₀ m • normalizedRamanujanHorizonVector m N))
    (hband1 : ∀ a₁ : ℕ → ℝ,
      (∑ m ∈ Icc 1 R₁, a₁ m • normalizedRamanujanHorizonVector m N) ∈
        (conductorSubspace R₀ N)ᗮ →
      (1 / 8 : ℝ) * primeAdjunctionMass R₁ a₁ +
        ((1 / 4 : ℝ) * Real.log (R₀ : ℝ) - C_band1 * c ^ 2 * (1 + Real.log c)) *
          ‖∑ m ∈ Icc 1 R₁, a₁ m • normalizedRamanujanHorizonVector m N‖ ^ 2 ≤
        completeWeilEnergy tiltedUnitSpline c N
          (∑ m ∈ Icc 1 R₁, a₁ m • normalizedRamanujanHorizonVector m N))
    (hband2 : ∀ {w : EuclideanSpace ℝ (PrimeHorizonIndex N)},
      w ∈ (conductorSubspace R₁ N)ᗮ →
      (b / c ^ 7) * poleDefect N (primeHorizonExtension w) +
        (k₁ / 4) * (∑ n ∈ Icc 1 (N / linearDefectCutoff c), primeHorizonExtension w n ^ 2) +
        (b * k₁ / (2 * c ^ 7)) *
          (∑ n ∈ Ioc (N / linearDefectCutoff c) N, primeHorizonExtension w n ^ 2) ≤
        completeWeilEnergy tiltedUnitSpline c N w)
    (hcr01_fn : ∀ a₀ : ℕ → ℝ,
      (∑ m ∈ Icc 1 R₀, a₀ m • normalizedRamanujanHorizonVector m N) ∈
        (conductorSubspace 1 N)ᗮ →
      ∀ {u₁ : EuclideanSpace ℝ (PrimeHorizonIndex N)}, u₁ ∈ (conductorSubspace R₀ N)ᗮ →
      2 * |⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
          (∑ m ∈ Icc 1 R₀, a₀ m • normalizedRamanujanHorizonVector m N), u₁⟫| ≤
        (1 / 32 : ℝ) * primeAdjunctionMass R₀ a₀ +
          (1 / 4 : ℝ) * ‖∑ m ∈ Icc 1 R₀, a₀ m • normalizedRamanujanHorizonVector m N‖ ^ 2 +
          (1 / 16 : ℝ) * Lh * ‖u₁‖ ^ 2)
    (hcr0w_fn : ∀ a₀ : ℕ → ℝ,
      (∑ m ∈ Icc 1 R₀, a₀ m • normalizedRamanujanHorizonVector m N) ∈
        (conductorSubspace 1 N)ᗮ →
      ∀ {w : EuclideanSpace ℝ (PrimeHorizonIndex N)}, w ∈ (conductorSubspace R₁ N)ᗮ →
      2 * |⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
          (∑ m ∈ Icc 1 R₀, a₀ m • normalizedRamanujanHorizonVector m N), w⟫| ≤
        (1 / 32 : ℝ) * primeAdjunctionMass R₀ a₀ +
          (1 / 4 : ℝ) * ‖∑ m ∈ Icc 1 R₀, a₀ m • normalizedRamanujanHorizonVector m N‖ ^ 2 +
          (k₁ / 32) * (∑ n ∈ Icc 1 (N / linearDefectCutoff c), primeHorizonExtension w n ^ 2) +
          (b * k₁ / (32 * c ^ 7)) *
            (∑ n ∈ Ioc (N / linearDefectCutoff c) N, primeHorizonExtension w n ^ 2) +
          (b * k₁ / (32 * c ^ 7)) * ‖w‖ ^ 2)
    (hcr1w_fn : ∀ a₁ : ℕ → ℝ,
      (∑ m ∈ Icc 1 R₁, a₁ m • normalizedRamanujanHorizonVector m N) ∈
        (conductorSubspace 1 N)ᗮ →
      ∀ {w : EuclideanSpace ℝ (PrimeHorizonIndex N)}, w ∈ (conductorSubspace R₁ N)ᗮ →
      2 * |⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
          (∑ m ∈ Icc 1 R₁, a₁ m • normalizedRamanujanHorizonVector m N), w⟫| ≤
        (1 / 32 : ℝ) * primeAdjunctionMass R₁ a₁ +
          (1 / 4 : ℝ) * ‖∑ m ∈ Icc 1 R₁, a₁ m • normalizedRamanujanHorizonVector m N‖ ^ 2 +
          (k₁ / 32) * (∑ n ∈ Icc 1 (N / linearDefectCutoff c), primeHorizonExtension w n ^ 2) +
          (b * k₁ / (32 * c ^ 7)) *
            (∑ n ∈ Ioc (N / linearDefectCutoff c) N, primeHorizonExtension w n ^ 2) +
          (b * k₁ / (32 * c ^ 7)) * ‖w‖ ^ 2)
    (hfl0 : κ₀ + 2 + 1 / 2 ≤ (3 / 4 : ℝ) * Real.log (Q₁ : ℝ) - Real.log c - C_coerc0)
    (hfl1 : κ₀ + 2 + (1 / 16 : ℝ) * Lh + 1 / 4 ≤
      (1 / 4 : ℝ) * Real.log (R₀ : ℝ) - C_band1 * c ^ 2 * (1 + Real.log c))
    (hfl2_P : κ₀ + 2 ≤ k₁ / 8)
    (hfl2_S : κ₀ + 2 ≤ 3 * b * k₁ / (8 * c ^ 7))
    {z : EuclideanSpace ℝ (PrimeHorizonIndex N)} (hz : z ∈ (conductorSubspace Q₁ N)ᗮ) :
    (b / (4 * c ^ 7)) * poleDefect N (primeHorizonExtension z) +
      (κ₀ + 2) * ‖z‖ ^ 2 ≤ completeWeilEnergy tiltedUnitSpline c N z := by
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hR₀2 : 2 ≤ R₀ := hQ2.trans hQR₀
  have hR₁2 : 2 ≤ R₁ := hR₀2.trans hR₀R₁
  obtain ⟨u₀, u₁, w, hz_eq, hu₀_mem, hu₀_orthQ, hu₁_mem, hu₁_orthR₀, hw_orthR₁, hnorm_split⟩ :=
    telescoped_three_band_orthogonal_split_confinement hQR₀ hR₀R₁ hz
  obtain ⟨a₀, -, ha₀⟩ := (mem_conductorSubspace_iff (M := R₀) (N := N) (x := u₀)).mp hu₀_mem
  obtain ⟨a₁, -, ha₁⟩ := (mem_conductorSubspace_iff (M := R₁) (N := N) (x := u₁)).mp hu₁_mem
  have hu₀_1 : u₀ ∈ (conductorSubspace 1 N)ᗮ := fun v hv =>
    hu₀_orthQ v (conductorSubspace_mono ((by norm_num : 1 ≤ 2).trans hQ2) N hv)
  have hu₁_1 : u₁ ∈ (conductorSubspace 1 N)ᗮ := fun v hv =>
    hu₁_orthR₀ v (conductorSubspace_mono ((by norm_num : 1 ≤ 2).trans hR₀2) N hv)
  have hdiag0 := hband0 a₀ (ha₀.symm ▸ hu₀_orthQ)
  rw [← ha₀] at hdiag0
  have hdiag1 := hband1 a₁ (ha₁.symm ▸ hu₁_orthR₀)
  rw [← ha₁] at hdiag1
  have hdiag2 := hband2 hw_orthR₁
  have hcr01 := hcr01_fn a₀ (ha₀.symm ▸ hu₀_1) hu₁_orthR₀
  rw [← ha₀] at hcr01
  have hcr0w := hcr0w_fn a₀ (ha₀.symm ▸ hu₀_1) hw_orthR₁
  rw [← ha₀] at hcr0w
  have hcr1w := hcr1w_fn a₁ (ha₁.symm ▸ hu₁_1) hw_orthR₁
  rw [← ha₁] at hcr1w
  have hdef0 := poleDefect_normalizedRamanujanPacket_le_three_halves_primeAdjunctionMass
    hR₀2 hRR₀ h18_R₀ a₀
  rw [← ha₀] at hdef0
  have hdef1 := poleDefect_normalizedRamanujanPacket_le_three_halves_primeAdjunctionMass
    hR₁2 hRR₁ h18_R₁ a₁
  rw [← ha₁] at hdef1
  have hdef_z := poleDefect_primeHorizonExtension_three_add_le N u₀ u₁ w
  rw [← hz_eq] at hdef_z
  have hbc7_16 : b / c ^ 7 ≤ 1 / 16 :=
    (div_le_self hb.le (one_le_pow₀ hc1)).trans hb16
  have hbc7_24 : b / c ^ 7 ≤ 1 / 24 := by
    -- Wait: 1/16 > 1/24! Instead, b / (4 * c^7) * 4 = b / c^7, wait:
    -- For u₀, we have (1 / 16) * E₀ ≥ (1 / 24) * D(u₀). And (b / c^7) * (3 / 4) ≤ (1 / 16) * (3 / 4) = 3 / 64 > 1 / 24!
    -- Wait: poleDefect_primeHorizonExtension_three_add_le has factor 4, so:
    -- (b / (4 * c^7)) * D(z) ≤ (b / c^7) * D(u₀) + (b / c^7) * D(u₁) + (b / c^7) * D(w)!
    -- Wait: if we multiply by b / (6 * c^7) instead of b / (4 * c^7), then:
    -- (b / (6 * c^7)) * D(z) ≤ (2 * b / (3 * c^7)) * (D(u₀) + D(u₁) + D(w))
    -- and 2 * b / (3 * c^7) ≤ 2 / (3 * 16) = 1 / 24!
    sorry
  sorry

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
