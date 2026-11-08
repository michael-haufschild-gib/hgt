import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.NonpolarCollarResidualsVanish
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.AllRatioDeepConductorPairings

/-!
# Low-conductor pairings with the prefix and collar

Deep-row cancellation pays the first band. The full residual budget pays the
second band and the far prefix. Nonpolar cancellation pays the far collar.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Finset Filter Topology
open scoped Classical BigOperators RealInnerProductSpace Matrix
namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open ArithmeticHodgeTheoryOfDegenerations BezoutValuationIncidence CompletedArithmeticForms
  RenormalizedArithmeticPotentialTheory RenormalizedArithmeticPotentialTheory.CompletedShell
  SpacingScaleHarmonicAnalysis

/-- The whole nonpolar low packet is paid by arbitrarily small fixed prefix and collar reserves. -/
theorem eventually_nonpolar_lowPacket_schur_payment
    {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R))
    {κ_P κ_S : ℝ} (hκP : 0 < κ_P) (hκS : 0 < κ_S) :
    ∀ᶠ N : ℕ in atTop,
      ∀ u₀ ∈ conductorSubspace ⌊Real.exp (Real.log (N : ℝ) ^ (1 / 2 : ℝ))⌋₊ N,
      ∀ u₁ w : EuclideanSpace ℝ (PrimeHorizonIndex N),
        8 * (∑ m ∈ Icc 2 (lowPacketCutoff N),
          ⟪conductorResidualVector (c N) m N, u₀ + u₁ + w⟫ ^ 2 /
            completedConductorEnergy tiltedUnitSpline (c N) m) ≤
        ‖u₀‖ ^ 2 + (Real.log (N : ℝ) ^ (1 / 2 : ℝ) / 32) * ‖u₁‖ ^ 2 +
          (κ_P * Real.log N / (1 + Real.log (Real.log N)) ^ 5) *
            (∑ n ∈ Icc 1 (N / linearDefectCutoff (c N)), primeHorizonExtension w n ^ 2) +
          (κ_S * Real.log N / c N ^ 7) *
            topCollarSeventhMass (N / linearDefectCutoff (c N)) N (primeHorizonExtension w) := by
  have hcost := (tendsto_nonpolar_lowPacket_collar_schur_cost hc hR hcrit).eventually
    (gt_mem_nhds (show 0 < κ_S / 48 by positivity))
  filter_upwards [eventually_critical_schur_pairing_except_collar hc hR hcrit hκP, hcost,
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop 0]
    with N hpair hcostN hL
  intro u₀ hu₀ u₁ w
  have hc0 : 0 < c N := zero_lt_one.trans_le (hc N)
  let M := N / linearDefectCutoff (c N)
  let D := ∑ m ∈ Icc 2 (lowPacketCutoff N),
    topCollarDualSeventhMass M N (conductorResidualVector (c N) m N) /
      completedConductorEnergy tiltedUnitSpline (c N) m
  have hs : Icc 2 (lowPacketCutoff N) ⊆ Icc 1 (lowPacketCutoff N) :=
    Icc_subset_Icc (by norm_num) le_rfl
  have hb := hpair (Icc 2 (lowPacketCutoff N)) hs M (Nat.div_le_self _ _) u₀ hu₀ u₁ w
  have hD : 48 * D ≤ κ_S * Real.log N / c N ^ 7 := by
    change c N ^ 7 / Real.log N * D < κ_S / 48 at hcostN
    have hh := mul_le_mul_of_nonneg_right hcostN.le
      (show 0 ≤ 48 * Real.log (N : ℝ) / c N ^ 7 by positivity)
    have he : (c N ^ 7 / Real.log N * D) * (48 * Real.log N / c N ^ 7) = 48 * D := by
      field_simp
    rw [he] at hh
    exact hh.trans_eq (by ring)
  have hpay := mul_le_mul_of_nonneg_right hD (topCollarSeventhMass_nonneg M N (primeHorizonExtension w))
  exact hb.trans (add_le_add_left hpay _)

/-- All low conductors, including the pole, decouple from the non-collar pieces. -/
theorem eventually_lowPacket_noncollar_schur_payment
    {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R))
    {κ_P : ℝ} (hκP : 0 < κ_P) :
    ∀ᶠ N : ℕ in atTop, ∀ M : ℕ, M ≤ N →
      ∀ u₀ ∈ conductorSubspace ⌊Real.exp (Real.log (N : ℝ) ^ (1 / 2 : ℝ))⌋₊ N,
      ∀ u₁ w : EuclideanSpace ℝ (PrimeHorizonIndex N),
        8 * (∑ m ∈ Icc 1 (lowPacketCutoff N),
          ⟪conductorResidualVector (c N) m N, u₀ + u₁ + horizonPrefixVector M w⟫ ^ 2 /
            completedConductorEnergy tiltedUnitSpline (c N) m) ≤
        ‖u₀‖ ^ 2 + (Real.log (N : ℝ) ^ (1 / 2 : ℝ) / 32) * ‖u₁‖ ^ 2 +
          (κ_P * Real.log N / (1 + Real.log (Real.log N)) ^ 5) *
            (∑ n ∈ Icc 1 M, primeHorizonExtension w n ^ 2) := by
  filter_upwards [eventually_critical_schur_pairing_except_collar hc hR hcrit hκP]
    with N hpair M hMN u₀ hu₀ u₁ w
  have hb := hpair (Icc 1 (lowPacketCutoff N)) (by rfl) M hMN u₀ hu₀ u₁ (horizonPrefixVector M w)
  have hprefix : (∑ n ∈ Icc 1 M, primeHorizonExtension (horizonPrefixVector M w) n ^ 2) =
      ∑ n ∈ Icc 1 M, primeHorizonExtension w n ^ 2 := by
    rw [primeHorizonExtension_horizonPrefixVector hMN]
    exact sum_congr rfl fun n hn => by rw [if_pos (mem_Icc.mp hn).2]
  have hcollar : topCollarSeventhMass M N (primeHorizonExtension (horizonPrefixVector M w)) = 0 := by
    rw [primeHorizonExtension_horizonPrefixVector hMN]
    unfold topCollarSeventhMass
    exact sum_eq_zero fun n hn => by
      rw [if_neg (by have := (mem_Ioc.mp hn).1; omega), zero_pow (by decide), mul_zero]
  rw [hprefix, hcollar, mul_zero, add_zero] at hb
  exact hb

/-- Cutting to the collar kills the prefix mass. -/
theorem prefix_mass_horizonCollarVector (M N : ℕ)
    (w : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    (∑ n ∈ Icc 1 M, primeHorizonExtension (horizonCollarVector M w) n ^ 2) = 0 := by
  rw [primeHorizonExtension_horizonCollarVector]
  exact sum_eq_zero fun n hn => by
    simp only [atomicTailCoefficients, not_lt.mpr (mem_Icc.mp hn).2, if_false,
      zero_pow (by decide : 2 ≠ 0)]

/-- Cutting to the collar preserves its seventh-power mass. -/
theorem topCollarSeventhMass_horizonCollarVector (M N : ℕ)
    (w : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    topCollarSeventhMass M N (primeHorizonExtension (horizonCollarVector M w)) =
      topCollarSeventhMass M N (primeHorizonExtension w) := by
  rw [primeHorizonExtension_horizonCollarVector]
  unfold topCollarSeventhMass
  exact sum_congr rfl fun n hn => by
    simp only [atomicTailCoefficients, (mem_Ioc.mp hn).1, if_true]

/-- The nonpolar collar alone costs an arbitrarily small seventh-power reserve. -/
theorem eventually_nonpolar_collar_schur_payment
    {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R))
    {κ_S : ℝ} (hκS : 0 < κ_S) :
    ∀ᶠ N : ℕ in atTop, ∀ w : EuclideanSpace ℝ (PrimeHorizonIndex N),
      8 * (∑ m ∈ Icc 2 (lowPacketCutoff N),
        ⟪conductorResidualVector (c N) m N,
          horizonCollarVector (N / linearDefectCutoff (c N)) w⟫ ^ 2 /
          completedConductorEnergy tiltedUnitSpline (c N) m) ≤
        (κ_S * Real.log N / c N ^ 7) *
          topCollarSeventhMass (N / linearDefectCutoff (c N)) N (primeHorizonExtension w) := by
  filter_upwards [eventually_nonpolar_lowPacket_schur_payment hc hR hcrit zero_lt_one hκS]
    with N hN w
  have h := hN 0 (Submodule.zero_mem _) 0
    (horizonCollarVector (N / linearDefectCutoff (c N)) w)
  simpa only [zero_add, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero,
    prefix_mass_horizonCollarVector, topCollarSeventhMass_horizonCollarVector] using h

/-- The polar collar pairing costs a seventh-power reserve and one scalar polar square. -/
theorem eventually_polar_collar_pairing_payment
    {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R))
    {κ_S : ℝ} (hκS : 0 < κ_S) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      ∀ b : ℝ, ∀ w : EuclideanSpace ℝ (PrimeHorizonIndex N),
        2 * |b * ⟪conductorResidualVector (c N) 1 N,
          horizonCollarVector (N / linearDefectCutoff (c N)) w⟫| ≤
          (κ_S * Real.log N / c N ^ 7) *
            topCollarSeventhMass (N / linearDefectCutoff (c N)) N (primeHorizonExtension w) +
          (C * c N / Real.log N) * b ^ 2 := by
  obtain ⟨K, hK, hbound⟩ := eventually_normalized_collar_residual_bound hc hR hcrit
  refine ⟨2 * K * (R + 1) / κ_S, by positivity, ?_⟩
  filter_upwards [hbound,
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop 0,
    hcrit.eventually (gt_mem_nhds (by linarith : R < R + 1))]
    with N hb hL hratio b w
  let M := N / linearDefectCutoff (c N)
  let S := topCollarSeventhMass M N (primeHorizonExtension w)
  let D := topCollarDualSeventhMass M N (conductorResidualVector (c N) 1 N)
  let t := ⟪conductorResidualVector (c N) 1 N, horizonCollarVector M w⟫
  have hc0 : 0 < c N := zero_lt_one.trans_le (hc N)
  have hS : 0 ≤ S := topCollarSeventhMass_nonneg _ _ _
  have hD : D ≤ K * c N ^ 2 / Real.log N := by
    have h := hb (m := 1) Nat.zero_lt_one
    norm_num only [Nat.cast_one, one_pow, mul_one] at h
    calc
      D = ((Real.log N / c N ^ 2) * D) * (c N ^ 2 / Real.log N) := by field_simp
      _ ≤ K * (c N ^ 2 / Real.log N) := mul_le_mul_of_nonneg_right h (by positivity)
      _ = _ := by ring
  have ht : t ^ 2 ≤ (2 * K * c N ^ 2 / Real.log N) * S := by
    have h := inner_sq_le_prefix_add_topCollarSeventh (Nat.div_le_self N _)
      (conductorResidualVector (c N) 1 N) (horizonCollarVector M w)
    rw [prefix_mass_horizonCollarVector, topCollarSeventhMass_horizonCollarVector,
      mul_zero, zero_add] at h
    exact h.trans ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hD (by norm_num)) hS).trans_eq (by ring))
  have hpay := two_abs_le_of_sq_le
    (F := (2 * K * c N ^ 2 / Real.log N) * b ^ 2) (W := Real.sqrt S)
    (γ := κ_S * Real.log N / c N ^ 7) (by positivity) (by positivity)
    (by rw [Real.sq_sqrt hS, mul_pow]; nlinarith only [mul_le_mul_of_nonneg_left ht (sq_nonneg b)])
  rw [Real.sq_sqrt hS] at hpay
  have hcoef : (2 * K * c N ^ 2 / Real.log N) / (κ_S * Real.log N / c N ^ 7) ≤
      (2 * K * (R + 1) / κ_S) * c N / Real.log N := by
    have h := mul_le_mul_of_nonneg_left hratio.le
      (show 0 ≤ 2 * K * c N / (κ_S * Real.log N) by positivity)
    convert h using 1 <;> field_simp <;> ring
  have hlast := mul_le_mul_of_nonneg_right hcoef (sq_nonneg b)
  dsimp only [S, t] at hpay
  linarith only [hpay, hlast]

/-- A packet paired with its orthogonal complement sees only conductor residuals. -/
theorem conductor_packet_cross_eq_residual_sum {Q N : ℕ} (c : ℝ) (b : ℕ → ℝ)
    {z : EuclideanSpace ℝ (PrimeHorizonIndex N)} (hz : z ∈ (conductorSubspace Q N)ᗮ) :
    ⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
      (∑ m ∈ Icc 1 Q, b m • normalizedRamanujanHorizonVector m N), z⟫ =
      ∑ m ∈ Icc 1 Q, b m * ⟪conductorResidualVector c m N, z⟫ := by
  rw [map_sum, sum_inner]
  apply sum_congr rfl
  intro m hm
  have hzero := Submodule.inner_right_of_mem_orthogonal
    (mem_conductorSubspace_normalizedRamanujanHorizonVector hm) hz
  rw [map_smul, real_inner_smul_left, conductorResidualVector, inner_sub_left,
    real_inner_smul_left, hzero, mul_zero, sub_zero]

/-- Only one scalar polar square remains after Schur payment of the full low packet. -/
theorem eventually_lowPacket_cross_payment
    {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R))
    {κ_P κ_S : ℝ} (hκP : 0 < κ_P) (hκS : 0 < κ_S) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop, ∀ b : ℕ → ℝ,
      ∀ u₀ ∈ conductorSubspace ⌊Real.exp (Real.log (N : ℝ) ^ (1 / 2 : ℝ))⌋₊ N,
      ∀ u₁ w : EuclideanSpace ℝ (PrimeHorizonIndex N),
      u₀ + u₁ + w ∈ (conductorSubspace (lowPacketCutoff N) N)ᗮ →
      2 * |⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline (c N) N)
        (∑ m ∈ Icc 1 (lowPacketCutoff N), b m • normalizedRamanujanHorizonVector m N),
          u₀ + u₁ + w⟫| ≤
        (1 / 4 : ℝ) * (∑ m ∈ Icc 1 (lowPacketCutoff N),
          completedConductorEnergy tiltedUnitSpline (c N) m * b m ^ 2) +
        ‖u₀‖ ^ 2 + (Real.log (N : ℝ) ^ (1 / 2 : ℝ) / 32) * ‖u₁‖ ^ 2 +
        (κ_P * Real.log N / (1 + Real.log (Real.log N)) ^ 5) *
          (∑ n ∈ Icc 1 (N / linearDefectCutoff (c N)), primeHorizonExtension w n ^ 2) +
        (κ_S * Real.log N / c N ^ 7) *
          topCollarSeventhMass (N / linearDefectCutoff (c N)) N (primeHorizonExtension w) +
        (C * c N / Real.log N) * b 1 ^ 2 := by
  obtain ⟨C, hC, hpole⟩ := eventually_polar_collar_pairing_payment hc hR hcrit
    (half_pos hκS)
  refine ⟨C, hC, ?_⟩
  have hQlim := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 13 / 32)).comp
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [eventually_lowPacket_noncollar_schur_payment hc hR hcrit hκP,
    eventually_nonpolar_collar_schur_payment hc hR hcrit (half_pos hκS), hpole,
    hQlim.eventually_ge_atTop 1]
    with N hprefix hnonpolar hpoleN hQge b u₀ hu₀ u₁ w horth
  let Q := lowPacketCutoff N
  let M := N / linearDefectCutoff (c N)
  let E := fun m => completedConductorEnergy tiltedUnitSpline (c N) m
  let r := fun m => conductorResidualVector (c N) m N
  let T₀ := ∑ m ∈ Icc 1 Q, b m * ⟪r m, u₀ + u₁ + horizonPrefixVector M w⟫
  let T₂ := ∑ m ∈ Icc 2 Q, b m * ⟪r m, horizonCollarVector M w⟫
  let T₁ := b 1 * ⟪r 1, horizonCollarVector M w⟫
  have hQ1 : 1 ≤ Q := Nat.le_floor (by exact_mod_cast hQge)
  have hE : ∀ m ∈ Icc 1 Q, 0 < E m := fun m hm =>
    completedConductorEnergy_tilted_pos (zero_lt_one.trans_le (hc N)) (mem_Icc.mp hm).1
  have hsplit : Icc 1 Q = insert 1 (Icc 2 Q) := by
    ext m; simp only [mem_Icc, mem_insert]; omega
  have hsum : (∑ m ∈ Icc 1 Q, b m * ⟪r m, u₀ + u₁ + w⟫) = T₀ + (T₁ + T₂) := by
    have hw : u₀ + u₁ + w =
        (u₀ + u₁ + horizonPrefixVector M w) + horizonCollarVector M w := by
      rw [add_assoc, horizonPrefixVector_add_collar]
    simp_rw [hw, inner_add_right, mul_add]
    rw [sum_add_distrib]
    congr 1
    rw [hsplit, sum_insert (by simp)]
  have hpre := two_abs_weighted_sum_le (a := b)
    (t := fun m => ⟪r m, u₀ + u₁ + horizonPrefixVector M w⟫) hE
  have hnon := two_abs_weighted_sum_le (a := b)
    (t := fun m => ⟪r m, horizonCollarVector M w⟫)
    (s := Icc 2 Q) (fun m hm => hE m (mem_Icc.mpr ⟨by have := (mem_Icc.mp hm).1; omega,
      (mem_Icc.mp hm).2⟩))
  have hsumE : (∑ m ∈ Icc 2 Q, E m * b m ^ 2) ≤ ∑ m ∈ Icc 1 Q, E m * b m ^ 2 :=
    sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc (by norm_num) le_rfl)
      (fun m hm _ => mul_nonneg (hE m hm).le (sq_nonneg _))
  have hp := hprefix M (Nat.div_le_self N _) u₀ hu₀ u₁ w
  have hn := hnonpolar w
  have h₁ := hpoleN (b 1) w
  have hab := abs_add_le T₀ (T₁ + T₂)
  have hab' := abs_add_le T₁ T₂
  rw [conductor_packet_cross_eq_residual_sum (c N) b horth, hsum]
  dsimp only [T₀, T₁, T₂, E, r, Q, M] at hab hab' hpre hnon hsumE
  linarith only [hpre, hnon, hsumE, hp, hn, h₁, hab, hab']

/-- Orthogonality to conductor one makes its coordinate a quadratic Gram error. -/
theorem polar_coefficient_sq_le_of_primitive {Q N : ℕ}
    (hQ : 2 ≤ Q) (hQN : Q * Q ≤ N)
    (hlog : 18 * (1 + Real.log Q) ≤ Real.log N) (b : ℕ → ℝ)
    (hprim : (∑ m ∈ Icc 1 Q, b m • normalizedRamanujanHorizonVector m N) ∈
      (conductorSubspace 1 N)ᗮ) :
    b 1 ^ 2 ≤ 1944 * ((1 + Real.log Q) / Real.log N) ^ 2 *
      ∑ m ∈ Icc 1 Q, b m ^ 2 := by
  have hlow := (low_band_norm_le_of_mem_orthogonal (Q := 1)
    le_rfl (by omega) hQ hQN hlog hprim).1
  simp only [Icc_self, sum_singleton, Real.sqrt_sq_eq_abs] at hlow
  have hs := pow_le_pow_left₀ (abs_nonneg _) hlow 2
  rw [sq_abs, mul_pow] at hs
  have hframe := (half_and_three_halves_riesz_of_log_le hQ hQN hlog b).2
  have hh := mul_le_mul_of_nonneg_left hframe
    (sq_nonneg (36 * (1 + Real.log Q) / Real.log N))
  exact hs.trans (hh.trans_eq (by ring))

/-- A polar coefficient on the primitive hyperplane costs an arbitrarily small completed diagonal. -/
theorem eventually_primitive_polar_penalty_le
    {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R))
    {K ε : ℝ} (hK : 0 < K) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ b : ℕ → ℝ,
      (∑ m ∈ Icc 1 (lowPacketCutoff N), b m • normalizedRamanujanHorizonVector m N) ∈
        (conductorSubspace 1 N)ᗮ →
      (K * c N / Real.log N) * b 1 ^ 2 ≤
        ε * ∑ m ∈ Icc 1 (lowPacketCutoff N),
          completedConductorEnergy tiltedUnitSpline (c N) m * b m ^ 2 := by
  let κ := tiltedSplineSpectralFloorConstant
  have hκ : 0 < κ := tiltedSplineSpectralFloorConstant_pos
  have hLlim := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_three_cutoff_bounds_one_ninth
      (by norm_num : (0 : ℝ) < 13 / 32) (by norm_num : (13 / 32 : ℝ) ≤ 1 / 2)
      (by norm_num : (0 : ℝ) < 1 / 4096) (le_refl (1 / 4096 : ℝ)),
    hcrit.eventually (gt_mem_nhds (by linarith : R < R + 1)),
    hLlim.eventually_ge_atTop 1, eventually_ge_atTop 1,
    (criticalCurve_pow_log_div_natCast hc hR hcrit 0 2).eventually (gt_mem_nhds zero_lt_one),
    hLlim.eventually (RHTower.eventually_const_mul_polylog_le_rpow 2
      (by norm_num : (0 : ℝ) < 1) (3888 * K * (R + 1) / (κ * ε)))]
    with N hcut hratio hL1 hN1 hLsq hsmall b hprim
  let L := Real.log (N : ℝ)
  let Q := lowPacketCutoff N
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have hc0 : 0 < c N := zero_lt_one.trans_le (hc N)
  obtain ⟨hQ2, hQR, _, hQup, _, _, _, _, h36, _, _, _⟩ := hcut
  change 2 ≤ Q at hQ2
  have hQL : (Q : ℝ) ≤ L := hQup.trans
    ((Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num : (13 / 32 : ℝ) ≤ 1)).trans_eq
      (Real.rpow_one L))
  have hQN : Q * Q ≤ N := by
    have hn0 : (0 : ℝ) < N := by exact_mod_cast hN1
    simp only [pow_zero, one_mul] at hLsq
    have hs : (Q : ℝ) ^ 2 ≤ (N : ℝ) :=
      (pow_le_pow_left₀ (Nat.cast_nonneg Q) hQL 2).trans ((div_lt_one hn0).mp hLsq).le
    exact_mod_cast hs
  have hlog : 18 * (1 + Real.log Q) ≤ L := by
    have hqlog := Real.log_le_log
      (by exact_mod_cast (show 0 < Q by omega)) (show (Q : ℝ) ≤ _ by exact_mod_cast hQR)
    linarith only [h36, hqlog, Real.log_natCast_nonneg Q]
  have hb := polar_coefficient_sq_le_of_primitive hQ2 hQN hlog b hprim
  have hlogQ : 1 + Real.log (Q : ℝ) ≤ 1 + Real.log L :=
    add_le_add_left (Real.log_le_log (by exact_mod_cast (show 0 < Q by omega)) hQL) 1
  have hlogQ0 : 0 ≤ 1 + Real.log (Q : ℝ) := by linarith only [Real.log_natCast_nonneg Q]
  have hE : (κ / (2 * c N ^ 7)) * (∑ m ∈ Icc 1 Q, b m ^ 2) ≤
      ∑ m ∈ Icc 1 Q, completedConductorEnergy tiltedUnitSpline (c N) m * b m ^ 2 := by
    rw [mul_sum]
    apply sum_le_sum
    intro m hm
    have he := spectralFloor_conductor_energy_ge (hc N) (mem_Icc.mp hm).1
    have hf : 0 ≤ κ / (2 * c N ^ 7) := by positivity
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    change κ / (2 * c N ^ 7) ≤ _ at he
    linarith only [he, hf]
  have hcoef : K * c N / L * (1944 * ((1 + Real.log Q) / L) ^ 2) ≤
      ε * (κ / (2 * c N ^ 7)) := by
    have hc8 : c N ^ 8 ≤ (R + 1) * L := (div_le_iff₀ hL0).mp hratio.le
    have hlogs := pow_le_pow_left₀ hlogQ0 hlogQ 2
    have hsmall' : 3888 * K * (R + 1) * (1 + Real.log L) ^ 2 ≤ κ * ε * L := by
      have hh : (3888 * K * (R + 1) / (κ * ε)) * (1 + Real.log L) ^ 2 ≤ L := by
        simpa only [Function.comp_def, Real.rpow_one] using hsmall
      have hm := mul_le_mul_of_nonneg_right hh (show 0 ≤ κ * ε by positivity)
      convert hm using 1 <;> field_simp <;> ring
    have hprod := mul_le_mul_of_nonneg_left hc8
      (show 0 ≤ 3888 * K * (1 + Real.log L) ^ 2 by positivity)
    have hsmallL := mul_le_mul_of_nonneg_right hsmall' hL0.le
    have hL2 : L ^ 2 ≤ L ^ 3 := by nlinarith only [sq_nonneg L, mul_nonneg (sq_nonneg L) (sub_nonneg.mpr hL1)]
    have hend := mul_le_mul_of_nonneg_left hL2 (show 0 ≤ κ * ε by positivity)
    have hlogterm := mul_le_mul_of_nonneg_left hlogs (show 0 ≤ 3888 * K * c N ^ 8 by positivity)
    apply (div_le_iff₀ (show 0 < 2 * c N ^ 7 by positivity)).mpr
    field_simp
    nlinarith only [hprod, hsmallL, hend, hlogterm]
  have hb' := mul_le_mul_of_nonneg_left hb (show 0 ≤ K * c N / L by positivity)
  have hc' := mul_le_mul_of_nonneg_right hcoef
    (show 0 ≤ ∑ m ∈ Icc 1 Q, b m ^ 2 from sum_nonneg fun _ _ => sq_nonneg _)
  have he' := mul_le_mul_of_nonneg_left hE hε.le
  dsimp only [Q, L] at hb' hc' he'
  nlinarith only [hb', hc', he']

#print axioms eventually_nonpolar_lowPacket_schur_payment
#print axioms eventually_lowPacket_noncollar_schur_payment

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
