import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheCriticalBandFarCrossIsPaid
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheFirstTwoBandsRetainCriticalCoercivity

/-!
# The critical complement retains weighted reserves

The three-band decomposition pays every cross while retaining independent
first-band, second-band, prefix, and seventh-power collar reserves.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Finset Filter Topology
open scoped Classical BigOperators RealInnerProductSpace Matrix
namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open CompletedArithmeticForms RenormalizedArithmeticPotentialTheory
  RenormalizedArithmeticPotentialTheory.CompletedShell SpacingScaleHarmonicAnalysis
  ArithmeticElectrostatics CriticalScaleArithmeticRigidity

/-- Three-band assembly preserves the weighted collar instead of replacing it
by the full norm. The prefix pays the norm cost when `b / c^7 ≤ 1`. -/
theorem critical_weighted_complement_assembly
    {Q₁ R₀ R₁ N : ℕ} {c b k₁ Lh K₀ K₁ C_coerc0 C_band1 : ℝ}
    (hQ2 : 2 ≤ Q₁) (hQR₀ : Q₁ ≤ R₀)
    (hc1 : 1 ≤ c) (hb : 0 < b) (hb_c7 : b / c ^ 7 ≤ 1) (hk₁_pos : 0 < k₁)
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
      (k₁ / 4) * (∑ n ∈ Icc 1 (N / linearDefectCutoff c), primeHorizonExtension w n ^ 2) +
        (b * k₁ / (2 * c ^ 7)) *
          topCollarSeventhMass (N / linearDefectCutoff c) N (primeHorizonExtension w) ≤
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
    (hfl0 : K₀ + 1 / 2 ≤ (3 / 4 : ℝ) * Real.log (Q₁ : ℝ) - Real.log c - C_coerc0)
    (hfl1 : K₁ + (1 / 16 : ℝ) * Lh + 1 / 4 ≤
      (1 / 4 : ℝ) * Real.log (R₀ : ℝ) - C_band1 * c ^ 2 * (1 + Real.log c))
    {u₀ u₁ w : EuclideanSpace ℝ (PrimeHorizonIndex N)}
    (hu₀_mem : u₀ ∈ conductorSubspace R₀ N) (hu₀_orthQ : u₀ ∈ (conductorSubspace Q₁ N)ᗮ)
    (hu₁_mem : u₁ ∈ conductorSubspace R₁ N) (hu₁_orthR₀ : u₁ ∈ (conductorSubspace R₀ N)ᗮ)
    (hw_orthR₁ : w ∈ (conductorSubspace R₁ N)ᗮ) :
    K₀ * ‖u₀‖ ^ 2 + K₁ * ‖u₁‖ ^ 2 +
      (k₁ / 8) * (∑ n ∈ Icc 1 (N / linearDefectCutoff c), primeHorizonExtension w n ^ 2) +
      (3 * b * k₁ / (8 * c ^ 7)) *
        topCollarSeventhMass (N / linearDefectCutoff c) N (primeHorizonExtension w) ≤
      completeWeilEnergy tiltedUnitSpline c N (u₀ + u₁ + w) := by
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hR₀2 : 2 ≤ R₀ := hQ2.trans hQR₀
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
  have hPw0 : 0 ≤ ∑ n ∈ Icc 1 (N / linearDefectCutoff c), primeHorizonExtension w n ^ 2 :=
    sum_nonneg fun _ _ => sq_nonneg _
  have hSw0 : 0 ≤ ∑ n ∈ Ioc (N / linearDefectCutoff c) N, primeHorizonExtension w n ^ 2 :=
    sum_nonneg fun _ _ => sq_nonneg _
  have hw_split : ‖w‖ ^ 2 =
      (∑ n ∈ Icc 1 (N / linearDefectCutoff c), primeHorizonExtension w n ^ 2) +
        (∑ n ∈ Ioc (N / linearDefectCutoff c) N, primeHorizonExtension w n ^ 2) := by
    rw [← sum_primeHorizonExtension_sq w,
      Ioc_eq_Icc_sdiff_Icc_telescoped (N / linearDefectCutoff c) N, add_comm]
    exact (sum_sdiff (Icc_subset_Icc le_rfl (Nat.div_le_self N _))).symm
  have hS7 := sum_sq_Ioc_le_topCollarSeventhMass
    (N / linearDefectCutoff c) N (primeHorizonExtension w)
  generalize (∑ n ∈ Icc 1 (N / linearDefectCutoff c), primeHorizonExtension w n ^ 2) = P_w at hdiag2 hcr0w hcr1w hPw0 hw_split ⊢
  generalize (∑ n ∈ Ioc (N / linearDefectCutoff c) N, primeHorizonExtension w n ^ 2) = S_w at hcr0w hcr1w hSw0 hw_split hS7
  generalize topCollarSeventhMass (N / linearDefectCutoff c) N
    (primeHorizonExtension w) = S7_w at hdiag2 hS7 ⊢
  have hfloor0 : K₀ * ‖u₀‖ ^ 2 + (1 / 2 : ℝ) * ‖u₀‖ ^ 2 ≤
      ((3 / 4 : ℝ) * Real.log (Q₁ : ℝ) - Real.log c - C_coerc0) * ‖u₀‖ ^ 2 := by
    rw [show K₀ * ‖u₀‖ ^ 2 + (1 / 2 : ℝ) * ‖u₀‖ ^ 2 = (K₀ + 1 / 2) * ‖u₀‖ ^ 2 by ring]
    exact mul_le_mul_of_nonneg_right hfl0 (sq_nonneg ‖u₀‖)
  have hfloor1 : K₁ * ‖u₁‖ ^ 2 + (1 / 16 : ℝ) * Lh * ‖u₁‖ ^ 2 + (1 / 4 : ℝ) * ‖u₁‖ ^ 2 ≤
      ((1 / 4 : ℝ) * Real.log (R₀ : ℝ) - C_band1 * c ^ 2 * (1 + Real.log c)) * ‖u₁‖ ^ 2 := by
    rw [show K₁ * ‖u₁‖ ^ 2 + (1 / 16 : ℝ) * Lh * ‖u₁‖ ^ 2 + (1 / 4 : ℝ) * ‖u₁‖ ^ 2 =
      (K₁ + (1 / 16 : ℝ) * Lh + 1 / 4) * ‖u₁‖ ^ 2 by ring]
    exact mul_le_mul_of_nonneg_right hfl1 (sq_nonneg ‖u₁‖)
  have hfloor2 : (k₁ / 8) * P_w + (3 * b * k₁ / (8 * c ^ 7)) * S7_w ≤
      (k₁ / 4) * P_w + (b * k₁ / (2 * c ^ 7)) * S7_w -
        2 * ((k₁ / 32) * P_w + (b * k₁ / (32 * c ^ 7)) * S_w +
          (b * k₁ / (32 * c ^ 7)) * ‖w‖ ^ 2) := by
    rw [hw_split]
    have hP := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hb_c7 hk₁_pos.le) hPw0
    have hS := mul_le_mul_of_nonneg_left hS7
      (show 0 ≤ b * k₁ / c ^ 7 by positivity)
    have e₁ : b / c ^ 7 * k₁ = b * k₁ / c ^ 7 := by ring
    rw [e₁, one_mul] at hP
    nlinarith only [hP, hS]
  have h3add := completeWeilEnergy_three_add_ge tiltedUnitSpline c u₀ u₁ w
  have hE₀_0 : 0 ≤ primeAdjunctionMass R₀ a₀ := primeAdjunctionMass_nonneg R₀ a₀
  have hE₁_0 : 0 ≤ primeAdjunctionMass R₁ a₁ := primeAdjunctionMass_nonneg R₁ a₁
  linarith only [h3add, hdiag0, hdiag1, hdiag2, hcr01, hcr0w, hcr1w,
    hfloor0, hfloor1, hfloor2, hE₀_0, hE₁_0]


/-- A small critical multiple keeps positive reserves on both bands, the far
prefix, and the weighted collar. The lower overlap restriction is subcritical. -/
theorem exists_critical_multiple_weighted_complement :
    ∃ K : ℝ, 0 < K ∧ 2 * K ≤ 1 ∧
      ∀ᶠ N : ℕ in atTop, ∀ c : ℝ,
        Real.log (N : ℝ) ^ (1 / 16 : ℝ) ≤ c →
        c ≤ 2 * K * Real.log (N : ℝ) ^ (1 / 8 : ℝ) →
        let L := Real.log (N : ℝ)
        let Q := ⌊L ^ (13 / 32 : ℝ)⌋₊
        let R₀ := ⌊Real.exp (L ^ (1 / 2 : ℝ))⌋₊
        let θ := 1 / (1 + Real.log L) ^ 5
        let R₁ := ⌊(N : ℝ) ^ θ⌋₊
        ∀ u₀ ∈ conductorSubspace R₀ N, u₀ ∈ (conductorSubspace Q N)ᗮ →
        ∀ u₁ ∈ conductorSubspace R₁ N, u₁ ∈ (conductorSubspace R₀ N)ᗮ →
        ∀ w ∈ (conductorSubspace R₁ N)ᗮ,
          4 * ‖u₀‖ ^ 2 + (3 + L ^ (1 / 2 : ℝ) / 32) * ‖u₁‖ ^ 2 +
          (θ * L / (16 * explicitConductorCutoffConstant)) *
            (∑ n ∈ Icc 1 (N / linearDefectCutoff c), primeHorizonExtension w n ^ 2) +
          (3 * dyadicTopMassConstant * L / (64 * c ^ 7)) *
            topCollarSeventhMass (N / linearDefectCutoff c) N (primeHorizonExtension w) ≤
          completeWeilEnergy tiltedUnitSpline c N (u₀ + u₁ + w) := by
  obtain ⟨K, hK, h2K, hfar⟩ := exists_critical_multiple_weighted_far_complement
  obtain ⟨Ccross, hCcross, hcross01⟩ := exists_band0_band1_cross_le
  obtain ⟨Ccoerc, Csmall, hCcoerc, hCsmall, hband0⟩ :=
    exists_completeWeilEnergy_ge_three_quarters_log_homogeneous
  obtain ⟨Cband, hCband, hband1⟩ := exists_band1_coercive_homogeneous
  let D := explicitConductorCutoffConstant
  let g := dyadicTopMassConstant
  let B := g * D / 4
  have hD : 0 < D := explicitConductorCutoffConstant_pos
  have hg : 0 < g := dyadicTopMassConstant_pos
  have hB : 0 < B := by dsimp only [B]; positivity
  refine ⟨K, hK, h2K, ?_⟩
  have hLlim : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hllim : Tendsto (fun N : ℕ => Real.log (Real.log (N : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp hLlim
  filter_upwards [hfar, eventually_critical_band_far_cross hB,
    eventually_three_cutoff_bounds_one_ninth
      (by norm_num : (0 : ℝ) < 13 / 32) (by norm_num : (13 / 32 : ℝ) ≤ 1 / 2)
      (by norm_num : (0 : ℝ) < 1 / 4096) (le_refl (1 / 4096 : ℝ)),
    eventually_log_nat_le_rpow_36_one_ninth,
    hLlim.eventually_ge_atTop 3000,
    hllim.eventually_ge_atTop (4096 + (1 + 4 + Ccoerc + 3 / 4) / (23 / 128)),
    hLlim.eventually (RHTower.eventually_const_mul_polylog_le_rpow 1
      (by norm_num : (0 : ℝ) < 1 / 128) 1),
    hLlim.eventually (RHTower.eventually_const_mul_polylog_le_rpow 5
      (by norm_num : (0 : ℝ) < 1 / 2) 1),
    hLlim.eventually (RHTower.eventually_const_mul_polylog_le_rpow 5
      (by norm_num : (0 : ℝ) < 7 / 16) B),
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 128)).comp hLlim).eventually_ge_atTop
      (18 * Csmall + 4 * Ccross + 32 * Cband)]
    with N hfarN hcrossN hcut hLX hL3000 hll hpoly hhalf hBpoly hlarge
  intro c hclo hc
  dsimp only
  intro u₀ hu₀ hu₀Q u₁ hu₁ hu₁R w hw
  let L := Real.log (N : ℝ)
  let t := 1 + Real.log L
  let θ := 1 / t ^ 5
  let R₀ := ⌊Real.exp (L ^ (1 / 2 : ℝ))⌋₊
  let R₁ := ⌊(N : ℝ) ^ θ⌋₊
  let Q := ⌊L ^ (13 / 32 : ℝ)⌋₊
  let b := B * t ^ 5
  let k := θ * L / (2 * D)
  change 4096 + (1 + 4 + Ccoerc + 3 / 4) / (23 / 128) ≤ Real.log L at hll
  change 18 * Csmall + 4 * Ccross + 32 * Cband ≤ L ^ (1 / 128 : ℝ) at hlarge
  have hL1 : 1 ≤ L := by linarith only [hL3000]
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have ht1 : 1 ≤ t := by dsimp only [t]; linarith only [Real.log_nonneg hL1]
  have ht0 : 0 < t := zero_lt_one.trans_le ht1
  have hθ : 0 < θ := by dsimp only [θ]; positivity
  have hb : 0 < b := by dsimp only [b]; positivity
  have hk : 0 < k := by dsimp only [k]; positivity
  have hc1 : 1 ≤ c := (Real.one_le_rpow hL1 (by norm_num)).trans hclo
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hcroot : c ≤ L ^ (1 / 8 : ℝ) := hc.trans (by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right h2K
      (Real.rpow_nonneg hL0.le (1 / 8 : ℝ)))
  have hcL : c ≤ L := hcroot.trans ((Real.rpow_le_rpow_of_exponent_le hL1
    (by norm_num : (1 / 8 : ℝ) ≤ 1)).trans_eq (Real.rpow_one L))
  have hθhi : θ ≤ 1 / 4096 := by
    apply one_div_le_one_div_of_le (by norm_num)
    have hpow : t ≤ t ^ 5 := by
      simpa only [pow_one] using pow_le_pow_right₀ ht1 (by norm_num : 1 ≤ 5)
    have hCpos : 0 ≤ (1 + 4 + Ccoerc + 3 / 4) / (23 / 128) := by positivity
    dsimp only [t, L] at hpow
    linarith only [hpow, hll, hCpos]
  obtain ⟨hQ2, hQR₀, -, -, hsqrtQ, hlogQ, hH₀, hlogR₀, h36₀, -, -, -⟩ := hcut
  change 2 ≤ Q at hQ2
  have hR₀2 : 2 ≤ R₀ := hQ2.trans hQR₀
  have hN1 : 1 ≤ N := by
    by_contra hn
    have : N = 0 := by omega
    subst this
    simp [L] at hL0
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hhalf' : t ^ 5 ≤ L ^ (1 / 2 : ℝ) := by simpa only [one_mul] using hhalf
  have hLhalf : L ^ (1 / 2 : ℝ) ≤ θ * L := by
    have h := mul_le_mul_of_nonneg_right hhalf' (Real.rpow_nonneg hL0.le (1 / 2 : ℝ))
    have he : L ^ (1 / 2 : ℝ) * L ^ (1 / 2 : ℝ) = L := by
      rw [← Real.rpow_add hL0]; norm_num
    rw [he] at h
    have h' := (le_div_iff₀ (show 0 < t ^ 5 by positivity)).mpr (by linarith only [h] :
      L ^ (1 / 2 : ℝ) * t ^ 5 ≤ L)
    change L ^ (1 / 2 : ℝ) ≤ 1 / t ^ 5 * L
    linarith only [h']
  have hR₀R₁ : R₀ ≤ R₁ := by
    apply Nat.floor_mono
    rw [Real.rpow_def_of_pos hN0]
    exact Real.exp_le_exp.mpr (by linarith only [hLhalf])
  have hR₁2 : 2 ≤ R₁ := hR₀2.trans hR₀R₁
  have hlogR₁ : Real.log (R₁ : ℝ) ≤ θ * L := by
    have h := Real.log_le_log (by exact_mod_cast (show 0 < R₁ by omega))
      (show (R₁ : ℝ) ≤ (N : ℝ) ^ θ from Nat.floor_le (by positivity))
    rwa [Real.log_rpow hN0] at h
  have h1080 : 1080 * (1 + Real.log (R₁ : ℝ)) ≤ L := by
    have h := mul_le_mul_of_nonneg_right hθhi hL0.le
    linarith only [hlogR₁, h, hL3000]
  have h36₁ : 36 * (1 + Real.log (R₁ : ℝ)) ≤ L := by
    linarith only [h1080, Real.log_natCast_nonneg R₁]
  obtain ⟨-, -, hw1, hrad, hR₀6, hnear₀, hup₀, htail₀, hc5, hc3R4, hc3R2, -⟩ :=
    rpow_horizon_N_bounds_one_ninth hN1 hR₀2 hc1 (by linarith only [hL3000]) hLX hcL h36₀
  obtain ⟨-, -, -, -, hR₁6, hnear₁, -, htail₁, -, -, -, -⟩ :=
    rpow_horizon_N_bounds_one_ninth hN1 hR₁2 hc1 (by linarith only [hL3000]) hLX hcL h36₁
  have hVc : 1 + Real.log c ≤ L ^ (1 / 128 : ℝ) := by
    have h := Real.log_le_log hc0 hcL
    have hp : 1 + Real.log L ≤ L ^ (1 / 128 : ℝ) := by
      simpa only [one_mul, pow_one] using hpoly
    linarith only [h, hp]
  obtain ⟨hsmall₀, hsmall01, hfloor₀, hfloor₁⟩ := critical_first_band_scalar_smallness
    (κ₀ := 1) hc1 hcroot hL1 rfl (by norm_num) hCsmall hCcross hVc hsqrtQ hlogQ hH₀ hlogR₀
    htail₀ hc5 hc3R4 hc3R2
    (by linarith only [hlarge, hCcross, hCband])
    (by linarith only [hlarge, hCsmall, hCband])
    (by linarith only [hlarge, hCsmall, hCcross])
    (by have h := hll; linarith only [h])
    (by norm_num; linarith only [hL3000])
  have hbc7 : b / c ^ 7 ≤ 1 := by
    rw [div_le_one (pow_pos hc0 7)]
    have hpow := pow_le_pow_left₀ (Real.rpow_nonneg hL0.le (1 / 16 : ℝ)) hclo 7
    rw [← Real.rpow_natCast (L ^ (1 / 16 : ℝ)), ← Real.rpow_mul hL0.le] at hpow
    norm_num at hpow
    exact hBpoly.trans hpow
  have hfarShape : ∀ {v : EuclideanSpace ℝ (PrimeHorizonIndex N)},
      v ∈ (conductorSubspace R₁ N)ᗮ →
      (k / 4) * (∑ n ∈ Icc 1 (N / linearDefectCutoff c), primeHorizonExtension v n ^ 2) +
      (b * k / (2 * c ^ 7)) * topCollarSeventhMass (N / linearDefectCutoff c) N
        (primeHorizonExtension v) ≤ completeWeilEnergy tiltedUnitSpline c N v := by
    intro v hv
    have h := hfarN c θ hc1 hc le_rfl hθhi v hv
    convert h using 1 <;> dsimp only [b, k, θ, B, D, g] <;> field_simp <;> ring
  have hcrossShape {R : ℕ} (hR2 : 2 ≤ R) (hRR₁ : R ≤ R₁) (a : ℕ → ℝ)
      (ha : (∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N) ∈
        (conductorSubspace 1 N)ᗮ) {v : EuclideanSpace ℝ (PrimeHorizonIndex N)}
      (hv : v ∈ (conductorSubspace R₁ N)ᗮ) :
      2 * |⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
        (∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N), v⟫| ≤
        (1 / 32 : ℝ) * primeAdjunctionMass R a +
        (1 / 4 : ℝ) * ‖∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 +
        (k / 32) * (∑ n ∈ Icc 1 (N / linearDefectCutoff c), primeHorizonExtension v n ^ 2) +
        (b * k / (32 * c ^ 7)) * (∑ n ∈ Ioc (N / linearDefectCutoff c) N, primeHorizonExtension v n ^ 2) +
        (b * k / (32 * c ^ 7)) * ‖v‖ ^ 2 := by
    have h := hcrossN c hc1 hcroot R hR2 hRR₁ a ha v hv
    refine h.trans_eq ?_
    dsimp only [b, k, θ, D]
    field_simp <;> ring
  have h := critical_weighted_complement_assembly hQ2 hQR₀ hc1 hb hbc7 hk
    (hband0 hQ2 hQR₀ hR₀6 h36₀ hc1 hcL hw1 hrad hnear₀ hsmall₀)
    (hband1 hR₀2 hR₀R₁ hR₁6 h1080 hc1 hcL hw1 hnear₁
      (htail₁.trans ((div_le_one hL0).mpr hL1)))
    hfarShape
    (hcross01 hR₀2 hR₀6 (by linarith only [h36₀, Real.log_natCast_nonneg R₀])
      hc1 hw1 hnear₀ hup₀ hH₀ hsmall01)
    (hcrossShape hR₀2 hR₀R₁) (hcrossShape hR₁2 le_rfl)
    hfloor₀ hfloor₁ hu₀ hu₀Q hu₁ hu₁R hw
  convert h using 1 <;> dsimp only [b, k, θ, B, D, g] <;> field_simp <;> ring

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_critical_multiple_weighted_complement
