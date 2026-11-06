import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheFarComplementHasAnExplicitRatioInterval
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheCriticalComplementRetainsWeightedReserves

/-!
# The critical complement on the certified ratio interval

On `0 < R ≤ min(1, (5/6) R₀)`, with `R₀ = farRatioRoot`, the far band keeps a sixteenth of its aliasing
reserve: `(5/16) D / R ≥ C + C′R`. So the first two conductor bands and the far band stay coercive at
every overlap with `c⁸ ≤ R log N` and `c ≥ (log N)^{1/16}`, on the whole complement of the low packet
`m ≤ (log N)^{13/32}` (`eventually_critical_complement_below_root`). Below `(log N)^{1/16}` the
subcritical theorem covers the whole space. Only the low packet and its Schur pairing fix a smaller multiple.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Finset Filter Topology
open scoped Classical BigOperators RealInnerProductSpace Matrix
namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory.ExplicitShell
open SpacingScaleHarmonicAnalysis ArithmeticLorentzianGeometry
  RenormalizedArithmeticPotentialTheory CompletedArithmeticForms
  CriticalScaleArithmeticRigidity ArithmeticElectrostatics ArithmeticEffectivityTheory
  BezoutValuationIncidence RenormalizedArithmeticPotentialTheory.CompletedShell

/-- Below `(5/6) R₀`, a sixteenth of the aliasing reserve survives the linear losses. -/
theorem farLinear_le_of_le_root {R : ℝ} (hR : 0 < R) (hRr : R ≤ 5 / 6 * farRatioRoot) :
    farLinearConstant + farRatioConstant * R ≤ 5 * dyadicTopMassConstant / (16 * R) := by
  obtain ⟨hr, hroot⟩ := farRatioRoot_spec
  have hC := farRatioConstant_pos
  have hg := dyadicTopMassConstant_pos
  have hrR : R ≤ farRatioRoot := by linarith only [hRr, hr]
  have h1 : farRatioConstant * R ≤ farRatioConstant * farRatioRoot :=
    mul_le_mul_of_nonneg_left hrR hC.le
  have h2 : farLinearConstant + farRatioConstant * farRatioRoot =
      3 * dyadicTopMassConstant / (8 * farRatioRoot) := by
    field_simp
    linear_combination 8 * hroot
  have h3 : 3 * dyadicTopMassConstant / (8 * farRatioRoot) ≤
      5 * dyadicTopMassConstant / (16 * R) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith only [mul_le_mul_of_nonneg_left hRr hg.le, hg, hr]
  linarith only [h1, h2, h3]

/-- The far band keeps the same weighted reserves as at a small critical multiple. -/
theorem eventually_far_complement_shape {R : ℝ} (hR : 0 < R) (hRr : R ≤ 5 / 6 * farRatioRoot) :
    ∀ᶠ N : ℕ in atTop, ∀ c θ : ℝ, 1 ≤ c → c ^ 8 ≤ R * Real.log N →
      1 / (1 + Real.log (Real.log (N : ℝ))) ^ 5 ≤ θ → θ ≤ 1 / 4096 →
      ∀ z ∈ (conductorSubspace ⌊(N : ℝ) ^ θ⌋₊ N)ᗮ,
        (θ * Real.log N / (8 * explicitConductorCutoffConstant)) *
            (∑ n ∈ Icc 1 (N / linearDefectCutoff c), primeHorizonExtension z n ^ 2) +
          (dyadicTopMassConstant * Real.log N / (16 * c ^ 7)) *
            topCollarSeventhMass (N / linearDefectCutoff c) N (primeHorizonExtension z) ≤
          completeWeilEnergy tiltedUnitSpline c N z := by
  filter_upwards [eventually_far_complement_at_ratio hR] with N hN
  intro c θ hc1 hc8 hθlo hθhi z hz
  refine le_trans ?_ (hN c θ hc1 hc8 hθlo hθhi z hz)
  refine add_le_add (le_refl _) (mul_le_mul_of_nonneg_right ?_ (topCollarSeventhMass_nonneg _ _ _))
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hg := dyadicTopMassConstant_pos
  have hlin := farLinear_le_of_le_root hR hRr
  have hratio : c * (5 * dyadicTopMassConstant / (16 * R)) ≤
      (5 / 16 : ℝ) * (dyadicTopMassConstant / c ^ 7) * Real.log N := by
    have e : c * (5 * dyadicTopMassConstant / (16 * R)) =
        (5 / 16 : ℝ) * dyadicTopMassConstant * (c ^ 8 / R) / c ^ 7 := by
      field_simp
    rw [e]
    have h1 : c ^ 8 / R ≤ Real.log N := by
      rw [div_le_iff₀ hR]
      linarith only [hc8]
    have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ (5 / 16 : ℝ) * dyadicTopMassConstant)
    have h3 := div_le_div_of_nonneg_right h2 (by positivity : 0 ≤ c ^ 7)
    refine h3.trans_eq ?_
    field_simp
  have hmul := mul_le_mul_of_nonneg_left hlin hc0.le
  have hsplit : dyadicTopMassConstant * Real.log N / (16 * c ^ 7) =
      (1 / 16 : ℝ) * (dyadicTopMassConstant / c ^ 7) * Real.log N := by
    field_simp
  rw [hsplit]
  nlinarith only [hmul, hratio]

/-- **The complement of the low packet on the certified ratio interval.** -/
theorem eventually_critical_complement_below_root {R : ℝ} (hR : 0 < R) (hR1 : R ≤ 1)
    (hRr : R ≤ 5 / 6 * farRatioRoot) :
    ∀ᶠ N : ℕ in atTop, ∀ c : ℝ,
      Real.log (N : ℝ) ^ (1 / 16 : ℝ) ≤ c → c ^ 8 ≤ R * Real.log N →
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
  have hfar := eventually_far_complement_shape hR hRr
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
  intro c hclo hc8
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
  have hcroot : c ≤ L ^ (1 / 8 : ℝ) := by
    have hpow : c ^ 8 ≤ (L ^ (1 / 8 : ℝ)) ^ 8 := by
      have e : (L ^ (1 / 8 : ℝ)) ^ 8 = L := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]
        norm_num
      rw [e]
      have hmul := mul_le_mul_of_nonneg_right hR1 hL0.le
      change c ^ 8 ≤ R * L at hc8
      linarith only [hc8, hmul]
    exact (pow_le_pow_iff_left₀ hc0.le (Real.rpow_nonneg hL0.le _) (by norm_num)).mp hpow
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
    exact h'.trans_eq (by ring)
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
    (κ₀ := 1) (C_coerc0 := Ccoerc) (C_band1 := Cband)
    hc1 hcroot hL1 rfl (by norm_num) hCsmall hCcross hVc hsqrtQ hlogQ hH₀ hlogR₀
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
    have h := hfarN c θ hc1 hc8 le_rfl hθhi v hv
    change (θ * L / (8 * D)) *
      (∑ n ∈ Icc 1 (N / linearDefectCutoff c), primeHorizonExtension v n ^ 2) +
      (g * L / (16 * c ^ 7)) * topCollarSeventhMass (N / linearDefectCutoff c) N
        (primeHorizonExtension v) ≤ _ at h
    convert h using 1 <;> dsimp only [b, k, θ, B] <;>
      field_simp [hD.ne', ht0.ne', hc0.ne'] <;> ring
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
    change _ ≤ (1 / 32 : ℝ) * primeAdjunctionMass R a +
      (1 / 4 : ℝ) * ‖∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 +
      (θ * L / (64 * D)) *
        (∑ n ∈ Icc 1 (N / linearDefectCutoff c), primeHorizonExtension v n ^ 2) +
      (B * L / (64 * D * c ^ 7)) *
        ((∑ n ∈ Ioc (N / linearDefectCutoff c) N, primeHorizonExtension v n ^ 2) + ‖v‖ ^ 2) at h
    refine h.trans_eq ?_
    dsimp only [b, k, θ]
    field_simp [hD.ne', ht0.ne', hc0.ne'] <;> ring
  have h := critical_weighted_complement_assembly hQ2 hQR₀ hc1 hb hbc7 hk
    (hband0 hQ2 hQR₀ hR₀6 h36₀ hc1 hcL hw1 hrad hnear₀ hsmall₀)
    (hband1 hR₀2 hR₀R₁ hR₁6 h1080 hc1 hcL hw1 hnear₁
      (htail₁.trans ((div_le_one hL0).mpr hL1)))
    hfarShape
    (hcross01 hR₀2 hR₀6 (by linarith only [h36₀, Real.log_natCast_nonneg R₀])
      hc1 hw1 hnear₀ hup₀ hH₀ hsmall01)
    (hcrossShape hR₀2 hR₀R₁) (hcrossShape hR₁2 le_rfl)
    hfloor₀ hfloor₁ hu₀ hu₀Q hu₁ hu₁R hw
  change 4 * ‖u₀‖ ^ 2 + (3 + L ^ (1 / 2 : ℝ) / 32) * ‖u₁‖ ^ 2 +
    (θ * L / (16 * D)) *
      (∑ n ∈ Icc 1 (N / linearDefectCutoff c), primeHorizonExtension w n ^ 2) +
    (3 * g * L / (64 * c ^ 7)) *
      topCollarSeventhMass (N / linearDefectCutoff c) N (primeHorizonExtension w) ≤ _
  convert h using 1 <;> dsimp only [b, k, θ, B] <;>
    field_simp [hD.ne', ht0.ne', hc0.ne'] <;> ring

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory.ExplicitShell
