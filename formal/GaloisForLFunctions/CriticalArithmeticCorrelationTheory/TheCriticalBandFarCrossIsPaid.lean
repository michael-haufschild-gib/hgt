import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheCriticalBandFarBudgetsSeparateTwoRates
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheCriticalFarComplementRetainsTheCollarWeight

/-!
# The critical band–far cross is paid

With conductor exponent `(1 + log log N)^(-5)`, the logarithmic eighth-power
loss is absorbed while a fixed multiple of the weighted collar reserve remains.
The estimate is uniform through `c = (log N)^(1/8)`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Finset Filter Topology
open scoped Classical BigOperators RealInnerProductSpace Matrix
namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open CompletedArithmeticForms RenormalizedArithmeticPotentialTheory
  RenormalizedArithmeticPotentialTheory.CompletedShell SpacingScaleHarmonicAnalysis
  ArithmeticElectrostatics CriticalScaleArithmeticRigidity

/-- Every band below the almost-polynomial cutoff has a uniform critical cross
payment, retaining distinct prefix and terminal masses. -/
theorem eventually_critical_band_far_cross {B : ℝ} (hB : 0 < B) :
    ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c → c ≤ Real.log (N : ℝ) ^ (1 / 8 : ℝ) →
      let L := Real.log (N : ℝ)
      let θ := 1 / (1 + Real.log L) ^ 5
      let R₁ := ⌊(N : ℝ) ^ θ⌋₊
      ∀ R : ℕ, 2 ≤ R → R ≤ R₁ → ∀ a : ℕ → ℝ,
        (∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N) ∈ (conductorSubspace 1 N)ᗮ →
      ∀ w ∈ (conductorSubspace R₁ N)ᗮ,
        2 * |⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
          (∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N), w⟫| ≤
          (1 / 32 : ℝ) * primeAdjunctionMass R a +
          (1 / 4 : ℝ) * ‖∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 +
          (θ * L / (64 * explicitConductorCutoffConstant)) *
            (∑ n ∈ Icc 1 (N / linearDefectCutoff c), primeHorizonExtension w n ^ 2) +
          (B * L / (64 * explicitConductorCutoffConstant * c ^ 7)) *
            ((∑ n ∈ Ioc (N / linearDefectCutoff c) N, primeHorizonExtension w n ^ 2) + ‖w‖ ^ 2) := by
  obtain ⟨Cpr, Cup, CupT, Cnp, hCpr, hCup, hCupT, hCnp, hcross⟩ :=
    exists_band_far_cross_le_reserve_shape
  obtain ⟨Kres, hKres, hres⟩ := exists_tiltedUnitSpline_quadratic_conductor_residual_variable_rate
  obtain ⟨Ktot, hKtot, htot⟩ := exists_div_totient_le_loglog
  let D := explicitConductorCutoffConstant
  let H := 256 * Real.exp 2 + 4
  let CB := 5 + Real.log (2 * H)
  let A := 2 * Ktot
  have hD : 0 < D := explicitConductorCutoffConstant_pos
  have hH1 : 1 ≤ H := by dsimp only [H]; linarith only [Real.exp_pos 2]
  have hCB : 0 ≤ CB := by
    have := Real.log_nonneg (show 1 ≤ 2 * H by linarith only [hH1])
    dsimp only [CB]; positivity
  have hA : 1 ≤ A := by dsimp only [A]; linarith only [hKtot]
  have hLlim : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hllim : Tendsto (fun N : ℕ => Real.log (Real.log (N : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp hLlim
  filter_upwards [eventually_log_nat_le_rpow_36_one_ninth,
    hLlim.eventually_ge_atTop (3000 + H), hllim.eventually_ge_atTop 4096,
    hLlim.eventually (RHTower.eventually_const_mul_polylog_le_rpow 5
      (by norm_num : (0 : ℝ) < 1) (4 * D + 4)),
    hLlim.eventually (eventually_critical_band_far_monomials hA),
    hLlim.eventually (eventually_critical_cross_payment_constants hD hB hA
      hCpr.le hCnp hCup hCupT hCB (zero_le_one.trans hH1) (show 0 ≤ 2 * Kres by positivity)),
    hres 0 le_rfl 16 (by norm_num)] with N hLX hlarge hll hpoly hmon hpay hresN
  intro c hc1 hc R hR2 hRR₁ a hu w hw
  let L := Real.log (N : ℝ)
  let t := 1 + Real.log L
  let θ := 1 / t ^ 5
  let b := B * t ^ 5
  let R₁ := ⌊(N : ℝ) ^ θ⌋₊
  let T := linearDefectCutoff c
  let M := N / T
  let Sg := Ktot * (1 + Real.log (1 + Real.log (R₁ : ℝ)))
  let ρ := Kres * (c ^ 2 * (1 + Real.log c) ^ 3 * L ^ (1 / (16 : ℝ)) / L +
    c ^ 10 * (L / N) ^ 2)
  have hL3000 : 3000 ≤ L := by linarith only [hlarge, hH1]
  have hL1 : 1 ≤ L := by linarith only [hL3000]
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have ht1 : 1 ≤ t := by dsimp only [t]; linarith only [Real.log_nonneg hL1]
  have ht0 : 0 < t := zero_lt_one.trans_le ht1
  have hθ : 0 < θ := by dsimp only [θ]; positivity
  have hb : 0 < b := by dsimp only [b]; positivity
  have hθhi : θ ≤ 1 / 4096 := by
    change 1 / t ^ 5 ≤ 1 / 4096
    apply one_div_le_one_div_of_le (by norm_num)
    have hpow : t ≤ t ^ 5 := by
      simpa only [pow_one] using pow_le_pow_right₀ ht1 (by norm_num : 1 ≤ 5)
    dsimp only [t, L] at hpow
    linarith only [hpow, hll]
  have hθL : 4 * D + 4 ≤ θ * L := by
    have hpoly' : (4 * D + 4) * t ^ 5 ≤ L := by
      simpa only [Real.rpow_one] using hpoly
    have h := (le_div_iff₀ (show 0 < t ^ 5 by positivity)).mpr hpoly'
    change 4 * D + 4 ≤ 1 / t ^ 5 * L
    linarith only [h]
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hcL : c ≤ L := hc.trans ((Real.rpow_le_rpow_of_exponent_le hL1
    (by norm_num : (1 / 8 : ℝ) ≤ 1)).trans_eq (Real.rpow_one L))
  have hN1 : 1 ≤ N := by
    by_contra hn
    have : N = 0 := by omega
    subst this
    simp [L] at hL0
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hNθ4 : 4 ≤ (N : ℝ) ^ θ := by
    rw [Real.rpow_def_of_pos hN0]
    have h := Real.add_one_le_exp (L * θ)
    change 4 ≤ Real.exp (L * θ)
    linarith only [h, hθL, hD]
  obtain ⟨hR₁2, hTN, hR₁M, hM2, -, -, -, hlogR₁⟩ :=
    critical_prefix_cutoff_geometry hθ (hθhi.trans (by norm_num)) hc1 hcL
      (by linarith only [hL3000]) (by linarith only [hlarge])
      ((div_le_iff₀ hθ).mpr (by linarith only [hθL, hD]))
      ((div_le_iff₀ hθ).mpr (by linarith only [hθL])) hLX hNθ4
  have hlogR : Real.log (R : ℝ) ≤ θ * L :=
    (Real.log_le_log (by exact_mod_cast (show 0 < R by omega))
      (by exact_mod_cast hRR₁)).trans hlogR₁
  have h36 : 36 * (1 + Real.log (R : ℝ)) ≤ L := by
    have h := mul_le_mul_of_nonneg_right hθhi hL0.le
    linarith only [hlogR, h, hL3000]
  have h18 : 18 * (1 + Real.log (R : ℝ)) ≤ L := by
    linarith only [h36, Real.log_natCast_nonneg R]
  obtain ⟨-, hwidth, -, hrad, hR6, hsize_near, hsize_up, -, -, -, -, -⟩ :=
    rpow_horizon_N_bounds_one_ninth hN1 hR2 hc1 (by linarith only [hL3000]) hLX hcL h36
  have hRN₁ := log_pow_mul_floor_rpow_pow_le hN1 hθ hθhi hL0.le hLX
  have hRN : L ^ 18 * (R : ℝ) ^ 16 ≤ N :=
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg R)
      (by exact_mod_cast hRR₁) 16) (by positivity)).trans hRN₁
  obtain ⟨hceil, hRK, h8c, hc4⟩ := near_ceil_side_conditions
    (by omega : 1 ≤ R) hc1 hcL (by linarith only [hL3000]) hRN
  have hRM : R * R ≤ M := (Nat.mul_le_mul hRR₁ hRR₁).trans hR₁M
  obtain ⟨hT3, -, -, hTup⟩ := linearDefectCutoff_bounds hc1
  have hNM : (N : ℝ) / M ≤ 2 * H * c := by
    have h := nat_div_div_le_two_mul (by omega : 1 ≤ T) hTN
    linarith only [h, hTup]
  have hTPC : terminalPacketCost R M N ≤ CB * (1 + Real.log c) := by
    have hcost := terminalPacketCost_nat_div_le (Q := R) (by omega : 1 ≤ T) hTN hRM
    have hT0 : (0 : ℝ) < T := by exact_mod_cast (show 0 < T by omega)
    have h := Real.log_le_log (show 0 < 2 * (T : ℝ) by positivity)
      (mul_le_mul_of_nonneg_left hTup zero_le_two)
    rw [show 2 * (H * c) = (2 * H) * c by ring,
      Real.log_mul (by positivity) hc0.ne'] at h
    have hlc := Real.log_nonneg hc1
    have hCB1 : 1 ≤ CB := by
      have := Real.log_nonneg (show 1 ≤ 2 * H by linarith only [hH1])
      dsimp only [CB]; linarith only [this]
    have hprod := mul_nonneg (sub_nonneg.mpr hCB1) hlc
    dsimp only [CB] at hprod ⊢
    nlinarith only [hcost, h, hprod]
  have hSg1 : 1 ≤ Sg := by
    have hl : 0 ≤ Real.log (1 + Real.log (R₁ : ℝ)) :=
      Real.log_nonneg (by linarith only [Real.log_natCast_nonneg R₁])
    exact one_le_mul_of_one_le_of_one_le hKtot (by linarith only [hl])
  have hSgA : Sg ≤ A * t := loglog_budget_le (zero_le_one.trans hKtot) hL1 (by
    have h := mul_le_mul_of_nonneg_right hθhi hL0.le
    linarith only [hlogR₁, h, hL3000])
  obtain ⟨hm1, hm2, hLτ, h7τ⟩ := hmon c Sg hc1 hc hSg1 hSgA
  have hLσ : 1 / L ≤ A ^ 2 * t ^ 3 :=
    (div_le_one hL0).mpr hL1 |>.trans
      (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hA) (one_le_pow₀ ht1))
  have hL11 : L ^ 11 ≤ N :=
    (pow_le_pow_right₀ hL1 (by norm_num : 11 ≤ 18)).trans
      ((le_mul_of_one_le_right (by positivity)
        (one_le_pow₀ (show (1 : ℝ) ≤ R by exact_mod_cast (show 1 ≤ R by omega)))).trans hRN)
  have hρ : ‖poleModeResidual c N‖ ^ 2 ≤ ρ := by
    have h := hresN 1 one_pos (by simp) c hc1 hwidth
    simpa only [poleModeResidual, Nat.cast_one, Real.log_one, add_zero, one_pow, one_mul,
      mul_one] using h
  have hρK := pole_rate_le hKres.le hc1 hcL hL1 (by norm_num : 1 ≤ (16 : ℕ))
    (by norm_num : 1 / ((16 : ℕ) : ℝ) ≤ 1 / 16) hL11
  have hlR : 1 + Real.log (R : ℝ) ≤ 2 * θ * L := by
    linarith only [hlogR, hθL, hD]
  obtain ⟨hθs, hσE, hσU⟩ := hpay
  have hEbudget := budgetE_le hL1 hc1 hcL hθ hD hb hCpr.le hCnp hCB
    (by linarith only [Real.log_nonneg hc1]) hSg1
    (by linarith only [Real.log_natCast_nonneg R]) hlR
    (by exact_mod_cast (show 1 ≤ R by omega)) hRN
    (terminalPacketCost_nonneg R (Nat.div_le_self N T)) hTPC hm1 hLσ hθs hσE
  have hUbudget := budgetU_two_rates_le hL1 hc1 hcL hθ hD hb hCpr.le hCnp hCup hCupT
    (zero_le_one.trans hH1) (show 0 ≤ 2 * Kres by positivity)
    (by linarith only [Real.log_nonneg hc1]) hSg1
    (Real.one_le_rpow hL1 (by norm_num))
    (by linarith only [Real.log_natCast_nonneg R]) hlR
    (by exact_mod_cast (show 1 ≤ R by omega)) hRN
    ((sq_nonneg _).trans hρ) hρK hNM hm1 hm2 hLσ hLτ h7τ hσU
  have hx := hcross hR2 hR6 (by omega : 1 ≤ M) (Nat.div_le_self N T) h18 hc1 h8c hc4
    hsize_near hsize_up hrad hceil hRK hSg1
    (div_totient_le_loglog_of_le hKtot htot hRR₁) hρ
    (show 0 < θ * L / (2 * D) by positivity) hb hEbudget hUbudget a hu
    (fun v hv => hw v (conductorSubspace_mono hRR₁ N hv))
  refine hx.trans_eq ?_
  dsimp only [b, θ, L, t, D]
  field_simp
  ring

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.eventually_critical_band_far_cross
