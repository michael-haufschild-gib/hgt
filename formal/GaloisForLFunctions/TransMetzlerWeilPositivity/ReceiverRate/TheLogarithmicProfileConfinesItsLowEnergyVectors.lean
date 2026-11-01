import GaloisForLFunctions.TransMetzlerWeilPositivity.ReceiverRate.TheLogarithmicProfileDecouplesConductorBands

/-!
# Quantitative confinement for the logarithmic profile

The complete prime-defect reserve confines bounded-energy vectors to conductors
with logarithm `O(T¹⁶)`, where `T` bounds overlap and reciprocal Fourier floor.
An enlarged cutoff makes the discarded tail pay its own cross interaction.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Finset Filter Topology
open scoped BigOperators RealInnerProductSpace Matrix Classical

namespace GaloisForLFunctions.TransMetzlerWeilPositivity.LogarithmicConductorSplit

open CompletedArithmeticForms RenormalizedArithmeticPotentialTheory
  RenormalizedArithmeticPotentialTheory.CompletedShell CriticalArithmeticCorrelationTheory
  SpacingScaleHarmonicAnalysis ArithmeticElectrostatics

private theorem exists_matrix_envelope_reserve :
    ∃ b B H : ℝ, 0 < b ∧ 0 < B ∧ 0 < H ∧
      ∀ᶠ c : ℝ in atTop, ∀ T : ℝ, c ≤ T →
        logarithmicSpectralControl logarithmicReserveRate c ≤ T →
        ∀ N : ℕ, H * T ^ 8 ≤ (N : ℝ) →
        ∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N),
          (b / T ^ 7) * poleDefect N (primeHorizonExtension x) - B * T ^ 9 * ‖x‖ ^ 2 ≤
            completeWeilEnergy zeroFreeLogProfile c N x := by
  obtain ⟨b, B, H, hb, hB, hH, hr⟩ := exists_zeroFreeLogProfile_complete_defect_reserve
  refine ⟨b, B, H, hb, hB, hH, ?_⟩
  filter_upwards [hr, eventually_ge_atTop (1 : ℝ)] with c hcres hc
  intro T hcT hcontrol N hN x
  have hc0 := zero_lt_one.trans_le hc
  have hT0 := hc0.trans_le hcT
  have hN0 : (0 : ℝ) < N := (mul_pos hH (pow_pos hT0 8)).trans_le hN
  have hN1 : 1 ≤ N := by exact_mod_cast (show 0 < N by exact_mod_cast hN0)
  have hh := hcres T hcT hcontrol N hN (primeHorizonExtension x)
  rw [sum_primeHorizonExtension_sq] at hh
  rw [completeWeilEnergy, completeWeilMatrix_inner_eq_weilQuad
    (contDiff_zeroFreeLogProfile.of_le (natCast_le_infty 2))
    zeroFreeLogProfile_eq_zero hc0 hN1, integral_atomDilate_sq (div_pos hc0 hN0)]
  exact hh

/-- Confinement retains three quarters of the norm and bounded complete Weil energy. -/
theorem exists_high_tail_suppression :
    ∃ C_R H_res : ℝ, 0 < C_R ∧ 0 < H_res ∧
      ∀ᶠ c : ℝ in atTop, ∀ T : ℝ, c ≤ T →
        logarithmicSpectralControl logarithmicReserveRate c ≤ T →
      ∀ {Q₁ N : ℕ},
        2 ≤ Q₁ → H_res * T ^ 8 ≤ N → c / N ≤ 1 / 3 →
        (∀ {R' : ℕ}, Q₁ ≤ R' → Real.log R' ≤ C_R * T ^ 16 + Real.log Q₁ →
          R' ^ 6 ≤ N ∧
          18 * (1 + Real.log R') ≤ Real.log N ∧
          ((R' * R' : ℕ) + 1 : ℝ) * (linearNearRowRadius c + 1) ≤ N ∧
          ((R' * R' : ℕ) + 1 : ℝ) * (c * Real.exp 1 + 1) ≤ N ∧
          (1 + Real.log R') / Real.sqrt (Real.log N) ≤ 1 ∧
          (1 + Real.log R') ^ 2 / Real.sqrt (Real.log N) ≤ 1 ∧
          (R' : ℝ) * Real.sqrt (Real.log N / N) ≤ 1) →
      ∀ {zHat : EuclideanSpace ℝ (PrimeHorizonIndex N)},
        zHat ∈ (conductorSubspace Q₁ N)ᗮ → ‖zHat‖ = 1 →
        completeWeilEnergy zeroFreeLogProfile c N zHat ≤
          2 →
      ∃ R' : ℕ, Q₁ ≤ R' ∧ Real.log R' ≤ C_R * T ^ 16 + Real.log Q₁ ∧
        ∃ u : EuclideanSpace ℝ (PrimeHorizonIndex N),
          u ∈ conductorSubspace R' N ∧ u ∈ (conductorSubspace Q₁ N)ᗮ ∧
          3 / 4 ≤ ‖u‖ ^ 2 ∧ ‖u‖ ≤ 1 ∧
          completeWeilEnergy zeroFreeLogProfile c N u ≤
            3 := by
  obtain ⟨b, B, H, hb, hB, hH, hres⟩ := exists_matrix_envelope_reserve
  obtain ⟨C_cross, hC_cross1, hcross⟩ := exists_completeWeilMatrix_orthog_cross_le
  let M₀ : ℝ := 2
  have hM₀ : 0 < M₀ := by norm_num [M₀]
  let K_coef := (B + M₀) / b
  have hK_coef : 0 < K_coef := by dsimp only [K_coef]; positivity
  let D := explicitConductorCutoffConstant
  have hD : 0 < D := explicitConductorCutoffConstant_pos
  let C_gap := D * (1 + (B + 4 * C_cross ^ 2) / b)
  have hC_gap : 0 < C_gap := by dsimp only [C_gap]; positivity
  let C_app := 16 * quadraticConfinementConstant * (K_coef + 1)
  have hC_app : 0 < C_app := by
    have := quadraticConfinementConstant_pos; dsimp only [C_app]; positivity
  let C_R := C_app + C_gap + 1
  have hC_R : 0 < C_R := by dsimp only [C_R]; positivity
  refine ⟨C_R, H, hC_R, hH, ?_⟩
  filter_upwards [hres, eventually_ge_atTop (1 : ℝ)] with c hres_c hc1
  intro T hcT hcontrol Q₁ N hQ₁ hHN hw1 hR'_conds zHat hz_orth hz_norm hz_energy
  have hT1 := hc1.trans hcT
  have hT0 : 0 < T := zero_lt_one.trans_le hT1
  have hc16 : 1 ≤ T ^ 16 := one_le_pow₀ hT1
  have hdef_le : poleDefect N (primeHorizonExtension zHat) ≤ K_coef * T ^ 16 := by
    have hr := hres_c T hcT hcontrol N hHN zHat
    rw [hz_norm, one_pow, mul_one] at hr
    have h1 : (b / T ^ 7) * poleDefect N (primeHorizonExtension zHat) ≤
        B * T ^ 9 + M₀ := by dsimp only [M₀]; linarith only [hr, hz_energy]
    have hc9 : 1 ≤ T ^ 9 := one_le_pow₀ hT1
    have h2 : B * T ^ 9 + M₀ ≤ (B + M₀) * T ^ 9 := by nlinarith only [hM₀, hc9]
    have h3 := (div_le_iff₀ (pow_pos hT0 7)).mp (by
      simpa only [div_mul_eq_mul_div] using h1.trans h2)
    dsimp only [K_coef]
    rw [div_mul_eq_mul_div, le_div_iff₀ hb]
    calc
      poleDefect N (primeHorizonExtension zHat) * b =
          b * poleDefect N (primeHorizonExtension zHat) := mul_comm _ _
      _ ≤ (B + M₀) * T ^ 9 * T ^ 7 := h3
      _ = (B + M₀) * T ^ 16 := by ring
  -- A fixed tolerance retains three quarters of the norm.
  obtain ⟨R₀, hR₀2, hR₀log, happ⟩ := exists_explicit_quadratic_conductor_projection
    (1 / 4) (by norm_num) (by norm_num) (K_coef * T ^ 16) (by positivity)
  have hR₀bound : Real.log R₀ ≤ C_app * T ^ 16 := by
    have hK1 : K_coef * T ^ 16 + 1 ≤ (K_coef + 1) * T ^ 16 := by linarith only [hc16]
    calc
      _ ≤ quadraticConfinementConstant / (1 / 4 : ℝ) ^ 2 * (K_coef * T ^ 16 + 1) := hR₀log
      _ ≤ quadraticConfinementConstant / (1 / 4 : ℝ) ^ 2 * ((K_coef + 1) * T ^ 16) :=
        mul_le_mul_of_nonneg_left hK1 (by have := quadraticConfinementConstant_pos; positivity)
      _ = _ := by dsimp only [C_app]; ring
  -- The enlarged cutoff makes the orthogonal tail itself coercive.
  let G : ℕ := ⌈Real.exp (C_gap * T ^ 16)⌉₊
  have hXpos : 0 < C_gap * T ^ 16 := mul_pos hC_gap (pow_pos hT0 16)
  have hexp1 : 1 < Real.exp (C_gap * T ^ 16) := by
    simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr hXpos
  have hceil : Real.exp (C_gap * T ^ 16) ≤ (G : ℝ) := Nat.le_ceil _
  have hGpos : (0 : ℝ) < G := (zero_lt_one.trans hexp1).trans_le hceil
  have hGlow : C_gap * T ^ 16 ≤ Real.log G := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hceil
  have hGup : Real.log G ≤ C_gap * T ^ 16 + 1 := by
    have hceilUp : (G : ℝ) < Real.exp (C_gap * T ^ 16) + 1 :=
      Nat.ceil_lt_add_one (Real.exp_pos _).le
    have hdouble : (G : ℝ) ≤ 2 * Real.exp (C_gap * T ^ 16) := by
      linarith only [hceilUp, hexp1]
    have hlog := Real.log_le_log hGpos hdouble
    rw [Real.log_mul (by norm_num) (Real.exp_ne_zero _), Real.log_exp] at hlog
    linarith only [hlog, Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  let R := max R₀ G
  let R' := max R Q₁
  have hQR' : Q₁ ≤ R' := le_max_right _ _
  have hR₀R' : R₀ ≤ R' := (le_max_left R₀ G).trans (le_max_left R Q₁)
  have hGR' : G ≤ R' := (le_max_right R₀ G).trans (le_max_left R Q₁)
  have hR'2 : 2 ≤ R' := hQ₁.trans hQR'
  have hRbound : Real.log R ≤ C_R * T ^ 16 := by
    rcases le_total R₀ G with hRG | hGR
    · rw [show R = G from max_eq_right hRG]
      dsimp only [C_R]
      nlinarith only [hGup, hc16, hC_app, pow_nonneg hT0.le 16]
    · rw [show R = R₀ from max_eq_left hGR]
      dsimp only [C_R]
      nlinarith only [hR₀bound, hC_gap, pow_nonneg hT0.le 16]
  have hR'_log : Real.log R' ≤ C_R * T ^ 16 + Real.log Q₁ := by
    have hQlog := Real.log_natCast_nonneg Q₁
    have hCr : 0 ≤ C_R * T ^ 16 := by positivity
    rcases le_total R Q₁ with hRQ | hQR
    · rw [show R' = Q₁ from max_eq_right hRQ]
      linarith only [hCr]
    · rw [show R' = R from max_eq_left hQR]
      linarith only [hRbound, hQlog]
  have hgapLog : C_gap * T ^ 16 ≤ Real.log R' :=
    hGlow.trans (Real.log_le_log hGpos (by exact_mod_cast hGR'))
  obtain ⟨hR6N, hlogN, hRNT_lin, hRNT_up, hlog_div1, hlog_div2, hR_sqrt⟩ :=
    hR'_conds hQR' hR'_log
  have hN2 : 2 ≤ N := by
    have hpow : R' ^ 1 ≤ R' ^ 6 :=
      Nat.pow_le_pow_right (by omega) (by norm_num)
    simp only [pow_one] at hpow
    omega
  let u := (conductorSubspace R' N).starProjection zHat
  let w := zHat - u
  have hu_mem : u ∈ conductorSubspace R' N :=
    (conductorSubspace R' N).starProjection_apply_mem zHat
  have hu_orthQ : u ∈ (conductorSubspace Q₁ N)ᗮ :=
    starProjection_mem_orthogonal_of_le (conductorSubspace_mono hQR' N) hz_orth
  have hu_orth1 : u ∈ (conductorSubspace 1 N)ᗮ := fun v hv =>
    hu_orthQ v (conductorSubspace_mono (by omega : 1 ≤ Q₁) N hv)
  have hw_orth : w ∈ (conductorSubspace R' N)ᗮ := sub_starProjection_mem_orthogonal _ zHat
  have hw_sq : ‖w‖ ^ 2 ≤ 1 / 4 := by
    have hpR_mem : (conductorSubspace R₀ N).starProjection zHat ∈ conductorSubspace R' N :=
      conductorSubspace_mono hR₀R' N ((conductorSubspace R₀ N).starProjection_apply_mem zHat)
    exact (norm_sub_starProjection_sq_le (conductorSubspace R' N) zHat _ hpR_mem).trans
      (happ N hN2 zHat hz_norm.le hdef_le)
  have hpyth := norm_starProjection_sq_add_sub_sq (conductorSubspace R' N) zHat
  change ‖u‖ ^ 2 + ‖w‖ ^ 2 = ‖zHat‖ ^ 2 at hpyth
  rw [hz_norm, one_pow] at hpyth
  have hu_sq_ge : 3 / 4 ≤ ‖u‖ ^ 2 := by linarith only [hpyth, hw_sq]
  have hu_le1 : ‖u‖ ≤ 1 := by nlinarith only [hpyth, sq_nonneg ‖w‖, norm_nonneg u]
  have hw_def : (Real.log R' / D - 1) * ‖w‖ ^ 2 ≤
      poleDefect N (primeHorizonExtension w) := by
    by_cases hw0 : ‖w‖ = 0
    · rw [hw0, zero_pow (by decide : 2 ≠ 0), mul_zero]
      exact poleDefect_nonneg _ _
    have hp0 : (conductorSubspace R' N).starProjection w = 0 := by
      let p := (conductorSubspace R' N).starProjection w
      have hp_mem : p ∈ conductorSubspace R' N :=
        (conductorSubspace R' N).starProjection_apply_mem w
      have hi : ⟪p, w⟫ = 0 := Submodule.inner_right_of_mem_orthogonal hp_mem hw_orth
      have hi' : ⟪w, p⟫ = 0 := by simpa only [real_inner_comm] using hi
      have hj := (conductorSubspace R' N).starProjection_inner_eq_zero w p hp_mem
      rw [inner_sub_left] at hj
      change ⟪w, p⟫ - ⟪p, p⟫ = 0 at hj
      rw [hi', real_inner_self_eq_norm_sq] at hj
      apply norm_eq_zero.mp
      nlinarith only [hj, norm_nonneg p]
    apply poleDefect_ge_explicit_of_norm_sub_starProjection_gt hR'2 hN2
    rw [hp0, sub_zero]
    have hp : 0 < ‖w‖ ^ 2 := sq_pos_of_ne_zero hw0
    linarith only [hp]
  have hgapCoeff : (B + 4 * C_cross ^ 2) * T ^ 16 ≤ b * (Real.log R' / D - 1) := by
    have hlow : (1 + (B + 4 * C_cross ^ 2) / b) * T ^ 16 ≤ Real.log R' / D := by
      apply (le_div_iff₀ hD).mpr
      calc
        ((1 + (B + 4 * C_cross ^ 2) / b) * T ^ 16) * D = C_gap * T ^ 16 := by
          dsimp only [C_gap]
          ring
        _ ≤ Real.log R' := hgapLog
    have hs := mul_le_mul_of_nonneg_left hlow hb.le
    have he : b * ((1 + (B + 4 * C_cross ^ 2) / b) * T ^ 16) =
        b * T ^ 16 + (B + 4 * C_cross ^ 2) * T ^ 16 := by
      field_simp [hb.ne']
    rw [he] at hs
    nlinarith only [hs, mul_le_mul_of_nonneg_left hc16 hb.le]
  have hgap9 : (B + 4 * C_cross ^ 2) * T ^ 9 ≤
      (b / T ^ 7) * (Real.log R' / D - 1) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (pow_pos hT0 7)]
    calc
      (B + 4 * C_cross ^ 2) * T ^ 9 * T ^ 7 = (B + 4 * C_cross ^ 2) * T ^ 16 := by ring
      _ ≤ b * (Real.log R' / D - 1) := hgapCoeff
  have hw_energy : 4 * C_cross ^ 2 * T ^ 6 * ‖w‖ ^ 2 ≤
      completeWeilEnergy zeroFreeLogProfile c N w := by
    have hr := hres_c T hcT hcontrol N hHN w
    have hd := mul_le_mul_of_nonneg_left hw_def (div_nonneg hb.le (pow_pos hT0 7).le)
    have hg := mul_le_mul_of_nonneg_right hgap9 (sq_nonneg ‖w‖)
    have hc69 := mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hT1 (show 6 ≤ 9 by norm_num))
      (show 0 ≤ 4 * C_cross ^ 2 * ‖w‖ ^ 2 by positivity)
    nlinarith only [hr, hd, hg, hc69]
  have htail_cost :
      2 * |⟪Matrix.toEuclideanLin (completeWeilMatrix zeroFreeLogProfile c N) u, w⟫| -
        completeWeilEnergy zeroFreeLogProfile c N w ≤ 1 / 4 := by
    have hcross' := hcross hR'2 hR6N hlogN hc1 hw1 hRNT_lin hRNT_up hlog_div1
      (hlog_div2.trans (one_le_pow₀ hc1))
      hR_sqrt hu_mem hu_orth1 hw_orth
    have hcross_aux : |⟪Matrix.toEuclideanLin (completeWeilMatrix zeroFreeLogProfile c N) u, w⟫| ≤
        C_cross * T ^ 3 * ‖u‖ * ‖w‖ := by
      apply hcross'.trans
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (zero_lt_one.trans_le hc1).le hcT 3)
            (zero_le_one.trans hC_cross1)) (norm_nonneg u)) (norm_nonneg w)
    have hcross_bound :
        2 * |⟪Matrix.toEuclideanLin (completeWeilMatrix zeroFreeLogProfile c N) u, w⟫| ≤
          2 * C_cross * T ^ 3 * ‖w‖ := by
      have hh := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hu_le1 (show 0 ≤ C_cross * T ^ 3 by positivity))
        (norm_nonneg w)
      nlinarith only [hcross_aux, hh]
    nlinarith only [hcross_bound, hw_energy, sq_nonneg (2 * C_cross * T ^ 3 * ‖w‖ - 1 / 2)]
  have hu_energy : completeWeilEnergy zeroFreeLogProfile c N u ≤
      3 := by
    have hz_split : zHat = u + w := by dsimp only [w]; abel
    have hexp := completeWeilEnergy_add_eq zeroFreeLogProfile c u w
    rw [← hz_split] at hexp
    linarith only [hexp, hz_energy, htail_cost,
      neg_abs_le ⟪Matrix.toEuclideanLin (completeWeilMatrix zeroFreeLogProfile c N) u, w⟫]
  exact ⟨R', hQR', hR'_log, u, hu_mem, hu_orthQ, hu_sq_ge, hu_le1, hu_energy⟩

end GaloisForLFunctions.TransMetzlerWeilPositivity.LogarithmicConductorSplit

#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.LogarithmicConductorSplit.exists_high_tail_suppression
