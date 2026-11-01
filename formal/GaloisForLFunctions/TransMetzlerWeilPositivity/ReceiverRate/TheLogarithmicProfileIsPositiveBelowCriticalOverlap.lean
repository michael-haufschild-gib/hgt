import GaloisForLFunctions.TransMetzlerWeilPositivity.ReceiverRate.TheLogarithmicConductorSplitFitsTheHorizon
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.EveryProfileWithoutRealFourierZerosIsUniformlyPositiveOnBoundedOverlap

/-!
# Complete Weil positivity below logarithmic Denjoy–Carleman overlap

The reciprocal Fourier floor fits a small power of `log N`. Conductor-band
confinement and coercivity exclude nonpositive vectors uniformly below a fixed
positive multiple of `loglog N·(logloglog N)²`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Finset Filter Topology
open scoped BigOperators RealInnerProductSpace Matrix Classical

namespace GaloisForLFunctions.TransMetzlerWeilPositivity

open CompletedArithmeticForms RenormalizedArithmeticPotentialTheory
  RenormalizedArithmeticPotentialTheory.CompletedShell CriticalArithmeticCorrelationTheory
  SpacingScaleHarmonicAnalysis ArithmeticElectrostatics LogarithmicConductorSplit

private theorem smooth_profile : ContDiff ℝ 2 zeroFreeLogProfile :=
  contDiff_zeroFreeLogProfile.of_le (natCast_le_infty 2)

/-- Large overlaps are positive whenever their reciprocal Fourier floor fits the power budget. -/
theorem exists_zeroFreeLogProfile_positive_power_budget :
    ∃ A : ℝ, ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, A ≤ c →
      logarithmicSpectralControl logarithmicReserveRate c ≤ Real.log (N : ℝ) ^ (1 / 256 : ℝ) →
        (completeWeilMatrix zeroFreeLogProfile c N).PosDef := by
  classical
  let α : ℝ := 1 / 256
  let q : ℝ := 1 / 16
  let ν : ℝ := 1 / 1000
  let k : ℕ := 8
  have hα : 0 < α := by norm_num [α]
  have hα_lt : α < 1 / 59 := by norm_num [α]
  have hα128 : α ≤ 1 / 128 := by norm_num [α]
  have hq : 0 < q := by norm_num [q]
  have hqmax : q ≤ 1 / 5 := by norm_num [q]
  have hν : 0 < ν := by norm_num [ν]
  have hν1000 : ν ≤ 1 / 1000 := le_rfl
  have hk : 1 ≤ k := by norm_num [k]
  have hsep : 4 * α - q / 2 ≤ -ν := by norm_num [α, q, ν]
  have hbudget_exp : 5 * q + 19 * α + 1 / (k : ℝ) - 1 ≤ -ν := by norm_num [α, q, k, ν]
  have hgap : 0 < q / 4 - α := by norm_num [α, q]
  obtain ⟨C_R, H_res, hC_R, hH_res, hsupp⟩ := exists_high_tail_suppression
  obtain ⟨C_coerc, C_small, hC_coerc, hC_small, hcoerc⟩ := exists_high_band_coercivity
  obtain ⟨K_res, hK_res, hres_unif⟩ := exists_completeWeil_uniform_conductor_residual_variable_rate
    smooth_profile zeroFreeLogProfile_eq_zero integral_zeroFreeLogProfile_sq_pos
  obtain ⟨A, hA⟩ := eventually_atTop.mp
    (hsupp.and (eventually_zeroFreeLogProfile_conductor_floor.and
      (eventually_logarithmic_reserves_ge_reciprocal.and (eventually_gt_atTop (1 : ℝ)))))
  refine ⟨max 2 A, ?_⟩
  have hLlim : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_floor_log_rpow_bounds hq hqmax,
    eventually_log_nat_le_rpow_36,
    eventually_powerLog_low_band_and_coercivity_gap hK_res hC_coerc hα hα_lt
      hq hqmax hν hk hbudget_exp hgap,
    hres_unif q hq.le k hk,
    hLlim.eventually_ge_atTop (max 2000 H_res),
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 7 / 10)).comp hLlim).eventually_ge_atTop 36,
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 400)).comp hLlim).eventually_ge_atTop
      (2 * C_R + 2),
    ((tendsto_rpow_atTop hν).comp hLlim).eventually_ge_atTop
      (20 * C_small + 3),
    eventually_ge_atTop 2] with
    N hQ_all hLX hlow_coerc hresN hL_max hL45 hCR_L hCs_L hN2
  dsimp only [Function.comp_def] at hL45 hCR_L hCs_L
  obtain ⟨hQ2, hQ_le, hQ_quarter, _, hQ4_N⟩ := hQ_all
  have hL2000 : 2000 ≤ Real.log (N : ℝ) := (le_max_left _ _).trans hL_max
  have hHL : H_res ≤ Real.log (N : ℝ) := (le_max_right _ _).trans hL_max
  have hN1 : 1 ≤ N := by omega
  let L := Real.log (N : ℝ)
  let Q₁ := ⌊L ^ q⌋₊
  intro c hAc hcontrol
  obtain ⟨hsuppc, hfloorc, hrecip, hcgt⟩ := hA c ((le_max_right 2 A).trans hAc)
  have hc1 := hcgt.le
  have hc0 := zero_lt_one.trans hcgt
  let T := L ^ α
  change logarithmicSpectralControl logarithmicReserveRate c ≤ T at hcontrol
  have hL1 : 1 ≤ L := by dsimp only [L]; linarith only [hL2000]
  have hL0 := zero_lt_one.trans_le hL1
  have hT1 : 1 ≤ T := Real.one_le_rpow hL1 hα.le
  have hT0 := zero_lt_one.trans_le hT1
  have hcT : c ≤ T := (le_logarithmicSpectralControl hcgt).trans hcontrol
  obtain ⟨_, hgramT, hres_sum_bound, hbudget, hcoerc_gapT⟩ := hlow_coerc T hT1 le_rfl
  have heqfloor : (2 : ℝ) / (2 * T ^ 7) = 1 / T ^ 7 := by ring
  rw [heqfloor] at hbudget
  have hgram : 9 * (1 + Real.log (Q₁ : ℝ)) / L *
      (|completeWeilSelfFinitePart zeroFreeLogProfile 1| + 2 * Real.log (Q₁ : ℝ) +
        3 * c ^ 4) ≤ 1 / 16 := by
    apply le_trans ?_ hgramT
    have hQlog := Real.log_natCast_nonneg Q₁
    gcongr
  have hcoerc_gap : 8 + C_coerc ≤ (1 / 4) * Real.log (Q₁ : ℝ) - Real.log c := by
    have hlog := Real.log_le_log hc0 hcT
    linarith only [hcoerc_gapT, hlog]
  have hQ_R'_log : Real.log (Q₁ : ℝ) ≤ C_R * T ^ 16 + Real.log (Q₁ : ℝ) := by
    have : 0 ≤ C_R * T ^ 16 := by positivity
    linarith only [this]
  obtain ⟨hTL, hlog36_Q, _, hlog18_Q, _, _, _, _, _, _⟩ :=
    rpow_horizon_L_smallness_bounds hα128 hqmax hν hν1000 hsep hN1 hQ2 le_rfl hT1 hC_R hC_small hH_res
      hL2000 hHL hLX hL45 hCR_L hCs_L hQ_le hQ_quarter (le_rfl : T ≤ L ^ α) hQ_R'_log
  have hcL := hcT.trans hTL
  obtain ⟨hHN, _, _, _, _, _, _, _, _, _⟩ :=
    rpow_horizon_N_bounds hN1 hQ2 hT1 hH_res hL2000 hHL hLX hTL hlog36_Q
  obtain ⟨_, hwidth, hw1, hradN, _, _, _, _, _, _⟩ :=
    rpow_horizon_N_bounds hN1 hQ2 hc1 hH_res hL2000 hHL hLX hcL hlog36_Q
  have hQQ_N : Q₁ * Q₁ ≤ N := by
    have hQ2' : 2 ≤ Q₁ := hQ2
    have h24 : Q₁ ^ 2 ≤ Q₁ ^ 4 := Nat.pow_le_pow_right (zero_lt_two.trans_le hQ2') (by norm_num)
    simpa only [sq] using h24.trans hQ4_N
  let rate := T ^ 5 / L + T ^ 10 * (L / (N : ℝ)) ^ 2 + T ^ 3 * L ^ (1 / (k : ℝ)) / L
  have hrate0 : 0 ≤ rate := by
    dsimp only [rate, L]; have := Real.log_natCast_nonneg N; positivity
  have hres_m : ∀ m ∈ Icc 1 Q₁,
      ‖Matrix.toEuclideanLin (completeWeilMatrix zeroFreeLogProfile c N)
          (normalizedRamanujanHorizonVector m N) -
        completedConductorEnergy zeroFreeLogProfile c m •
          normalizedRamanujanHorizonVector m N‖ ^ 2 ≤ K_res * (m : ℝ) ^ 4 * rate := by
    intro m hm
    obtain ⟨hm1, hmQ⟩ := mem_Icc.mp hm
    have hmL : (m : ℝ) ≤ L ^ q :=
      (by exact_mod_cast hmQ : (m : ℝ) ≤ Q₁).trans hQ_le
    apply (hresN m hm1 hmL c hc1 hwidth).trans
    dsimp only [rate]
    gcongr
  have hres_sum_Q :
      (∑ m ∈ Icc 1 Q₁,
        ‖Matrix.toEuclideanLin (completeWeilMatrix zeroFreeLogProfile c N)
            (normalizedRamanujanHorizonVector m N) -
          completedConductorEnergy zeroFreeLogProfile c m •
            normalizedRamanujanHorizonVector m N‖ ^ 2) ≤ 1 / 128 := by
    have hterm : ∀ m ∈ Icc 1 Q₁,
        ‖Matrix.toEuclideanLin (completeWeilMatrix zeroFreeLogProfile c N)
            (normalizedRamanujanHorizonVector m N) -
          completedConductorEnergy zeroFreeLogProfile c m •
            normalizedRamanujanHorizonVector m N‖ ^ 2 ≤ K_res * (Q₁ : ℝ) ^ 4 * rate := by
      intro m hm
      have hmQ : (m : ℝ) ≤ Q₁ := by exact_mod_cast (mem_Icc.mp hm).2
      exact (hres_m m hm).trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg m) hmQ 4) hK_res.le) hrate0)
    have hsum := sum_le_sum hterm
    rw [sum_const, nsmul_eq_mul, Nat.card_Icc, Nat.add_sub_cancel] at hsum
    exact (hsum.trans_eq (by ring : (Q₁ : ℝ) * (K_res * (Q₁ : ℝ) ^ 4 * rate) =
      K_res * (Q₁ : ℝ) ^ 5 * rate)).trans hres_sum_bound
  have hfloor : ∀ m ∈ Icc 1 Q₁,
      1 / T ^ 7 ≤ completedConductorEnergy zeroFreeLogProfile c m := by
    intro m hm
    have hTp : T ≤ T ^ 7 := by
      simpa only [pow_one] using pow_le_pow_right₀ hT1 (by norm_num : 1 ≤ 7)
    have hcontrol0 : 0 < logarithmicSpectralControl logarithmicReserveRate c := Real.exp_pos _
    calc
      1 / T ^ 7 ≤ 1 / T := div_le_div_of_nonneg_left zero_le_one hT0 hTp
      _ ≤ (logarithmicSpectralControl logarithmicReserveRate c)⁻¹ := by
        simpa only [one_div] using div_le_div_of_nonneg_left zero_le_one hcontrol0 hcontrol
      _ ≤ zeroFreeLogConductorFloor c := hrecip.2
      _ ≤ _ := hfloorc m (mem_Icc.mp hm).1
  apply matrix_posDef_of_uniform_conductor_budget
    (R := Q₁) (Q := Q₁) (rate := rate) (e := 1 / T ^ 7)
    (completeWeilMatrix_isHermitian zeroFreeLogProfile c N)
    (completedConductorEnergy zeroFreeLogProfile c)
    (by positivity) hK_res hrate0 le_rfl hQ2 hQ4_N hfloor
  · intro x hx hneg
    have hxE : completeWeilEnergy zeroFreeLogProfile c N x ≤ 0 := hneg
    apply exists_raw_approx_of_starProjection_sq_le hN2 x
    by_contra hdist_not
    have hdist : 1 / 4 < ‖x - (conductorSubspace Q₁ N).starProjection x‖ ^ 2 :=
      lt_of_not_ge hdist_not
    obtain ⟨zHat, hz_orth, hz_norm, hz_energy⟩ :=
      low_band_decoupling_unit_orthogonal hQ2 hQQ_N hlog18_Q hc1 hres_sum_Q hgram
        hx hxE hdist
    have hR'_conds : ∀ {R' : ℕ}, Q₁ ≤ R' → Real.log (R' : ℝ) ≤ C_R * T ^ 16 + Real.log (Q₁ : ℝ) →
        R' ^ 6 ≤ N ∧
        18 * (1 + Real.log (R' : ℝ)) ≤ Real.log (N : ℝ) ∧
        ((R' * R' : ℕ) + 1 : ℝ) * (linearNearRowRadius c + 1) ≤ (N : ℝ) ∧
        ((R' * R' : ℕ) + 1 : ℝ) * (c * Real.exp 1 + 1) ≤ (N : ℝ) ∧
        (1 + Real.log (R' : ℝ)) / Real.sqrt (Real.log (N : ℝ)) ≤ 1 ∧
        (1 + Real.log (R' : ℝ)) ^ 2 / Real.sqrt (Real.log (N : ℝ)) ≤ 1 ∧
        (R' : ℝ) * Real.sqrt (Real.log (N : ℝ) / (N : ℝ)) ≤ 1 := by
      intro R' hQR' hR'_log
      obtain ⟨_, _, h1, h2, h3, h4, h5, h6, h7, _⟩ :=
        rpow_horizon_L_smallness_bounds_of_le_envelope hα128 hqmax hν hν1000 hsep hN1 hQ2 hQR' hc1 hcT hC_R hC_small hH_res
          hL2000 hHL hLX hL45 hCR_L hCs_L hQ_le hQ_quarter (le_rfl : T ≤ L ^ α) hR'_log
      exact ⟨h1, h2, h3, h4, h5, h6, h7⟩
    obtain ⟨R', hQR', hR'_log, u, hu_mem, hu_orthQ, hu_sq_ge, hu_le1, hu_energy⟩ :=
      hsuppc T hcT hcontrol hQ2 hHN hw1 hR'_conds hz_orth hz_norm hz_energy
    obtain ⟨_, hlog36_R', hR6N, _, hRNT_lin, _, _, _, _, hsum_small⟩ :=
      rpow_horizon_L_smallness_bounds_of_le_envelope hα128 hqmax hν hν1000 hsep hN1 hQ2 hQR' hc1 hcT hC_R hC_small hH_res
        hL2000 hHL hLX hL45 hCR_L hCs_L hQ_le hQ_quarter (le_rfl : T ≤ L ^ α) hR'_log
    have hlb := hcoerc hQ2 hQR' hR6N hlog36_R' hc1 hcL hw1 hradN hRNT_lin
      hsum_small hu_mem hu_orthQ hu_sq_ge hu_le1
    linarith only [hu_energy, hlb, hcoerc_gap]
  · intro m hm
    exact hres_m m hm
  · exact hbudget

/-- A fixed smooth zero-free logarithmic profile is positive uniformly below a critical multiple. -/
theorem exists_zeroFreeLogProfile_completeWeilMatrix_posDef_critical_overlap :
    ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c → c ≤ ε * dcScale N →
      (completeWeilMatrix zeroFreeLogProfile c N).PosDef := by
  obtain ⟨A, hlarge⟩ := exists_zeroFreeLogProfile_positive_power_budget
  let K := max 1 (max A (Real.exp 1))
  have hK : 1 ≤ K := le_max_left _ _
  have hbounded := eventually_noRealZero_completeWeilMatrix_posDef_uniform_overlap
    smooth_profile zeroFreeLogProfile_eq_zero paperFT_zeroFreeLogProfile_ne_zero hK
  let ε := (1 / 256 : ℝ) / (4 * logarithmicReserveRate)
  refine ⟨ε, by dsimp only [ε]; exact div_pos (by norm_num) (by have := logarithmicReserveRate_pos; positivity), ?_⟩
  filter_upwards [hlarge, hbounded,
    eventually_logarithmicSpectralControl_le_log_rpow logarithmicReserveRate_pos
      (by norm_num : (0 : ℝ) < 1 / 256)] with N hlargeN hboundedN hbudgetN
  intro c hc hcup
  by_cases hcK : c ≤ K
  · exact hboundedN c hc hcK
  · have hKc := (lt_of_not_ge hcK).le
    have hAc : A ≤ c := (le_max_left A (Real.exp 1)).trans ((le_max_right 1 _).trans hKc)
    have hec : Real.exp 1 ≤ c := (le_max_right A (Real.exp 1)).trans ((le_max_right 1 _).trans hKc)
    exact hlargeN c hAc (hbudgetN c hec hcup)

/-- The same rough regime reaches a positive multiple of the exact sinc critical overlap. -/
theorem exists_zeroFreeLogProfile_completeWeilMatrix_posDef_sincCritical_overlap :
    ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c →
      c ≤ ε * sincCriticalOverlap N → (completeWeilMatrix zeroFreeLogProfile c N).PosDef := by
  obtain ⟨ε, hε, hpos⟩ := exists_zeroFreeLogProfile_completeWeilMatrix_posDef_critical_overlap
  have hD : 0 < 96 * Real.exp 1 := by positivity
  refine ⟨ε / (96 * Real.exp 1), div_pos hε hD, ?_⟩
  filter_upwards [hpos, eventually_sincCriticalOverlap_le] with N hN hcritical
  intro c hc hcup
  apply hN c hc
  calc
    c ≤ (ε / (96 * Real.exp 1)) * sincCriticalOverlap N := hcup
    _ ≤ (ε / (96 * Real.exp 1)) * (96 * Real.exp 1 * dcScale N) :=
      mul_le_mul_of_nonneg_left hcritical.1 (div_pos hε hD).le
    _ = ε * dcScale N := by
      rw [← mul_assoc, div_mul_cancel₀ ε hD.ne']

end GaloisForLFunctions.TransMetzlerWeilPositivity

#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.exists_zeroFreeLogProfile_positive_power_budget
#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.exists_zeroFreeLogProfile_completeWeilMatrix_posDef_critical_overlap
#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.exists_zeroFreeLogProfile_completeWeilMatrix_posDef_sincCritical_overlap
