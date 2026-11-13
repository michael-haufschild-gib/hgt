import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.CriticalCausalEnergyTranslation
import GaloisForLFunctions.HTGeometry.TwoModeSquareCombination

/-!
# Stability of the critical half-line energy

Exponential confinement absorbs the lower-order prime and pole forms.
One-sided smooth recovery and compactness identify zero-energy limits.
These estimates control variations transverse to the
unique ground-state line.
-/

noncomputable section
open MeasureTheory Set Filter Topology Zeta23
open _root_.RHTower
namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open CriticalArithmeticCorrelationTheory ArithmeticCastelnuovoSeveri
  ArithmeticPositivityTheory SpacingScaleHarmonicAnalysis WindowTowerOfSpecZ
  CohomologyOfWindowsOfSpecZ


/-- The measurable prime form is bounded by the lower exponential norm. -/
theorem CriticalHalfLineEnergyDomain.prime_bound {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) :
    |primeSum F| ≤ 2 * vonMangoldtThreeHalvesMass * exponentialSourceMass F := by
  have hz : WeightedTwo (fun _ : ℝ => (0 : ℝ)) :=
    ⟨aestronglyMeasurable_const, by simp only [mul_zero, zero_pow two_ne_zero]; exact integrable_zero _ _ _⟩
  have h := abs_primeSum_sub_le hF.weighted hz
  have hp : primeSum (fun _ : ℝ => (0 : ℝ)) = 0 := by simp [primeSum]
  have hs : exponentialSourceMass (fun _ : ℝ => (0 : ℝ)) = 0 := by
    simp [exponentialSourceMass]
  rw [hp, hs, sub_zero, Real.sqrt_zero, add_zero,
    show (fun t => F t - 0) = F from funext fun t => sub_zero _] at h
  rw [Real.mul_self_sqrt (exponentialSourceMass_nonneg F)] at h
  exact h

/-- Weighted Cauchy–Schwarz controls the negative polar square. -/
theorem CriticalHalfLineEnergyDomain.sinh_bound {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) :
    sinhHalfMoment F ^ 2 ≤ exponentialSourceMass F * (∫ u : ℝ, Real.exp (-|u|)) := by
  have h := (abs_integral_mul_kernel_le hF.weighted
    (Real.continuous_sinh.comp (continuous_id.div_const 2)) abs_sinh_half_le_exp).2
  have hi : 0 ≤ ∫ u : ℝ, Real.exp (-|u|) := integral_nonneg fun u => (Real.exp_pos _).le
  have hh := pow_le_pow_left₀ (abs_nonneg _) h 2
  simpa only [sq_abs, mul_pow, Real.sq_sqrt (exponentialSourceMass_nonneg F),
    Real.sq_sqrt hi, sinhHalfMoment, Function.comp_apply, id_eq] using hh

/-- The global Gamma lower bound and Plancherel control its negative part. -/
theorem CriticalHalfLineEnergyDomain.arch_lower {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) :
    -(10 + Real.log 4) * (∫ u, F u ^ 2) ≤ archForm F := by
  have hi : Integrable (cx F) := hF.integrable.ofReal (𝕜 := ℂ)
  have hc : MemLp (cx F) 2 volume := by
    apply (memLp_two_iff_integrable_sq_norm hi.aestronglyMeasurable).mpr
    simpa only [cx, Complex.norm_real, Real.norm_eq_abs, sq_abs] using hF.sq
  have hb := _root_.RHTower.KernelStrip.integrable_norm_sq_paperFT
    hi hc
  have hpl := _root_.RHTower.KernelStrip.integral_norm_sq_paperFT_of_memLp
    hi hc
  simp only [cx, Complex.norm_real, Real.norm_eq_abs, sq_abs] at hpl
  have hle : (∫ r : ℝ, -(10 + Real.log 4) * ‖paperFT (cx F) r‖ ^ 2) ≤
      ∫ r : ℝ, ‖paperFT (cx F) r‖ ^ 2 * EF.gammaBracket r := by
    apply integral_mono (hb.const_mul _) hF.gamma
    intro r
    have hγ := _root_.RHTower.WeilWorkPBAP.joint_gamma_lower_log r
    have hl := Real.log_nonneg (show 1 ≤ 2 + |r| by linarith only [abs_nonneg r])
    have hlow : -(10 + Real.log 4) ≤ EF.gammaBracket r := by linarith only [hγ, hl]
    simpa only [mul_comm (-(10 + Real.log 4))] using
      mul_le_mul_of_nonneg_left hlow (sq_nonneg ‖paperFT (cx F) r‖)
  rw [integral_const_mul, hpl] at hle
  have hp := mul_le_mul_of_nonneg_left hle (by positivity : 0 ≤ 1 / (2 * Real.pi))
  have he : (1 / (2 * Real.pi)) * (-(10 + Real.log 4) *
      (2 * Real.pi * ∫ u, F u ^ 2)) = -(10 + Real.log 4) * ∫ u, F u ^ 2 := by
    field_simp
  rw [he] at hp
  exact hp

/-- Exponential confinement controls the eighth mass up to an ordinary square-mass remainder. -/
theorem criticalHalfLineFullEnergy_coercive_remainder {R : ℝ} (hR : 0 < R) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ {F : ℝ → ℝ}, CriticalHalfLineEnergyDomain F →
      (criticalAliasCoefficient R / 2) * (∫ u, F u ^ 2 * Real.exp (-(8 * u))) ≤
        criticalHalfLineFullEnergy R F + B * ∫ u, F u ^ 2 := by
  let J : ℝ := ∫ u : ℝ, Real.exp (-|u|)
  let C : ℝ := 2 * vonMangoldtThreeHalvesMass + 2 * J
  let D : ℝ := 10 + Real.log 4
  have hJ : 0 ≤ J := integral_nonneg fun u => (Real.exp_pos _).le
  have hC : 0 ≤ C := add_nonneg
    (mul_nonneg (by norm_num) vonMangoldtThreeHalvesMass_nonneg)
    (mul_nonneg (by norm_num) hJ)
  have hD : 0 ≤ D := by
    have h := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
    dsimp only [D]
    linarith only [h]
  have ha := criticalAliasCoefficient_positive hR
  have hl : Tendsto (fun Y : ℝ => C * Real.exp (-(6 * Y))) atTop (𝓝 0) := by
    have ht : Tendsto (fun Y : ℝ => 6 * Y) atTop atTop :=
      tendsto_id.const_mul_atTop (by norm_num)
    simpa only [Function.comp_def, mul_zero] using
      (Real.tendsto_exp_neg_atTop_nhds_zero.comp ht).const_mul C
  obtain ⟨Y, hsmall, hY⟩ :=
    ((hl.eventually (gt_mem_nhds (half_pos ha))).and (eventually_ge_atTop (0 : ℝ))).exists
  refine ⟨D + C * Real.exp (2 * Y), add_nonneg hD (mul_nonneg hC (Real.exp_pos _).le), ?_⟩
  intro F hF
  have hp := (le_abs_self (primeSum F)).trans hF.prime_bound
  have hs := hF.sinh_bound
  have hg := hF.arch_lower
  have hw := (exponentialSourceMass_le_of_support hY hF.meas.aestronglyMeasurable
    hF.sq hF.exponential (Eventually.of_forall fun u hu =>
      hF.support u (hY.trans hu.le))).2
  have hcw := mul_le_mul_of_nonneg_left hw hC
  have hW : 0 ≤ ∫ u, F u ^ 2 * Real.exp (-(8 * u)) :=
    integral_nonneg fun u => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
  have he := mul_le_mul_of_nonneg_right hsmall.le hW
  dsimp only [criticalHalfLineFullEnergy]
  rw [halfLineExpMass_eq_full hF.support]
  dsimp only [C, D, J] at hcw he ⊢
  nlinarith only [hp, hs, hg, hcw, he, sq_nonneg (coshHalfMoment F)]

/-- Smooth terminal-window tests belong to the actual half-line domain. -/
theorem criticalHalfLineEnergyDomain_of_window {A : ℝ} {H : ℝ → ℝ}
    (hH : IsWindowTest A H) : CriticalHalfLineEnergyDomain H := by
  have hs : HasCompactSupport (fun u => H u ^ 2) := by
    have heq : (fun u => H u ^ 2) = H * H := by
      funext u
      exact pow_two (H u)
    rw [heq]
    exact hH.hasCompactSupport.mul_right
  have hz (u : ℝ) (hu : 0 < u) : H u = 0 :=
    hH.vanish u (fun h => (not_lt_of_ge h.2) hu)
  have hz0 : H 0 = 0 := by
    have ht := hH.continuous.continuousAt.tendsto.comp
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    have he : ∀ k : ℕ, H (1 / ((k : ℝ) + 1)) = 0 := fun k => hz _ (by positivity)
    have ht0 : Tendsto (fun k : ℕ => H (1 / ((k : ℝ) + 1))) atTop (𝓝 0) := by
      simpa only [he] using (tendsto_const_nhds (x := (0 : ℝ)))
    exact tendsto_nhds_unique ht ht0
  refine ⟨hH.continuous.measurable,
    hH.continuous.integrable_of_hasCompactSupport hH.hasCompactSupport,
    (hH.continuous.pow 2).integrable_of_hasCompactSupport hs,
    ((hH.continuous.pow 2).mul (by fun_prop)).integrable_of_hasCompactSupport hs.mul_right,
    ?_, ?_⟩
  · intro u hu
    rcases eq_or_lt_of_le hu with rfl | hlt
    · exact hz0
    · exact hz u hlt
  · exact _root_.RHTower.integrable_normSq_paperFT_mul_gammaBracket
      hH.contDiff hH.hasCompactSupport

/-- One-sided smooth recovery preserves square mass and approximates the full energy from above. -/
theorem exists_window_energy_recovery {R : ℝ} (hR : 0 < R)
    {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    (hmass : (∫ u, F u ^ 2) ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ (A : ℝ) (H : ℝ → ℝ), 0 ≤ A ∧ IsWindowTest A H ∧
      (∫ u, H u ^ 2) ≤ ∫ u, F u ^ 2 ∧
      (∫ u, (H u - F u) ^ 2) < ε ∧
      (∫ u, H u ^ 2 * Real.exp (-(8 * u))) ≤
        2 * (∫ u, F u ^ 2 * Real.exp (-(8 * u))) ∧
      criticalHalfLineFullEnergy R H < criticalHalfLineFullEnergy R F + ε := by
  let W : ℝ := ∫ u, F u ^ 2 * Real.exp (-(8 * u))
  have hW : 0 ≤ W := integral_nonneg fun u => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
  have htrunc (T : ℝ) (hT : Real.exp factorialSpanGammaOffset ≤ T) :
      truncatedWeilForm F T + criticalAliasCoefficient R *
        (∫ u in Iio 0, F u ^ 2 * Real.exp (-(8 * u))) ≤ criticalHalfLineFullEnergy R F := by
    have h := lowGammaForm_le_archForm_of_integrable hF.gamma hT
    dsimp only [truncatedWeilForm, criticalHalfLineFullEnergy]
    linarith only [h]
  obtain ⟨C, A, H, hC, hwin, hnorm, hexp, hL2, hd, harch⟩ :=
    exists_window_sequence_of_gammaLiminf_bound hF.meas hF.integrable hF.sq hF.exponential
      le_rfl hF.support htrunc
  have hH8 (k : ℕ) : (∫ u, H k u ^ 2 * Real.exp (-(8 * u))) ≤
      Real.exp 8 * W := by
    have he : (∫ u, H k u ^ 2 * Real.exp (-(8 * u))) = exponentialMass 8 (H k) :=
      integral_congr_ae (Eventually.of_forall fun u => mul_comm _ _)
    have hk : 8 / ((k : ℝ) + 1) ≤ 8 := by
      apply (div_le_iff₀ (by positivity : 0 < (k : ℝ) + 1)).mpr
      nlinarith only [Nat.cast_nonneg (α := ℝ) k]
    rw [he]
    have hb := hexp k
    rw [halfLineExpMass_eq_full hF.support] at hb
    exact hb.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hk) hW)
  have hHsupport (k : ℕ) (u : ℝ) (hu : 1 < u) : H k u = 0 :=
    (hwin k).2.vanish u (fun h => by linarith only [hu, h.2])
  obtain ⟨hP, hCos, hSin⟩ := tendsto_prime_and_pole_of_strong_limit
    (fun k => (hwin k).2.continuous) (fun k => (hwin k).2.hasCompactSupport)
    hF.weighted (fun k => (hnorm k).trans hmass) hH8
    (Eventually.of_forall hHsupport) hd
  have harch' (k : ℕ) : archForm (H k) ≤ archForm F + C / ((k : ℝ) + 1) := by
    have h := harch k
    dsimp only [criticalHalfLineFullEnergy] at h
    linarith only [h]
  let U : ℕ → ℝ := fun k => archForm F + C / ((k : ℝ) + 1) - primeSum (H k) +
    (2 * coshHalfMoment (H k) ^ 2 - 2 * sinhHalfMoment (H k) ^ 2) +
    criticalAliasCoefficient R * (Real.exp (8 / ((k : ℝ) + 1)) * W)
  have hU (k : ℕ) : criticalHalfLineFullEnergy R (H k) ≤ U k := by
    have hb := hexp k
    rw [halfLineExpMass_eq_full hF.support] at hb
    have he : exponentialMass 8 (H k) = ∫ u, H k u ^ 2 * Real.exp (-(8 * u)) :=
      integral_congr_ae (Eventually.of_forall fun u => mul_comm _ _)
    rw [he] at hb
    have hbd := mul_le_mul_of_nonneg_left hb (criticalAliasCoefficient_positive hR).le
    dsimp only [criticalHalfLineFullEnergy, U]
    rw [halfLineExpMass_eq_full (criticalHalfLineEnergyDomain_of_window (hwin k).2).support]
    linarith only [harch' k, hbd]
  have hδ : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hCδ : Tendsto (fun k : ℕ => C / ((k : ℝ) + 1)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, one_mul, mul_zero] using hδ.const_mul C
  have h8δ : Tendsto (fun k : ℕ => 8 / ((k : ℝ) + 1)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, one_mul, mul_zero] using hδ.const_mul (8 : ℝ)
  have hexplim : Tendsto (fun k : ℕ => Real.exp (8 / ((k : ℝ) + 1))) atTop (𝓝 1) := by
    simpa only [Real.exp_zero, Function.comp_def] using (Real.continuous_exp.tendsto 0).comp h8δ
  have hlim : Tendsto U atTop (𝓝 (criticalHalfLineFullEnergy R F)) := by
    have h := ((((tendsto_const_nhds (x := archForm F)).add hCδ).sub hP).add
      (((hCos.pow 2).const_mul 2).sub ((hSin.pow 2).const_mul 2))).add
        ((hexplim.mul_const W).const_mul (criticalAliasCoefficient R))
    simpa only [add_zero, one_mul, criticalHalfLineFullEnergy,
      halfLineExpMass_eq_full hF.support, U, W] using h
  obtain ⟨k, hkL2, hkE, hk8⟩ := ((hL2.eventually (gt_mem_nhds hε)).and
    ((hlim.eventually (gt_mem_nhds (lt_add_of_pos_right _ hε))).and
      (hexplim.eventually (ge_mem_nhds (by norm_num : (1 : ℝ) < 2))))).exists
  refine ⟨A k, H k, (hwin k).1, (hwin k).2, hnorm k, hkL2, ?_, (hU k).trans_lt hkE⟩
  have hb := hexp k
  rw [halfLineExpMass_eq_full hF.support] at hb
  have he : (∫ u, H k u ^ 2 * Real.exp (-(8 * u))) = exponentialMass 8 (H k) :=
    integral_congr_ae (Eventually.of_forall fun u => mul_comm _ _)
  rw [he]
  exact hb.trans (mul_le_mul_of_nonneg_right hk8 hW)

/-- Fatou transfers a convergent upper bound without assuming convergence of weighted masses. -/
private theorem weighted_sq_le_of_L1_tendsto_bound {U : ℕ → ℝ → ℝ} {F w : ℝ → ℝ}
    (hU : ∀ n, Integrable (U n)) (hF : Integrable F)
    (hL1 : Tendsto (fun n => ∫ u, ‖U n u - F u‖) atTop (𝓝 0))
    (hw : Continuous w) (hUw : ∀ n, MemLp (fun u => w u * U n u) 2 volume)
    {b : ℕ → ℝ} {B : ℝ} (hb : Tendsto b atTop (𝓝 B))
    (hbound : ∀ n, (∫ u, (w u * U n u) ^ 2) ≤ b n) :
    (∫ u, (w u * F u) ^ 2) ≤ B := by
  have hB : 0 ≤ B := ge_of_tendsto hb (Eventually.of_forall fun n =>
    (integral_nonneg fun u : ℝ => sq_nonneg (w u * U n u)).trans (hbound n))
  by_contra hnot
  have hlt : B < ∫ u, (w u * F u) ^ 2 := lt_of_not_ge hnot
  let M : ℝ := (B + (∫ u, (w u * F u) ^ 2)) / 2
  have hBM : B < M := by dsimp only [M]; linarith only [hlt]
  have hMF : M < ∫ u, (w u * F u) ^ 2 := by dsimp only [M]; linarith only [hlt]
  have hM : 0 ≤ M := hB.trans hBM.le
  obtain ⟨s, hs, hae⟩ := exists_seq_ae_tendsto_of_L1 hU hF hL1
  have hbound' : ∀ᶠ n in atTop,
      eLpNorm (fun u => w u * U (s n) u) 2 volume ≤ ENNReal.ofReal (Real.sqrt M) := by
    filter_upwards [hs.eventually (hb.eventually (ge_mem_nhds hBM))] with n hn
    exact eLpNorm_two_le_of_integral_sq_le (hUw (s n)) ((hbound (s n)).trans hn)
  have hae' : ∀ᵐ u, Tendsto (fun n => w u * U (s n) u) atTop (𝓝 (w u * F u)) := by
    filter_upwards [hae] with u hu
    exact hu.const_mul _
  have he := Lp.eLpNorm_le_of_ae_tendsto hbound'
    (fun n => (hUw (s n)).aestronglyMeasurable) hae'
  have hlim := (integral_sq_le_of_eLpNorm_two_le
    (hw.aestronglyMeasurable.mul hF.aestronglyMeasurable) hM he).2
  exact (not_lt_of_ge hlim) hMF

/-- A normalized smooth sequence of vanishing critical energy has an actual ground-state limit. -/
theorem exists_groundState_of_smooth_energy_limit {R : ℝ} (hR : 0 < R)
    {U : ℕ → ℝ → ℝ} (hUd : ∀ n, ContDiff ℝ 2 (U n))
    (hUc : ∀ n, HasCompactSupport (U n))
    (hUs : ∀ n u, 0 ≤ u → U n u = 0)
    (hmass : ∀ n, (∫ u, U n u ^ 2) ≤ 1)
    (hmasslim : Tendsto (fun n => ∫ u, U n u ^ 2) atTop (𝓝 1))
    {M : ℝ} (hM : 0 ≤ M)
    (hweight : ∀ n, (∫ u, U n u ^ 2 * Real.exp (-(8 * u))) ≤ M)
    (hEbound : ∀ n, criticalHalfLineFullEnergy R (U n) ≤ 2)
    (hElim : Tendsto (fun n => criticalHalfLineFullEnergy R (U n)) atTop (𝓝 0)) :
    ∃ (F : ℝ → ℝ) (s : ℕ → ℕ), StrictMono s ∧ IsCriticalHalfLineGroundState R F ∧
      Tendsto (fun n => ∫ u, (U (s n) u - F u) ^ 2) atTop (𝓝 0) ∧
      Tendsto (fun n => ∫ u, ‖U (s n) u - F u‖) atTop (𝓝 0) := by
  have ha := criticalAliasCoefficient_positive hR
  have hUi (n : ℕ) : Integrable (U n) :=
    (hUd n).continuous.integrable_of_hasCompactSupport (hUc n)
  have hweil (n : ℕ) : weilQuad (U n) ≤ 2 := by
    have h := hEbound n
    rw [criticalHalfLineFullEnergy, ← weilQuad_eq_arch_sub_prime_add_pole (hUd n) (hUc n)] at h
    have hp : 0 ≤ criticalAliasCoefficient R *
        ∫ u in Iio 0, U n u ^ 2 * Real.exp (-(8 * u)) :=
      mul_nonneg ha.le (integral_nonneg fun u => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)
    linarith only [h, hp]
  obtain ⟨F, s, hs, hFm, hFi, hF2, hmassF, hF8, hweightF, hFs, hL2, hL1, hnormlim⟩ :=
    exists_strong_negative_limit_of_bounded_weilQuad hUd hUc hmass hM hweight
      (fun n u hu => hUs n u (by
        have hp : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        exact (hp.trans hu).le))
      hweil
  have hnorm : (∫ u, F u ^ 2) = 1 :=
    tendsto_nhds_unique hnormlim (hmasslim.comp hs.tendsto_atTop)
  have hFW : WeightedTwo F := (exponentialSourceMass_le_of_support (Y := 0) le_rfl
    hFm.aestronglyMeasurable hF2 hF8 (Eventually.of_forall fun u hu => hFs u hu.le)).1
  have hsup : ∀ᶠ n in atTop, ∀ u, 1 < u → U (s n) u = 0 :=
    Eventually.of_forall fun n u hu => hUs _ u (zero_le_one.trans hu.le)
  have hd := tendsto_exponentialSourceMass_sub
    (fun n => (hUd (s n)).continuous) (fun n => hUc (s n))
    hFm.aestronglyMeasurable hF2 hF8 (fun n => hweight (s n)) hsup
    (Eventually.of_forall fun u hu => hFs u (zero_le_one.trans hu.le))
    (fun ε hε => hL2.eventually (ge_mem_nhds hε))
  obtain ⟨hP, hC, hS⟩ := tendsto_prime_and_pole_of_strong_limit
    (fun n => (hUd (s n)).continuous) (fun n => hUc (s n)) hFW
    (fun n => hmass (s n)) (fun n => hweight (s n)) hsup hd
  refine ⟨F, s, hs, ⟨hFm, hFi, hF2, hnorm, hF8, hFs, ?_⟩, hL2, hL1⟩
  intro T hT
  have hX : Tendsto (fun n => truncatedWeilForm (U (s n)) T) atTop
      (𝓝 (truncatedWeilForm F T)) :=
    ((tendsto_lowGammaForm (fun n => hUi (s n)) hFi hL1 T).sub hP).add
      (((hC.pow 2).const_mul 2).sub ((hS.pow 2).const_mul 2))
  let b : ℕ → ℝ := fun n =>
    (criticalHalfLineFullEnergy R (U (s n)) - truncatedWeilForm (U (s n)) T) /
      criticalAliasCoefficient R
  have hb : Tendsto b atTop (𝓝 (-truncatedWeilForm F T / criticalAliasCoefficient R)) := by
    simpa only [zero_sub, b, Function.comp_apply] using ((hElim.comp hs.tendsto_atTop).sub hX).div_const
      (criticalAliasCoefficient R)
  let w : ℝ → ℝ := fun u => Real.exp (-(4 * u))
  have hw : Continuous w := by fun_prop
  have hsq (u x : ℝ) : (w u * x) ^ 2 = x ^ 2 * Real.exp (-(8 * u)) := by
    dsimp only [w]
    rw [mul_pow, ← Real.exp_nat_mul]
    rw [mul_comm]
    congr 2
    push_cast
    ring
  have hbound (n : ℕ) : (∫ u, (w u * U (s n) u) ^ 2) ≤ b n := by
    simp_rw [hsq]
    dsimp only [b]
    apply (le_div_iff₀ ha).mpr
    have ht := truncatedWeilForm_le_weilQuad (hUd (s n)) (hUc (s n)) hT
    dsimp only [criticalHalfLineFullEnergy, truncatedWeilForm] at ht ⊢
    rw [halfLineExpMass_eq_full (hUs (s n))]
    rw [weilQuad_eq_arch_sub_prime_add_pole (hUd (s n)) (hUc (s n))] at ht
    linarith only [ht]
  have hlim := weighted_sq_le_of_L1_tendsto_bound (fun n => hUi (s n)) hFi hL1 hw
    (fun n => (hw.mul (hUd (s n)).continuous).memLp_of_hasCompactSupport (hUc (s n)).mul_left)
    hb hbound
  simp_rw [hsq] at hlim
  have hfin := (le_div_iff₀ ha).mp hlim
  rw [halfLineExpMass_eq_full hFs]
  linarith only [hfin]


private theorem domain_sub {F G : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    (hG : CriticalHalfLineEnergyDomain G) : CriticalHalfLineEnergyDomain (fun u => F u - G u) := by
  simpa only [neg_one_mul, sub_eq_add_neg] using hF.add_const_mul hG (-1)

private theorem pair_integrable {F G : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    (hG : CriticalHalfLineEnergyDomain G) : Integrable (fun u => F u * G u) :=
  HTGeometry.integrable_mul_of_sq_integrable hF.meas.aestronglyMeasurable
    hG.meas.aestronglyMeasurable hF.sq hG.sq

private theorem tendsto_pair_difference {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    {U V : ℕ → ℝ → ℝ} (hU : ∀ n, CriticalHalfLineEnergyDomain (U n))
    (hV : ∀ n, CriticalHalfLineEnergyDomain (V n))
    (hd : Tendsto (fun n => ∫ u, (U n u - V n u) ^ 2) atTop (𝓝 0)) :
    Tendsto (fun n => (∫ u, F u * U n u) - ∫ u, F u * V n u) atTop (𝓝 0) := by
  have hdiff (n : ℕ) := domain_sub (hU n) (hV n)
  have hs : Tendsto (fun n => Real.sqrt ((∫ u, F u ^ 2) *
      ∫ u, (U n u - V n u) ^ 2)) atTop (𝓝 0) := by
    simpa only [mul_zero, Real.sqrt_zero] using (hd.const_mul (∫ u, F u ^ 2)).sqrt
  have hp : Tendsto (fun n => ∫ u, F u * (U n u - V n u)) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun n => ?_) hs
    simpa only [Real.norm_eq_abs] using HTGeometry.abs_integral_mul_le_sqrt
      hF.meas.aestronglyMeasurable (hdiff n).meas.aestronglyMeasurable
      hF.sq (hdiff n).sq
  have he (n : ℕ) : (∫ u, F u * (U n u - V n u)) =
      (∫ u, F u * U n u) - ∫ u, F u * V n u := by
    simp_rw [mul_sub]
    exact integral_sub (pair_integrable hF (hU n)) (pair_integrable hF (hV n))
  simpa only [he] using hp

/-- The ordinary square norm has a positive gap transverse to the actual ground state. -/
theorem criticalHalfLineFullEnergy_transverse_L2_gap
    {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ {G : ℝ → ℝ}, CriticalHalfLineEnergyDomain G →
      (∫ u, F u * G u) = 0 → δ * (∫ u, G u ^ 2) ≤ criticalHalfLineFullEnergy W₀ G := by
  by_contra hnot
  push Not at hnot
  have hdF := criticalHalfLineEnergyDomain_of_groundState hF
  let e : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hepos (n : ℕ) : 0 < e n := by dsimp only [e]; positivity
  have hele (n : ℕ) : e n ≤ 1 := by
    dsimp only [e]
    exact div_le_one_of_le₀ (by linarith only [Nat.cast_nonneg (α := ℝ) n]) (by positivity)
  have helim : Tendsto e atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hnormalized (n : ℕ) : ∃ G : ℝ → ℝ, CriticalHalfLineEnergyDomain G ∧
      (∫ u, G u ^ 2) = 1 ∧ (∫ u, F u * G u) = 0 ∧
      criticalHalfLineFullEnergy W₀ G < e n := by
    obtain ⟨G, hdG, horth, hE⟩ := hnot (e n) (hepos n)
    have hE0 := criticalHalfLineFullEnergy_nonneg_at_windowThreshold hW ht hdG
    let m : ℝ := ∫ u, G u ^ 2
    have hm : 0 < m := by
      by_contra hn
      have hmn : m = 0 := le_antisymm (not_lt.mp hn) (integral_nonneg fun u => sq_nonneg _)
      change criticalHalfLineFullEnergy W₀ G < e n * m at hE
      rw [hmn, mul_zero] at hE
      exact (not_lt_of_ge hE0) hE
    let c : ℝ := (Real.sqrt m)⁻¹
    have hc : 0 < c := inv_pos.mpr (Real.sqrt_pos.mpr hm)
    have hcm : c ^ 2 * m = 1 := by
      calc
        _ = c ^ 2 * (Real.sqrt m) ^ 2 := by rw [Real.sq_sqrt hm.le]
        _ = 1 := by
          dsimp only [c]
          rw [inv_pow, inv_mul_cancel₀ (pow_ne_zero 2 (Real.sqrt_pos.mpr hm).ne')]
    refine ⟨fun u => c * G u, hdG.const_mul c, ?_, ?_, ?_⟩
    · simp_rw [mul_pow]
      rw [integral_const_mul]
      exact hcm
    · have heq : (fun u => F u * (c * G u)) = fun u => c * (F u * G u) :=
        funext fun u => by ring
      rw [heq, integral_const_mul, horth, mul_zero]
    · rw [criticalHalfLineFullEnergy_const_mul]
      have hh := mul_lt_mul_of_pos_left hE (sq_pos_of_pos hc)
      have heq : c ^ 2 * (e n * m) = e n := by rw [mul_left_comm, hcm, mul_one]
      exact hh.trans_eq heq
  choose G hdG hnG hoG heG using hnormalized
  obtain ⟨B, hB, hgarding⟩ := criticalHalfLineFullEnergy_coercive_remainder hW
  have ha := criticalAliasCoefficient_positive hW
  let M : ℝ := (1 + B) / (criticalAliasCoefficient W₀ / 2)
  have hM : 0 ≤ M := div_nonneg (by linarith only [hB]) (half_pos ha).le
  have hG8 (n : ℕ) : (∫ u, G n u ^ 2 * Real.exp (-(8 * u))) ≤ M := by
    apply (le_div_iff₀ (half_pos ha)).mpr
    have h := hgarding (hdG n)
    rw [hnG n, mul_one] at h
    nlinarith only [h, (heG n).le, hele n]
  -- Smooth recovery retains normalization and vanishing energy.
  have hrec (n : ℕ) := exists_window_energy_recovery hW (hdG n) (hnG n).le (hepos n)
  choose A H hA hHwin hnH hdH hH8 heH using hrec
  have hDH (n : ℕ) := criticalHalfLineEnergyDomain_of_window (hHwin n)
  have hdiff (n : ℕ) := domain_sub (hDH n) (hdG n)
  have herr : Tendsto (fun n => ∫ u, (H n u - G n u) ^ 2) atTop (𝓝 0) :=
    squeeze_zero (fun n => integral_nonneg fun u => sq_nonneg _) (fun n => (hdH n).le) helim
  have hmasslim : Tendsto (fun n => ∫ u, H n u ^ 2) atTop (𝓝 1) := by
    have h := HTGeometry.tendsto_integral_sq_add_of_tendsto_zero
      (Eventually.of_forall fun n => (hdG n).meas.aestronglyMeasurable)
      (Eventually.of_forall fun n => (hdiff n).meas.aestronglyMeasurable)
      (Eventually.of_forall fun n => (hdG n).sq)
      (Eventually.of_forall fun n => (hdiff n).sq)
      (show Tendsto (fun n => ∫ u, G n u ^ 2) atTop (𝓝 1) by
        simpa only [hnG] using (tendsto_const_nhds (x := (1 : ℝ)))) herr
    exact h.congr fun n => integral_congr_ae (Eventually.of_forall fun u => by congr 1; ring)
  have hEs (n : ℕ) : criticalHalfLineFullEnergy W₀ (H n) ≤ 2 * e n := by
    have hh := heH n
    linarith only [hh, heG n]
  have hElim : Tendsto (fun n => criticalHalfLineFullEnergy W₀ (H n)) atTop (𝓝 0) := by
    have hzero : Tendsto (fun n => 2 * e n) atTop (𝓝 0) := by
      simpa only [mul_zero] using helim.const_mul 2
    exact squeeze_zero (fun n => criticalHalfLineFullEnergy_nonneg_at_windowThreshold hW ht (hDH n))
      hEs hzero
  -- The compact limit is a normalized critical state and remains orthogonal to F.
  obtain ⟨K, s, hs, hK, hL2, _⟩ := exists_groundState_of_smooth_energy_limit hW
    (fun n => (hHwin n).contDiff) (fun n => (hHwin n).hasCompactSupport)
    (fun n => (hDH n).support) (fun n => (hnH n).trans (hnG n).le) hmasslim
    (mul_nonneg (by norm_num) hM)
    (fun n => (hH8 n).trans (mul_le_mul_of_nonneg_left (hG8 n) (by norm_num)))
    (fun n => (hEs n).trans (by nlinarith only [hele n])) hElim
  have hdK := criticalHalfLineEnergyDomain_of_groundState hK
  have hpair0 := tendsto_pair_difference hdF hDH hdG herr
  simp only [hoG, sub_zero] at hpair0
  have hpair := tendsto_pair_difference hdF (fun n => hDH (s n)) (fun _ => hdK) hL2
  have hpairlim := hpair.add_const (∫ u, F u * K u)
  simp only [sub_add_cancel, zero_add] at hpairlim
  have horth : (∫ u, F u * K u) = 0 :=
    tendsto_nhds_unique hpairlim (hpair0.comp hs.tendsto_atTop)
  -- The only normalized critical states are the two signs of F.
  rcases criticalHalfLineGroundState_unique_up_to_sign hW ht hK hF with heq | heq
  · have hm : (∫ u, F u * K u) = ∫ u, F u ^ 2 := by
      apply integral_congr_ae
      filter_upwards [heq] with u hu
      rw [hu, pow_two]
    rw [horth, hF.2.2.2.1] at hm
    norm_num at hm
  · have hm : (∫ u, F u * K u) = -(∫ u, F u ^ 2) := by
      rw [← integral_neg]
      apply integral_congr_ae
      filter_upwards [heq] with u hu
      rw [hu]
      ring
    rw [horth, hF.2.2.2.1] at hm
    norm_num at hm

/-- Critical energy controls the full exponential mass on the ordinary orthogonal complement. -/
theorem criticalHalfLineFullEnergy_transverse_exponential_gap
    {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ {G : ℝ → ℝ}, CriticalHalfLineEnergyDomain G →
      (∫ u, F u * G u) = 0 → γ * (∫ u, G u ^ 2 * Real.exp (-(8 * u))) ≤
        criticalHalfLineFullEnergy W₀ G := by
  obtain ⟨δ, hδ, hgap⟩ := criticalHalfLineFullEnergy_transverse_L2_gap hW ht hF
  obtain ⟨B, hB, hgard⟩ := criticalHalfLineFullEnergy_coercive_remainder hW
  have ha := criticalAliasCoefficient_positive hW
  have hden : 0 < δ + B := add_pos_of_pos_of_nonneg hδ hB
  refine ⟨δ * (criticalAliasCoefficient W₀ / 2) / (δ + B), by positivity, ?_⟩
  intro G hG ho
  have hg := mul_le_mul_of_nonneg_left (hgard hG) hδ.le
  have hl := mul_le_mul_of_nonneg_left (hgap hG ho) hB
  calc
    _ = (δ * (criticalAliasCoefficient W₀ / 2) *
        (∫ u, G u ^ 2 * Real.exp (-(8 * u)))) / (δ + B) := by ring
    _ ≤ _ := (div_le_iff₀ hden).mpr (by nlinarith only [hg, hl])


/-- Remove the ordinary-L² projection onto a normalized ground state. -/
def criticalHalfLineNeutralPart (F G : ℝ → ℝ) : ℝ → ℝ :=
  fun u => G u - (∫ v, F v * G v) * F u

theorem CriticalHalfLineEnergyDomain.neutralPart {F G : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (hG : CriticalHalfLineEnergyDomain G) :
    CriticalHalfLineEnergyDomain (criticalHalfLineNeutralPart F G) := by
  change CriticalHalfLineEnergyDomain (fun u => G u - (∫ v, F v * G v) * F u)
  simpa only [criticalHalfLineNeutralPart, neg_mul, sub_eq_add_neg] using
    hG.add_const_mul hF (-(∫ v, F v * G v))

theorem criticalHalfLineNeutralPart_orthogonal {W₀ : ℝ} {F G : ℝ → ℝ}
    (hF : IsCriticalHalfLineGroundState W₀ F) (hG : CriticalHalfLineEnergyDomain G) :
    (∫ u, F u * criticalHalfLineNeutralPart F G u) = 0 := by
  have hdF := criticalHalfLineEnergyDomain_of_groundState hF
  have heq : (fun u => F u * criticalHalfLineNeutralPart F G u) =
      fun u => F u * G u - (∫ v, F v * G v) * F u ^ 2 := by
    funext u
    dsimp only [criticalHalfLineNeutralPart]
    ring
  rw [heq, integral_sub (pair_integrable hdF hG) (hdF.sq.const_mul _),
    integral_const_mul, hF.2.2.2.1, mul_one, sub_self]

/-- Removing the ground component preserves every bit of critical energy. -/
theorem criticalHalfLineFullEnergy_neutralPart
    {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F G : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F)
    (hG : CriticalHalfLineEnergyDomain G) :
    criticalHalfLineFullEnergy W₀ (criticalHalfLineNeutralPart F G) =
      criticalHalfLineFullEnergy W₀ G := by
  have hdF := criticalHalfLineEnergyDomain_of_groundState hF
  have h := criticalHalfLineFullEnergy_add_const_mul W₀ hG hdF (-(∫ v, F v * G v))
  rw [criticalHalfLineMixedEnergy_symm W₀ hG hdF,
    criticalHalfLineMixedEnergy_groundState_eq_zero hW ht hF hG,
    criticalHalfLineFullEnergy_groundState_eq_zero hW ht hF,
    mul_zero, mul_zero, add_zero, add_zero] at h
  change criticalHalfLineFullEnergy W₀ (fun u => G u - (∫ v, F v * G v) * F u) = _
  simpa only [criticalHalfLineNeutralPart, neg_mul, sub_eq_add_neg] using h

/-- Small critical energy forces exponential-norm proximity to the ground-state line. -/
theorem criticalHalfLineFullEnergy_controls_neutralPart
    {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ {G : ℝ → ℝ}, CriticalHalfLineEnergyDomain G →
      γ * (∫ u, criticalHalfLineNeutralPart F G u ^ 2 * Real.exp (-(8 * u))) ≤
        criticalHalfLineFullEnergy W₀ G := by
  obtain ⟨γ, hγ, hgap⟩ := criticalHalfLineFullEnergy_transverse_exponential_gap hW ht hF
  refine ⟨γ, hγ, ?_⟩
  intro G hG
  have h := hgap ((criticalHalfLineEnergyDomain_of_groundState hF).neutralPart hG)
    (criticalHalfLineNeutralPart_orthogonal hF hG)
  rwa [criticalHalfLineFullEnergy_neutralPart hW ht hF hG] at h

private theorem sourceMass_le_eighthMass {G : ℝ → ℝ} (hG : CriticalHalfLineEnergyDomain G) :
    exponentialSourceMass G ≤ ∫ u, G u ^ 2 * Real.exp (-(8 * u)) := by
  apply integral_mono hG.weighted.sq hG.exponential
  intro u
  change (Real.exp |u| * G u) ^ 2 ≤ G u ^ 2 * Real.exp (-(8 * u))
  by_cases hu : 0 ≤ u
  · simp only [hG.support u hu, mul_zero, zero_pow two_ne_zero, zero_mul, le_refl]
  · have hun : u ≤ 0 := (lt_of_not_ge hu).le
    rw [mul_pow, abs_of_nonpos hun, ← Real.exp_nat_mul, mul_comm]
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    apply Real.exp_le_exp.mpr
    push_cast
    linarith only [hun]

theorem integral_polarSourceProfile_neutralPart {F G : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (hG : CriticalHalfLineEnergyDomain G) :
    (∫ u, criticalHalfLineNeutralPart F G u * polarSourceProfile u) =
      (∫ u, G u * polarSourceProfile u) -
        (∫ v, F v * G v) * (∫ u, F u * polarSourceProfile u) := by
  have heq : (fun u => criticalHalfLineNeutralPart F G u * polarSourceProfile u) =
      fun u => G u * polarSourceProfile u -
        (∫ v, F v * G v) * (F u * polarSourceProfile u) := by
    funext u
    dsimp only [criticalHalfLineNeutralPart]
    ring
  rw [heq, integral_sub (integrable_mul_polarSourceProfile hG.weighted)
    ((integrable_mul_polarSourceProfile hF.weighted).const_mul _), integral_const_mul]

/-- The polar functional differs from its ground-state component by an energy-bounded term. -/
theorem criticalHalfLine_polar_residual_energy_bound
    {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {G : ℝ → ℝ}, CriticalHalfLineEnergyDomain G →
      ((∫ u, G u * polarSourceProfile u) -
        (∫ v, F v * G v) * (∫ u, F u * polarSourceProfile u)) ^ 2 ≤
          C * criticalHalfLineFullEnergy W₀ G := by
  obtain ⟨γ, hγ, hgap⟩ := criticalHalfLineFullEnergy_controls_neutralPart hW ht hF
  let J : ℝ := ∫ u, (Real.exp (-|u|) * polarSourceProfile u) ^ 2
  have hJ : 0 ≤ J := integral_nonneg fun u => sq_nonneg _
  refine ⟨J / γ, div_nonneg hJ hγ.le, ?_⟩
  intro G hG
  have hdF := criticalHalfLineEnergyDomain_of_groundState hF
  have hdN := hdF.neutralPart hG
  have hcs := sq_integral_mul_polarSourceProfile_le hdN.weighted
  rw [integral_polarSourceProfile_neutralPart hdF hG] at hcs
  have hmass := mul_le_mul_of_nonneg_right (sourceMass_le_eighthMass hdN) hJ
  have he := mul_le_mul_of_nonneg_left (hgap hG) (div_nonneg hJ hγ.le)
  have hcoef : J / γ * (γ *
      (∫ u, criticalHalfLineNeutralPart F G u ^ 2 * Real.exp (-(8 * u)))) =
      (∫ u, criticalHalfLineNeutralPart F G u ^ 2 * Real.exp (-(8 * u))) * J := by
    field_simp [hγ.ne']
  rw [hcoef] at he
  exact hcs.trans (hmass.trans he)

/-- Failure of RH supplies a stable critical-state line and an energy-controlled polar residual. -/
theorem riemannHypothesis_or_exists_stable_criticalHalfLineGroundState :
    RiemannHypothesis ∨ ∃ (W₀ : ℝ) (F : ℝ → ℝ) (γ C : ℝ), 0 < W₀ ∧
      (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal) ∧
      IsCriticalHalfLineGroundState W₀ F ∧ 0 < γ ∧ 0 ≤ C ∧
      ∀ G : ℝ → ℝ, CriticalHalfLineEnergyDomain G →
        γ * (∫ u, criticalHalfLineNeutralPart F G u ^ 2 * Real.exp (-(8 * u))) ≤
          criticalHalfLineFullEnergy W₀ G ∧
        ((∫ u, G u * polarSourceProfile u) -
          (∫ v, F v * G v) * (∫ u, F u * polarSourceProfile u)) ^ 2 ≤
            C * criticalHalfLineFullEnergy W₀ G := by
  rcases riemannHypothesis_or_exists_criticalHalfLineGroundState with hRH | ⟨W₀, F, hW, ht, hF⟩
  · exact Or.inl hRH
  · obtain ⟨γ, hγ, hgap⟩ := criticalHalfLineFullEnergy_controls_neutralPart hW ht hF
    obtain ⟨C, hC, hpolar⟩ := criticalHalfLine_polar_residual_energy_bound hW ht hF
    exact Or.inr ⟨W₀, F, γ, C, hW, ht, hF, hγ, hC, fun G hG => ⟨hgap hG, hpolar hG⟩⟩


#print axioms criticalHalfLineFullEnergy_coercive_remainder
#print axioms exists_window_energy_recovery
#print axioms exists_groundState_of_smooth_energy_limit
#print axioms criticalHalfLineFullEnergy_transverse_exponential_gap
#print axioms riemannHypothesis_or_exists_stable_criticalHalfLineGroundState

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
