import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheCriticalHalfLineFormHasItsActualDomain

/-!
# The window threshold controls the full measurable half-line form

One-sided window approximation preserves the actual Gamma upper bound and
converges in the weighted norm. Window-pencil positivity therefore extends
to every finite-energy half-line profile. The critical state's full energy
vanishes at the global window threshold independently of the polar threshold.
-/

noncomputable section
open MeasureTheory Filter Set Topology Zeta23
open _root_.RHTower

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open CriticalArithmeticCorrelationTheory ArithmeticCastelnuovoSeveri
  ArithmeticPositivityTheory SpacingScaleHarmonicAnalysis WindowTowerOfSpecZ
  CohomologyOfWindowsOfSpecZ RenormalizedArithmeticPotentialTheory

private theorem splineAtom_mul_alias {R : ℝ} (hR : 0 < R) :
    splineAtom * criticalAliasCoefficient R = 7 * tiltedJordanOne / R := by
  unfold splineAtom criticalAliasCoefficient
  have h1 : (∫ u, tiltedUnitSpline u) ≠ 0 := integral_tiltedUnitSpline_ne_zero
  have h2 : (∫ u, tiltedUnitSpline u ^ 2) ≠ 0 := integral_tiltedUnitSpline_sq_pos.ne'
  field_simp [h1, pow_ne_zero 2 h1, h2, hR.ne']

private theorem windowPencil_nonneg_below {R A : ℝ} (hR : 0 < R)
    (hlt : (R : EReal) < windowThreshold A) {H : ℝ → ℝ} (hH : IsWindowTest A H) :
    0 ≤ windowPencil R H := by
  by_cases hz : H = 0
  · subst H
    have hf := weilQuad_ge_neg_exponentialMass hH (by norm_num : (1 : ℝ) < 8)
    have hm : exponentialMass 8 (0 : ℝ → ℝ) = 0 := by simp [exponentialMass]
    rw [hm, mul_zero, neg_zero] at hf
    rw [windowPencil, hm, mul_zero, add_zero]
    exact mul_nonneg splineAtom_pos.le hf
  · exact (pencil_pos_of_lt_windowThreshold hR hlt hH hz).le

/-- The literal full form is nonnegative below the global window threshold
on every normalized measurable finite-energy profile. -/
theorem criticalHalfLineFullEnergy_nonneg_normalized_below_windowThreshold
    {R : ℝ} (hR : 0 < R)
    (hlt : (R : EReal) < ⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A)
    {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) (hnorm : (∫ u, F u ^ 2) ≤ 1) :
    0 ≤ criticalHalfLineFullEnergy R F := by
  let I₈ : ℝ := ∫ u in Iio 0, F u ^ 2 * Real.exp (-(8 * u))
  have hI₈ : 0 ≤ I₈ := integral_nonneg fun u => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
  have htrunc (T : ℝ) (hT : Real.exp factorialSpanGammaOffset ≤ T) :
      truncatedWeilForm F T + criticalAliasCoefficient R * I₈ ≤ criticalHalfLineFullEnergy R F := by
    have hh := lowGammaForm_le_archForm_of_integrable hF.gamma hT
    dsimp only [truncatedWeilForm, criticalHalfLineFullEnergy, I₈]
    linarith only [hh]
  obtain ⟨C, A, H, _, hwin, hmass, hexp, _, hd, harch⟩ :=
    exists_window_sequence_of_gammaLiminf_bound hF.meas hF.integrable hF.sq hF.exponential
      le_rfl hF.support htrunc
  have hHcont (k : ℕ) : Continuous (H k) := (hwin k).2.contDiff.continuous
  have hHcompact (k : ℕ) : HasCompactSupport (H k) := (hwin k).2.hasCompactSupport
  have hHsupport (k : ℕ) (u : ℝ) (hu : 1 < u) : H k u = 0 :=
    (hwin k).2.vanish u (fun hh => by linarith only [hu, hh.2])
  have hH8 (k : ℕ) : (∫ u, H k u ^ 2 * Real.exp (-(8 * u))) ≤ Real.exp 8 * I₈ := by
    have he : (∫ u, H k u ^ 2 * Real.exp (-(8 * u))) = exponentialMass 8 (H k) :=
      integral_congr_ae (Eventually.of_forall fun u => mul_comm _ _)
    have hk : 8 / ((k : ℝ) + 1) ≤ 8 := by
      apply (div_le_iff₀ (by positivity : 0 < (k : ℝ) + 1)).mpr
      nlinarith only [Nat.cast_nonneg (α := ℝ) k]
    rw [he]
    exact (hexp k).trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hk) hI₈)
  obtain ⟨hP, hC, hS⟩ := tendsto_prime_and_pole_of_strong_limit hHcont hHcompact hF.weighted
    (fun k => (hmass k).trans hnorm) hH8 (Eventually.of_forall hHsupport) hd
  have harch' (k : ℕ) : archForm (H k) ≤ archForm F + C / ((k : ℝ) + 1) := by
    have hh := harch k
    dsimp only [criticalHalfLineFullEnergy, I₈] at hh
    linarith only [hh]
  let U : ℕ → ℝ := fun k =>
    splineAtom * (archForm F + C / ((k : ℝ) + 1) - primeSum (H k) +
      (2 * coshHalfMoment (H k) ^ 2 - 2 * sinhHalfMoment (H k) ^ 2)) +
      (7 * tiltedJordanOne / R) * (Real.exp (8 / ((k : ℝ) + 1)) * I₈)
  have hU (k : ℕ) : windowPencil R (H k) ≤ U k := by
    have hΓ := mul_le_mul_of_nonneg_left (harch' k) splineAtom_pos.le
    have he := mul_le_mul_of_nonneg_left (hexp k)
      (by have := tiltedJordanOne_pos; positivity : 0 ≤ 7 * tiltedJordanOne / R)
    dsimp only [U, windowPencil]
    rw [weilQuad_eq_arch_sub_prime_add_pole (hwin k).2.contDiff (hHcompact k)]
    linarith only [hΓ, he]
  have hδ : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hCδ : Tendsto (fun k : ℕ => C / ((k : ℝ) + 1)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, one_mul, mul_zero] using hδ.const_mul C
  have h8δ : Tendsto (fun k : ℕ => 8 / ((k : ℝ) + 1)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, one_mul, mul_zero] using hδ.const_mul (8 : ℝ)
  have hexplim : Tendsto (fun k : ℕ => Real.exp (8 / ((k : ℝ) + 1))) atTop (𝓝 1) := by
    simpa only [Real.exp_zero, Function.comp_def] using (Real.continuous_exp.tendsto 0).comp h8δ
  have hlim : Tendsto U atTop (𝓝 (splineAtom * criticalHalfLineFullEnergy R F)) := by
    have h1 := ((((tendsto_const_nhds (x := archForm F)).add hCδ).sub hP).add
      (((hC.pow 2).const_mul 2).sub ((hS.pow 2).const_mul 2))).const_mul splineAtom
    have h2 := (hexplim.mul_const I₈).const_mul (7 * tiltedJordanOne / R)
    refine (h1.add h2).trans (le_of_eq ?_)
    congr 1
    calc
      _ = splineAtom * (archForm F - primeSum F +
          (2 * coshHalfMoment F ^ 2 - 2 * sinhHalfMoment F ^ 2)) +
          (splineAtom * criticalAliasCoefficient R) * I₈ := by
        rw [splineAtom_mul_alias hR]
        ring
      _ = _ := by dsimp only [criticalHalfLineFullEnergy, I₈]; ring
  have hnonneg (k : ℕ) : 0 ≤ U k :=
    (windowPencil_nonneg_below hR
      (hlt.trans_le (iInf_le_of_le (A k) (iInf_le _ (hwin k).1))) (hwin k).2).trans (hU k)
  have hh : -(splineAtom * criticalHalfLineFullEnergy R F) ≤ 0 :=
    le_of_tendsto hlim.neg (Eventually.of_forall fun k => neg_nonpos.mpr (hnonneg k))
  exact (mul_nonneg_iff_of_pos_left splineAtom_pos).mp (neg_nonpos.mp hh)

/-- Scalar normalization extends window positivity to the full measurable domain. -/
theorem criticalHalfLineFullEnergy_nonneg_below_windowThreshold
    {R : ℝ} (hR : 0 < R)
    (hlt : (R : EReal) < ⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A)
    {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) :
    0 ≤ criticalHalfLineFullEnergy R F := by
  let m : ℝ := ∫ u, F u ^ 2
  let c : ℝ := 1 / (Real.sqrt m + 1)
  have hm : 0 ≤ m := integral_nonneg fun u => sq_nonneg _
  have hc : 0 < c := by dsimp only [c]; positivity
  have hs : 0 ≤ Real.sqrt m := Real.sqrt_nonneg m
  have hden : Real.sqrt m + 1 ≠ 0 := by positivity
  have hcEq : c * (Real.sqrt m + 1) = 1 := by dsimp only [c]; field_simp
  have hcs0 : 0 ≤ c * Real.sqrt m := mul_nonneg hc.le hs
  have hcs1 : c * Real.sqrt m ≤ 1 := by nlinarith only [hc.le, hcEq]
  have hnorm : (∫ u, (c * F u) ^ 2) ≤ 1 := by
    calc
      _ = c ^ 2 * m := by simp_rw [mul_pow]; exact integral_const_mul _ _
      _ = (c * Real.sqrt m) ^ 2 := by rw [mul_pow, Real.sq_sqrt hm]
      _ ≤ 1 := by simpa only [one_pow] using pow_le_pow_left₀ hcs0 hcs1 2
  have hp := criticalHalfLineFullEnergy_nonneg_normalized_below_windowThreshold hR hlt
    (hF.const_mul c) hnorm
  rw [criticalHalfLineFullEnergy_const_mul] at hp
  exact (mul_nonneg_iff_of_pos_left (sq_pos_of_pos hc)).mp hp

/-- Every finite-energy profile has nonnegative full energy at the global
window threshold, without a polar-threshold equality. -/
theorem criticalHalfLineFullEnergy_nonneg_at_windowThreshold
    {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) :
    0 ≤ criticalHalfLineFullEnergy W₀ F := by
  have hWne : W₀ ≠ 0 := hW.ne'
  have hc : ContinuousAt (fun R : ℝ => -(criticalHalfLineFullEnergy R F)) W₀ := by
    dsimp only [criticalHalfLineFullEnergy, criticalAliasCoefficient]
    simp only [div_eq_mul_inv, mul_inv_rev]
    fun_prop (disch := assumption)
  have hh : -(criticalHalfLineFullEnergy W₀ F) ≤ 0 :=
    le_of_tendsto (hc.tendsto.mono_left
      (show 𝓝[<] W₀ ≤ 𝓝 W₀ from nhdsWithin_le_nhds)) (by
        filter_upwards [Ioo_mem_nhdsLT hW] with R hR
        apply neg_nonpos.mpr
        apply criticalHalfLineFullEnergy_nonneg_below_windowThreshold hR.1 ?_ hF
        rw [hthreshold, EReal.coe_lt_coe_iff]
        exact hR.2)
  exact neg_nonpos.mp hh

/-- Every actual critical state has zero full energy at the global window threshold. -/
theorem criticalHalfLineFullEnergy_groundState_eq_zero
    {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    criticalHalfLineFullEnergy W₀ F = 0 :=
  le_antisymm (criticalHalfLineFullEnergy_nonpos hF)
    (criticalHalfLineFullEnergy_nonneg_at_windowThreshold hW hthreshold
      (criticalHalfLineEnergyDomain_of_groundState hF))

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
