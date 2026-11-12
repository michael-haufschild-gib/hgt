import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheCriticalHalfLineStateHasCausalCoordinates

/-!
# The critical half-line state's full energy vanishes at the polar threshold

Absolute Gamma integrability gives the actual limit of its frequency
truncations. Their nonnegative tails compare every large truncation to
the full form. In the remaining finite-threshold case, positivity at all
smaller ratios gives the reverse inequality at the endpoint. The state's
full energy is therefore zero, without a smoothness hypothesis.
-/

noncomputable section

open MeasureTheory Set Filter Topology Zeta23
open _root_.RHTower

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

open CriticalArithmeticCorrelationTheory ArithmeticCastelnuovoSeveri
  ArithmeticPositivityTheory SpacingScaleHarmonicAnalysis WindowTowerOfSpecZ

/-- The literal full half-line energy, with prime, pole and alias terms retained. -/
def criticalHalfLineFullEnergy (R : ℝ) (F : ℝ → ℝ) : ℝ :=
  archForm F - primeSum F + (2 * coshHalfMoment F ^ 2 - 2 * sinhHalfMoment F ^ 2) +
    criticalAliasCoefficient R * (∫ u in Iio 0, F u ^ 2 * Real.exp (-(8 * u)))

/-- Integrable Gamma energy is the limit of the actual frequency truncations. -/
theorem tendsto_lowGammaForm_atTop_of_integrable {F : ℝ → ℝ}
    (hi : Integrable (fun r : ℝ => ‖paperFT (cx F) r‖ ^ 2 * EF.gammaBracket r)) :
    Tendsto (fun N : ℕ => lowGammaForm F (N : ℝ)) atTop (𝓝 (archForm F)) := by
  let s : ℕ → Set ℝ := fun N => (highFrequencies (N : ℝ))ᶜ
  have hsm (N : ℕ) : MeasurableSet (s N) := (measurableSet_highFrequencies _).compl
  have hmono : Monotone s := by
    intro m n hmn r hr
    change ¬ (m : ℝ) ≤ |r| at hr
    change ¬ (n : ℝ) ≤ |r|
    exact fun h => hr ((by exact_mod_cast hmn : (m : ℝ) ≤ n).trans h)
  have hu : (⋃ N, s N) = univ := by
    apply eq_univ_of_forall
    intro r
    obtain ⟨N, hN⟩ := exists_nat_gt |r|
    exact mem_iUnion.mpr ⟨N, not_le.mpr hN⟩
  have hh := tendsto_setIntegral_of_monotone hsm hmono hi.integrableOn
  rw [hu, setIntegral_univ] at hh
  exact hh.const_mul (1 / (2 * Real.pi))

/-- Every large Gamma truncation lies below the full integral even for
an arbitrary integrable profile; the omitted tail has nonnegative weight. -/
theorem lowGammaForm_le_archForm_of_integrable {F : ℝ → ℝ}
    (hi : Integrable (fun r : ℝ => ‖paperFT (cx F) r‖ ^ 2 * EF.gammaBracket r))
    {T : ℝ} (hT : Real.exp factorialSpanGammaOffset ≤ T) :
    lowGammaForm F T ≤ archForm F := by
  let k : ℝ → ℝ := fun r => ‖paperFT (cx F) r‖ ^ 2 * EF.gammaBracket r
  have hT0 : 0 < T := (Real.exp_pos _).trans_le hT
  have hlog : 0 ≤ Real.log T - factorialSpanGammaOffset := by
    have hh := Real.log_le_log (Real.exp_pos _) hT
    rw [Real.log_exp] at hh
    linarith only [hh]
  have hnonneg : 0 ≤ᵐ[volume.restrict (highFrequencies T)] k :=
    (ae_restrict_iff' (measurableSet_highFrequencies T)).mpr
      (Eventually.of_forall fun r hr => mul_nonneg (sq_nonneg _)
        (hlog.trans (gammaBracket_ge_log_of_le_abs hT0 hr)))
  have htail : 0 ≤ ∫ r in highFrequencies T, k r := integral_nonneg_of_ae hnonneg
  have hsplit := integral_add_compl (measurableSet_highFrequencies T) hi
  change (∫ r in highFrequencies T, k r) +
    (∫ r in (highFrequencies T)ᶜ, k r) = ∫ r, k r at hsplit
  have hle : (∫ r in (highFrequencies T)ᶜ, k r) ≤ ∫ r, k r := by
    linarith only [hsplit, htail]
  exact mul_le_mul_of_nonneg_left hle (by positivity : 0 ≤ 1 / (2 * Real.pi))

/-- The state defining inequality survives removal of the Gamma cutoff. -/
theorem criticalHalfLineFullEnergy_nonpos {W₀ : ℝ} {F : ℝ → ℝ}
    (hF : IsCriticalHalfLineGroundState W₀ F) : criticalHalfLineFullEnergy W₀ F ≤ 0 := by
  have hl := tendsto_lowGammaForm_atTop_of_integrable
    (integrable_gamma_of_criticalHalfLineGroundState hF)
  have he := ((hl.sub_const (primeSum F)).add_const
    (2 * coshHalfMoment F ^ 2 - 2 * sinhHalfMoment F ^ 2)).add_const
      (criticalAliasCoefficient W₀ * (∫ u in Iio 0, F u ^ 2 * Real.exp (-(8 * u))))
  apply le_of_tendsto he
  filter_upwards [eventually_ge_atTop ⌈Real.exp factorialSpanGammaOffset⌉₊] with N hN
  exact hF.2.2.2.2.2.2 N ((Nat.le_ceil _).trans (by exact_mod_cast hN))

/-- At equality of the polar and window thresholds, every critical state
has zero full energy. All integrability is supplied by the state itself. -/
theorem criticalHalfLineFullEnergy_eq_zero_of_threshold_equality
    {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    (hpolar : polarPaymentCriticalThreshold = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    criticalHalfLineFullEnergy W₀ F = 0 := by
  have hbelow := polarPaymentCriticalThreshold_eq_iInf_windowThreshold_iff_halfLinePolarPositive.mp
    (hpolar.trans hthreshold.symm)
  have hpos (R : ℝ) (hR : R ∈ Ioo 0 W₀) : 0 < criticalHalfLineFullEnergy R F := by
    have hRthreshold : (R : EReal) < ⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A := by
      rw [hthreshold, EReal.coe_lt_coe_iff]
      exact hR.2
    obtain ⟨T, hT, hp⟩ := hbelow R hR.1 hRthreshold F 0
      hF.1 hF.2.1 hF.2.2.1 hF.2.2.2.1.le hF.2.2.2.2.1 hF.2.2.2.2.2.1
      (by rw [hF.2.2.2.1]; norm_num)
    simp only [zero_pow (by omega : 2 ≠ 0), mul_zero, zero_mul, add_zero] at hp
    have hΓ := lowGammaForm_le_archForm_of_integrable
      (integrable_gamma_of_criticalHalfLineGroundState hF) hT
    dsimp only [truncatedWeilForm] at hp
    dsimp only [criticalHalfLineFullEnergy]
    linarith only [hp, hΓ]
  have hWne : W₀ ≠ 0 := hW.ne'
  have hc : ContinuousAt (fun R : ℝ => -(criticalHalfLineFullEnergy R F)) W₀ := by
    dsimp only [criticalHalfLineFullEnergy, criticalAliasCoefficient]
    simp only [div_eq_mul_inv, mul_inv_rev]
    fun_prop (disch := assumption)
  have hnonneg : 0 ≤ criticalHalfLineFullEnergy W₀ F := by
    have hh : -(criticalHalfLineFullEnergy W₀ F) ≤ 0 :=
      le_of_tendsto (hc.tendsto.mono_left
        (show 𝓝[<] W₀ ≤ 𝓝 W₀ from nhdsWithin_le_nhds))
        (by filter_upwards [Ioo_mem_nhdsLT hW] with R hR; exact neg_nonpos.mpr (hpos R hR).le)
    linarith only [hh]
  exact le_antisymm (criticalHalfLineFullEnergy_nonpos hF) hnonneg

/-- The unconditional threshold classification has an actual zero-energy
state in its remaining case, with the established polar orthogonality retained. -/
theorem criticalHalfLine_fullEnergy_classification :
    RiemannHypothesis ∨
      polarPaymentCriticalThreshold < (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) ∨
      ∃ (W₀ : ℝ) (F : ℝ → ℝ), 0 < W₀ ∧
        polarPaymentCriticalThreshold = (W₀ : EReal) ∧
        (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal) ∧
        IsCriticalHalfLineGroundState W₀ F ∧ criticalHalfLineFullEnergy W₀ F = 0 ∧
        (∫ u, F u * polarSourceProfile u) = 0 := by
  rcases polarPaymentCriticalThreshold_windowThreshold_classification with
    hRH | hlt | ⟨_, W₀, hW, hpolar, hthreshold, ⟨F, hF⟩, horth⟩
  · exact Or.inl hRH.1
  · exact Or.inr (Or.inl hlt.2)
  · exact Or.inr (Or.inr ⟨W₀, F, hW, hpolar, hthreshold, hF,
      criticalHalfLineFullEnergy_eq_zero_of_threshold_equality hW hthreshold hpolar hF,
      horth F hF⟩)

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
