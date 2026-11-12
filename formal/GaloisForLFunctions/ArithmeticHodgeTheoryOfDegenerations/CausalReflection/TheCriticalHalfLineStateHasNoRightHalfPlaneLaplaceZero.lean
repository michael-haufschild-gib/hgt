import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.ThePairedReflectionHasPositiveEnergyDefect

/-!
# Actual critical states have no right-half-plane Laplace zero

A conjugate pair of reflections preserves the actual domain and arithmetic
energy while losing a positive sum of weighted resolvent energies. Endpoint
nonnegativity forces the first resolvent to vanish, hence the original state.
The positive real axis is supplied by the single real reflection theorem.
-/

noncomputable section
open MeasureTheory Filter Set Topology Zeta23
open _root_.RHTower

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open CriticalArithmeticCorrelationTheory ArithmeticCastelnuovoSeveri HTGeometry
  WindowTowerOfSpecZ

/-- A nonreal right-half-plane Laplace zero annihilates every actual zero-energy profile. -/
theorem ae_eq_zero_of_fullEnergy_zero_of_nonreal_laplace_zero
    {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hd : CriticalHalfLineEnergyDomain F)
    (henergy : criticalHalfLineFullEnergy W₀ F = 0)
    {a b : ℝ} (ha : 0 < a) (hb : b ≠ 0)
    (hz : negativeHalfLineLaplace (cx F) (modulatedLaplaceRate a b) = 0) :
    F =ᵐ[volume] 0 := by
  have hH := hd.realPairedCausalReflection ha hb hz
  have hpos := criticalHalfLineFullEnergy_nonneg_at_windowThreshold hW hthreshold hH
  rw [criticalHalfLineFullEnergy_realPairedCausalReflection ha hb hd hz,
    henergy, zero_sub] at hpos
  have hcoef : 0 < criticalAliasCoefficient W₀ * (4 * a * (4 / Real.pi)) :=
    mul_pos (criticalAliasCoefficient_positive hW)
      (mul_pos (mul_pos (by norm_num) ha) (by positivity))
  have hneg : 0 ≤ -pairedCausalResolventEnergy a b (4 / Real.pi) (cx F) :=
    (mul_nonneg_iff_of_pos_left hcoef).mp (by simpa only [mul_neg] using hpos)
  have hmass : pairedCausalResolventEnergy a b (4 / Real.pi) (cx F) = 0 :=
    le_antisymm (neg_nonneg.mp hneg) (pairedCausalResolventEnergy_nonneg _ _ _ _)
  have hfirst : (∫ u, ‖causalLaplaceWeighted (4 / Real.pi)
      (modulatedCausalConvolution a b (cx F)) u‖ ^ 2) = 0 := by
    have h1 := integral_nonneg fun u => sq_nonneg
      ‖causalLaplaceWeighted (4 / Real.pi) (modulatedCausalConvolution a b (cx F)) u‖
    have h2 := integral_nonneg fun u => sq_nonneg
      ‖causalLaplaceWeighted (4 / Real.pi)
        (modulatedCausalConvolution a (-b) (modulatedCausalReflection a b (cx F))) u‖
    unfold pairedCausalResolventEnergy at hmass
    linarith only [h1, h2, hmass]
  have hK := memLp_weighted_modulatedCausalConvolution (add_pos ha (by positivity)) b
    hd.memLp_weightedComplex
  have hKi := (memLp_two_iff_integrable_sq_norm hK.aestronglyMeasurable).mp hK
  have hae := (integral_eq_zero_iff_of_nonneg_ae
    (Eventually.of_forall fun u => sq_nonneg
      ‖causalLaplaceWeighted (4 / Real.pi) (modulatedCausalConvolution a b (cx F)) u‖) hKi).mp hfirst
  have hKzero : modulatedCausalConvolution a b (cx F) =ᵐ[volume] 0 := by
    filter_upwards [hae] with u hu
    have hn : ‖causalLaplaceWeighted (4 / Real.pi) (modulatedCausalConvolution a b (cx F)) u‖ = 0 := by
      nlinarith only [hu]
    have hv := norm_eq_zero.mp hn
    change Complex.exp (-(Real.pi * (4 / Real.pi) * u : ℝ)) *
      modulatedCausalConvolution a b (cx F) u = 0 at hv
    exact (mul_eq_zero.mp hv).resolve_left (Complex.exp_ne_zero _)
  have hFzero := ae_eq_zero_of_modulatedCausalConvolution_ae_zero ha b
    (hd.integrable.ofReal (𝕜 := ℂ)) hKzero
  filter_upwards [hFzero] with u hu
  change (F u : ℂ) = 0 at hu
  change F u = 0
  exact_mod_cast hu

/-- Every right-half-plane Laplace zero forces an actual zero-energy profile to vanish. -/
theorem ae_eq_zero_of_fullEnergy_zero_of_complex_laplace_zero
    {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hd : CriticalHalfLineEnergyDomain F)
    (henergy : criticalHalfLineFullEnergy W₀ F = 0)
    {z : ℂ} (hzpos : 0 < z.re) (hz : negativeHalfLineLaplace (cx F) z = 0) :
    F =ᵐ[volume] 0 := by
  by_cases him : z.im = 0
  · have he : z = (z.re : ℂ) := by
      apply Complex.ext
      · rfl
      · simpa only [Complex.ofReal_im] using him
    rw [he, negativeHalfLineLaplace_ofReal] at hz
    exact ae_eq_zero_of_criticalHalfLineFullEnergy_eq_zero_of_laplace_zero
      hW hthreshold hd henergy hzpos (Complex.ofReal_eq_zero.mp hz)
  · have ha : 0 < z.re / Real.pi := div_pos hzpos Real.pi_pos
    have hb : z.im / (2 * Real.pi) ≠ 0 :=
      div_ne_zero him (mul_ne_zero (by norm_num) Real.pi_ne_zero)
    have he : modulatedLaplaceRate (z.re / Real.pi) (z.im / (2 * Real.pi)) = z := by
      ext <;> simp [modulatedLaplaceRate] <;> field_simp [Real.pi_ne_zero]
    apply ae_eq_zero_of_fullEnergy_zero_of_nonreal_laplace_zero hW hthreshold hd henergy ha hb
    rw [he]
    exact hz

/-- The actual critical-state Laplace transform is zero-free throughout the open right half-plane. -/
theorem criticalHalfLineGroundState_complexLaplace_ne_zero
    {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F)
    {z : ℂ} (hzpos : 0 < z.re) : negativeHalfLineLaplace (cx F) z ≠ 0 := by
  intro hz
  have hFzero := ae_eq_zero_of_fullEnergy_zero_of_complex_laplace_zero
    hW hthreshold (criticalHalfLineEnergyDomain_of_groundState hF)
    (criticalHalfLineFullEnergy_groundState_eq_zero hW hthreshold hF) hzpos hz
  have hnorm0 : (∫ u, F u ^ 2) = 0 := by
    calc
      _ = ∫ _u : ℝ, (0 : ℝ) := by
        refine integral_congr_ae ?_
        filter_upwards [hFzero] with u hu
        change F u ^ 2 = 0
        change F u = 0 at hu
        rw [hu]
        norm_num
      _ = 0 := by simp
  have hnorm := hF.2.2.2.1
  linarith only [hnorm0, hnorm]

/-- Failure of RH yields an actual critical state with no right-half-plane Laplace zero. -/
theorem riemannHypothesis_or_exists_complexLaplaceZeroFree_criticalHalfLineGroundState :
    RiemannHypothesis ∨ ∃ (W₀ : ℝ) (F : ℝ → ℝ), 0 < W₀ ∧
      (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal) ∧
      IsCriticalHalfLineGroundState W₀ F ∧
      ∀ z : ℂ, 0 < z.re → negativeHalfLineLaplace (cx F) z ≠ 0 := by
  rcases riemannHypothesis_or_exists_criticalHalfLineGroundState with hRH | ⟨W₀, F, hW, ht, hF⟩
  · exact Or.inl hRH
  · exact Or.inr ⟨W₀, F, hW, ht, hF,
      fun _ hzpos => criticalHalfLineGroundState_complexLaplace_ne_zero hW ht hF hzpos⟩

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
