import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.HalfLinePolarThresholdAndGroundStateOrthogonality
import GaloisForLFunctions.RHTower.RiemannKernelStripLPMaximality
import GaloisForLFunctions.RHTower.WeilWorkPBAPJointCoercivity
import GaloisForLFunctions.RHTower.WeilPaperRealificationEnergy
import GaloisForLFunctions.HTGeometry.IntegrableOfBoundedWindows
import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheHalfLineLogarithmicFormHasItsActualInverse

/-!
# Critical half-line states lie in the actual logarithmic form domain

The global Gamma lower bound turns bounded signed truncations into bounded
nonnegative window masses after adding a constant times the Fourier mass.
Plancherel pays that addition using the state's existing L² hypothesis.
The full Gamma integral and logarithmic graph norm are therefore finite.
Reflection then puts the actual state in the range of causal convolution.
-/

noncomputable section

open MeasureTheory Set Filter Topology Complex Zeta23
open scoped FourierTransform
open _root_.RHTower

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

open CriticalArithmeticCorrelationTheory ArithmeticCastelnuovoSeveri
  ArithmeticPositivityTheory SpacingScaleHarmonicAnalysis
  CanonicalSystemOfTheWindowTower WindowTowerOfSpecZ

private theorem memLp_cx_of_integrable_sq {F : ℝ → ℝ}
    (hF1 : Integrable F) (hF2 : Integrable (fun u => F u ^ 2)) :
    MemLp (cx F) 2 volume := by
  have hFc : Integrable (cx F) := hF1.ofReal (𝕜 := ℂ)
  apply (memLp_two_iff_integrable_sq_norm hFc.aestronglyMeasurable).mpr
  simpa only [cx, Complex.norm_real, Real.norm_eq_abs, sq_abs] using hF2

private theorem integrable_shifted_gamma_of_bounded_truncations {F : ℝ → ℝ}
    (hF1 : Integrable F) (hF2 : Integrable (fun u => F u ^ 2))
    {T₀ B : ℝ} (hB : ∀ T : ℝ, T₀ ≤ T → lowGammaForm F T ≤ B) :
    Integrable (fun r : ℝ => ‖paperFT (cx F) r‖ ^ 2 *
      (EF.gammaBracket r + (10 + Real.log 4))) := by
  let C : ℝ := 10 + Real.log 4
  let b : ℝ → ℝ := fun r => ‖paperFT (cx F) r‖ ^ 2
  let g : ℝ → ℝ := fun r => b r * (EF.gammaBracket r + C)
  have hC : 0 ≤ C := by
    have hh := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
    dsimp only [C]
    linarith only [hh]
  have hbc : Continuous b := (continuous_paperFT_cx hF1).norm.pow 2
  have hbi : Integrable b :=
    _root_.RHTower.KernelStrip.integrable_norm_sq_paperFT
      (hF1.ofReal (𝕜 := ℂ)) (memLp_cx_of_integrable_sq hF1 hF2)
  have hgc : Continuous g :=
    hbc.mul (WeilHerglotz.continuous_gammaBracket.add continuous_const)
  have hgn (r : ℝ) : 0 ≤ g r := by
    have hl := _root_.RHTower.WeilWorkPBAP.joint_gamma_lower_log r
    have hn := Real.log_nonneg (by linarith only [abs_nonneg r] : 1 ≤ 2 + |r|)
    exact mul_nonneg (sq_nonneg _) (by dsimp only [C]; linarith only [hl, hn])
  have hgi : Integrable g := by
    apply HTGeometry.integrable_of_bounded_windows hgc hgn
      (C := 2 * Real.pi * B + (∫ r, b r) * C)
    intro n
    let T : ℝ := max T₀ ((n : ℝ) + 1)
    let S : Set ℝ := (highFrequencies T)ᶜ
    have hST : S ⊆ Icc (-T) T := compl_highFrequencies_subset T
    have hbS : IntegrableOn b S := hbi.integrableOn
    have hgS : IntegrableOn g S :=
      (hgc.continuousOn.integrableOn_compact isCompact_Icc).mono_set hST
    have hγS : IntegrableOn (fun r => b r * EF.gammaBracket r) S :=
      ((hbc.mul WeilHerglotz.continuous_gammaBracket).continuousOn.integrableOn_compact
        isCompact_Icc).mono_set hST
    have hsub : Icc (-(n : ℝ)) (n : ℝ) ⊆ S := by
      intro r hr
      have hab : |r| ≤ (n : ℝ) := abs_le.mpr hr
      have hT : (n : ℝ) + 1 ≤ T := le_max_right _ _
      change ¬ T ≤ |r|
      linarith only [hab, hT]
    have heq : (∫ r in S, g r) =
        2 * Real.pi * lowGammaForm F T + (∫ r in S, b r) * C := by
      have he (r : ℝ) : g r = b r * EF.gammaBracket r + b r * C := by
        dsimp only [g]
        ring
      simp_rw [he]
      rw [integral_add hγS (hbS.mul_const C), integral_mul_const]
      dsimp only [lowGammaForm, S, b]
      field_simp
    calc
      _ ≤ ∫ r in S, g r := setIntegral_mono_set hgS
        (Eventually.of_forall hgn) (Eventually.of_forall fun r hr => hsub hr)
      _ = _ := heq
      _ ≤ 2 * Real.pi * B + (∫ r, b r) * C :=
        add_le_add (mul_le_mul_of_nonneg_left (hB T (le_max_left _ _)) (by positivity))
          (mul_le_mul_of_nonneg_right
            (setIntegral_le_integral hbi (Eventually.of_forall fun r => sq_nonneg _)) hC)
  exact hgi

/-- The actual critical state has an absolutely convergent full Gamma
integral; bounded truncations do not leave an unproved integrability premise. -/
theorem integrable_gamma_of_criticalHalfLineGroundState {W₀ : ℝ} {F : ℝ → ℝ}
    (hF : IsCriticalHalfLineGroundState W₀ F) :
    Integrable (fun r : ℝ => ‖paperFT (cx F) r‖ ^ 2 * EF.gammaBracket r) := by
  rcases hF with ⟨_, hF1, hF2, _, _, _, htrunc⟩
  let B : ℝ := primeSum F - (2 * coshHalfMoment F ^ 2 - 2 * sinhHalfMoment F ^ 2) -
    criticalAliasCoefficient W₀ * (∫ u in Iio 0, F u ^ 2 * Real.exp (-(8 * u)))
  have hB (T : ℝ) (hT : Real.exp factorialSpanGammaOffset ≤ T) : lowGammaForm F T ≤ B := by
    have hh := htrunc T hT
    dsimp only [truncatedWeilForm] at hh
    dsimp only [B]
    linarith only [hh]
  have hg := integrable_shifted_gamma_of_bounded_truncations hF1 hF2 hB
  have hb : Integrable (fun r : ℝ => ‖paperFT (cx F) r‖ ^ 2) :=
    _root_.RHTower.KernelStrip.integrable_norm_sq_paperFT
    (hF1.ofReal (𝕜 := ℂ)) (memLp_cx_of_integrable_sq hF1 hF2)
  apply (hg.sub (hb.mul_const (10 + Real.log 4))).congr
  exact Eventually.of_forall fun r => by
    dsimp only [Pi.sub_apply, cx]
    ring

/-- The exact positive reference symbol is bounded by the Gamma weight
and a constant; its logarithm has the same normalization as the causal factor. -/
theorem positiveLogarithmicSymbol_le_gamma_add (r : ℝ) :
    positiveLogarithmicSymbol r ≤ EF.gammaBracket r + (11 + Real.log 4) := by
  have hs : 1 + r ^ 2 ≤ (2 + |r|) ^ 2 := by
    nlinarith only [sq_abs r, abs_nonneg r]
  have hl := Real.log_le_log (by positivity : 0 < 1 + r ^ 2) hs
  rw [Real.log_pow] at hl
  have hγ := _root_.RHTower.WeilWorkPBAP.joint_gamma_lower_log r
  dsimp only [positiveLogarithmicSymbol]
  norm_num only [Nat.cast_ofNat] at hl
  linarith only [hl, hγ]

/-- The full logarithmic energy of the actual state is finite in the
literal paper Fourier convention. -/
theorem integrable_logarithmic_energy_of_criticalHalfLineGroundState
    {W₀ : ℝ} {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    Integrable (fun r : ℝ => positiveLogarithmicSymbol r * ‖paperFT (cx F) r‖ ^ 2) := by
  have hF1 := hF.2.1
  have hF2 := hF.2.2.1
  have hb : Integrable (fun r : ℝ => ‖paperFT (cx F) r‖ ^ 2) :=
    _root_.RHTower.KernelStrip.integrable_norm_sq_paperFT
    (hF1.ofReal (𝕜 := ℂ)) (memLp_cx_of_integrable_sq hF1 hF2)
  have hmajor := (integrable_gamma_of_criticalHalfLineGroundState hF).add
    (hb.mul_const (11 + Real.log 4))
  apply hmajor.mono'
    ((continuous_positiveLogarithmicSymbol.mul
      ((continuous_paperFT_cx hF1).norm.pow 2)).aestronglyMeasurable)
  refine Eventually.of_forall fun r => ?_
  dsimp only [Pi.mul_apply, Pi.pow_apply, Pi.add_apply, cx]
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (zero_le_one.trans (one_le_positiveLogarithmicSymbol r)) (sq_nonneg _))]
  calc
    _ ≤ (EF.gammaBracket r + (11 + Real.log 4)) * ‖paperFT (cx F) r‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (positiveLogarithmicSymbol_le_gamma_add r) (sq_nonneg _)
    _ = _ := by ring

/-- Every actual critical half-line state has causal logarithmic coordinates:
one L² source reproduces its reflected profile under the literal convolution. -/
theorem exists_causal_coordinates_of_criticalHalfLineGroundState
    {W₀ : ℝ} {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    ∃ v : LogarithmicHalfLineL2,
      ((logarithmicConvolution (v : HTGeometry.RealLineL2) : HTGeometry.RealLineL2) : ℝ → ℂ)
        =ᵐ[volume] fun t => (F (-t) : ℂ) := by
  let g : ℝ → ℂ := fun t => (F (-t) : ℂ)
  have hF1 : Integrable F := hF.2.1
  have hF2 : Integrable (fun t => F t ^ 2) := hF.2.2.1
  have hg1 : Integrable g := (hF1.ofReal (𝕜 := ℂ)).comp_neg
  have hg2 : MemLp g 2 volume := by
    apply (memLp_two_iff_integrable_sq_norm hg1.aestronglyMeasurable).mpr
    simpa only [g, Complex.norm_real, Real.norm_eq_abs, sq_abs] using hF2.comp_neg
  let u : HTGeometry.RealLineL2 := hg2.toLp g
  have hhalf : u ∈ _root_.RHTower.halfLineL2 := by
    rw [_root_.RHTower.mem_halfLineL2_iff]
    filter_upwards [hg2.coeFn_toLp] with t ht
    intro htneg
    rw [ht]
    change (F (-t) : ℂ) = 0
    rw [hF.2.2.2.2.2.1 (-t) (by linarith only [htneg]), Complex.ofReal_zero]
  have hfourier (ξ : ℝ) : 𝓕 g ξ = paperFT (cx F) ((2 * Real.pi * ξ : ℝ) : ℂ) := by
    have hh := paperFT_ofReal_eq_fourier g (-(2 * Real.pi) * ξ)
    have harg : -(-(2 * Real.pi) * ξ) / (2 * Real.pi) = ξ := by field_simp
    rw [harg] at hh
    rw [← hh]
    change paperFT (fun t => cx F (-t)) ((-(2 * Real.pi) * ξ : ℝ) : ℂ) = _
    rw [_root_.RHTower.WeilWorkPBAP.paperFT_reflect_complex]
    congr 1
    push_cast
    ring
  have henergy : HasLogarithmicEnergy u := by
    apply (hasLogarithmicEnergy_iff_integrable u).mpr
    have hi := (integrable_logarithmic_energy_of_criticalHalfLineGroundState hF).comp_mul_left'
      (show 2 * Real.pi ≠ 0 by positivity)
    apply hi.congr
    filter_upwards [GaloisForLFunctions.RHTower.coeFn_fourier_toLp hg1 hg2] with ξ hξ
    change ((Lp.fourierTransformₗᵢ ℝ ℂ) u : ℝ → ℂ) ξ = 𝓕 g ξ at hξ
    rw [hξ, hfourier]
  obtain ⟨v, hv⟩ := (hasLogarithmicEnergy_iff_mem_range (⟨u, hhalf⟩ : LogarithmicHalfLineL2)).mp henergy
  refine ⟨v, ?_⟩
  have heq : logarithmicConvolution (v : HTGeometry.RealLineL2) = u := congrArg Subtype.val hv
  rw [heq]
  exact hg2.coeFn_toLp

/-- The unconditional ground-state dichotomy produces a state in the
actual causal logarithmic range, with its full Gamma integral finite. -/
theorem riemannHypothesis_or_exists_causal_criticalHalfLineGroundState :
    RiemannHypothesis ∨ ∃ (W₀ : ℝ) (F : ℝ → ℝ), 0 < W₀ ∧
      (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal) ∧
      IsCriticalHalfLineGroundState W₀ F ∧
      Integrable (fun r : ℝ => ‖paperFT (cx F) r‖ ^ 2 * EF.gammaBracket r) ∧
      ∃ v : LogarithmicHalfLineL2,
        ((logarithmicConvolution (v : HTGeometry.RealLineL2) : HTGeometry.RealLineL2) : ℝ → ℂ)
          =ᵐ[volume] fun t => (F (-t) : ℂ) := by
  rcases riemannHypothesis_or_exists_criticalHalfLineGroundState with hRH | ⟨W₀, F, hW, hthr, hF⟩
  · exact Or.inl hRH
  · exact Or.inr ⟨W₀, F, hW, hthr, hF,
      integrable_gamma_of_criticalHalfLineGroundState hF,
      exists_causal_coordinates_of_criticalHalfLineGroundState hF⟩

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
