import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheCausalReflectionPreservesThePoleProduct

/-!
# Actual critical half-line states have no positive real Laplace zero

Reflecting at a positive Laplace zero preserves support, the full form domain,
Gamma energy, prime correlations and the pole product. The exponential mass
strictly decreases unless the resolvent vanishes. Endpoint nonnegativity and
zero critical energy then force a zero state, contradicting unit norm.
-/

noncomputable section
open MeasureTheory Filter Set Topology Zeta23
open scoped Convolution
open _root_.RHTower

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open CriticalArithmeticCorrelationTheory ArithmeticCastelnuovoSeveri HTGeometry
  SpacingScaleHarmonicAnalysis CohomologyOfWindowsOfSpecZ WindowTowerOfSpecZ
  RenormalizedArithmeticPotentialTheory

private theorem halfLineExpMass_eq_full {F : ℝ → ℝ}
    (hF : ∀ u, 0 ≤ u → F u = 0) :
    (∫ u in Iio 0, F u ^ 2 * Real.exp (-(8 * u))) =
      ∫ u, F u ^ 2 * Real.exp (-(8 * u)) := by
  rw [← integral_indicator measurableSet_Iio]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  dsimp only
  by_cases hu : u ∈ Iio (0 : ℝ)
  · rw [indicator_of_mem hu]
  · rw [indicator_of_notMem hu, hF u (le_of_not_gt hu)]
    simp

private theorem criticalAliasCoefficient_positive {R : ℝ} (hR : 0 < R) :
    0 < criticalAliasCoefficient R := by
  unfold criticalAliasCoefficient
  exact div_pos
    (mul_pos (mul_pos (by norm_num) integral_tiltedUnitSpline_sq_pos) tiltedJordanOne_pos)
    (mul_pos (pow_pos RenormalizedIntersectionTheory.integral_tiltedUnitSpline_pos 2) hR)

/-- At a positive Laplace zero, the complete form loses exactly the positive
weighted resolvent energy. -/
theorem criticalHalfLineFullEnergy_realCausalReflection {a : ℝ} (ha : 0 < a)
    {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    (hz : (∫ u, Real.exp (Real.pi * a * u) * F u) = 0) (R : ℝ) :
    criticalHalfLineFullEnergy R (realCausalReflection a F) =
      criticalHalfLineFullEnergy R F - criticalAliasCoefficient R * (16 * a / Real.pi) *
        (∫ u, realCausalConvolution a F u ^ 2 * Real.exp (-(8 * u))) := by
  have hx : 2 * Real.pi * (4 / Real.pi) = 8 := by field_simp [Real.pi_ne_zero] <;> ring
  have hw : Integrable (fun u => F u ^ 2 * Real.exp (-(2 * Real.pi * (4 / Real.pi) * u))) := by
    simpa only [hx] using hF.exponential
  have hm := realCausalReflection_weighted_energy (a := a) (x := 4 / Real.pi)
    (add_pos ha (by positivity)) hF.integrable hw
  simp only [hx] at hm
  unfold criticalHalfLineFullEnergy
  rw [archForm_realCausalReflection ha hF.integrable,
    primeSum_realCausalReflection ha hF.integrable hF.sq,
    poleTerm_realCausalReflection ha hF hz,
    halfLineExpMass_eq_full (realCausalReflection_support_of_laplace_zero a hF.support hz),
    halfLineExpMass_eq_full hF.support, hm]
  ring

/-- A zero-energy profile with a positive real Laplace zero vanishes almost everywhere. -/
theorem ae_eq_zero_of_criticalHalfLineFullEnergy_eq_zero_of_laplace_zero
    {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hd : CriticalHalfLineEnergyDomain F)
    (henergy : criticalHalfLineFullEnergy W₀ F = 0)
    {s : ℝ} (hs : 0 < s) (hzero : (∫ u, F u * Real.exp (s * u)) = 0) :
    F =ᵐ[volume] 0 := by
  let a : ℝ := s / Real.pi
  have ha : 0 < a := div_pos hs Real.pi_pos
  have hpa : Real.pi * a = s := by
    dsimp only [a]
    field_simp [Real.pi_ne_zero] <;> ring
  have hz : (∫ u, Real.exp (Real.pi * a * u) * F u) = 0 := by
    calc
      _ = ∫ u, F u * Real.exp (s * u) := by
        refine integral_congr_ae (Eventually.of_forall fun u => ?_)
        dsimp only
        rw [hpa, mul_comm]
      _ = 0 := hzero
  have hH := hd.realCausalReflection ha hz
  have hpos := criticalHalfLineFullEnergy_nonneg_at_windowThreshold hW hthreshold hH
  rw [criticalHalfLineFullEnergy_realCausalReflection ha hd hz,
    henergy, zero_sub] at hpos
  have hcoef : 0 < criticalAliasCoefficient W₀ * (16 * a / Real.pi) :=
    mul_pos (criticalAliasCoefficient_positive hW) (div_pos (mul_pos (by norm_num) ha) Real.pi_pos)
  have hneg : 0 ≤ -(∫ u, realCausalConvolution a F u ^ 2 * Real.exp (-(8 * u))) :=
    (mul_nonneg_iff_of_pos_left hcoef).mp (by simpa only [mul_neg] using hpos)
  have hmass : (∫ u, realCausalConvolution a F u ^ 2 * Real.exp (-(8 * u))) = 0 :=
    le_antisymm (neg_nonneg.mp hneg)
      (integral_nonneg fun u => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)
  have h8 := integrable_exponential_realCausalConvolution ha hd
  have hae := (integral_eq_zero_iff_of_nonneg_ae
    (Eventually.of_forall fun u => mul_nonneg
      (sq_nonneg (realCausalConvolution a F u))
      (le_of_lt (Real.exp_pos (-(8 * u))))) h8).mp hmass
  have hKzero : realCausalConvolution a F =ᵐ[volume] 0 := by
    filter_upwards [hae] with u hu
    change realCausalConvolution a F u ^ 2 * Real.exp (-(8 * u)) = 0 at hu
    have hsq := (mul_eq_zero.mp hu).resolve_right (Real.exp_ne_zero _)
    change realCausalConvolution a F u = 0
    nlinarith only [hsq]
  have hKczero : (causalFourierExponential a ⋆[ContinuousLinearMap.mul ℂ ℂ] cx F) =ᵐ[volume] 0 := by
    filter_upwards [hKzero] with u hu
    have hh : (realCausalConvolution a F u : ℂ) = 0 := by exact_mod_cast hu
    exact (coe_realCausalConvolution a F u).symm.trans hh
  have hFczero := ae_eq_zero_of_causalExponentialConvolution_ae_zero ha
    (hd.integrable.ofReal (𝕜 := ℂ)) hKczero
  filter_upwards [hFczero] with u hu
  exact_mod_cast hu

/-- Every actual critical state has nonzero Laplace value at every positive real argument. -/
theorem criticalHalfLineGroundState_laplace_ne_zero
    {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F)
    {s : ℝ} (hs : 0 < s) : (∫ u, F u * Real.exp (s * u)) ≠ 0 := by
  intro hzero
  have hFzero := ae_eq_zero_of_criticalHalfLineFullEnergy_eq_zero_of_laplace_zero
    hW hthreshold (criticalHalfLineEnergyDomain_of_groundState hF)
    (criticalHalfLineFullEnergy_groundState_eq_zero hW hthreshold hF) hs hzero
  have hnorm0 : (∫ u, F u ^ 2) = 0 := by
    calc
      _ = ∫ _u : ℝ, (0 : ℝ) := by
        refine integral_congr_ae ?_
        filter_upwards [hFzero] with u hu
        have hfu : F u = 0 := hu
        change F u ^ 2 = 0
        rw [hfu]
        norm_num
      _ = 0 := by simp
  have hnorm := hF.2.2.2.1
  linarith only [hnorm0, hnorm]

/-- Failure of RH produces an actual critical state whose positive real
Laplace values are all nonzero. -/
theorem riemannHypothesis_or_exists_laplaceZeroFree_criticalHalfLineGroundState :
    RiemannHypothesis ∨ ∃ (W₀ : ℝ) (F : ℝ → ℝ), 0 < W₀ ∧
      (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal) ∧
      IsCriticalHalfLineGroundState W₀ F ∧
      ∀ s : ℝ, 0 < s → (∫ u, F u * Real.exp (s * u)) ≠ 0 := by
  rcases riemannHypothesis_or_exists_criticalHalfLineGroundState with hRH | ⟨W₀, F, hW, ht, hF⟩
  · exact Or.inl hRH
  · exact Or.inr ⟨W₀, F, hW, ht, hF,
      fun _ hs => criticalHalfLineGroundState_laplace_ne_zero hW ht hF hs⟩

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
