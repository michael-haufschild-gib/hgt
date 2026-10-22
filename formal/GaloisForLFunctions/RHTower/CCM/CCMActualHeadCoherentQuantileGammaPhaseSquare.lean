import GaloisForLFunctions.RHTower.CCM.CCMActualHeadCoherentQuantileGammaProducer

/-!
# Phase-preserving Γ square on actual quantile heads

The reciprocal higher-Binet pair defines a literal `SoninL2` square whose cross term is the
completed prime--polar current before any Cauchy estimate.  This is not a source positivity
claim: it gives an exact normal form in which the remaining RH-bearing datum is a lower bound
for a phase-preserving square against the two displayed positive energies.

At the singular zero clock both reciprocal weights vanish and the translation increment is zero;
the proof treats that point separately.  Thus no fictitious unit reciprocal is inserted at zero.
-/

open Complex MeasureTheory Set Filter Topology
open scoped ENNReal InnerProduct InnerProductSpace BigOperators ComplexConjugate

noncomputable section

namespace RHTower

/-- Reciprocal higher-Binet phase square.  Unlike the coherent chi-square alone, this retains the
literal Γ--prime--polar cross phase. -/
def ccmActualHeadCoherentQuantileGammaPhaseSquare
    (T : ℝ) (N : ℕ) (f : SoninL2) : ℝ :=
  ∫ r : ℝ,
    ‖(Real.sqrt (ccmGammaHigherBinetModeDensity |r|) : ℂ) •
          (logTranslationCLM r f - f) +
        (Real.sqrt (ccmGammaHigherBinetDualDensity |r|) : ℂ) •
          ccmActualHeadQuantileCompletedCoherentField T N f r‖ ^ 2

/-- Pointwise phase expansion.  Away from zero the Binet weights are reciprocal; at zero the
translation increment vanishes, which supplies the same cross-term identity without division. -/
theorem ccmActualHeadCoherentQuantileGammaPhaseSquare_integrand_eq
    (T : ℝ) (N : ℕ) (f : SoninL2) (r : ℝ) :
    ‖(Real.sqrt (ccmGammaHigherBinetModeDensity |r|) : ℂ) •
          (logTranslationCLM r f - f) +
        (Real.sqrt (ccmGammaHigherBinetDualDensity |r|) : ℂ) •
          ccmActualHeadQuantileCompletedCoherentField T N f r‖ ^ 2 =
      ccmGammaHigherBinetModeDensity |r| *
          ccmActualHeadTranslationDefect |r| f +
        2 * (inner ℂ (logTranslationCLM r f - f)
          (ccmActualHeadQuantileCompletedCoherentField T N f r)).re +
        ‖ccmActualHeadQuantileCompletedCoherentField T N f r‖ ^ 2 *
          ccmGammaHigherBinetDualDensity |r| := by
  let m := ccmGammaHigherBinetModeDensity |r|
  let d := ccmGammaHigherBinetDualDensity |r|
  let x := logTranslationCLM r f - f
  let y := ccmActualHeadQuantileCompletedCoherentField T N f r
  have hm : 0 ≤ m := by
    by_cases hr : r = 0
    · subst r
      simp [m, ccmGammaHigherBinetModeDensity]
    · exact (ccmGammaHigherBinetModeDensity_pos (abs_pos.mpr hr)).le
  have hd : 0 ≤ d := ccmGammaHigherBinetDualDensity_nonneg (abs_nonneg r)
  change ‖(Real.sqrt m : ℂ) • x + (Real.sqrt d : ℂ) • y‖ ^ 2 = _
  rw [norm_add_sq (𝕜 := ℂ)]
  have hmx : ‖(Real.sqrt m : ℂ) • x‖ ^ 2 = m * ‖x‖ ^ 2 := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt hm]
  have hdy : ‖(Real.sqrt d : ℂ) • y‖ ^ 2 = ‖y‖ ^ 2 * d := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt hd]
    ring
  rw [hmx, hdy]
  have hcross : (inner ℂ ((Real.sqrt m : ℂ) • x)
      ((Real.sqrt d : ℂ) • y)).re = (inner ℂ x y).re := by
    by_cases hr : r = 0
    · subst r
      have hx : x = 0 := by
        dsimp only [x]
        rw [logTranslationCLM_zero_apply]
        simp
      simp [hx]
    · have hroot : Real.sqrt m * Real.sqrt d = 1 := by
        calc
          Real.sqrt m * Real.sqrt d = Real.sqrt (m * d) := (Real.sqrt_mul hm d).symm
          _ = Real.sqrt 1 := by
            congr 1
            dsimp only [m, d]
            rw [ccmGammaHigherBinetModeDensity_mul_dual (abs_pos.mpr hr)]
          _ = 1 := Real.sqrt_one
      rw [inner_smul_left, inner_smul_right]
      have hstar : starRingEnd ℂ (Real.sqrt m : ℂ) = (Real.sqrt m : ℂ) := by simp
      have hrootC : (Real.sqrt m : ℂ) * (Real.sqrt d : ℂ) = 1 := by
        rw [← Complex.ofReal_mul, hroot]
        norm_num
      rw [hstar, ← mul_assoc, hrootC, one_mul]
  change m * ‖x‖ ^ 2 + 2 * (inner ℂ ((Real.sqrt m : ℂ) • x)
      ((Real.sqrt d : ℂ) • y)).re + ‖y‖ ^ 2 * d = _
  rw [hcross]
  dsimp only [m, d, x, y]
  rw [ccmActualHeadTranslationDefect_abs]
  rfl

/-- Exact integrated phase-square identity on the canonical actual head. -/
theorem ccmActualHeadCoherentQuantileGammaPhaseSquare_eq_actual_terms
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) :
    let f := ccmArchimedeanFormToAperture a u
    let N := Nat.floor (Real.exp (2 * a.1)) + 1
    ccmActualHeadCoherentQuantileGammaPhaseSquare (2 * a.1) N (f : SoninL2) =
      2 * ccmActualHeadGammaHigherBinetModeEnergy (f : SoninL2) +
        2 * ccmActualHeadCompletedQuantileCurrent a f +
        ccmActualHeadCoherentQuantileGammaChiSquare (2 * a.1) N (f : SoninL2) := by
  let f := ccmArchimedeanFormToAperture a u
  let N := Nat.floor (Real.exp (2 * a.1)) + 1
  have hmode := integrable_ccmGammaHigherBinetSymmetricEnergy_formDomain a u
  have hmode' : Integrable (fun r : ℝ =>
      ccmGammaHigherBinetModeDensity |r| *
        ccmActualHeadTranslationDefect |r| (f : SoninL2)) := by
    simpa only [f] using hmode
  have hinner := integrable_ccmActualHeadCompletedCoherentInnerField (2 * a.1) N (f : SoninL2)
  have hchi := integrable_ccmActualHeadCoherentQuantileGammaChiSquareDensity (2 * a.1) N (f : SoninL2)
  have hcurrent : (∫ r : ℝ, (inner ℂ (logTranslationCLM r (f : SoninL2) - f)
      (ccmActualHeadQuantileCompletedCoherentField (2 * a.1) N (f : SoninL2) r)).re) =
      ccmActualHeadCompletedQuantileCurrent a f := by
    unfold ccmActualHeadCompletedQuantileCurrent
    exact (ccmActualHeadCompletedQuantileCurrent_eq_integral_coherentField a f).symm
  dsimp only
  unfold ccmActualHeadCoherentQuantileGammaPhaseSquare
  calc
    _ = ∫ r : ℝ,
        ccmGammaHigherBinetModeDensity |r| * ccmActualHeadTranslationDefect |r| (f : SoninL2) +
          2 * (inner ℂ (logTranslationCLM r (f : SoninL2) - f)
            (ccmActualHeadQuantileCompletedCoherentField (2 * a.1) N (f : SoninL2) r)).re +
          ‖ccmActualHeadQuantileCompletedCoherentField (2 * a.1) N (f : SoninL2) r‖ ^ 2 *
            ccmGammaHigherBinetDualDensity |r| := by
      apply integral_congr_ae
      filter_upwards with r
      exact ccmActualHeadCoherentQuantileGammaPhaseSquare_integrand_eq (2 * a.1) N (f : SoninL2) r
    _ = (∫ r : ℝ,
          ccmGammaHigherBinetModeDensity |r| * ccmActualHeadTranslationDefect |r| (f : SoninL2)) +
          (∫ r : ℝ, 2 * (inner ℂ (logTranslationCLM r (f : SoninL2) - f)
            (ccmActualHeadQuantileCompletedCoherentField (2 * a.1) N (f : SoninL2) r)).re) +
          (∫ r : ℝ, ‖ccmActualHeadQuantileCompletedCoherentField (2 * a.1) N (f : SoninL2) r‖ ^ 2 *
            ccmGammaHigherBinetDualDensity |r|) := by
      have hsum := hmode'.add (hinner.const_mul 2)
      have hsumint := integral_add hmode' (hinner.const_mul 2)
      calc
        _ = (∫ r : ℝ,
            ccmGammaHigherBinetModeDensity |r| * ccmActualHeadTranslationDefect |r| (f : SoninL2) +
              2 * (inner ℂ (logTranslationCLM r (f : SoninL2) - f)
                (ccmActualHeadQuantileCompletedCoherentField (2 * a.1) N (f : SoninL2) r)).re) +
            (∫ r : ℝ, ‖ccmActualHeadQuantileCompletedCoherentField (2 * a.1) N (f : SoninL2) r‖ ^ 2 *
              ccmGammaHigherBinetDualDensity |r|) := by
          simpa only [Pi.add_apply] using integral_add hsum hchi
        _ = _ := by
          have h := congrArg (fun z : ℝ => z +
              (∫ r : ℝ, ‖ccmActualHeadQuantileCompletedCoherentField (2 * a.1) N (f : SoninL2) r‖ ^ 2 *
                ccmGammaHigherBinetDualDensity |r|)) hsumint
          simpa only [Pi.add_apply] using h
    _ = _ := by
      rw [MeasureTheory.integral_const_mul,
        integral_ccmGammaHigherBinetSymmetricEnergy_formDomain a u, hcurrent]
      rfl

/-- Exact source normal form whose only unsolved datum is phase-sensitive, not a norm bound. -/
theorem ccmRestrictedWeilSourceQuadratic_eq_coherentQuantileGammaPhaseSquare_normalForm
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) :
    let f := ccmArchimedeanFormToAperture a u
    let N := Nat.floor (Real.exp (2 * a.1)) + 1
    ccmRestrictedWeilSourceQuadratic a u =
      (2 * gammaHardyPhaseRate 0 + 4) * ‖f‖ ^ 2 +
        ccmActualHeadCoherentQuantileGammaPhaseSquare (2 * a.1) N (f : SoninL2) -
          ccmActualHeadGammaHigherBinetModeEnergy (f : SoninL2) -
          ccmActualHeadCoherentQuantileGammaChiSquare (2 * a.1) N (f : SoninL2) := by
  let f := ccmArchimedeanFormToAperture a u
  let N := Nat.floor (Real.exp (2 * a.1)) + 1
  have hsource := ccmRestrictedWeilSourceQuadratic_eq_quantileAutocorrelation a u
  have hphase := ccmActualHeadCoherentQuantileGammaPhaseSquare_eq_actual_terms a u
  let S := ccmOutgoingQuantileCellAutocorrelationCurrent N (f : SoninL2)
  let R := ∫ h in ccmOutgoingPrimeQuantileBoundary N..(2 * a.1),
    Real.exp (h / 2) * ccmActualHeadSymmetricAutocorrelation h (f : SoninL2)
  have hout' : ccmActualHeadOutgoingQuantileAutocorrelationCurrent a f =
      4 * ‖f‖ ^ 2 + 2 * S + 2 * R := by
    unfold ccmActualHeadOutgoingQuantileAutocorrelationCurrent
    dsimp only [N, S, R, ccmOutgoingQuantileCellAutocorrelationCurrent]
  have hout : ccmActualHeadOutgoingQuantileAutocorrelationCurrent a f =
      4 * ‖f‖ ^ 2 + 2 * ccmActualHeadCompletedQuantileCurrent a f := by
    rw [hout']
    unfold ccmActualHeadCompletedQuantileCurrent
    dsimp only [N, S, R, ccmOutgoingQuantileCellAutocorrelationCurrent]
    ring
  dsimp only at hsource hphase ⊢
  rw [hsource, hout, hphase]
  ring

/-- Source nonnegativity is exactly the phase-sensitive gap inequality.  It does not follow from
the nonnegativity of the square alone, because the higher-Binet and coherent energies remain. -/
theorem ccmRestrictedWeilSourceQuadratic_nonneg_iff_coherentQuantileGammaPhaseSquare_gap
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) :
    let f := ccmArchimedeanFormToAperture a u
    let N := Nat.floor (Real.exp (2 * a.1)) + 1
    0 ≤ ccmRestrictedWeilSourceQuadratic a u ↔
      ccmActualHeadGammaHigherBinetModeEnergy (f : SoninL2) +
          ccmActualHeadCoherentQuantileGammaChiSquare (2 * a.1) N (f : SoninL2) ≤
        ccmActualHeadCoherentQuantileGammaPhaseSquare (2 * a.1) N (f : SoninL2) +
          (2 * gammaHardyPhaseRate 0 + 4) * ‖f‖ ^ 2 := by
  rw [ccmRestrictedWeilSourceQuadratic_eq_coherentQuantileGammaPhaseSquare_normalForm]
  constructor <;> intro h <;> linarith

end RHTower
