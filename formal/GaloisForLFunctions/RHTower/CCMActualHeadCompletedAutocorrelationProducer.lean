import GaloisForLFunctions.RHTower.CCMActualHeadGammaWallOutgoingProducer

/-!
# Completed-error current on actual Gamma-head autocorrelations

For an actual aperture head `f`, let

`C_f(h) = Re (<U_h f,f> + <U_{-h}f,f>)/2`.

Then `E_f(h)=2||f||^2-2C_f(h)`.  Substitution into the completed-error
quadrature cancels every scalar polar and prime mass exactly.  The remaining current is

`2 integral_[0,2a] 2 cosh(h/2) C_f(h) dh
  - 2 sum Lambda(n)/sqrt(n) C_f(log n)`.

After the first Binet Gamma mode is cancelled against the decaying polar half, the same current
has the outgoing normal form

`4||f||^2 + 2 integral_[0,2a] exp(h/2) C_f(h) dh
  - 2 sum Lambda(n)/sqrt(n) C_f(log n)`.

The full and outgoing producers are unconditionally equal to the restricted-Weil source
quadratic.  No derivative of the autocorrelation, RH premise, common-clock identification,
numerical computation, or new axiom is used.
-/

open Complex MeasureTheory Set Filter Topology
open scoped ENNReal InnerProduct InnerProductSpace BigOperators

noncomputable section

namespace RHTower

/-- Real symmetric autocorrelation of one literal physical head. -/
def ccmActualHeadSymmetricAutocorrelation (h : ℝ) (f : SoninL2) : ℝ :=
  (inner ℂ (logTranslationCLM h f) f +
    inner ℂ (logTranslationCLM (-h) f) f).re / 2

theorem continuous_ccmActualHeadSymmetricAutocorrelation (f : SoninL2) :
    Continuous fun h : ℝ => ccmActualHeadSymmetricAutocorrelation h f := by
  unfold ccmActualHeadSymmetricAutocorrelation
  have htrans : Continuous fun h : ℝ => logTranslationCLM h f :=
    continuous_logTranslationCLM f
  have htransNeg : Continuous fun h : ℝ => logTranslationCLM (-h) f :=
    htrans.comp continuous_neg
  exact (Complex.continuous_re.comp
    ((htrans.inner continuous_const).add
      (htransNeg.inner continuous_const))).div_const 2

/-- Translation loss is the scalar mass minus twice the real autocorrelation. -/
theorem ccmActualHeadTranslationDefect_eq_norm_sub_symmetricAutocorrelation
    (h : ℝ) (f : SoninL2) :
    ccmActualHeadTranslationDefect h f =
      2 * ‖f‖ ^ 2 - 2 * ccmActualHeadSymmetricAutocorrelation h f := by
  unfold ccmActualHeadTranslationDefect ccmActualHeadSymmetricAutocorrelation
  rw [logTranslation_defect_eq]
  ring

/-- Completed-error Stieltjes current evaluated directly on the actual head autocorrelation. -/
def ccmActualHeadCompletedErrorAutocorrelationCurrent
    (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a) : ℝ :=
  2 * (∫ h in Icc (0 : ℝ) (2 * a.1),
      2 * Real.cosh (h / 2) *
        ccmActualHeadSymmetricAutocorrelation h f.1) -
    2 * ∑ n ∈ Finset.Icc 2 (Nat.floor (Real.exp (2 * a.1))),
      criticalMellinAtomWeight n *
        ccmActualHeadSymmetricAutocorrelation (Real.log n) f.1

theorem ccmPrimeTranslationDefectEnergy_eq_mass_sub_autocorrelation
    (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a) :
    ccmPrimeTranslationDefectEnergy a f =
      2 * criticalMellinPrimeMass (2 * a.1) * ‖f‖ ^ 2 -
        2 * ∑ n ∈ Finset.Icc 2 (Nat.floor (Real.exp (2 * a.1))),
          criticalMellinAtomWeight n *
            ccmActualHeadSymmetricAutocorrelation (Real.log n) f.1 := by
  unfold ccmPrimeTranslationDefectEnergy
  change (∑ n ∈ Finset.Icc 2 (Nat.floor (Real.exp (2 * a.1))),
      criticalMellinAtomWeight n *
        ccmActualHeadTranslationDefect (Real.log n) f.1) = _
  simp_rw [ccmActualHeadTranslationDefect_eq_norm_sub_symmetricAutocorrelation]
  rw [criticalMellinPrimeMass_eq_atomSum]
  rw [show ‖(f.1 : SoninL2)‖ = ‖f‖ by rfl]
  calc
    (∑ n ∈ Finset.Icc 2 (Nat.floor (Real.exp (2 * a.1))),
        criticalMellinAtomWeight n *
          (2 * ‖f‖ ^ 2 -
            2 * ccmActualHeadSymmetricAutocorrelation (Real.log n) f.1)) =
        ∑ n ∈ Finset.Icc 2 (Nat.floor (Real.exp (2 * a.1))),
          (2 * (criticalMellinAtomWeight n * ‖f‖ ^ 2) -
            2 * (criticalMellinAtomWeight n *
              ccmActualHeadSymmetricAutocorrelation (Real.log n) f.1)) := by
      apply Finset.sum_congr rfl
      intro n hn
      ring
    _ = _ := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      rw [← Finset.sum_mul]
      ring

theorem ccmContinuousPolarTranslationDefectEnergy_eq_mass_sub_autocorrelation
    (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a) :
    ccmContinuousPolarTranslationDefectEnergy a f =
      8 * Real.sinh a.1 * ‖f‖ ^ 2 -
        2 * (∫ h in Icc (0 : ℝ) (2 * a.1),
          2 * Real.cosh (h / 2) *
            ccmActualHeadSymmetricAutocorrelation h f.1) := by
  let W : ℝ → ℝ := fun h => 2 * Real.cosh (h / 2)
  let C : ℝ → ℝ := fun h => ccmActualHeadSymmetricAutocorrelation h f.1
  have hW : Continuous W := by
    dsimp only [W]
    fun_prop
  have hC : Continuous C := by
    exact continuous_ccmActualHeadSymmetricAutocorrelation f.1
  have hmass : IntegrableOn (fun h => (2 * ‖f‖ ^ 2) * W h)
      (Icc (0 : ℝ) (2 * a.1)) :=
    (continuous_const.mul hW).integrableOn_Icc
  have hcorr : IntegrableOn (fun h => 2 * (W h * C h))
      (Icc (0 : ℝ) (2 * a.1)) :=
    (continuous_const.mul (hW.mul hC)).integrableOn_Icc
  unfold ccmContinuousPolarTranslationDefectEnergy
  rw [show (∫ h in Icc (0 : ℝ) (2 * a.1),
      2 * Real.cosh (h / 2) * ccmActualHeadTranslationDefect h f.1) =
      ∫ h in Icc (0 : ℝ) (2 * a.1),
        (2 * ‖f‖ ^ 2) * W h - 2 * (W h * C h) by
    apply integral_congr_ae
    filter_upwards with h
    rw [ccmActualHeadTranslationDefect_eq_norm_sub_symmetricAutocorrelation]
    dsimp only [W, C]
    rw [show ‖(f.1 : SoninL2)‖ = ‖f‖ by rfl]
    ring]
  rw [integral_sub hmass hcorr]
  have hmassValue :
      (∫ h in Icc (0 : ℝ) (2 * a.1), (2 * ‖f‖ ^ 2) * W h) =
        8 * Real.sinh a.1 * ‖f‖ ^ 2 := by
    rw [integral_const_mul]
    have hWValue :
        (∫ h in Icc (0 : ℝ) (2 * a.1), W h) = 4 * Real.sinh a.1 := by
      simpa only [W] using integral_Icc_two_mul_cosh_half a
    rw [hWValue]
    ring
  have hcorrValue :
      (∫ h in Icc (0 : ℝ) (2 * a.1), 2 * (W h * C h)) =
        2 * ∫ h in Icc (0 : ℝ) (2 * a.1), W h * C h := by
    rw [integral_const_mul]
  rw [hmassValue, hcorrValue]

/-- Exact regularity-free integration-by-parts law: the completed-error defect quadrature is the
signed Stieltjes current on the actual autocorrelation. -/
theorem ccmActualHeadCompletedErrorQuadrature_eq_autocorrelationCurrent
    (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a) :
    ccmActualHeadCompletedErrorQuadrature a f =
      ccmActualHeadCompletedErrorAutocorrelationCurrent a f := by
  rw [ccmActualHeadCompletedErrorQuadrature,
    ccmPrimeTranslationDefectEnergy_eq_mass_sub_autocorrelation,
    ccmContinuousPolarTranslationDefectEnergy_eq_mass_sub_autocorrelation,
    ccmActualHeadTranslationDefect_two_aperture,
    criticalMellinCompletedError_eq_polar_sub_primeMass]
  unfold ccmActualHeadCompletedErrorAutocorrelationCurrent
  ring

/-- Full prime--polar--Gamma producer written only through one actual autocorrelation and the
positive Gamma translation energy. -/
def ccmRestrictedWeilActualHeadCompletedAutocorrelationProducer
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) : ℝ :=
  let f := ccmArchimedeanFormToAperture a u
  2 * gammaHardyPhaseRate 0 * ‖f‖ ^ 2 +
    ccmActualHeadGammaAutocorrelationEnergy (f : SoninL2) +
    ccmActualHeadCompletedErrorAutocorrelationCurrent a f

theorem ccmRestrictedWeilActualHeadCompletedAutocorrelationProducer_eq_sourceQuadratic
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) :
    ccmRestrictedWeilActualHeadCompletedAutocorrelationProducer a u =
      ccmRestrictedWeilSourceQuadratic a u := by
  rw [ccmRestrictedWeilActualHeadCompletedAutocorrelationProducer,
    ← ccmActualHeadCompletedErrorQuadrature_eq_autocorrelationCurrent]
  exact ccmRestrictedWeilActualHeadPrimePolarGammaProducer_eq_sourceQuadratic a u

/-- Growing-half polar autocorrelation current after cancellation of the first Gamma Binet mode. -/
def ccmActualHeadOutgoingAutocorrelationCurrent
    (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a) : ℝ :=
  4 * ‖f‖ ^ 2 +
    2 * (∫ h in Icc (0 : ℝ) (2 * a.1),
      Real.exp (h / 2) * ccmActualHeadSymmetricAutocorrelation h f.1) -
    2 * ∑ n ∈ Finset.Icc 2 (Nat.floor (Real.exp (2 * a.1))),
      criticalMellinAtomWeight n *
        ccmActualHeadSymmetricAutocorrelation (Real.log n) f.1

theorem integral_Icc_exp_half (a : SuzukiPositiveAperture) :
    (∫ h in Icc (0 : ℝ) (2 * a.1), Real.exp (h / 2)) =
      2 * Real.exp a.1 - 2 := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith [a.property])]
  let P : ℝ → ℝ := fun h => 2 * Real.exp (h / 2)
  have hderiv : ∀ x ∈ uIcc (0 : ℝ) (2 * a.1),
      HasDerivAt P (Real.exp (x / 2)) x := by
    intro x hx
    dsimp only [P]
    apply (((Real.hasDerivAt_exp (x / 2)).comp x
      ((hasDerivAt_id x).div_const 2)).const_mul 2).congr_deriv
    ring
  have hint : IntervalIntegrable (fun h : ℝ => Real.exp (h / 2))
      volume 0 (2 * a.1) := by
    exact (by fun_prop : Continuous fun h : ℝ =>
      Real.exp (h / 2)).intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  dsimp only [P]
  rw [show (2 * a.1) / 2 = a.1 by ring]
  norm_num

theorem ccmActualHeadOutgoingPolarEnergy_eq_mass_sub_autocorrelation
    (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a) :
    ccmActualHeadOutgoingPolarEnergy a f =
      (4 * Real.exp a.1 - 4) * ‖f‖ ^ 2 -
        2 * (∫ h in Icc (0 : ℝ) (2 * a.1),
          Real.exp (h / 2) *
            ccmActualHeadSymmetricAutocorrelation h f.1) := by
  let W : ℝ → ℝ := fun h => Real.exp (h / 2)
  let C : ℝ → ℝ := fun h => ccmActualHeadSymmetricAutocorrelation h f.1
  have hW : Continuous W := by
    dsimp only [W]
    fun_prop
  have hC : Continuous C :=
    continuous_ccmActualHeadSymmetricAutocorrelation f.1
  have hmass : IntegrableOn (fun h => (2 * ‖f‖ ^ 2) * W h)
      (Icc (0 : ℝ) (2 * a.1)) :=
    (continuous_const.mul hW).integrableOn_Icc
  have hcorr : IntegrableOn (fun h => 2 * (W h * C h))
      (Icc (0 : ℝ) (2 * a.1)) :=
    (continuous_const.mul (hW.mul hC)).integrableOn_Icc
  unfold ccmActualHeadOutgoingPolarEnergy
  rw [show (∫ h in Icc (0 : ℝ) (2 * a.1),
      Real.exp (h / 2) * ccmActualHeadTranslationDefect h f.1) =
      ∫ h in Icc (0 : ℝ) (2 * a.1),
        (2 * ‖f‖ ^ 2) * W h - 2 * (W h * C h) by
    apply integral_congr_ae
    filter_upwards with h
    rw [ccmActualHeadTranslationDefect_eq_norm_sub_symmetricAutocorrelation]
    dsimp only [W, C]
    rw [show ‖(f.1 : SoninL2)‖ = ‖f‖ by rfl]
    ring]
  rw [integral_sub hmass hcorr, integral_const_mul,
    integral_const_mul, integral_Icc_exp_half]
  dsimp only [W, C]
  ring

/-- First-Gamma-renormalized producer.  The arithmetic scalar mass has disappeared; only the
positive higher Gamma energy and signed boundary autocorrelation current remain. -/
def ccmRestrictedWeilActualHeadGammaBoundaryAutocorrelationProducer
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) : ℝ :=
  let f := ccmArchimedeanFormToAperture a u
  2 * gammaHardyPhaseRate 0 * ‖f‖ ^ 2 +
    ccmActualHeadGammaHigherBinetModeEnergy (f : SoninL2) +
    ccmActualHeadOutgoingAutocorrelationCurrent a f

theorem ccmRestrictedWeilActualHeadGammaBoundaryAutocorrelationProducer_eq_outgoingProducer
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) :
    ccmRestrictedWeilActualHeadGammaBoundaryAutocorrelationProducer a u =
      ccmRestrictedWeilActualHeadGammaWallOutgoingProducer a u := by
  rw [ccmRestrictedWeilActualHeadGammaBoundaryAutocorrelationProducer,
    ccmRestrictedWeilActualHeadGammaWallOutgoingProducer]
  rw [ccmActualHeadPrimeWallChordEnergy_formDomain,
    ccmPrimeTranslationDefectEnergy_eq_mass_sub_autocorrelation,
    ccmActualHeadOutgoingPolarEnergy_eq_mass_sub_autocorrelation,
    ccmActualHeadTranslationDefect_two_aperture]
  unfold ccmActualHeadOutgoingAutocorrelationCurrent
  ring

theorem ccmRestrictedWeilActualHeadGammaBoundaryAutocorrelationProducer_eq_sourceQuadratic
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) :
    ccmRestrictedWeilActualHeadGammaBoundaryAutocorrelationProducer a u =
      ccmRestrictedWeilSourceQuadratic a u := by
  rw [ccmRestrictedWeilActualHeadGammaBoundaryAutocorrelationProducer_eq_outgoingProducer,
    ccmRestrictedWeilActualHeadGammaWallOutgoingProducer_eq_sourceQuadratic]

theorem ccmRestrictedWeilCanonicalGroundHead_gammaBoundaryAutocorrelationProducer_eq_ground_add_tail
    (a : SuzukiPositiveAperture) (n : ℕ) :
    ccmRestrictedWeilActualHeadGammaBoundaryAutocorrelationProducer a
        (ccmRestrictedWeilCanonicalGroundHead a n) =
      ccmRestrictedWeilGroundEnergy a *
          ‖ccmArchimedeanFormToAperture a
            (ccmRestrictedWeilCanonicalGroundHead a n)‖ ^ 2 +
        ccmRestrictedWeilCanonicalGroundHeadDefect a n := by
  rw [ccmRestrictedWeilActualHeadGammaBoundaryAutocorrelationProducer_eq_outgoingProducer,
    ccmRestrictedWeilCanonicalGroundHead_gammaWallOutgoingProducer_eq_ground_add_tail]

theorem ccmRestrictedWeilCanonicalGroundHead_reversePrimeBound_iff_gammaBoundaryAutocorrelationProducer_nonneg
    (a : SuzukiPositiveAperture) (n : ℕ) :
    CCMRestrictedWeilCanonicalGroundHeadReversePrimeBound a n ↔
      0 ≤ ccmRestrictedWeilActualHeadGammaBoundaryAutocorrelationProducer a
        (ccmRestrictedWeilCanonicalGroundHead a n) := by
  rw [ccmRestrictedWeilCanonicalGroundHead_reversePrimeBound_iff_gammaWallOutgoingProducer_nonneg,
    ccmRestrictedWeilActualHeadGammaBoundaryAutocorrelationProducer_eq_outgoingProducer]

end RHTower
