import GaloisForLFunctions.RHTower.CCMGuinandWeilArchimedeanFirstJet
import GaloisForLFunctions.RHTower.CCMPublishedRestrictedWeilMatrix

/-!
# Completed centered Guinand--Weil source matrix

This file reconstructs the whole published centered restricted-Weil matrix from its physical
source channels.  The polar and prime terms act as one order-zero continuous functional on the
compact horizon.  The singular Gamma term is treated at its actual distributional order: the odd
coordinate is endpoint-cancelled by the sine, while the diagonal uses the restricted-Weil
first-jet subtraction proved in `CCMGuinandWeilArchimedeanFirstJet`.

The capstone theorem is an entrywise identity for every positive aperture and every finite
centered packet, not only a source-vector comparison.
-/

noncomputable section

open scoped BigOperators Interval

namespace RHTower

open Matrix MeasureTheory Set Filter Topology

/-- Real interval expansion of the critical-Mellin pairing for every continuous real test. -/
theorem ccmCriticalMellinStieltjesPairing_real_re_interval
    {a : ℝ} (ha : 0 ≤ a) {F : ℝ → ℝ} (hF : Continuous F) :
    (criticalMellinStieltjesPairing a (fun h => (F h : ℂ))).re =
      (∫ h in (0 : ℝ)..(2 * a), F h * (2 * Real.cosh (h / 2))) -
      ∑ k ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊,
        criticalMellinAtomWeight k * F (Real.log k) := by
  let FC : ℝ → ℂ := fun h =>
    (F h : ℂ) * (2 * Real.cosh (h / 2) : ℂ)
  have hFCcont : Continuous FC := by
    dsimp only [FC]
    fun_prop
  have hFCint : Integrable FC (volume.restrict (Set.Ioc (0 : ℝ) (2 * a))) :=
    hFCcont.continuousOn.integrableOn_Icc.mono_set fun h hh => ⟨hh.1.le, hh.2⟩
  have hintRe :
      (∫ h in Set.Ioc (0 : ℝ) (2 * a), FC h).re =
        ∫ h in (0 : ℝ)..(2 * a), F h * (2 * Real.cosh (h / 2)) := by
    calc
      (∫ h in Set.Ioc (0 : ℝ) (2 * a), FC h).re =
          ∫ h in Set.Ioc (0 : ℝ) (2 * a), (FC h).re :=
        (integral_re hFCint).symm
      _ = ∫ h in Set.Ioc (0 : ℝ) (2 * a),
          F h * (2 * Real.cosh (h / 2)) := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with h
        dsimp only [FC]
        simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          zero_mul, sub_zero]
        norm_num
      _ = _ := (intervalIntegral.integral_of_le (by positivity :
        (0 : ℝ) ≤ 2 * a)).symm
  rw [criticalMellinStieltjesPairing, Complex.sub_re, hintRe]
  simp only [Complex.ofReal_re, Complex.re_sum, Complex.mul_re,
    Complex.ofReal_im, zero_mul, sub_zero]

/-- The order-zero polar--prime source reads the transported diagonal tent--cosine test exactly. -/
theorem ccmGuinandWeilPolarPrimeContinuousDiagonal_eq_critical
    {a : ℝ} (ha : 0 < a) (mode : ℤ) :
    ccmGuinandWeilContinuousDiagonalValue
        (ccmGuinandWeilPolarPrimeSourceFunctional ha) mode =
      (criticalMellinStieltjesPairing a
        (fun h => (ccmGuinandWeilDiagonalLogTest a mode h : ℂ))).re := by
  have hpole :
      2 * (∫ h in (0 : ℝ)..(2 * a),
        ccmGuinandWeilWeightedCosineCoordinate mode
            (ccmGuinandWeilLogToHorizon a h) *
          (2 * Real.cosh (h / 2))) =
        ∫ h in (0 : ℝ)..(2 * a),
          ccmGuinandWeilDiagonalLogTest a mode h *
            (2 * Real.cosh (h / 2)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro h hh
    have hh' : h ∈ Set.Icc (0 : ℝ) (2 * a) := by
      simpa [Set.uIcc_of_le (by positivity : (0 : ℝ) ≤ 2 * a)] using hh
    change 2 *
        (ccmGuinandWeilWeightedCosineCoordinate mode
            (ccmGuinandWeilLogToHorizon a h) * (2 * Real.cosh (h / 2))) =
      ccmGuinandWeilDiagonalLogTest a mode h * (2 * Real.cosh (h / 2))
    rw [← mul_assoc,
      ccmGuinandWeilWeightedCosineCoordinate_logToHorizon ha mode hh']
  have hprime :
      2 * (∑ k ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊,
        -criticalMellinAtomWeight k *
          ccmGuinandWeilWeightedCosineCoordinate mode
            (ccmGuinandWeilLogToHorizon a (Real.log k))) =
        -∑ k ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊,
          criticalMellinAtomWeight k *
            ccmGuinandWeilDiagonalLogTest a mode (Real.log k) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    have hklog := ccmGuinandWeilPrimeLog_mem (a := a) hk
    rw [← ccmGuinandWeilWeightedCosineCoordinate_logToHorizon ha mode hklog]
    ring
  rw [ccmGuinandWeilContinuousDiagonalValue,
    ccmGuinandWeilPolarPrimeSourceFunctional_apply,
    ccmCriticalMellinStieltjesPairing_real_re_interval ha.le (by
      unfold ccmGuinandWeilDiagonalLogTest
      fun_prop)]
  rw [mul_add, hpole, hprime]
  ring

/-- Singular Gamma contribution to the diagonal, with the restricted-Weil endpoint subtraction. -/
def ccmGuinandWeilArchimedeanDiagonalValue
    (a : ℝ) (mode : ℤ) : ℝ :=
  -ccmPublishedRestrictedArchimedeanPairing a
    (ccmGuinandWeilDiagonalLogTest a mode)

/-- Mixed-order diagonal source: continuous polar--prime channel plus renormalized Gamma channel. -/
def ccmGuinandWeilCompletedDiagonalValue
    {a : ℝ} (ha : 0 < a) (mode : ℤ) : ℝ :=
  ccmGuinandWeilContinuousDiagonalValue
      (ccmGuinandWeilPolarPrimeSourceFunctional ha) mode +
    ccmGuinandWeilArchimedeanDiagonalValue a mode

/-- The completed physical diagonal is exactly the published restricted-Weil tent--cosine value. -/
theorem ccmGuinandWeilCompletedDiagonalValue_eq_restrictedWeil
    {a : ℝ} (ha : 0 < a) (mode : ℤ) :
    ccmGuinandWeilCompletedDiagonalValue ha mode =
      ccmPublishedRestrictedWeilPairing a
        (ccmGuinandWeilDiagonalLogTest a mode) := by
  rw [ccmGuinandWeilCompletedDiagonalValue, ccmGuinandWeilArchimedeanDiagonalValue,
    ccmGuinandWeilPolarPrimeContinuousDiagonal_eq_critical ha mode,
    ccmPublishedRestrictedWeilPairing]
  ring

/-- Integer-mode extension of the literal polar--prime odd-source dictionary. -/
theorem ccmGuinandWeilPolarPrimeIntegerOddSourceValue_eq_published
    {a : ℝ} (ha : 0 < a) (mode : ℤ) :
    ccmGuinandWeilContinuousSourceValue
        (ccmGuinandWeilPolarPrimeSourceFunctional ha) mode =
      ccmPublishedPolarPrimeSineCoefficient a
        (ccmGuinandWeilPhysicalFrequencyInt a mode) := by
  let xi := ccmGuinandWeilPhysicalFrequencyInt a mode
  have hpole :
      (∫ h in (0 : ℝ)..(2 * a),
        ccmGuinandWeilSineCoordinate mode
            (ccmGuinandWeilLogToHorizon a h) *
          (2 * Real.cosh (h / 2))) =
        -∫ h in (0 : ℝ)..(2 * a),
          Real.sin (xi * h) * (2 * Real.cosh (h / 2)) := by
    calc
      _ = ∫ h in (0 : ℝ)..(2 * a),
          (-Real.sin (xi * h)) * (2 * Real.cosh (h / 2)) := by
        apply intervalIntegral.integral_congr
        intro h hh
        have hh' : h ∈ Set.Icc (0 : ℝ) (2 * a) := by
          simpa [Set.uIcc_of_le (by positivity : (0 : ℝ) ≤ 2 * a)] using hh
        change ccmGuinandWeilSineCoordinate mode
              (ccmGuinandWeilLogToHorizon a h) * (2 * Real.cosh (h / 2)) =
          (-Real.sin (xi * h)) * (2 * Real.cosh (h / 2))
        rw [ccmGuinandWeilSineCoordinate_logToHorizon_int ha mode hh']
      _ = _ := by
        rw [← intervalIntegral.integral_neg]
        apply intervalIntegral.integral_congr
        intro h _hh
        ring
  have hprime :
      (∑ k ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊,
        -criticalMellinAtomWeight k *
          ccmGuinandWeilSineCoordinate mode
            (ccmGuinandWeilLogToHorizon a (Real.log k))) =
        ∑ k ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊,
          criticalMellinAtomWeight k * Real.sin (xi * Real.log k) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [ccmGuinandWeilSineCoordinate_logToHorizon_int ha mode
      (ccmGuinandWeilPrimeLog_mem hk)]
    dsimp only [xi]
    ring
  rw [ccmGuinandWeilContinuousSourceValue,
    ccmGuinandWeilPolarPrimeSourceFunctional_apply, hpole, hprime,
    ccmPublishedPolarPrimeSineCoefficient,
    ccmCriticalMellinStieltjesPairing_sine_re_interval ha.le]
  dsimp only [xi]
  ring

/-- Endpoint-cancelled Gamma odd coordinate at an arbitrary integer mode. -/
def ccmGuinandWeilArchimedeanIntegerOddSourceValue
    (a : ℝ) (mode : ℤ) : ℝ :=
  -(∫ h in (0 : ℝ)..(2 * a),
      ccmGuinandWeilSineCoordinate mode
          (ccmGuinandWeilLogToHorizon a h) *
          ccmPublishedArchimedeanDensity h) / Real.pi

/-- The integer-mode Gamma odd integrand is genuinely interval integrable. -/
theorem ccmGuinandWeil_intervalIntegrable_archimedeanIntegerOddSourceIntegrand
    {a : ℝ} (ha : 0 < a) (mode : ℤ) :
    IntervalIntegrable
      (fun h : ℝ =>
        ccmGuinandWeilSineCoordinate mode
            (ccmGuinandWeilLogToHorizon a h) *
          ccmPublishedArchimedeanDensity h)
      volume 0 (2 * a) := by
  have hsin := ccmGuinandWeil_intervalIntegrable_sin_mul_archimedeanDensity
    (L := 2 * a) (xi := ccmGuinandWeilPhysicalFrequencyInt a mode)
      (by positivity)
  refine hsin.neg.congr ?_
  intro h hh
  rw [Set.uIoc_of_le (by positivity : (0 : ℝ) ≤ 2 * a)] at hh
  have hh' : h ∈ Set.Icc (0 : ℝ) (2 * a) := ⟨hh.1.le, hh.2⟩
  change -(Real.sin (ccmGuinandWeilPhysicalFrequencyInt a mode * h) *
      ccmPublishedArchimedeanDensity h) =
    ccmGuinandWeilSineCoordinate mode
        (ccmGuinandWeilLogToHorizon a h) *
      ccmPublishedArchimedeanDensity h
  rw [ccmGuinandWeilSineCoordinate_logToHorizon_int ha mode hh']
  ring

/-- The endpoint-cancelled integer Gamma source equals the published archimedean coefficient. -/
theorem ccmGuinandWeilArchimedeanIntegerOddSourceValue_eq_published
    {a : ℝ} (ha : 0 < a) (mode : ℤ) :
    ccmGuinandWeilArchimedeanIntegerOddSourceValue a mode =
      ccmPublishedArchimedeanSineCoefficient a
        (ccmGuinandWeilPhysicalFrequencyInt a mode) := by
  let xi := ccmGuinandWeilPhysicalFrequencyInt a mode
  have hcoordinate :
      (∫ h in (0 : ℝ)..(2 * a),
        ccmGuinandWeilSineCoordinate mode
            (ccmGuinandWeilLogToHorizon a h) *
          ccmPublishedArchimedeanDensity h) =
        -∫ h in (0 : ℝ)..(2 * a),
          Real.sin (xi * h) * ccmPublishedArchimedeanDensity h := by
    calc
      _ = ∫ h in (0 : ℝ)..(2 * a),
          (-Real.sin (xi * h)) * ccmPublishedArchimedeanDensity h := by
        apply intervalIntegral.integral_congr
        intro h hh
        have hh' : h ∈ Set.Icc (0 : ℝ) (2 * a) := by
          simpa [Set.uIcc_of_le (by positivity : (0 : ℝ) ≤ 2 * a)] using hh
        change ccmGuinandWeilSineCoordinate mode
              (ccmGuinandWeilLogToHorizon a h) *
              ccmPublishedArchimedeanDensity h =
          (-Real.sin (xi * h)) * ccmPublishedArchimedeanDensity h
        rw [ccmGuinandWeilSineCoordinate_logToHorizon_int ha mode hh']
      _ = _ := by
        rw [← intervalIntegral.integral_neg]
        apply intervalIntegral.integral_congr
        intro h _hh
        ring
  rw [ccmGuinandWeilArchimedeanIntegerOddSourceValue, hcoordinate,
    ccmPublishedArchimedeanSineCoefficient,
    ← intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * a)]
  ring

/-- Complete mixed-order odd source at every integer Fourier mode. -/
def ccmGuinandWeilCompletedIntegerOddSourceValue
    {a : ℝ} (ha : 0 < a) (mode : ℤ) : ℝ :=
  ccmGuinandWeilContinuousSourceValue
      (ccmGuinandWeilPolarPrimeSourceFunctional ha) mode +
    ccmGuinandWeilArchimedeanIntegerOddSourceValue a mode

/-- Integer-mode complete source dictionary, including polar, prime, and Gamma channels. -/
theorem ccmGuinandWeilCompletedIntegerOddSourceValue_eq_published
    {a : ℝ} (ha : 0 < a) (mode : ℤ) :
    ccmGuinandWeilCompletedIntegerOddSourceValue ha mode =
      ccmPublishedSourceSineCoefficient a
        (ccmGuinandWeilPhysicalFrequencyInt a mode) := by
  rw [ccmGuinandWeilCompletedIntegerOddSourceValue,
    ccmGuinandWeilPolarPrimeIntegerOddSourceValue_eq_published ha mode,
    ccmGuinandWeilArchimedeanIntegerOddSourceValue_eq_published ha mode,
    ccmPublishedSourceSineCoefficient]
  ring

/-- Integer physical frequency specializes definitionally to the published centered frequency. -/
theorem ccmGuinandWeilPhysicalFrequencyInt_centered
    (a : ℝ) (N : ℕ) (i : Fin (2 * N + 1)) :
    ccmGuinandWeilPhysicalFrequencyInt a (ccmPublishedCenteredMode N i) =
      ccmPublishedCenteredFrequency a N i := by
  rfl

/-- Completed odd source restricted to a finite centered packet. -/
def ccmGuinandWeilCompletedCenteredSource
    {a : ℝ} (ha : 0 < a) (N : ℕ) (i : Fin (2 * N + 1)) : ℝ :=
  ccmGuinandWeilCompletedIntegerOddSourceValue ha (ccmPublishedCenteredMode N i)

/-- Completed diagonal source restricted to a finite centered packet. -/
def ccmGuinandWeilCompletedCenteredDiagonal
    {a : ℝ} (ha : 0 < a) (N : ℕ) (i : Fin (2 * N + 1)) : ℝ :=
  ccmGuinandWeilCompletedDiagonalValue ha (ccmPublishedCenteredMode N i)

/-- Every completed centered odd coordinate equals its published source coordinate. -/
theorem ccmGuinandWeilCompletedCenteredSource_eq_published
    {a : ℝ} (ha : 0 < a) (N : ℕ) (i : Fin (2 * N + 1)) :
    ccmGuinandWeilCompletedCenteredSource ha N i =
      ccmPublishedCenteredSource a N i := by
  rw [ccmGuinandWeilCompletedCenteredSource,
    ccmGuinandWeilCompletedIntegerOddSourceValue_eq_published,
    ccmGuinandWeilPhysicalFrequencyInt_centered,
    ccmPublishedCenteredSource_eq_sourceSineCoefficient]

/-- Every completed centered diagonal coordinate equals its published diagonal coordinate. -/
theorem ccmGuinandWeilCompletedCenteredDiagonal_eq_published
    {a : ℝ} (ha : 0 < a) (N : ℕ) (i : Fin (2 * N + 1)) :
    ccmGuinandWeilCompletedCenteredDiagonal ha N i =
      ccmPublishedCenteredDiagonal a N i := by
  rw [ccmGuinandWeilCompletedCenteredDiagonal,
    ccmGuinandWeilCompletedDiagonalValue_eq_restrictedWeil,
    ccmPublishedCenteredDiagonal]
  congr 2

/-- Whole divided-difference packet generated by the completed mixed-order physical source. -/
def ccmGuinandWeilCompletedCenteredSourceMatrix
    {a : ℝ} (ha : 0 < a) (N : ℕ) :
    Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℝ :=
  ccmDividedDifferenceMatrix
    (ccmPublishedCenteredClock N)
    (ccmGuinandWeilCompletedCenteredSource ha N)
    (ccmGuinandWeilCompletedCenteredDiagonal ha N)

/-- **Whole-matrix source weld.** The completed physical source packet is exactly the published
restricted-Weil matrix for every positive aperture and every centered packet size. -/
theorem ccmGuinandWeilCompletedCenteredSourceMatrix_eq_published
    {a : ℝ} (ha : 0 < a) (N : ℕ) :
    ccmGuinandWeilCompletedCenteredSourceMatrix ha N =
      ccmPublishedRestrictedWeilMatrix a N := by
  have hsource : ccmGuinandWeilCompletedCenteredSource ha N =
      ccmPublishedCenteredSource a N := by
    funext i
    exact ccmGuinandWeilCompletedCenteredSource_eq_published ha N i
  have hdiagonal : ccmGuinandWeilCompletedCenteredDiagonal ha N =
      ccmPublishedCenteredDiagonal a N := by
    funext i
    exact ccmGuinandWeilCompletedCenteredDiagonal_eq_published ha N i
  rw [ccmGuinandWeilCompletedCenteredSourceMatrix, ccmPublishedRestrictedWeilMatrix,
    hsource, hdiagonal]

end RHTower
