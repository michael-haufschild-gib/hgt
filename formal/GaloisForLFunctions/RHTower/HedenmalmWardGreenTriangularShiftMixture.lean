import GaloisForLFunctions.RHTower.HedenmalmWardGreenRemovableExtensionKernelProjection
import GaloisForLFunctions.RHTower.XiWardCubicTranslationEnergySeparator

/-!
# Triangular positive-shift representation of the removable Ward kernel

The inverse-square Ward defect is exactly a compact triangular Laplace mixture of reflected
exponentials, including its removable value at zero. Rewriting those exponentials as normalized
positive source-shift energy gains removes inverse-Green division before the five-shift scalar is
formed. This is a source-operation landing; it does not yet provide the height-local arithmetic
trace ceiling.
-/

open Complex MeasureTheory Set
open scoped Interval

namespace RHTower

noncomputable section

open HedenmalmThetaSource

def wardTriangularExpPairMixture (k a : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..2 * k,
    (2 * k - u) * (Real.exp (u * a) + Real.exp (-(u * a)))

theorem wardTriangularExpPairMixture_eq (k a : ℝ) :
    wardTriangularExpPairMixture k a = wardRemovableExpPairQuotient k a := by
  by_cases ha : a = 0
  · subst a
    rw [wardTriangularExpPairMixture, wardRemovableExpPairQuotient_zero]
    simp only [mul_zero, neg_zero, Real.exp_zero]
    have haffine :
        (∫ u in (0 : ℝ)..2 * k, (2 * k - u)) = 2 * k ^ (2 : ℕ) := by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := fun u : ℝ => 2 * k * u - u ^ (2 : ℕ) / 2)]
      · ring
      · intro u _hu
        have hraw := (((hasDerivAt_id u).const_mul (2 * k)).sub
          (((hasDerivAt_id u).pow 2).div_const 2))
        convert hraw using 1
        · ext x
          simp
        · simp
      · exact (show Continuous (fun u : ℝ => 2 * k - u) by fun_prop).intervalIntegrable _ _
    rw [show (fun u : ℝ => (2 * k - u) * (1 + 1)) =
        fun u : ℝ => 2 * (2 * k - u) by funext u; ring,
      intervalIntegral.integral_const_mul, haffine]
    ring

  · have hplus (u : ℝ) :
        HasDerivAt
          (fun x : ℝ => Real.exp (x * a) *
            ((2 * k - x) / a + 1 / a ^ (2 : ℕ)))
          ((2 * k - u) * Real.exp (u * a)) u := by
      have hraw := ((Real.hasDerivAt_exp (u * a)).comp u
          ((hasDerivAt_id u).mul_const a)).mul
        ((((hasDerivAt_const u (2 * k)).sub (hasDerivAt_id u)).div_const a).add_const
          (1 / a ^ (2 : ℕ)))
      have hcalc :
          Real.exp (u * a) * (1 * a) *
                (((fun x : ℝ => 2 * k) - (id : ℝ → ℝ)) u / a + 1 / a ^ (2 : ℕ)) +
              (Real.exp ∘ fun y : ℝ => id y * a) u * ((0 - 1) / a) =
            (2 * k - u) * Real.exp (u * a) := by
        simp
        field_simp [ha]
        ring
      have hraw' : HasDerivAt
          ((Real.exp ∘ fun y : ℝ => id y * a) *
            fun x : ℝ => ((fun _ : ℝ => 2 * k) - (id : ℝ → ℝ)) x / a + 1 / a ^ (2 : ℕ))
          ((2 * k - u) * Real.exp (u * a)) u := by
        rw [← hcalc]
        exact hraw
      exact hraw'.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun x => by
        simp [Function.comp_def]))
    have hminus (u : ℝ) :
        HasDerivAt
          (fun x : ℝ => Real.exp (-(x * a)) *
            (-((2 * k - x) / a) + 1 / a ^ (2 : ℕ)))
          ((2 * k - u) * Real.exp (-(u * a))) u := by
      have hinner : HasDerivAt (fun x : ℝ => -x * a) (-a) u := by
        simpa [Function.comp_def] using
          ((hasDerivAt_neg (u * a)).comp u ((hasDerivAt_id u).mul_const a))
      have hraw := ((Real.hasDerivAt_exp (-u * a)).comp u hinner).mul
        (((((hasDerivAt_const u (2 * k)).sub (hasDerivAt_id u)).div_const a).neg).add_const
          (1 / a ^ (2 : ℕ)))
      have hcalc :
          Real.exp (-u * a) * -a *
                ((-fun x : ℝ => ((fun _ : ℝ => 2 * k) - (id : ℝ → ℝ)) x / a) u +
                  1 / a ^ (2 : ℕ)) +
              (Real.exp ∘ fun x : ℝ => -x * a) u * -((0 - 1) / a) =
            (2 * k - u) * Real.exp (-(u * a)) := by
        simp [neg_mul]
        field_simp [ha]
        ring
      have hraw' : HasDerivAt
          ((Real.exp ∘ fun x : ℝ => -x * a) *
            fun x : ℝ =>
              (-fun y : ℝ => ((fun _ : ℝ => 2 * k) - (id : ℝ → ℝ)) y / a) x +
                1 / a ^ (2 : ℕ))
          ((2 * k - u) * Real.exp (-(u * a))) u := by
        rw [← hcalc]
        exact hraw
      exact hraw'.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun x => by
        simp [Function.comp_def, neg_mul]))
    have hplusInt : IntervalIntegrable
        (fun u : ℝ => (2 * k - u) * Real.exp (u * a)) volume 0 (2 * k) := by
      exact (show Continuous (fun u : ℝ =>
        (2 * k - u) * Real.exp (u * a)) by fun_prop).intervalIntegrable _ _
    have hminusInt : IntervalIntegrable
        (fun u : ℝ => (2 * k - u) * Real.exp (-(u * a))) volume 0 (2 * k) := by
      exact (show Continuous (fun u : ℝ =>
        (2 * k - u) * Real.exp (-(u * a))) by fun_prop).intervalIntegrable _ _
    rw [wardTriangularExpPairMixture]
    have hsplit :
        (∫ u in (0 : ℝ)..2 * k,
          (2 * k - u) * (Real.exp (u * a) + Real.exp (-(u * a)))) =
        (∫ u in (0 : ℝ)..2 * k, (2 * k - u) * Real.exp (u * a)) +
          ∫ u in (0 : ℝ)..2 * k, (2 * k - u) * Real.exp (-(u * a)) := by
      rw [← intervalIntegral.integral_add hplusInt hminusInt]
      apply intervalIntegral.integral_congr
      intro u hu
      ring
    rw [hsplit,
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun u _ => hplus u) hplusInt,
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun u _ => hminus u) hminusInt]
    rw [← invSq_expPairDefect_eq_wardRemovable ha]
    field_simp [ha]
    simp [Real.exp_zero]
    ring

theorem wardTriangularExpPairMixture_neg (k a : ℝ) :
    wardTriangularExpPairMixture k (-a) = wardTriangularExpPairMixture k a := by
  unfold wardTriangularExpPairMixture
  apply intervalIntegral.integral_congr
  intro u hu
  change (2 * k - u) *
      (Real.exp (u * -a) + Real.exp (-(u * -a))) =
    (2 * k - u) * (Real.exp (u * a) + Real.exp (-(u * a)))
  rw [show u * -a = -(u * a) by ring, neg_neg]
  ring

/-- The triangular pair kernel written using only positive source-shift energy gains. -/
def wardTriangularPositiveShiftPairGain (k : ℝ) (z : ℂ) : ℝ :=
  ∫ u in (0 : ℝ)..2 * k,
    (2 * k - u) *
      (centeredRealSourceShiftEnergyGain (u / 2) z +
        centeredRealSourceShiftEnergyGain (u / 2) (starRingEnd ℂ z))

theorem wardTriangularPositiveShiftPairGain_eq (k : ℝ) (z : ℂ) :
    wardTriangularPositiveShiftPairGain k z =
      wardRemovableExpPairQuotient k z.im := by
  rw [← wardTriangularExpPairMixture_eq k z.im]
  unfold wardTriangularPositiveShiftPairGain wardTriangularExpPairMixture
  apply intervalIntegral.integral_congr
  intro u hu
  change (2 * k - u) *
      (centeredRealSourceShiftEnergyGain (u / 2) z +
        centeredRealSourceShiftEnergyGain (u / 2) (starRingEnd ℂ z)) =
    (2 * k - u) * (Real.exp (u * z.im) + Real.exp (-(u * z.im)))
  rw [centeredRealSourceShiftEnergyGain_eq_exp,
    centeredRealSourceShiftEnergyGain_eq_exp]
  have hc : ((starRingEnd ℂ) z).im = -z.im := by simp
  rw [hc,
    show 2 * (u / 2) * z.im = u * z.im by ring,
    show 2 * (u / 2) * -z.im = -(u * z.im) by ring]

/-- Five-shift Ward scalar as one finite combination of compact positive-shift mixtures. -/
def fiveShiftWardTriangularPositiveShiftMixture (a : ℝ) : ℝ :=
  fiveShiftWardCoefficientOne * wardTriangularExpPairMixture 1 a -
    fiveShiftWardCoefficientTwo * wardTriangularExpPairMixture 2 a +
    fiveShiftWardCoefficientThree * wardTriangularExpPairMixture 3 a -
    fiveShiftWardCoefficientFour * wardTriangularExpPairMixture 4 a +
    wardTriangularExpPairMixture 5 a

theorem fiveShiftWardTriangularPositiveShiftMixture_eq (a : ℝ) :
    fiveShiftWardTriangularPositiveShiftMixture a =
      fiveShiftWardRemovableSourceScalar a := by
  simp only [fiveShiftWardTriangularPositiveShiftMixture,
    fiveShiftWardRemovableSourceScalar, wardTriangularExpPairMixture_eq]

theorem fiveShiftWardRemovableSourceScalar_neg (a : ℝ) :
    fiveShiftWardRemovableSourceScalar (-a) =
      fiveShiftWardRemovableSourceScalar a := by
  rw [← fiveShiftWardTriangularPositiveShiftMixture_eq (-a),
    ← fiveShiftWardTriangularPositiveShiftMixture_eq a]
  simp only [fiveShiftWardTriangularPositiveShiftMixture,
    wardTriangularExpPairMixture_neg]

/-- Five-shift removable scalar written entirely in compact positive source-shift gains. -/
def fiveShiftWardPositiveShiftPairGain (z : ℂ) : ℝ :=
  fiveShiftWardCoefficientOne * wardTriangularPositiveShiftPairGain 1 z -
    fiveShiftWardCoefficientTwo * wardTriangularPositiveShiftPairGain 2 z +
    fiveShiftWardCoefficientThree * wardTriangularPositiveShiftPairGain 3 z -
    fiveShiftWardCoefficientFour * wardTriangularPositiveShiftPairGain 4 z +
    wardTriangularPositiveShiftPairGain 5 z

theorem fiveShiftWardPositiveShiftPairGain_eq (z : ℂ) :
    fiveShiftWardPositiveShiftPairGain z =
      fiveShiftWardRemovableSourceScalar z.im := by
  simp only [fiveShiftWardPositiveShiftPairGain,
    fiveShiftWardRemovableSourceScalar, wardTriangularPositiveShiftPairGain_eq]

/-- The compact positive-shift mixture retains the uniform Ward quantum throughout the strip,
including the removable critical-line value. -/
theorem fiveShiftWardPositiveShiftPairGain_ge
    {z : ℂ} (hz : |z.im| ≤ 1 / 2) :
    1 / 81 ≤ fiveShiftWardPositiveShiftPairGain z := by
  rw [fiveShiftWardPositiveShiftPairGain_eq]
  by_cases hzero : z.im = 0
  · rw [hzero, fiveShiftWardRemovableSourceScalar_zero]
    exact fiveShiftWardKernelJump_ge
  · have habs0 : 0 < |z.im| := abs_pos.mpr hzero
    have hpunct : |z.im| ≠ 0 := ne_of_gt habs0
    have hbase := fiveShiftEulerGammaPairedRenormalizedFeature_one_ge habs0 hz
    rw [← fiveShiftWardRemovableSourceScalar_eq_renormalizedFeature hpunct] at hbase
    by_cases him : 0 ≤ z.im
    · rwa [abs_of_nonneg him] at hbase
    · have him' : z.im < 0 := lt_of_not_ge him
      rw [abs_of_neg him', fiveShiftWardRemovableSourceScalar_neg z.im] at hbase
      simpa using hbase

theorem fiveShiftWardGreenRemovableExtension_one_eq_sourceScalar (a : ℝ) :
    fiveShiftWardGreenRemovableExtension 1 a =
      fiveShiftWardRemovableSourceScalar a := by
  by_cases ha : a = 0
  · subst a
    simp [fiveShiftWardGreenRemovableExtension, fiveShiftWardKernelJump,
      fiveShiftWardPairCoefficientOne, fiveShiftWardPairCoefficientTwo,
      fiveShiftWardPairCoefficientThree, fiveShiftWardPairCoefficientFour,
      fiveShiftWardCoefficientOne, fiveShiftWardCoefficientTwo,
      fiveShiftWardCoefficientThree, fiveShiftWardCoefficientFour]
    ring
  · rw [← fiveShiftEulerGammaPairedRenormalizedFeature_eq_removableExtension 1 ha,
      ← fiveShiftWardRemovableSourceScalar_eq_renormalizedFeature ha]

/-- Copywise removable Ward current with inverse-Green division eliminated in favor of compact
positive source shifts. -/
theorem fiveShiftWardGreenRemovableCriticalFeatureCurrent_eq_positiveShiftPairGain
    (t : ℝ) (q : XiZeroCopy) :
    fiveShiftWardGreenRemovableCriticalFeatureCurrent t q =
      fiveShiftWardPositiveShiftPairGain (xiSpectralPoint q) *
        Complex.normSq (criticalFeatureCauchyKernelTest t (xiSpectralPoint q)) := by
  rw [fiveShiftWardGreenRemovableCriticalFeatureCurrent,
    fiveShiftWardGreenRemovableExtension_one_eq_sourceScalar,
    fiveShiftWardPositiveShiftPairGain_eq]
  have him : (xiSpectralPoint q).im = -((q.1 : ℂ).re - 1 / 2) := by
    rw [xiSpectralPoint_im_eq]
    ring
  rw [him, fiveShiftWardRemovableSourceScalar_neg]

end

end RHTower
