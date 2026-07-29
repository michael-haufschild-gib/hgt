import GaloisForLFunctions.RHTower.CCMPublishedSourceSineCoefficient
import GaloisForLFunctions.RHTower.XiShiftPrimeExposure

/-!
# The even-shift sieve of the published CCM source

Multiplication by `1 - exp (-2h)` is the physical-space coboundary of the even spectral shift
`s ↦ s + 2`.  On the published CCM source it removes the singular archimedean density exactly:

`(1 - exp (-2h)) * rho_infinity(h) = exp (-h / 2)` for `h > 0`.

Thus the filtered finite-aperture source has an elementary Gamma channel and the polar--prime
part remains one coupled Stieltjes carrier.  At every physical CCM frequency, Stieltjes
integration by parts gives an exact completed-error derivative moment.  No sign or RH premise is
used.
-/

open scoped BigOperators
open MeasureTheory Set Finset

noncomputable section

namespace RHTower

/-- Test obtained from a damped sine by the physical-space coboundary of `s ↦ s + 2`. -/
def ccmPublishedEvenShiftSievedTest (sigma xi h : ℝ) : ℝ :=
  Real.exp (-sigma * h) * (1 - Real.exp (-2 * h)) * Real.sin (xi * h)

/-- The physical even-shift sieve is literally the difference of two damping translates. -/
theorem ccmPublishedEvenShiftSievedTest_eq_shiftDifference
    (sigma xi h : ℝ) :
    ccmPublishedEvenShiftSievedTest sigma xi h =
      Real.exp (-sigma * h) * Real.sin (xi * h) -
        Real.exp (-(sigma + 2) * h) * Real.sin (xi * h) := by
  rw [ccmPublishedEvenShiftSievedTest]
  rw [show -(sigma + 2) * h = -sigma * h + (-2 * h) by ring,
    Real.exp_add]
  ring

/-- Derivative of the even-shift-sieved sine test. -/
def ccmPublishedEvenShiftSievedTestDeriv (sigma xi h : ℝ) : ℝ :=
  (-sigma * Real.exp (-sigma * h)) * (1 - Real.exp (-2 * h)) * Real.sin (xi * h) +
    Real.exp (-sigma * h) * (2 * Real.exp (-2 * h)) * Real.sin (xi * h) +
    Real.exp (-sigma * h) * (1 - Real.exp (-2 * h)) *
      (xi * Real.cos (xi * h))

/-- Finite archimedean coefficient after the even-shift sieve. -/
def ccmPublishedEvenShiftSievedArchCoefficient (a sigma xi : ℝ) : ℝ :=
  (1 / Real.pi) * ∫ h in Ioc (0 : ℝ) (2 * a),
    ccmPublishedEvenShiftSievedTest sigma xi h * ccmPublishedArchimedeanDensity h

/-- Coupled polar--prime coefficient after the even-shift sieve. -/
def ccmPublishedEvenShiftSievedPolarPrimeCoefficient (a sigma xi : ℝ) : ℝ :=
  -(criticalMellinStieltjesPairing a
    (fun h => (ccmPublishedEvenShiftSievedTest sigma xi h : ℂ))).re / Real.pi

/-- Actual finite-aperture CCM source after applying the even damping coboundary. -/
def ccmPublishedEvenShiftSievedSourceCoefficient (a sigma xi : ℝ) : ℝ :=
  ccmPublishedEvenShiftSievedArchCoefficient a sigma xi +
    ccmPublishedEvenShiftSievedPolarPrimeCoefficient a sigma xi

/-- Completed-error derivative moment carrying every possible sign obstruction after the
even-shift sieve. -/
def ccmPublishedEvenShiftSievedCompletedErrorMoment (a sigma xi : ℝ) : ℝ :=
  (∫ h in Ioc (0 : ℝ) (2 * a),
    (criticalMellinCompletedError h : ℂ) *
      (ccmPublishedEvenShiftSievedTestDeriv sigma xi h : ℂ)).re

/-- The CCM Gamma density is removed exactly by the even damping coboundary. -/
theorem one_sub_exp_neg_two_mul_ccmPublishedArchimedeanDensity
    {h : ℝ} (hh : 0 < h) :
    (1 - Real.exp (-2 * h)) * ccmPublishedArchimedeanDensity h =
      Real.exp (-h / 2) := by
  rw [ccmPublishedArchimedeanDensity]
  have heh : Real.exp h ≠ 0 := ne_of_gt (Real.exp_pos h)
  have hehone : 1 < Real.exp h := by
    simpa using (Real.exp_lt_exp.mpr hh)
  have hsq : Real.exp h ^ 2 - 1 ≠ 0 := by
    have : 1 < Real.exp h ^ 2 := by nlinarith [hehone, Real.exp_pos h]
    linarith
  rw [show Real.exp (-2 * h) = (Real.exp (2 * h))⁻¹ by
    rw [← Real.exp_neg]; ring_nf]
  rw [show Real.exp (-h) = (Real.exp h)⁻¹ by rw [Real.exp_neg]]
  rw [show Real.exp (2 * h) = Real.exp h * Real.exp h by
    rw [← Real.exp_add]; ring_nf]
  rw [show Real.exp (-h / 2) = Real.exp (h / 2) / Real.exp h by
    rw [← Real.exp_sub]
    congr 1
    ring]
  field_simp [heh, hsq]

/-- The sieved archimedean coefficient is an ordinary exponentially damped sine integral; its
`1/h` singularity has disappeared. -/
theorem ccmPublishedEvenShiftSievedArchCoefficient_eq_elementary
    (a sigma xi : ℝ) :
    ccmPublishedEvenShiftSievedArchCoefficient a sigma xi =
      (1 / Real.pi) * ∫ h in Ioc (0 : ℝ) (2 * a),
        Real.exp (-(sigma + 1 / 2) * h) * Real.sin (xi * h) := by
  rw [ccmPublishedEvenShiftSievedArchCoefficient]
  congr 1
  apply MeasureTheory.integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with h hh
  have hhpos : 0 < h := hh.1
  have hd := one_sub_exp_neg_two_mul_ccmPublishedArchimedeanDensity hhpos
  rw [ccmPublishedEvenShiftSievedTest]
  calc
    Real.exp (-sigma * h) * (1 - Real.exp (-2 * h)) *
          Real.sin (xi * h) * ccmPublishedArchimedeanDensity h =
        Real.exp (-sigma * h) * Real.sin (xi * h) *
          ((1 - Real.exp (-2 * h)) * ccmPublishedArchimedeanDensity h) := by ring
    _ = Real.exp (-sigma * h) * Real.sin (xi * h) * Real.exp (-h / 2) := by rw [hd]
    _ = Real.exp (-(sigma + 1 / 2) * h) * Real.sin (xi * h) := by
      rw [show -(sigma + 1 / 2) * h = -sigma * h + (-h / 2) by ring,
        Real.exp_add]
      ring

/-- Elementary antiderivative for the exponentially damped sine exposed by the CCM
even-shift sieve. -/
def ccmPublishedDampedSinePrimitive (kappa xi h : ℝ) : ℝ :=
  Real.exp (-kappa * h) *
    (-kappa * Real.sin (xi * h) - xi * Real.cos (xi * h)) /
      (kappa ^ 2 + xi ^ 2)

/-- Derivative law for the damped-sine primitive. -/
theorem hasDerivAt_ccmPublishedDampedSinePrimitive
    {kappa xi : ℝ} (hden : kappa ^ 2 + xi ^ 2 ≠ 0) (h : ℝ) :
    HasDerivAt (ccmPublishedDampedSinePrimitive kappa xi)
      (Real.exp (-kappa * h) * Real.sin (xi * h)) h := by
  have hE : HasDerivAt (fun x : ℝ => Real.exp (-kappa * x))
      (-kappa * Real.exp (-kappa * h)) h := by
    convert (Real.hasDerivAt_exp (-kappa * h)).comp h
      ((hasDerivAt_id h).const_mul (-kappa)) using 1
    all_goals ring
  have hsin : HasDerivAt (fun x : ℝ => Real.sin (xi * x))
      (xi * Real.cos (xi * h)) h := by
    convert (Real.hasDerivAt_sin (xi * h)).comp h
      ((hasDerivAt_id h).const_mul xi) using 1
    all_goals ring
  have hcos : HasDerivAt (fun x : ℝ => Real.cos (xi * x))
      (-xi * Real.sin (xi * h)) h := by
    convert (Real.hasDerivAt_cos (xi * h)).comp h
      ((hasDerivAt_id h).const_mul xi) using 1
    all_goals ring
  have hnum : HasDerivAt
      (fun x : ℝ => -kappa * Real.sin (xi * x) - xi * Real.cos (xi * x))
      (-kappa * (xi * Real.cos (xi * h)) - xi * (-xi * Real.sin (xi * h))) h :=
    (hsin.const_mul (-kappa)).sub (hcos.const_mul xi)
  convert (hE.mul hnum).div_const (kappa ^ 2 + xi ^ 2) using 1
  all_goals
    dsimp only [ccmPublishedDampedSinePrimitive]
    field_simp
    ring

/-- Closed finite-aperture damped-sine integral when the endpoint completes a full period. -/
theorem integral_Ioc_exp_neg_mul_sin_of_full_period
    {kappa xi H : ℝ} (hH : 0 ≤ H) (hden : kappa ^ 2 + xi ^ 2 ≠ 0)
    (hsin : Real.sin (xi * H) = 0) (hcos : Real.cos (xi * H) = 1) :
    (∫ h in Ioc (0 : ℝ) H,
      Real.exp (-kappa * h) * Real.sin (xi * h)) =
        xi * (1 - Real.exp (-kappa * H)) / (kappa ^ 2 + xi ^ 2) := by
  rw [← intervalIntegral.integral_of_le hH]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun h _hh => hasDerivAt_ccmPublishedDampedSinePrimitive hden h)
    ((by fun_prop : Continuous (fun h : ℝ =>
      Real.exp (-kappa * h) * Real.sin (xi * h))).intervalIntegrable 0 H)]
  rw [ccmPublishedDampedSinePrimitive, ccmPublishedDampedSinePrimitive,
    hsin, hcos]
  simp only [Real.sin_zero, Real.cos_zero, mul_zero,
    Real.exp_zero, one_mul]
  field_simp
  ring

/-- The displayed derivative is the genuine derivative of the sieved test. -/
theorem hasDerivAt_ccmPublishedEvenShiftSievedTest
    (sigma xi h : ℝ) :
    HasDerivAt (ccmPublishedEvenShiftSievedTest sigma xi)
      (ccmPublishedEvenShiftSievedTestDeriv sigma xi h) h := by
  have hA : HasDerivAt (fun x : ℝ => Real.exp (-sigma * x))
      (-sigma * Real.exp (-sigma * h)) h := by
    convert (Real.hasDerivAt_exp (-sigma * h)).comp h
      ((hasDerivAt_id h).const_mul (-sigma)) using 1
    all_goals ring
  have hB : HasDerivAt (fun x : ℝ => 1 - Real.exp (-2 * x))
      (2 * Real.exp (-2 * h)) h := by
    convert (hasDerivAt_const h 1).sub
      ((Real.hasDerivAt_exp (-2 * h)).comp h
        ((hasDerivAt_id h).const_mul (-2))) using 1
    all_goals ring
  have hC : HasDerivAt (fun x : ℝ => Real.sin (xi * x))
      (xi * Real.cos (xi * h)) h := by
    convert (Real.hasDerivAt_sin (xi * h)).comp h
      ((hasDerivAt_id h).const_mul xi) using 1
    all_goals ring
  convert (hA.mul hB).mul hC using 1
  all_goals
    simp only [ccmPublishedEvenShiftSievedTestDeriv, Pi.mul_apply]
    ring

/-- Physical clock frequencies kill the endpoint of the sieved test just as they kill the
unfiltered sine test. -/
theorem ccmPublishedEvenShiftSievedTest_physical_endpoint
    {a : ℝ} (ha : a ≠ 0) (sigma : ℝ) (n : ℕ) :
    ccmPublishedEvenShiftSievedTest sigma
      (ccmPublishedPhysicalFrequency a n) (2 * a) = 0 := by
  rw [ccmPublishedEvenShiftSievedTest,
    sin_ccmPublishedPhysicalFrequency_mul_endpoint ha n]
  ring

/-- Physical CCM frequencies also complete the cosine period at the aperture endpoint. -/
theorem ccmPublishedPhysicalFrequency_cos_endpoint
    {a : ℝ} (ha : a ≠ 0) (n : ℕ) :
    Real.cos (ccmPublishedPhysicalFrequency a n * (2 * a)) = 1 := by
  have harg : ccmPublishedPhysicalFrequency a n * (2 * a) =
      n * (2 * Real.pi) := by
    rw [ccmPublishedPhysicalFrequency]
    field_simp
  rw [harg, Real.cos_nat_mul_two_pi]

/-- **Positive Gamma law for the physical CCM even-shift sieve.**  The full-period clock turns
the desingularized Gamma channel into one explicit positive rational-exponential term. -/
theorem ccmPublishedEvenShiftSievedArchCoefficient_physical_eq
    {a kappa : ℝ} (ha : 0 < a) (hkappa : 0 < kappa) (n : ℕ) :
    ccmPublishedEvenShiftSievedArchCoefficient a (kappa - 1 / 2)
        (ccmPublishedPhysicalFrequency a n) =
      (1 / Real.pi) *
        (ccmPublishedPhysicalFrequency a n *
          (1 - Real.exp (-kappa * (2 * a))) /
            (kappa ^ 2 + ccmPublishedPhysicalFrequency a n ^ 2)) := by
  rw [ccmPublishedEvenShiftSievedArchCoefficient_eq_elementary]
  have hden : kappa ^ 2 + ccmPublishedPhysicalFrequency a n ^ 2 ≠ 0 := by
    positivity
  rw [show -((kappa - 1 / 2) + 1 / 2) = -kappa by ring]
  rw [integral_Ioc_exp_neg_mul_sin_of_full_period (by positivity) hden
    (sin_ccmPublishedPhysicalFrequency_mul_endpoint ha.ne' n)
    (ccmPublishedPhysicalFrequency_cos_endpoint ha.ne' n)]

/-- The physical Gamma term is strictly positive at every nonzero clock mode. -/
theorem ccmPublishedEvenShiftSievedArchCoefficient_physical_pos
    {a kappa : ℝ} (ha : 0 < a) (hkappa : 0 < kappa) {n : ℕ} (hn : 0 < n) :
    0 < ccmPublishedEvenShiftSievedArchCoefficient a (kappa - 1 / 2)
      (ccmPublishedPhysicalFrequency a n) := by
  rw [ccmPublishedEvenShiftSievedArchCoefficient_physical_eq ha hkappa n]
  have hxi : 0 < ccmPublishedPhysicalFrequency a n := by
    rw [ccmPublishedPhysicalFrequency]
    positivity
  have hexp : Real.exp (-kappa * (2 * a)) < 1 := by
    rw [← Real.exp_zero]
    apply Real.exp_lt_exp.mpr
    have : 0 < kappa * (2 * a) := by positivity
    linarith
  positivity

/-- Stieltjes integration by parts for the filtered polar--prime channel. -/
theorem ccmPublishedEvenShiftSievedPolarPrimeCoefficient_eq_completedErrorMoment
    {a : ℝ} (ha : 0 < a) (sigma : ℝ) (n : ℕ) :
    ccmPublishedEvenShiftSievedPolarPrimeCoefficient a sigma
        (ccmPublishedPhysicalFrequency a n) =
      ccmPublishedEvenShiftSievedCompletedErrorMoment a sigma
        (ccmPublishedPhysicalFrequency a n) / Real.pi := by
  let xi : ℝ := ccmPublishedPhysicalFrequency a n
  let F : ℝ → ℂ := fun h => (ccmPublishedEvenShiftSievedTest sigma xi h : ℂ)
  let F' : ℝ → ℂ := fun h => (ccmPublishedEvenShiftSievedTestDeriv sigma xi h : ℂ)
  have hF : ∀ x ∈ Set.Icc (0 : ℝ) (2 * a), HasDerivAt F (F' x) x := by
    intro x _hx
    have hr := hasDerivAt_ccmPublishedEvenShiftSievedTest sigma xi x
    have hc :=
      (Complex.ofRealCLM.hasFDerivAt.comp x hr.hasFDerivAt).hasDerivAt
    simpa only [F, F', Function.comp_apply, ContinuousLinearMap.coe_comp,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
      one_smul] using hc
  have hF' : IntervalIntegrable F' volume 0 (2 * a) := by
    have hc : Continuous F' := by
      dsimp only [F', ccmPublishedEvenShiftSievedTestDeriv]
      fun_prop
    exact hc.intervalIntegrable 0 (2 * a)
  have hFend : F (2 * a) = 0 := by
    simp only [F]
    exact_mod_cast ccmPublishedEvenShiftSievedTest_physical_endpoint
      ha.ne' sigma n
  have hpair := criticalMellinStieltjesPairing_integrationByParts
    ha.le hF hF' hFend
  rw [ccmPublishedEvenShiftSievedPolarPrimeCoefficient, hpair]
  simp only [Complex.neg_re, neg_neg]
  rw [ccmPublishedEvenShiftSievedCompletedErrorMoment]

/-- **Finite CCM even-shift source law.**  The actual filtered source is the elementary
half-density sine channel plus one completed-error derivative moment. -/
theorem ccmPublishedEvenShiftSievedSourceCoefficient_physical_eq
    {a : ℝ} (ha : 0 < a) (sigma : ℝ) (n : ℕ) :
    ccmPublishedEvenShiftSievedSourceCoefficient a sigma
        (ccmPublishedPhysicalFrequency a n) =
      (1 / Real.pi) * (∫ h in Ioc (0 : ℝ) (2 * a),
        Real.exp (-(sigma + 1 / 2) * h) *
          Real.sin (ccmPublishedPhysicalFrequency a n * h)) +
      ccmPublishedEvenShiftSievedCompletedErrorMoment a sigma
        (ccmPublishedPhysicalFrequency a n) / Real.pi := by
  rw [ccmPublishedEvenShiftSievedSourceCoefficient,
    ccmPublishedEvenShiftSievedArchCoefficient_eq_elementary,
    ccmPublishedEvenShiftSievedPolarPrimeCoefficient_eq_completedErrorMoment ha sigma n]

/-- **Finite-aperture Euler--Gamma separation law.**  At every physical mode the complete
even-shift-sieved CCM source is an explicit positive Gamma budget plus exactly one arithmetic
completed-error moment, with no residual archimedean singularity. -/
theorem ccmPublishedEvenShiftSievedSourceCoefficient_physical_closed
    {a kappa : ℝ} (ha : 0 < a) (hkappa : 0 < kappa) (n : ℕ) :
    ccmPublishedEvenShiftSievedSourceCoefficient a (kappa - 1 / 2)
        (ccmPublishedPhysicalFrequency a n) =
      (ccmPublishedPhysicalFrequency a n *
          (1 - Real.exp (-kappa * (2 * a))) /
            (kappa ^ 2 + ccmPublishedPhysicalFrequency a n ^ 2) +
        ccmPublishedEvenShiftSievedCompletedErrorMoment a (kappa - 1 / 2)
          (ccmPublishedPhysicalFrequency a n)) / Real.pi := by
  rw [ccmPublishedEvenShiftSievedSourceCoefficient,
    ccmPublishedEvenShiftSievedArchCoefficient_physical_eq ha hkappa n,
    ccmPublishedEvenShiftSievedPolarPrimeCoefficient_eq_completedErrorMoment
      ha (kappa - 1 / 2) n]
  ring

/-- **Exact obstruction threshold.**  A negative physical sieved CCM source occurs precisely
when the completed prime-error moment crosses the negative of the explicit positive Gamma
budget.  This is the sharp remaining source inequality, not an estimate. -/
theorem ccmPublishedEvenShiftSievedSourceCoefficient_physical_neg_iff
    {a kappa : ℝ} (ha : 0 < a) (hkappa : 0 < kappa) (n : ℕ) :
    ccmPublishedEvenShiftSievedSourceCoefficient a (kappa - 1 / 2)
        (ccmPublishedPhysicalFrequency a n) < 0 ↔
      ccmPublishedEvenShiftSievedCompletedErrorMoment a (kappa - 1 / 2)
          (ccmPublishedPhysicalFrequency a n) <
        -(ccmPublishedPhysicalFrequency a n *
          (1 - Real.exp (-kappa * (2 * a))) /
            (kappa ^ 2 + ccmPublishedPhysicalFrequency a n ^ 2)) := by
  rw [ccmPublishedEvenShiftSievedSourceCoefficient_physical_closed ha hkappa n]
  constructor
  · intro hneg
    rcases (div_neg_iff.mp hneg) with hbad | hsum
    · exact False.elim ((not_lt_of_ge Real.pi_pos.le) hbad.2)
    · linarith [hsum.1]
  · intro hmoment
    apply div_neg_iff.mpr
    right
    exact ⟨by linarith, Real.pi_pos⟩

end RHTower
