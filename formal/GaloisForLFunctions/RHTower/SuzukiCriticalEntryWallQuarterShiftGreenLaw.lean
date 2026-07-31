import GaloisForLFunctions.RHTower.SuzukiCausalEntryThirdJetBoundaryLaw
import GaloisForLFunctions.RHTower.SuzukiCriticalApertureQuarterShiftCurrent

/-!
# Critical entry-wall quarter-shift Green law

The delayed-hinge near/far gap satisfies an exact causal transport equation:

`(d/dell - I*z) gap'' = z^2 * exp (I*a*z) * endpointTrace`.

For a prime power `n = p^(e+1)`, its entry wall is `a = log(n)/2`.  At that wall the oscillatory
factor is exactly the conjugated critical Gamma-height phase `exp(I*t*log(n)/2)`.  Consequently
the existing quarter-shift atom is a uniquely calibrated third-jet entry forcing, and its geometric
depth resolvent is the exact sum of those forcings.  No RH premise, positivity hypothesis,
estimate, numerical computation, or Xi-zero data is used.
-/

open Complex
open scoped ComplexConjugate

namespace RHTower

noncomputable section

/-! ## Exact causal Green equation -/

/-- Second delay jet of the completed near/far gap. -/
def suzukiDelayedHingeCompletedGapJet2
    (ell : ℝ) (highMoment wholeMoment z : ℂ) : ℂ :=
  suzukiDelayedHingeNearCompletedJet2 ell highMoment z -
    suzukiDelayedHingeFarCompletedJet2 ell wholeMoment z

/-- Third delay jet of the completed near/far gap. -/
def suzukiDelayedHingeCompletedGapJet3
    (a ell : ℝ) (highMoment wholeMoment endpointTrace z : ℂ) : ℂ :=
  suzukiDelayedHingeNearCompletedJet3 a ell highMoment endpointTrace z -
    suzukiDelayedHingeFarCompletedJet3 ell wholeMoment z

/-- **All-depth entry Ward law.**  The transported third jet is exactly the endpoint reporter,
not merely at the entry wall. -/
theorem suzukiDelayedHingeCompletedGapJet3_sub_transport
    (a ell : ℝ) (highMoment wholeMoment endpointTrace z : ℂ) :
    suzukiDelayedHingeCompletedGapJet3 a ell highMoment wholeMoment endpointTrace z -
        I * z * suzukiDelayedHingeCompletedGapJet2 ell highMoment wholeMoment z =
      z ^ 2 * suzukiOscillatoryKernel z a * endpointTrace := by
  simp only [suzukiDelayedHingeCompletedGapJet3,
    suzukiDelayedHingeCompletedGapJet2,
    suzukiDelayedHingeNearCompletedJet2,
    suzukiDelayedHingeFarCompletedJet2,
    suzukiDelayedHingeNearCompletedJet3,
    suzukiDelayedHingeFarCompletedJet3]
  ring_nf

/-- The gap second jet differentiates to the gap third jet. -/
theorem hasDerivAt_suzukiDelayedHingeCompletedGapJet2
    (a ell : ℝ) (z endpointTrace wholeMoment : ℂ)
    (highMoment : ℝ → ℂ)
    (hHigh : HasDerivAt highMoment
      (suzukiOscillatoryKernel z (a - ell) * endpointTrace) ell) :
    HasDerivAt
      (fun u => suzukiDelayedHingeCompletedGapJet2 u
        (highMoment u) wholeMoment z)
      (suzukiDelayedHingeCompletedGapJet3 a ell
        (highMoment ell) wholeMoment endpointTrace z) ell := by
  have hnear := hasDerivAt_suzukiDelayedHingeNearCompletedJet2
    a ell z endpointTrace highMoment hHigh
  have hosc := hasDerivAt_suzukiOscillatoryKernel z ell
  have hfar : HasDerivAt
      (fun u => suzukiDelayedHingeFarCompletedJet2 u wholeMoment z)
      (suzukiDelayedHingeFarCompletedJet3 ell wholeMoment z) ell := by
    refine ((hosc.const_mul (z ^ 2)).mul_const wholeMoment).congr_deriv ?_
    simp only [suzukiDelayedHingeFarCompletedJet3]
    ring_nf
  exact hnear.sub hfar

/-- Differential form of the causal Green equation: the derivative of the second gap jet is its
transport part plus the endpoint forcing. -/
theorem hasDerivAt_suzukiDelayedHingeCompletedGapJet2_eq_transport_add_endpoint
    (a ell : ℝ) (z endpointTrace wholeMoment : ℂ)
    (highMoment : ℝ → ℂ)
    (hHigh : HasDerivAt highMoment
      (suzukiOscillatoryKernel z (a - ell) * endpointTrace) ell) :
    HasDerivAt
      (fun u => suzukiDelayedHingeCompletedGapJet2 u
        (highMoment u) wholeMoment z)
      (I * z * suzukiDelayedHingeCompletedGapJet2 ell
          (highMoment ell) wholeMoment z +
        z ^ 2 * suzukiOscillatoryKernel z a * endpointTrace) ell := by
  have hgap := hasDerivAt_suzukiDelayedHingeCompletedGapJet2
    a ell z endpointTrace wholeMoment highMoment hHigh
  convert hgap using 1
  have hward := suzukiDelayedHingeCompletedGapJet3_sub_transport
    a ell (highMoment ell) wholeMoment endpointTrace z
  calc
    I * z * suzukiDelayedHingeCompletedGapJet2 ell
          (highMoment ell) wholeMoment z +
        z ^ 2 * suzukiOscillatoryKernel z a * endpointTrace =
      z ^ 2 * suzukiOscillatoryKernel z a * endpointTrace +
        I * z * suzukiDelayedHingeCompletedGapJet2 ell
          (highMoment ell) wholeMoment z := by ring_nf
    _ = suzukiDelayedHingeCompletedGapJet3 a ell
        (highMoment ell) wholeMoment endpointTrace z :=
      (sub_eq_iff_eq_add.mp hward).symm

/-! ## Prime-power entry walls and critical phase -/

/-- Aperture at which the delay `log(p^(e+1))` enters the finite source interval. -/
def suzukiPrimePowerEntryWallAperture (p : Nat.Primes) (e : ℕ) : ℝ :=
  Real.log (xiGammaEulerValuationNat (p, e) : ℝ) / 2

theorem two_mul_suzukiPrimePowerEntryWallAperture
    (p : Nat.Primes) (e : ℕ) :
    2 * suzukiPrimePowerEntryWallAperture p e =
      Real.log (xiGammaEulerValuationNat (p, e) : ℝ) := by
  rw [suzukiPrimePowerEntryWallAperture]
  ring_nf

/-- One valuation step moves the entry wall by exactly half a prime logarithm. -/
theorem suzukiPrimePowerEntryWallAperture_succ
    (p : Nat.Primes) (e : ℕ) :
    suzukiPrimePowerEntryWallAperture p (e + 1) =
      suzukiPrimePowerEntryWallAperture p e + Real.log (p : ℝ) / 2 := by
  rw [suzukiPrimePowerEntryWallAperture, suzukiPrimePowerEntryWallAperture,
    xiGammaEulerValuationNat, xiGammaEulerValuationNat]
  push_cast
  rw [Real.log_pow, Real.log_pow]
  push_cast
  ring_nf

/-- The causal entry-wall phase is exactly the conjugated critical Gamma-height phase. -/
theorem suzukiOscillatoryKernel_primePowerEntryWall_eq_criticalPhase
    (t : ℝ) (p : Nat.Primes) (e : ℕ) :
    suzukiOscillatoryKernel (t : ℂ)
        (suzukiPrimePowerEntryWallAperture p e) =
      Complex.exp
        ((((t * Real.log (xiGammaEulerValuationNat (p, e) : ℝ) / 2 : ℝ) : ℂ) * I)) := by
  simp only [suzukiOscillatoryKernel, suzukiPrimePowerEntryWallAperture]
  congr 1
  push_cast
  ring_nf

/-- The wall phase itself has the exact half-log valuation recursion. -/
theorem suzukiOscillatoryKernel_primePowerEntryWall_succ
    (t : ℝ) (p : Nat.Primes) (e : ℕ) :
    suzukiOscillatoryKernel (t : ℂ)
        (suzukiPrimePowerEntryWallAperture p (e + 1)) =
      Complex.exp ((((t * Real.log (p : ℝ) / 2 : ℝ) : ℂ) * I)) *
        suzukiOscillatoryKernel (t : ℂ)
          (suzukiPrimePowerEntryWallAperture p e) := by
  rw [suzukiPrimePowerEntryWallAperture_succ]
  simp only [suzukiOscillatoryKernel, ← Complex.exp_add]
  congr 1
  push_cast
  ring_nf

/-! ## Exact quarter-shift calibration -/

/-- Real endpoint amplitude selected by the critical Gamma density and cubic aperture innovation.
The observer aperture `b` is deliberately distinct from the entry-wall aperture. -/
def suzukiCriticalEntryWallEndpointAmplitude
    (h b : ℝ) (p : Nat.Primes) (e : ℕ) : ℝ :=
  Real.sqrt
      (Real.log (p : ℝ) / (xiGammaEulerValuationNat (p, e) : ℝ) *
        Real.exp ((1 / 2 : ℝ) *
          Real.log (xiGammaEulerValuationNat (p, e) : ℝ))) *
    xiMobiusCubicNormalizedInnovationFeature h b (p, e)

/-- **Critical atom/entry-wall factorization.**  Every quarter-shift atom is its real endpoint
amplitude times the causal phase at the corresponding prime-power wall. -/
theorem suzukiCriticalApertureBoundaryAtom_eq_entryWallAmplitude_mul_kernel
    (h b t : ℝ) (p : Nat.Primes) (e : ℕ) :
    suzukiCriticalApertureBoundaryAtom h b t p e =
      (suzukiCriticalEntryWallEndpointAmplitude h b p e : ℂ) *
        suzukiOscillatoryKernel (t : ℂ)
          (suzukiPrimePowerEntryWallAperture p e) := by
  simp only [suzukiCriticalApertureBoundaryAtom,
    xiGammaEulerHeightBoundaryFeature,
    suzukiCriticalEntryWallEndpointAmplitude]
  simp only [show -(-1 / 2 : ℝ) = 1 / 2 by norm_num]
  rw [star_mul]
  change
    conj (Complex.exp
      (-(((t * Real.log (xiGammaEulerValuationNat (p, e) : ℝ) / 2 : ℝ) : ℂ) * I))) *
        conj ((Real.sqrt
          (Real.log (p : ℝ) / (xiGammaEulerValuationNat (p, e) : ℝ) *
            Real.exp ((1 / 2 : ℝ) *
              Real.log (xiGammaEulerValuationNat (p, e) : ℝ))) : ℂ)) *
      (xiMobiusCubicNormalizedInnovationFeature h b (p, e) : ℂ) = _
  rw [← Complex.exp_conj, Complex.conj_ofReal]
  simp only [map_neg, map_mul, Complex.conj_ofReal, Complex.conj_I]
  rw [suzukiOscillatoryKernel_primePowerEntryWall_eq_criticalPhase]
  push_cast
  ring_nf

/-- Third-jet entry forcing carried by one critical prime-power atom. -/
def suzukiCriticalEntryWallThirdJetAtom
    (h b t : ℝ) (p : Nat.Primes) (e : ℕ) : ℂ :=
  (t : ℂ) ^ 2 * suzukiCriticalApertureBoundaryAtom h b t p e

/-- **Entry-current identification.**  With the source-selected endpoint amplitude, the actual
near/far third-jet defect at the prime-power wall is exactly the quarter-shift atom times `t^2`. -/
theorem suzukiDelayedHingeCompletedJet3_entryWall_eq_criticalThirdJetAtom
    (h b t : ℝ) (p : Nat.Primes) (e : ℕ) (wholeMoment : ℂ) :
    suzukiDelayedHingeNearCompletedJet3
          (suzukiPrimePowerEntryWallAperture p e)
          (2 * suzukiPrimePowerEntryWallAperture p e)
          wholeMoment
          (suzukiCriticalEntryWallEndpointAmplitude h b p e : ℂ) (t : ℂ) -
        suzukiDelayedHingeFarCompletedJet3
          (2 * suzukiPrimePowerEntryWallAperture p e) wholeMoment (t : ℂ) =
      suzukiCriticalEntryWallThirdJetAtom h b t p e := by
  rw [suzukiDelayedHingeCompletedJet3_entryWall_sub,
    suzukiCriticalEntryWallThirdJetAtom,
    suzukiCriticalApertureBoundaryAtom_eq_entryWallAmplitude_mul_kernel]
  ring_nf

/-- Valuation recursion is therefore also the exact recursion of entry-wall third-jet forces. -/
theorem suzukiCriticalEntryWallThirdJetAtom_succ
    (h b t : ℝ) (p : Nat.Primes) (e : ℕ) :
    suzukiCriticalEntryWallThirdJetAtom h b t p (e + 1) =
      suzukiCriticalApertureDepthRatio h b t p *
        suzukiCriticalEntryWallThirdJetAtom h b t p e := by
  rw [suzukiCriticalEntryWallThirdJetAtom,
    suzukiCriticalEntryWallThirdJetAtom,
    suzukiCriticalApertureBoundaryAtom_succ]
  ring_nf

/-- The entry-wall third-jet forcing is summable in valuation depth. -/
theorem summable_suzukiCriticalEntryWallThirdJetAtom
    {h b : ℝ} (hh : 0 < h) (hb : 0 < b) (t : ℝ) (p : Nat.Primes) :
    Summable (suzukiCriticalEntryWallThirdJetAtom h b t p) := by
  exact (summable_suzukiCriticalApertureBoundaryAtom hh hb t p).mul_left ((t : ℂ) ^ 2)

/-- **Completed causal entry current.**  The quarter-shift resolvent is precisely the sum of all
calibrated prime-power third-jet forcings. -/
theorem tsum_suzukiCriticalEntryWallThirdJetAtom_eq_resolvent
    {h b : ℝ} (hh : 0 < h) (hb : 0 < b) (t : ℝ) (p : Nat.Primes) :
    (∑' e : ℕ, suzukiCriticalEntryWallThirdJetAtom h b t p e) =
      (t : ℂ) ^ 2 * suzukiCriticalApertureBoundaryAtom h b t p 0 *
        (1 - suzukiCriticalApertureDepthRatio h b t p)⁻¹ := by
  rw [show (∑' e : ℕ, suzukiCriticalEntryWallThirdJetAtom h b t p e) =
      (t : ℂ) ^ 2 * ∑' e : ℕ, suzukiCriticalApertureBoundaryAtom h b t p e by
        simp only [suzukiCriticalEntryWallThirdJetAtom]
        rw [tsum_mul_left]
        ]
  rw [tsum_suzukiCriticalApertureBoundaryAtom_eq_resolvent hh hb]
  ring_nf

/-- Off the spectral center, matching the critical entry forcing determines the endpoint trace
uniquely. -/
theorem suzukiCriticalEntryWallEndpointAmplitude_unique
    (h b t : ℝ) (p : Nat.Primes) (e : ℕ) (endpointTrace : ℂ)
    (ht : t ≠ 0)
    (hmatch :
      (t : ℂ) ^ 2 *
          suzukiOscillatoryKernel (t : ℂ)
            (suzukiPrimePowerEntryWallAperture p e) * endpointTrace =
        suzukiCriticalEntryWallThirdJetAtom h b t p e) :
    endpointTrace = (suzukiCriticalEntryWallEndpointAmplitude h b p e : ℂ) := by
  rw [suzukiCriticalEntryWallThirdJetAtom,
    suzukiCriticalApertureBoundaryAtom_eq_entryWallAmplitude_mul_kernel] at hmatch
  have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht
  have hkernel : suzukiOscillatoryKernel (t : ℂ)
      (suzukiPrimePowerEntryWallAperture p e) ≠ 0 := by
    exact Complex.exp_ne_zero _
  have hcoeff : (t : ℂ) ^ 2 *
      suzukiOscillatoryKernel (t : ℂ)
        (suzukiPrimePowerEntryWallAperture p e) ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 htC) hkernel
  apply mul_left_cancel₀ hcoeff
  calc
    ((t : ℂ) ^ 2 *
        suzukiOscillatoryKernel (t : ℂ)
          (suzukiPrimePowerEntryWallAperture p e)) * endpointTrace =
      (t : ℂ) ^ 2 *
        (suzukiOscillatoryKernel (t : ℂ)
          (suzukiPrimePowerEntryWallAperture p e) * endpointTrace) := by ring_nf
    _ = (t : ℂ) ^ 2 *
        ((suzukiCriticalEntryWallEndpointAmplitude h b p e : ℂ) *
          suzukiOscillatoryKernel (t : ℂ)
            (suzukiPrimePowerEntryWallAperture p e)) := by
      simpa only [mul_assoc] using hmatch
    _ = ((t : ℂ) ^ 2 *
        suzukiOscillatoryKernel (t : ℂ)
          (suzukiPrimePowerEntryWallAperture p e)) *
          (suzukiCriticalEntryWallEndpointAmplitude h b p e : ℂ) := by
        ring_nf

end

end RHTower
