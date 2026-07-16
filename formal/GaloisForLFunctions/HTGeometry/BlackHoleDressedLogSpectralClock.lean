import GaloisForLFunctions.HTGeometry.GammaBoseSpectralHankel
import GaloisForLFunctions.HTGeometry.DigammaPolynomialCarrier
import GaloisForLFunctions.HTGeometry.ArgumentScalingInvariance
import GaloisForLFunctions.HTGeometry.ExponentialObservationHypertranscendence

/-!
# The black-hole far-zone dressed logarithm is a Gamma spectral clock

The all-order Schwarzschild dynamical Love response found by Solon contains the universal far-zone
coordinate

`tau(eta) = log(R_S / R) - 2 * sum_{k >= 2} zeta(k) * eta^(k-1)`.

The physics derivation identifies this tower with the Newtonian scattering phase coming from
`Gamma(1 - eta)`.  The exact analytic coordinate is

`tau_L(eta) = L + 2 * (digamma(1 - eta) + gamma_E)`.

Indeed, its positive-order Taylor derivatives are

`tau_L^(m+1)(0) = -2 * (m+1)! * zeta(m+2)`.

This file connects that physics coordinate directly to `GammaBoseSpectralHankel`.  After removing
the universal negative factorial scale, the whole far-zone jet is exactly the positive reciprocal
integer spectral clock `gammaBoseMoment 1`.  Hence every finite Hankel block is positive definite,
the jet escapes every fixed finite oscillator or state-space model, and it satisfies no
positive-order linear recurrence.  Separately, the dressed logarithm itself is
hypertranscendental for every choice of the scale constant `L`.

This is the requested motif in literal form: the non-finite structure is carried by the complete
observability jet of a clock coordinate, not by temporal evolution.

Physics provenance: M. P. Solon, *Universal Closed Form for Dynamical Love Numbers of Black Holes*,
arXiv:2606.19281 (2026).
-/

namespace HTGeometry

noncomputable section

/-- Universal far-zone dressed logarithm of the Schwarzschild dynamical response.  The parameter
`scaleLog` is the scheme/scale constant `log(R_S/R)`; positive-order derivatives do not depend on
it. -/
def blackHoleFarZoneDressedLog (scaleLog eta : ℂ) : ℂ :=
  scaleLog + 2 *
    (Complex.digamma (1 - eta) + (Real.eulerMascheroniConstant : ℂ))

/-- **Black-hole/Gamma value relation.**  The complete positive-order jet of the far-zone dressed
logarithm is the Riemann-zeta tower carried by the reciprocal integer spectrum. -/
theorem iteratedDeriv_blackHoleFarZoneDressedLog_succ
    (scaleLog : ℂ) (m : ℕ) :
    iteratedDeriv (m + 1) (blackHoleFarZoneDressedLog scaleLog) 0 =
      -2 * ((m + 1).factorial : ℂ) * (gammaBoseMoment 1 m : ℂ) := by
  have hfun : blackHoleFarZoneDressedLog scaleLog =
      fun eta =>
        (scaleLog + 2 * (Real.eulerMascheroniConstant : ℂ)) +
          2 * Complex.digamma (1 - eta) := by
    funext eta
    simp only [blackHoleFarZoneDressedLog]
    ring
  rw [hfun, iteratedDeriv_const_add (by omega)]
  rw [congrFun (GaloisForLFunctions.iteratedDeriv_const_mul_field
    (2 : ℂ) (fun eta => Complex.digamma (1 - eta)) (m + 1)) 0]
  rw [congrFun (iteratedDeriv_comp_const_sub (m + 1) Complex.digamma 1) 0]
  simp only [sub_zero, smul_eq_mul]
  have hgamma :
      iteratedDeriv (m + 1) Complex.digamma (1 : ℂ) =
        (-1 : ℂ) ^ (m + 2) * ((m + 1).factorial : ℂ) *
          (gammaBoseMoment 1 m : ℂ) := by
    simpa using
      (iteratedDeriv_digamma_eq_gammaBoseMoment (a := 1) (by norm_num) m)
  rw [hgamma]
  have hsign :
      (-1 : ℂ) ^ (m + 1) * (-1 : ℂ) ^ (m + 2) = -1 := by
    rw [← pow_add, show m + 1 + (m + 2) = 2 * (m + 1) + 1 by omega,
      pow_add, pow_mul]
    norm_num
  calc
    2 * (((-1 : ℂ) ^ (m + 1)) *
          ((-1 : ℂ) ^ (m + 2) * ((m + 1).factorial : ℂ) *
            (gammaBoseMoment 1 m : ℂ))) =
        2 * (((-1 : ℂ) ^ (m + 1)) * ((-1 : ℂ) ^ (m + 2))) *
          ((m + 1).factorial : ℂ) * (gammaBoseMoment 1 m : ℂ) := by ring
    _ = -2 * ((m + 1).factorial : ℂ) * (gammaBoseMoment 1 m : ℂ) := by
      rw [hsign]
      ring

/-- The signed factorial-normalized far-zone jet read by the observer. -/
def normalizedBlackHoleFarZoneJet (scaleLog : ℂ) (m : ℕ) : ℝ :=
  (-iteratedDeriv (m + 1) (blackHoleFarZoneDressedLog scaleLog) 0 /
    (2 * ((m + 1).factorial : ℂ))).re

/-- The normalized black-hole far-zone jet is exactly the positive Gamma/Bose spectral moment
clock, independently of the scale convention. -/
theorem normalizedBlackHoleFarZoneJet_eq_gammaBoseMoment
    (scaleLog : ℂ) (m : ℕ) :
    normalizedBlackHoleFarZoneJet scaleLog m = gammaBoseMoment 1 m := by
  rw [normalizedBlackHoleFarZoneJet,
    iteratedDeriv_blackHoleFarZoneDressedLog_succ]
  have hfac : ((m + 1).factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (m + 1)
  field_simp
  simp

/-- The same jet value is the Riemann-zeta coefficient `zeta(m+2)` in the dressed logarithm. -/
theorem normalizedBlackHoleFarZoneJet_ofReal_eq_riemannZeta
    (scaleLog : ℂ) (m : ℕ) :
    (normalizedBlackHoleFarZoneJet scaleLog m : ℂ) =
      riemannZeta ((m + 2 : ℕ) : ℂ) := by
  rw [normalizedBlackHoleFarZoneJet_eq_gammaBoseMoment,
    gammaBoseMoment_one_ofReal_eq_riemannZeta]

/-- Every finite Hankel block of the physical far-zone zeta clock is positive definite. -/
theorem normalizedBlackHoleFarZoneJet_hankel_posDef
    (scaleLog : ℂ) (n : ℕ) :
    (momentHankelMatrix (normalizedBlackHoleFarZoneJet scaleLog) n).PosDef := by
  have hseq : normalizedBlackHoleFarZoneJet scaleLog = gammaBoseMoment 1 := by
    funext m
    exact normalizedBlackHoleFarZoneJet_eq_gammaBoseMoment scaleLog m
  rw [hseq]
  exact gammaBoseHankel_posDef (by norm_num) n

/-- Every finite Hankel determinant of the physical far-zone zeta clock is strictly positive. -/
theorem det_normalizedBlackHoleFarZoneJet_hankel_pos
    (scaleLog : ℂ) (n : ℕ) :
    0 < (momentHankelMatrix (normalizedBlackHoleFarZoneJet scaleLog) n).det :=
  (normalizedBlackHoleFarZoneJet_hankel_posDef scaleLog n).det_pos

/-- No fixed finite oscillator palette reproduces arbitrarily long windows of the black-hole
far-zone clock jet. -/
theorem normalizedBlackHoleFarZoneJet_not_fixedSpectralWidthLocalClosure
    (scaleLog : ℂ) (d : ℕ) :
    ¬ FixedSpectralWidthLocalClosure d (normalizedBlackHoleFarZoneJet scaleLog) := by
  apply not_fixedSpectralWidthLocalClosure_of_det_ne_zero
  exact ne_of_gt
    (det_normalizedBlackHoleFarZoneJet_hankel_pos scaleLog (d + 1))

/-- No fixed-dimensional linear hidden-state response reproduces arbitrarily long windows of the
black-hole far-zone clock jet. -/
theorem normalizedBlackHoleFarZoneJet_not_fixedStateSpaceDimensionLocalClosure
    (scaleLog : ℂ) (d : ℕ) :
    ¬ FixedStateSpaceDimensionLocalClosure d
      (normalizedBlackHoleFarZoneJet scaleLog) := by
  apply not_fixedStateSpaceDimensionLocalClosure_of_det_ne_zero
  exact ne_of_gt
    (det_normalizedBlackHoleFarZoneJet_hankel_pos scaleLog (d + 1))

/-- The normalized far-zone clock jet obeys no positive-order linear recurrence. -/
theorem normalizedBlackHoleFarZoneJet_not_linearRecurrence
    (scaleLog : ℂ) (E : LinearRecurrence ℝ) (horder : E.order ≠ 0) :
    ¬ E.IsSolution (normalizedBlackHoleFarZoneJet scaleLog) := by
  have hseq : normalizedBlackHoleFarZoneJet scaleLog = gammaBoseMoment 1 := by
    funext m
    exact normalizedBlackHoleFarZoneJet_eq_gammaBoseMoment scaleLog m
  rw [hseq]
  have hjet : signedNormalizedDigammaJet 1 = gammaBoseMoment 1 := by
    funext m
    exact signedNormalizedDigammaJet_eq_gammaBoseMoment (by norm_num) m
  rw [← hjet]
  exact signedNormalizedDigammaJet_not_linearRecurrence (by norm_num) E horder

/-- **Hypertranscendental black-hole clock.**  For every scale constant, the far-zone dressed
logarithm satisfies no algebraic differential equation over `C(eta)`. -/
theorem hypertranscendental_blackHoleFarZoneDressedLog (scaleLog : ℂ) :
    GaloisForLFunctions.Hypertranscendental
      (blackHoleFarZoneDressedLog scaleLog) := by
  let C : ℂ := scaleLog + 2 * (Real.eulerMascheroniConstant : ℂ)
  let f : ℂ → ℂ := fun z => 2 * Complex.digamma z + C
  have hf : GaloisForLFunctions.Hypertranscendental f := by
    simpa only [f, Polynomial.eval_C] using
      (GaloisForLFunctions.hypertranscendental_smul_digamma_add_polynomial
        (M := (2 : ℂ)) (by norm_num) (Polynomial.C C))
  have hshift : GaloisForLFunctions.Hypertranscendental (fun z => f (z + 1)) :=
    (GaloisForLFunctions.hypertranscendental_comp_add_const_iff
      (f := f) 1).2 hf
  have hscale : GaloisForLFunctions.Hypertranscendental
      (fun z => (fun w => f (w + 1)) (-1 * z)) :=
    (GaloisForLFunctions.hypertranscendental_comp_const_mul_iff_uncond
      (f := fun w => f (w + 1)) (c := (-1 : ℂ)) (by norm_num)).2 hshift
  have hfun : blackHoleFarZoneDressedLog scaleLog =
      fun z => (fun w => f (w + 1)) (-1 * z) := by
    funext z
    have harg : -1 * z + 1 = 1 - z := by ring
    change blackHoleFarZoneDressedLog scaleLog z = f (-1 * z + 1)
    rw [harg]
    simp only [blackHoleFarZoneDressedLog, f, C]
    ring
  rw [hfun]
  exact hscale

end

end HTGeometry

namespace HTGeometry

noncomputable section

/-! ## The complete Schwarzschild response, not only its dressed clock -/

/-- The leading-log RG kernel for every Schwarzschild multipole `ell >= 1` in Solon's closed
response formula.  `seed` is `L^(1)_{ell,s}` and `nu` is `nu^(2)_{ell,s}`. -/
def blackHoleHigherMultipoleRGKernel (seed nu y : ℂ) : ℂ :=
  seed / (-4 * nu) * (Complex.exp (-4 * nu * y) - 1)

/-- The derivative of the higher-multipole RG kernel is the horizon seed times its exponential
phase. -/
theorem hasDerivAt_blackHoleHigherMultipoleRGKernel
    (seed nu y : ℂ) (hnu : nu ≠ 0) :
    HasDerivAt (blackHoleHigherMultipoleRGKernel seed nu)
      (seed * Complex.exp (-4 * nu * y)) y := by
  have hlin : HasDerivAt (fun z : ℂ => -4 * nu * z) (-4 * nu) y := by
    simpa using (hasDerivAt_id y).const_mul (-4 * nu)
  have hraw := (hlin.cexp.sub_const 1).const_mul (seed / (-4 * nu))
  convert hraw using 1
  field_simp [hnu]

/-- The paper's complete normalized response for `ell >= 1`, after the dressed running variable
`y = -eta^2 tau / 2` is inserted.  The second term is exactly `-eta Phi'(y)/2`. -/
def blackHoleHigherMultipoleDressedResponse
    (seed nu eta tau : ℂ) : ℂ :=
  blackHoleHigherMultipoleRGKernel seed nu (-1 / 2 * eta ^ 2 * tau) -
    1 / 2 * eta * seed *
      Complex.exp (-4 * nu * (-1 / 2 * eta ^ 2 * tau))

/-- **Complete higher-multipole value relation.**  The full Schwarzschild response is an affine
observation of one exponential of the hypertranscendental dressed-log source. -/
theorem blackHoleHigherMultipoleDressedResponse_eq_exponentialAffine
    (seed nu eta tau : ℂ) (hnu : nu ≠ 0) :
    blackHoleHigherMultipoleDressedResponse seed nu eta tau =
      seed / (-4 * nu) *
        ((1 + 2 * nu * eta) *
          Complex.exp (2 * nu * eta ^ 2 * tau) - 1) := by
  have harg : -4 * nu * (-1 / 2 * eta ^ 2 * tau) =
      2 * nu * eta ^ 2 * tau := by ring
  rw [blackHoleHigherMultipoleDressedResponse,
    blackHoleHigherMultipoleRGKernel, harg]
  field_simp [hnu]
  ring

/-- The complete higher-multipole response as a readout of its exponential phase. -/
def blackHoleHigherMultipolePhaseReadout
    (seed nu eta phase : ℂ) : ℂ :=
  seed / (-4 * nu) * ((1 + 2 * nu * eta) * phase - 1)

/-- The dressed response is the phase readout evaluated on the Gamma-clock exponential. -/
theorem blackHoleHigherMultipoleDressedResponse_eq_phaseReadout
    (seed nu eta tau : ℂ) (hnu : nu ≠ 0) :
    blackHoleHigherMultipoleDressedResponse seed nu eta tau =
      blackHoleHigherMultipolePhaseReadout seed nu eta
        (Complex.exp (2 * nu * eta ^ 2 * tau)) := by
  simpa [blackHoleHigherMultipolePhaseReadout] using
    blackHoleHigherMultipoleDressedResponse_eq_exponentialAffine
      seed nu eta tau hnu

/-- **Exact phase recovery.**  A nondegenerate higher-multipole Love response algebraically
recovers the exponential clock phase. -/
theorem blackHoleHigherMultipolePhaseReadout_recover
    (seed nu eta phase : ℂ) (hseed : seed ≠ 0) (hnu : nu ≠ 0)
    (haffine : 1 + 2 * nu * eta ≠ 0) :
    ((-4 * nu) / seed *
        blackHoleHigherMultipolePhaseReadout seed nu eta phase + 1) /
      (1 + 2 * nu * eta) = phase := by
  apply (div_eq_iff haffine).2
  rw [blackHoleHigherMultipolePhaseReadout]
  field_simp [hseed, hnu]
  ring

/-- The complete higher-multipole Love response is a faithful observation of its clock phase. -/
theorem blackHoleHigherMultipolePhaseReadout_injective
    (seed nu eta : ℂ) (hseed : seed ≠ 0) (hnu : nu ≠ 0)
    (haffine : 1 + 2 * nu * eta ≠ 0) :
    Function.Injective (blackHoleHigherMultipolePhaseReadout seed nu eta) := by
  intro phase₁ phase₂ hresponse
  have hrecovered := congrArg
    (fun response =>
      ((-4 * nu) / seed * response + 1) / (1 + 2 * nu * eta))
    hresponse
  simpa only [blackHoleHigherMultipolePhaseReadout_recover
    seed nu eta phase₁ hseed hnu haffine,
    blackHoleHigherMultipolePhaseReadout_recover
      seed nu eta phase₂ hseed hnu haffine] using hrecovered

/-- The monopole response written directly in terms of its exponential RG phase `phase`. -/
def blackHoleMonopoleDressedResponse (eta phase : ℂ) : ℂ :=
  ((3 / 2) * phase - 1 / 3) / (1 - phase) +
    49 / 18 * eta * phase / (1 - phase) ^ 2

/-- **Cleared monopole value relation.**  Away from the pole `phase = 1`, the full monopole
response is algebraically related to the exponential phase by a quadratic equation. -/
theorem blackHoleMonopoleDressedResponse_cleared
    (eta phase : ℂ) (hphase : phase ≠ 1) :
    blackHoleMonopoleDressedResponse eta phase * (1 - phase) ^ 2 =
      ((3 / 2) * phase - 1 / 3) * (1 - phase) +
        49 / 18 * eta * phase := by
  rw [blackHoleMonopoleDressedResponse]
  have hden : 1 - phase ≠ 0 := sub_ne_zero.mpr (Ne.symm hphase)
  field_simp [hden]

end


end HTGeometry

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions
open scoped Differential

noncomputable section

/-! ## Differential-algebraic transport through the response law -/

/-- The abstract differential-field version of the higher-multipole Schwarzschild response.
The base field contains the frequency coordinate `eta` and the rational matching data. -/
theorem hypertranscendentalOver_blackHoleHigherMultipoleResponse
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E]
    [CharZero F] [CharZero E]
    {tau phase : E} {seed nu eta : F}
    (hseed : seed ≠ 0) (hnu : nu ≠ 0) (heta : eta ≠ 0)
    (haffine : 1 + 2 * nu * eta ≠ 0)
    (htau : HypertranscendentalOver F tau)
    (hlog : phase′ / phase =
      (algebraMap F E (2 * nu * eta ^ 2) * tau)′) :
    HypertranscendentalOver F
      (algebraMap F E (seed / (-4 * nu)) *
        (algebraMap F E (1 + 2 * nu * eta) * phase - 1)) := by
  apply hypertranscendentalOver_exponentialAffineObservable
    (a := 2 * nu * eta ^ 2) (b := 1 + 2 * nu * eta)
      (c := seed / (-4 * nu))
  · exact mul_ne_zero (mul_ne_zero (by norm_num) hnu) (pow_ne_zero 2 heta)
  · exact haffine
  · exact div_ne_zero hseed (mul_ne_zero (by norm_num) hnu)
  · exact htau
  · exact hlog

/-- **Full monopole observability transfer.**  The cleared quadratic response relation is already
enough to prevent the Möbius/Riccati monopole channel from hiding an HT phase.  The nonzero
frequency coordinate certifies that the relation polynomial is genuinely nonzero. -/
theorem hypertranscendentalOver_blackHoleMonopoleResponse
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E]
    [CharZero F] [CharZero E]
    {phase response : E} {eta : F} (heta : eta ≠ 0)
    (hphase : HypertranscendentalOver F phase)
    (hrel : response * (1 - phase) ^ 2 =
      ((3 / 2) * phase - 1 / 3) * (1 - phase) +
        algebraMap F E (49 / 18 * eta) * phase) :
    HypertranscendentalOver F response := by
  let S := differentialAdjoin F ({response} : Set E)
  let responseS : S :=
    ⟨response, subset_differentialAdjoin F ({response} : Set E) rfl⟩
  let X : MvPolynomial (Fin 1) S := MvPolynomial.X 0
  let Q : MvPolynomial (Fin 1) S :=
    MvPolynomial.C responseS * (1 - X) ^ 2 -
      (MvPolynomial.C (algebraMap F S (3 / 2)) * X -
        MvPolynomial.C (algebraMap F S (1 / 3))) * (1 - X) -
      MvPolynomial.C (algebraMap F S (49 / 18 * eta)) * X
  have hetaCoeff : (49 / 18 : F) * eta ≠ 0 := by
    exact mul_ne_zero (div_ne_zero (by norm_num) (by norm_num)) heta
  have hetaCoeffS : algebraMap F S (49 / 18 * eta) ≠ 0 :=
    (map_ne_zero (algebraMap F S)).2 hetaCoeff
  have hQ : Q ≠ 0 := by
    intro hzero
    have hev := congrArg (MvPolynomial.eval (fun _ : Fin 1 => (1 : S))) hzero
    have hvanish : -algebraMap F S (49 / 18 * eta) = 0 := by
      simpa [Q, X] using hev
    exact hetaCoeffS (neg_eq_zero.mp hvanish)
  apply hypertranscendentalOver_input_of_finiteJetConstraint
    (h := response) hphase hQ
  change MvPolynomial.aeval
    (fun j : Fin 1 => differentialJet (j : ℕ) phase) Q = 0
  have hrespMap : algebraMap S E responseS = response := rfl
  simp [Q, X, hrespMap]
  norm_num [map_div₀, map_mul, map_ofNat] at hrel ⊢
  linear_combination hrel

end

end GaloisForLFunctions.HTGeometry
