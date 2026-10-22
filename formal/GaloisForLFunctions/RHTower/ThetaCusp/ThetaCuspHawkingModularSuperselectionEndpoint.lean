import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBackreactionPassivityEndpoint
import GaloisForLFunctions.RHTower.XiSourceModularTypeSuperselectionLaw

/-!
# Theta-cusp Hawking modular-superselection endpoint

The Hawking backreaction route supplies more than terminology here.  Its physical boundary
observable defines a dimensionless horizon charge: port dissipation divided by twice source mass
and positive closed-state energy.  The anomaly dissipation law proves that this charge is exactly
the imaginary resonance frequency.

For a positive-charge two-ended Hawking resonance, Xi evenness selects an actual right-half divisor
copy whose source-modular charge is exactly the same number.  Existing modular superselection then
forces two unconditional conclusions for the reflected arithmetic horizon sectors:

* no finite-Rees-moderate family can sew them;
* every exact sewing family has norm beyond every inverse Wold--Rees power.

The final endpoint isolates the remaining producer without pretending it is proved.  Finite-Rees
partner recoverability is equivalent to RH because any positive Hawking horizon charge makes such
recovery impossible, while the reflected resonance excludes negative charge.  A causal,
high-frequency-transparent mirror/material model would advance RH only by deriving this precise
finite-grade recovery property from its scattering hypotheses.
-/

open Complex Filter Asymptotics GaloisForLFunctions

noncomputable section

namespace RHTower

open HedenmalmThetaSource

/-- Dimensionless Hawking horizon charge extracted from physical port dissipation.  Its denominator
is strictly positive at every two-ended backreaction resonance. -/
def thetaCuspHawkingBackreactionHorizonCharge
    (r : ThetaCuspHawkingBackreactionResonantMode) : ℝ :=
  thetaCuspHawkingBackreactionPortDissipation r /
    (2 * thetaSource.mass * thetaCuspHawkingBackreactionPhysicalEnergy r)

/-- **[PROVED] Hawking horizon-charge law.**  Normalized physical boundary dissipation is exactly
the imaginary resonance frequency. -/
theorem thetaCuspHawkingBackreactionHorizonCharge_eq_im
    (r : ThetaCuspHawkingBackreactionResonantMode) :
    thetaCuspHawkingBackreactionHorizonCharge r = r.1.im := by
  rw [thetaCuspHawkingBackreactionHorizonCharge,
    thetaCuspHawkingBackreactionPortDissipation_eq]
  have hden :
      2 * thetaSource.mass * thetaCuspHawkingBackreactionPhysicalEnergy r ≠ 0 :=
    ne_of_gt (mul_pos (mul_pos (by norm_num) thetaSource.mass_pos)
      (thetaCuspHawkingBackreactionPhysicalEnergy_pos r))
  rw [div_eq_iff hden]
  ring

/-- A positive Hawking horizon charge is realized by an actual right-half Xi divisor copy.  Its
spectral coordinate is the reflected Hawking resonance and its modular charge is the normalized
physical dissipation. -/
theorem exists_xiRightZeroCopy_of_thetaCuspHawkingBackreactionHorizonCharge_pos
    (r : ThetaCuspHawkingBackreactionResonantMode)
    (hpos : 0 < thetaCuspHawkingBackreactionHorizonCharge r) :
    ∃ q : XiRightZeroCopy,
      xiSpectralPoint q.1 = -r.1 ∧
      xiRightSourceModularCharge q =
        thetaCuspHawkingBackreactionHorizonCharge r := by
  have him : 0 < r.1.im := by
    rwa [thetaCuspHawkingBackreactionHorizonCharge_eq_im] at hpos
  have hneg : XiC (-r.1) = 0 := by
    rw [XiC_even]
    exact thetaCuspHawkingBackreactionResonantMode_XiC_eq_zero r
  obtain ⟨q0, hq0⟩ :=
    (XiC_eq_zero_iff_exists_xiZeroCopy (-r.1)).mp hneg
  have hright : 0 < (I * xiSpectralPoint q0).re := by
    rw [hq0]
    simp only [mul_neg, Complex.neg_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub]
    simpa only [neg_neg] using him
  let q : XiRightZeroCopy := ⟨q0, hright⟩
  refine ⟨q, hq0, ?_⟩
  rw [thetaCuspHawkingBackreactionHorizonCharge_eq_im,
    xiRightSourceModularCharge]
  have hcenter := congrArg Complex.re (I_mul_xiSpectralPoint q0)
  rw [hq0] at hcenter
  simp only [mul_neg, Complex.neg_re, Complex.mul_re,
    Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub,
    Complex.sub_re] at hcenter
  norm_num at hcenter ⊢
  exact hcenter.symm

/-- **[PROVED] Hawking modular-superselection certificate.**  Every positive-charge two-ended
Hawking resonance carries one actual right-half Xi copy whose common charge simultaneously
controls physical port dissipation and the complete source-modular superselection law. -/
theorem thetaCuspHawkingBackreaction_modularSuperselection_certificate
    (r : ThetaCuspHawkingBackreactionResonantMode)
    (hpos : 0 < thetaCuspHawkingBackreactionHorizonCharge r) :
    ∃ q : XiRightZeroCopy,
      xiSpectralPoint q.1 = -r.1 ∧
      xiRightSourceModularCharge q =
        thetaCuspHawkingBackreactionHorizonCharge r ∧
      thetaCuspHawkingBackreactionPortDissipation r =
        2 * thetaSource.mass * xiRightSourceModularCharge q *
          thetaCuspHawkingBackreactionPhysicalEnergy r ∧
      XiRightSourceModularTypeSuperselectionCertificate q := by
  obtain ⟨q, hspectral, hcharge⟩ :=
    exists_xiRightZeroCopy_of_thetaCuspHawkingBackreactionHorizonCharge_pos r hpos
  refine ⟨q, hspectral, hcharge, ?_,
    xiRightSourceModularTypeSuperselection_law q⟩
  simpa only [hcharge, thetaCuspHawkingBackreactionHorizonCharge_eq_im] using
    thetaCuspHawkingBackreactionPortDissipation_eq r

/-- **[PROVED] Finite-grade horizon-sewing obstruction.**  No finite-Rees-moderate operator family
can recover the reflected arithmetic sector selected by a positive physical Hawking charge. -/
theorem no_finiteReesOperator_sews_positive_thetaCuspHawkingHorizon
    (r : ThetaCuspHawkingBackreactionResonantMode)
    (hpos : 0 < thetaCuspHawkingBackreactionHorizonCharge r)
    (K : ℕ) (R : ℕ → (ℝ →L[ℝ] ℝ))
    (hR : ReesOperatorGradeAtMost atTop
      primeWoldBoundaryVolumeBelow K R) :
    (fun N =>
      R N
        (primeValuationSquaredHellingerBelow
          (thetaCuspHawkingBackreactionHorizonCharge r) N)) ≠
      primeValuationSquaredHellingerBelow
        (-thetaCuspHawkingBackreactionHorizonCharge r) := by
  obtain ⟨q, _, hcharge⟩ :=
    exists_xiRightZeroCopy_of_thetaCuspHawkingBackreactionHorizonCharge_pos r hpos
  simpa only [hcharge] using
    no_finiteReesOperator_sews_xiRightModularSectors q K R hR

/-- **[PROVED] Essential horizon-sewing cost.**  Exact reflected-sector recovery at a positive
physical Hawking charge has operator norm beyond every finite inverse Wold--Rees power. -/
theorem thetaCuspHawkingHorizonSewingOperatorNorm_beyondEveryReesOrder
    (r : ThetaCuspHawkingBackreactionResonantMode)
    (hpos : 0 < thetaCuspHawkingBackreactionHorizonCharge r)
    (R : ℕ → (ℝ →L[ℝ] ℝ))
    (hsew :
      (fun N =>
        R N
          (primeValuationSquaredHellingerBelow
            (thetaCuspHawkingBackreactionHorizonCharge r) N)) =
        primeValuationSquaredHellingerBelow
          (-thetaCuspHawkingBackreactionHorizonCharge r))
    (K : ℕ) :
    (fun N => (primeWoldBoundaryVolumeBelow N)⁻¹ ^ K) =o[atTop]
      (fun N => ‖R N‖) := by
  obtain ⟨q, _, hcharge⟩ :=
    exists_xiRightZeroCopy_of_thetaCuspHawkingBackreactionHorizonCharge_pos r hpos
  apply xiRightModularSewingOperatorNorm_beyondEveryReesOrder q R
  simpa only [hcharge] using hsew

/-- **[OPEN PRODUCER]** Mathematical interface expected from a sufficiently local, causal,
high-frequency-transparent horizon material: every positive physical Hawking charge admits exact
reflected-sector recovery by some finite-Rees-moderate family.  This file does not derive that
implication from scattering theory. -/
def ThetaCuspHawkingFiniteReesPartnerRecoverable : Prop :=
  ∀ r : ThetaCuspHawkingBackreactionResonantMode,
    0 < thetaCuspHawkingBackreactionHorizonCharge r →
      ∃ (K : ℕ) (R : ℕ → (ℝ →L[ℝ] ℝ)),
        ReesOperatorGradeAtMost atTop
          primeWoldBoundaryVolumeBelow K R ∧
        (fun N =>
          R N
            (primeValuationSquaredHellingerBelow
              (thetaCuspHawkingBackreactionHorizonCharge r) N)) =
          primeValuationSquaredHellingerBelow
            (-thetaCuspHawkingBackreactionHorizonCharge r)

/-- **[BRIDGE] Hawking modular-superselection endpoint.**  Finite-grade recovery of every positive
physical horizon charge is equivalent to RH.  Forward direction uses the unconditional sewing
obstruction above; reflected Hawking resonance excludes negative charge.  Reverse direction is
vacuous because RH leaves no nonzero horizon charge.  Hard producer remains the explicitly marked
scattering-to-finite-grade implication, not this equivalence. -/
theorem thetaCuspHawkingFiniteReesPartnerRecoverable_iff_riemannHypothesis :
    ThetaCuspHawkingFiniteReesPartnerRecoverable ↔ RiemannHypothesis := by
  rw [riemannHypothesis_iff_thetaCuspHawkingBackreactionResonances_real]
  constructor
  · intro hrecover alpha hres
    let r : ThetaCuspHawkingBackreactionResonantMode := ⟨alpha, hres⟩
    have hnonpos : ¬ 0 < thetaCuspHawkingBackreactionHorizonCharge r := by
      intro hpos
      obtain ⟨K, R, hR, hsew⟩ := hrecover r hpos
      exact
        (no_finiteReesOperator_sews_positive_thetaCuspHawkingHorizon
          r hpos K R hR) hsew
    have him_le : r.1.im ≤ 0 := by
      rw [thetaCuspHawkingBackreactionHorizonCharge_eq_im] at hnonpos
      exact le_of_not_gt hnonpos
    let rr := thetaCuspHawkingBackreactionReflectedResonantMode r
    have href_nonpos :
        ¬ 0 < thetaCuspHawkingBackreactionHorizonCharge rr := by
      intro hpos
      obtain ⟨K, R, hR, hsew⟩ := hrecover rr hpos
      exact
        (no_finiteReesOperator_sews_positive_thetaCuspHawkingHorizon
          rr hpos K R hR) hsew
    have href_im_le : rr.1.im ≤ 0 := by
      rw [thetaCuspHawkingBackreactionHorizonCharge_eq_im] at href_nonpos
      exact le_of_not_gt href_nonpos
    rw [thetaCuspHawkingBackreactionReflectedResonantMode_im] at href_im_le
    change alpha.im = 0
    dsimp only [r] at him_le
    linarith
  · intro hreal r hpos
    have him : r.1.im = 0 := hreal r.1 r.2
    rw [thetaCuspHawkingBackreactionHorizonCharge_eq_im, him] at hpos
    linarith

end RHTower
