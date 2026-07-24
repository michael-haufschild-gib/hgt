import GaloisForLFunctions.RHTower.PrimeArchThetaSingleGibbsRationalEnclosureGate
import GaloisForLFunctions.RHTower.PrimeArchThetaTwoChannelVirialRayleighRitz

/-!
# Theta single-Gibbs two-channel hypervirial closure

The finite rational enclosure of the first theta-cusp Gibbs moments already supplies the fixed
quadratic Morse certificate.  The quadratic channel embeds as `(1,-1/2)` in the optimized
two-channel span; exact Rayleigh--Ritz elimination and polarized hypervirial replacement then
produce the full two-channel curvature certificate.  The same enclosure discharges every
constant/linear prime--archimedean source inequality, leaving only the degree-two tail for the
complete integer cone and RH.
-/

open Complex Polynomial

namespace RHTower

noncomputable section

/-- **Single-Gibbs/two-channel hypervirial closure universality.**  One finite rational moment
enclosure forces the two-channel hypervirial Rayleigh--Ritz certificate, retains the relaxed
low-degree inequality, and proves every linear source-Hankel test.  The existing degree-two tail
then supplies both the complete integer cone and RH. -/
theorem
    thetaCuspFirstAtomSingleGibbs_twoChannelHypervirialClosure_of_rationalEnclosure
    (h : ThetaCuspFirstAtomSingleGibbsRationalMomentEnclosure) :
    ThetaCuspFirstRadialTwoChannelVirialRayleighRitzCertificate ∧
    (16 * ((3005 / 2997 : ℝ) *
          thetaCuspBornWittenRadialRawMoment 0 0 1) *
          ((3005 / 2997 : ℝ) *
            thetaCuspBornWittenRadialRawMoment 2 0 1) ≤
        45 * thetaCuspBornWittenRadialRawMoment 1 0 1 ^ 2) ∧
    (∀ a b : ℝ, 0 ≤ (primeArchSourceTraceHankel (C a + C b * X)).re) ∧
    (PrimeArchSourceTraceHankelIntDegreeTwoTailNonnegative →
      PrimeArchSourceTraceHankelIntNonnegative ∧ RiemannHypothesis) := by
  have hlow :=
    thetaCuspFirstAtomSingleGibbsLowDegreeCertificate_of_rationalMomentEnclosure h
  have hreduced :=
    (thetaCuspFirstAtomSingleGibbsLowDegreeCertificate_iff).1 hlow
  have hmorse := hreduced.1
  have hrelaxed := hreduced.2
  have hquadraticVirial :=
    thetaCusp_quadraticVirialEnergyCertificate_of_morseQuadraticEnvelope hmorse
  have hquadraticStein :=
    quadraticSteinEnergyCertificate_iff_virialEnergyCertificate.2
      hquadraticVirial
  have htwoChannel :=
    twoChannelSteinEnergyCertificate_of_quadraticSteinEnergyCertificate
      hquadraticStein
  have hrayleigh :=
    thetaCuspFirstRadialTwoChannelRayleighRitzCertificate_iff.2 htwoChannel
  have hhypervirial :=
    thetaCuspFirstRadialTwoChannelVirialRayleighRitzCertificate_iff.2
      hrayleigh
  refine ⟨hhypervirial, hrelaxed, ?_, ?_⟩
  · exact
      forall_primeArchSourceTraceHankel_linear_nonneg_of_twoChannelVirialRayleighRitz
        hhypervirial hrelaxed
  · intro htail
    exact
      ⟨primeArchSourceTraceHankelIntNonnegative_of_twoChannelSteinEnergy_of_degreeTwoTail
          htwoChannel hrelaxed htail,
        riemannHypothesis_of_twoChannelVirialRayleighRitz_of_primeArchDegreeTwoTail
          hhypervirial hrelaxed htail⟩

/-- The rational enclosure and the unchanged degree-two source tail are sufficient for RH,
through the exact two-channel hypervirial closure. -/
theorem
    riemannHypothesis_of_singleGibbsRationalEnclosure_of_primeArchDegreeTwoTail
    (h : ThetaCuspFirstAtomSingleGibbsRationalMomentEnclosure)
    (htail : PrimeArchSourceTraceHankelIntDegreeTwoTailNonnegative) :
    RiemannHypothesis :=
  (thetaCuspFirstAtomSingleGibbs_twoChannelHypervirialClosure_of_rationalEnclosure
    h).2.2.2 htail |>.2

end

end RHTower
