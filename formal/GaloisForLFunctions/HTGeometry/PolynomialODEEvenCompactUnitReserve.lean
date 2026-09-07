import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactBlock0
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactBlock1
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactBlock2
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactBlock3
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactBlock4
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactBlock5
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactBlock6
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactBlock7
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactBlock8
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactBlock9
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactBlock10
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactBlock11

/-! # Exact global positive reserve of the coupled compact determinant polynomial -/
namespace HTGeometry
noncomputable section
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000

/-- Full exact polynomial certificate, with every determinant coefficient retained. -/
def evenCompactUnitPolynomial (r t v : ℝ) : ℝ :=
  (((evenCompactUnitBlock0 r t v +
    (evenCompactUnitBlock1 r t v +
    evenCompactUnitBlock2 r t v)) +
    (evenCompactUnitBlock3 r t v +
    (evenCompactUnitBlock4 r t v +
    evenCompactUnitBlock5 r t v))) +
    ((evenCompactUnitBlock6 r t v +
    (evenCompactUnitBlock7 r t v +
    evenCompactUnitBlock8 r t v)) +
    (evenCompactUnitBlock9 r t v +
    (evenCompactUnitBlock10 r t v +
    evenCompactUnitBlock11 r t v))))

/-- The positive quartic controls every signed high-degree contribution. -/
theorem evenCompactUnitPolynomial_lower {r t v : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    (1/1000 : ℝ) ≤ evenCompactUnitPolynomial r t v := by
  have hl : (((evenCompactUnitBlock0Lower r t v +
    (evenCompactUnitBlock1Lower r t v +
    evenCompactUnitBlock2Lower r t v)) +
    (evenCompactUnitBlock3Lower r t v +
    (evenCompactUnitBlock4Lower r t v +
    evenCompactUnitBlock5Lower r t v))) +
    ((evenCompactUnitBlock6Lower r t v +
    (evenCompactUnitBlock7Lower r t v +
    evenCompactUnitBlock8Lower r t v)) +
    (evenCompactUnitBlock9Lower r t v +
    (evenCompactUnitBlock10Lower r t v +
    evenCompactUnitBlock11Lower r t v)))) = evenCompactQuartic r t v := by
    unfold evenCompactUnitBlock0Lower evenCompactUnitBlock1Lower evenCompactUnitBlock2Lower evenCompactUnitBlock3Lower evenCompactUnitBlock4Lower evenCompactUnitBlock5Lower evenCompactUnitBlock6Lower evenCompactUnitBlock7Lower evenCompactUnitBlock8Lower evenCompactUnitBlock9Lower evenCompactUnitBlock10Lower evenCompactUnitBlock11Lower evenCompactQuartic
    ring
  have he : evenCompactUnitPolynomial r t v = evenCompactQuartic r t v+(((evenCompactUnitBlock0Remainder r t v +
    (evenCompactUnitBlock1Remainder r t v +
    evenCompactUnitBlock2Remainder r t v)) +
    (evenCompactUnitBlock3Remainder r t v +
    (evenCompactUnitBlock4Remainder r t v +
    evenCompactUnitBlock5Remainder r t v))) +
    ((evenCompactUnitBlock6Remainder r t v +
    (evenCompactUnitBlock7Remainder r t v +
    evenCompactUnitBlock8Remainder r t v)) +
    (evenCompactUnitBlock9Remainder r t v +
    (evenCompactUnitBlock10Remainder r t v +
    evenCompactUnitBlock11Remainder r t v)))) := by
    unfold evenCompactUnitPolynomial
    rw [evenCompactUnitBlock0_eq hr0 hr1 ht0 ht1 hv0 hv1, evenCompactUnitBlock1_eq hr0 hr1 ht0 ht1 hv0 hv1, evenCompactUnitBlock2_eq hr0 hr1 ht0 ht1 hv0 hv1, evenCompactUnitBlock3_eq hr0 hr1 ht0 ht1 hv0 hv1, evenCompactUnitBlock4_eq hr0 hr1 ht0 ht1 hv0 hv1, evenCompactUnitBlock5_eq hr0 hr1 ht0 ht1 hv0 hv1, evenCompactUnitBlock6_eq hr0 hr1 ht0 ht1 hv0 hv1, evenCompactUnitBlock7_eq hr0 hr1 ht0 ht1 hv0 hv1, evenCompactUnitBlock8_eq hr0 hr1 ht0 ht1 hv0 hv1, evenCompactUnitBlock9_eq hr0 hr1 ht0 ht1 hv0 hv1, evenCompactUnitBlock10_eq hr0 hr1 ht0 ht1 hv0 hv1, evenCompactUnitBlock11_eq hr0 hr1 ht0 ht1 hv0 hv1]
    rw [← hl]
    ring
  have h0 := evenCompactUnitBlock0_remainder_nonneg hr0 ht0 hv0
  have h1 := evenCompactUnitBlock1_remainder_nonneg hr0 ht0 hv0
  have h2 := evenCompactUnitBlock2_remainder_nonneg hr0 ht0 hv0
  have h3 := evenCompactUnitBlock3_remainder_nonneg hr0 ht0 hv0
  have h4 := evenCompactUnitBlock4_remainder_nonneg hr0 ht0 hv0
  have h5 := evenCompactUnitBlock5_remainder_nonneg hr0 ht0 hv0
  have h6 := evenCompactUnitBlock6_remainder_nonneg hr0 ht0 hv0
  have h7 := evenCompactUnitBlock7_remainder_nonneg hr0 ht0 hv0
  have h8 := evenCompactUnitBlock8_remainder_nonneg hr0 ht0 hv0
  have h9 := evenCompactUnitBlock9_remainder_nonneg hr0 ht0 hv0
  have h10 := evenCompactUnitBlock10_remainder_nonneg hr0 ht0 hv0
  have h11 := evenCompactUnitBlock11_remainder_nonneg hr0 ht0 hv0
  have hrem : 0 ≤ (((evenCompactUnitBlock0Remainder r t v +
    (evenCompactUnitBlock1Remainder r t v +
    evenCompactUnitBlock2Remainder r t v)) +
    (evenCompactUnitBlock3Remainder r t v +
    (evenCompactUnitBlock4Remainder r t v +
    evenCompactUnitBlock5Remainder r t v))) +
    ((evenCompactUnitBlock6Remainder r t v +
    (evenCompactUnitBlock7Remainder r t v +
    evenCompactUnitBlock8Remainder r t v)) +
    (evenCompactUnitBlock9Remainder r t v +
    (evenCompactUnitBlock10Remainder r t v +
    evenCompactUnitBlock11Remainder r t v)))) := by positivity
  rw [he]
  exact (evenCompactQuartic_lower hr0 hr1 ht0 ht1 hv0 hv1).trans (le_add_of_nonneg_right hrem)

end
end HTGeometry
