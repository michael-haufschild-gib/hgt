import GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolarHalfLineDomain

/-!
# Full-half-line signed prime–polar Chebyshev transport

All arithmetic sums and work integrals are admitted by actual compact support.
The upper endpoint disappears at a cutoff constructed from the source alone.
The resulting global scalar identity and signed Gram transport estimates hold
for every compact continuous source and every annular parameter, without grid
blindness, source differentiation, or an arithmetic error estimate.
-/

open MeasureTheory Set
open scoped BigOperators CompactlySupported
namespace GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole
noncomputable section
set_option autoImplicit false

/-- Derivative of the exponentially weighted annular average used in Abel summation. -/
def abelKernel (f : C_c(ℝ, ℝ)) (a b x : ℝ) : ℝ :=
  Real.exp (-x / 2) * (correlationAverageSlope f a b x - correlationAverage f a b x / 2)

/-- The negative-exponential polar branch remains in the full-half-line identity. -/
def shadowKernel (f : C_c(ℝ, ℝ)) (a b x : ℝ) : ℝ :=
  Real.exp (-x / 2) * correlationAverage f a b x

private theorem continuous_abelKernel (f : C_c(ℝ, ℝ)) (a b : ℝ) :
    Continuous (abelKernel f a b) := by
  have hH := continuous_correlationAverage f a b
  have hV := continuous_correlationAverageSlope f a b
  unfold abelKernel
  fun_prop

private theorem continuous_shadowKernel (f : C_c(ℝ, ℝ)) (a b : ℝ) :
    Continuous (shadowKernel f a b) := by
  have hH := continuous_correlationAverage f a b
  unfold shadowKernel
  fun_prop

private theorem abelKernel_tail (f : C_c(ℝ, ℝ)) (a b x : ℝ)
    (hx : cutoff (sourceCutoff f) ≤ x) : abelKernel f a b x = 0 := by
  rw [abelKernel, correlationAverageSlope_eq_zero_of_sourceCutoff_le f a b hx,
    correlationAverage_eq_zero_of_sourceCutoff_le f a b hx, zero_div, sub_self, mul_zero]

private theorem shadowKernel_tail (f : C_c(ℝ, ℝ)) (a b x : ℝ)
    (hx : cutoff (sourceCutoff f) ≤ x) : shadowKernel f a b x = 0 := by
  rw [shadowKernel, correlationAverage_eq_zero_of_sourceCutoff_le f a b hx, mul_zero]

/-- Local boundedness of the actual Chebyshev step error and compact source support
admit the entire discrepancy-work integral, without an arithmetic asymptotic. -/
theorem integrableOn_abelKernel_logError (f : C_c(ℝ, ℝ)) (a b : ℝ) :
    IntegrableOn (fun x => abelKernel f a b x * logError x) (Ici 0) := by
  apply integrableOn_halfLine_of_tail _ (sourceCutoff f)
    (integrable_mul_logError _ (continuous_abelKernel f a b) _)
  intro x hx
  rw [abelKernel_tail f a b x hx, zero_mul]

theorem integrableOn_shadowKernel (f : C_c(ℝ, ℝ)) (a b : ℝ) :
    IntegrableOn (shadowKernel f a b) (Ici 0) :=
  integrableOn_halfLine_of_tail _ (sourceCutoff f)
    (continuous_shadowKernel f a b).integrableOn_Icc (shadowKernel_tail f a b)

/-- Boundary-free upper endpoint; the origin contribution and polar shadow persist. -/
def fullChebyshevWork (f : C_c(ℝ, ℝ)) (a b : ℝ) : ℝ :=
  correlationAverage f a b 0 -
    (∫ x in Ici (0 : ℝ), abelKernel f a b x * logError x) -
    ∫ x in Ici (0 : ℝ), shadowKernel f a b x

/-- Every larger source cutoff computes exactly the same global Chebyshev work. -/
theorem chebyshevWork_eq_full (f : C_c(ℝ, ℝ)) (a b : ℝ) (N : ℕ)
    (hN : sourceCutoff f ≤ N) : chebyshevWork f a b N = fullChebyshevWork f a b := by
  have hEnd := correlationAverage_eq_zero_of_sourceCutoff_le f a b (cutoff_mono hN)
  have hq := integral_halfLine_eq_of_tail (fun x => abelKernel f a b x * logError x) N
    (fun x hx => by rw [abelKernel_tail f a b x ((cutoff_mono hN).trans hx), zero_mul])
  have hs := integral_halfLine_eq_of_tail (shadowKernel f a b) N
    (fun x hx => shadowKernel_tail f a b x ((cutoff_mono hN).trans hx))
  change correlationAverage f a b 0 +
      Real.exp (-cutoff N / 2) * correlationAverage f a b (cutoff N) * logError (cutoff N) -
      (∫ x in Icc 0 (cutoff N), abelKernel f a b x * logError x) -
      (∫ x in Icc 0 (cutoff N), shadowKernel f a b x) =
    correlationAverage f a b 0 -
      (∫ x in Ici (0 : ℝ), abelKernel f a b x * logError x) -
      ∫ x in Ici (0 : ℝ), shadowKernel f a b x
  rw [hEnd, mul_zero, zero_mul, add_zero, hq, hs]

/-- Exact full-half-line Stieltjes identity for every compact continuous source. -/
theorem fullPairing_average_eq_fullChebyshevWork (f : C_c(ℝ, ℝ)) (a b : ℝ) :
    fullPairing (correlationAverage f a b) = fullChebyshevWork f a b := by
  rw [fullPairing_average_eq f a b (sourceCutoff f) le_rfl,
    pairing_correlationAverage_eq]
  exact chebyshevWork_eq_full f a b (sourceCutoff f) le_rfl

/-- The literal infinite signed pairing is coupled to admitted global Chebyshev
work. Every nonnegative cutoff extension supplies an unconditional packet bound. -/
theorem abs_fullPairing_sub_fullChebyshevWork_le_packet (f : C_c(ℝ, ℝ))
    (a b : ℝ) (K : ℕ) :
    |fullPairing (autocorr f) - fullChebyshevWork f a b| ≤
      packetTransportCost f (sourceCutoff f + K) a b := by
  have hN : sourceCutoff f ≤ sourceCutoff f + K := Nat.le_add_right _ _
  rw [fullPairing_autocorr_eq f _ hN, ← chebyshevWork_eq_full f a b _ hN]
  exact abs_pairing_sub_chebyshevWork_le_packet f a b _

/-- Global signed prime–polar coupling with local Lévy energy and the exact
reciprocal archimedean penalty, with no analytic interface assumptions. -/
theorem abs_fullPairing_sub_fullChebyshevWork_le_packet_levy (f : C_c(ℝ, ℝ))
    (a b c : ℝ) (K : ℕ) :
    |fullPairing (autocorr f) - fullChebyshevWork f a b| ≤
      Real.exp c * (∫ y in Real.exp a..Real.exp a + Real.exp b,
        (autocorr f 0 - autocorr f y) * archLevySinhWeight y) +
      packetEnergy f (sourceCutoff f + K) / (2 * Real.exp c * Real.exp b ^ 2) *
        ∫ y in Real.exp a..Real.exp a + Real.exp b, Real.exp (-y / 2) * Real.sinh y :=
  (abs_fullPairing_sub_fullChebyshevWork_le_packet f a b K).trans
    (packetTransportCost_le_levy f (sourceCutoff f + K) a b c)

end
end GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
