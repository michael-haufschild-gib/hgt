import GaloisForLFunctions.RHTower.XiQuotientRealDecay
import GaloisForLFunctions.RHTower.XiWeilCauchyCoreMultiplicity
import GaloisForLFunctions.RHTower.CCM.CCMPublishedRestrictedWeilMatrix
import GaloisForLFunctions.RHTower.CCM.CCMRectangularTwoEdge

/-!
# The C1--O open-core reduction

Absolute-domain Cauchy packet source sums converge to the Hilbert pairing supplied by the closed
C1 resolvent core.  Consequently, convergence of those same sums to any independently specified
arithmetic value is equivalent to equality of that value with the Hilbert pairing.  Specializing
the arithmetic value to the literal published CCM restricted-Weil functional, or to any entry of
its finite matrix, isolates the C1--O connector exactly.

This module does not assert that the connector holds.  It also records the unconditional closed-core
membership of the square-summable rectangular profiles and exact negativity transport on the
absolute-domain packet class.
-/

open Complex Filter

namespace RHTower

noncomputable section

/-- Evaluation vector of a finite Cauchy packet whose nodes lie in the absolute prime-source
half-plane. -/
def xiAbsoluteCauchyPacketEvaluation (s : Finset ℂ) (c : ℂ → ℂ)
    (hzhalf : ∀ z ∈ s, 1 < (1 / 2 + z * I).re) :
    lp (fun _ : XiZeroCopy => ℂ) 2 :=
  xiWeilEvaluationLp (xiWeilCauchyPacket s c)
    (XiWeilSquareSummable_cauchyPacket c
      (fun z hz => XiC_ne_zero_of_one_lt_centered_re (hzhalf z hz)))

/-- Finite prime-plus-archimedean divided-difference source pairing for two Cauchy packets. -/
def cOnePrimeArchPacketSource (s : Finset ℂ) (c : ℂ → ℂ)
    (t : Finset ℂ) (d : ℂ → ℂ) : ℂ :=
  ∑ z ∈ s, ∑ w ∈ t,
    c z * (starRingEnd ℂ) (d w) *
      ((primeArchSourceRelativeTrace ((starRingEnd ℂ) w) -
        primeArchSourceRelativeTrace z) / (z - (starRingEnd ℂ) w))

/-- C1's continuous Hilbert extension against one fixed right Cauchy packet. -/
def cOneExtendedPairing (t : Finset ℂ) (d : ℂ → ℂ)
    (hd : XiWeilSquareSummable (xiWeilCauchyPacket t d))
    (v : lp (fun _ : XiZeroCopy => ℂ) 2) : ℂ :=
  inner ℂ (xiWeilLineConjLp
    (xiWeilEvaluationLp (xiWeilCauchyPacket t d) hd)) v

/-- Absolute-domain source sums converge to C1's continuous Hilbert extension along every
convergent packet approximation. -/
theorem tendsto_cOnePrimeArchPacketSource
    {sn : ℕ → Finset ℂ} {cn : ℕ → ℂ → ℂ} {t : Finset ℂ} {d : ℂ → ℂ}
    (hzhalf : ∀ n, ∀ z ∈ sn n, 1 < (1 / 2 + z * I).re)
    (hwhalf : ∀ w ∈ t, 1 < (1 / 2 + (starRingEnd ℂ) w * I).re)
    (hsep : ∀ n, ∀ z ∈ sn n, ∀ w ∈ t, z ≠ (starRingEnd ℂ) w)
    (hd : XiWeilSquareSummable (xiWeilCauchyPacket t d))
    {v : lp (fun _ : XiZeroCopy => ℂ) 2}
    (hconv : Tendsto
      (fun n => xiAbsoluteCauchyPacketEvaluation (sn n) (cn n) (hzhalf n))
      atTop (nhds v)) :
    Tendsto (fun n => cOnePrimeArchPacketSource (sn n) (cn n) t d)
      atTop (nhds (cOneExtendedPairing t d hd v)) := by
  let hreg : ∀ n, ∀ z ∈ sn n, XiC z ≠ 0 :=
    fun n z hz => XiC_ne_zero_of_one_lt_centered_re (hzhalf n z hz)
  have hconv' : Tendsto
      (fun n => xiWeilEvaluationLp (xiWeilCauchyPacket (sn n) (cn n))
        (XiWeilSquareSummable_cauchyPacket (cn n) (hreg n)))
      atTop (nhds v) := by
    simpa only [xiAbsoluteCauchyPacketEvaluation] using hconv
  simpa only [cOnePrimeArchPacketSource, cOneExtendedPairing] using
    tendsto_primeArchSource_packetSum_of_tendsto hreg hzhalf hwhalf hsep hd hconv'

/-- **Closed-class reduction.**  For a fixed convergent absolute-domain approximation, its source
sums converge to a proposed arithmetic value exactly when that value equals C1's Hilbert limit. -/
theorem tendsto_cOnePrimeArchPacketSource_iff_eq_extendedPairing
    {sn : ℕ → Finset ℂ} {cn : ℕ → ℂ → ℂ} {t : Finset ℂ} {d : ℂ → ℂ}
    (hzhalf : ∀ n, ∀ z ∈ sn n, 1 < (1 / 2 + z * I).re)
    (hwhalf : ∀ w ∈ t, 1 < (1 / 2 + (starRingEnd ℂ) w * I).re)
    (hsep : ∀ n, ∀ z ∈ sn n, ∀ w ∈ t, z ≠ (starRingEnd ℂ) w)
    (hd : XiWeilSquareSummable (xiWeilCauchyPacket t d))
    {v : lp (fun _ : XiZeroCopy => ℂ) 2}
    (hconv : Tendsto
      (fun n => xiAbsoluteCauchyPacketEvaluation (sn n) (cn n) (hzhalf n))
      atTop (nhds v)) (A : ℂ) :
    Tendsto (fun n => cOnePrimeArchPacketSource (sn n) (cn n) t d)
        atTop (nhds A) ↔
      A = cOneExtendedPairing t d hd v := by
  have hsource := tendsto_cOnePrimeArchPacketSource hzhalf hwhalf hsep hd hconv
  constructor
  · intro hA
    exact tendsto_nhds_unique hA hsource
  · intro hA
    rwa [hA]

/-- **C1--O connector, literal functional form.**  The packet source converges to the published
restricted-Weil value exactly when that literal O value is the C1 Hilbert limit. -/
theorem tendsto_cOnePrimeArchPacketSource_to_publishedWeil_iff_connector
    {sn : ℕ → Finset ℂ} {cn : ℕ → ℂ → ℂ} {t : Finset ℂ} {d : ℂ → ℂ}
    (hzhalf : ∀ n, ∀ z ∈ sn n, 1 < (1 / 2 + z * I).re)
    (hwhalf : ∀ w ∈ t, 1 < (1 / 2 + (starRingEnd ℂ) w * I).re)
    (hsep : ∀ n, ∀ z ∈ sn n, ∀ w ∈ t, z ≠ (starRingEnd ℂ) w)
    (hd : XiWeilSquareSummable (xiWeilCauchyPacket t d))
    {v : lp (fun _ : XiZeroCopy => ℂ) 2}
    (hconv : Tendsto
      (fun n => xiAbsoluteCauchyPacketEvaluation (sn n) (cn n) (hzhalf n))
      atTop (nhds v)) (a : ℝ) (F : ℝ → ℝ) :
    Tendsto (fun n => cOnePrimeArchPacketSource (sn n) (cn n) t d) atTop
        (nhds (ccmPublishedRestrictedWeilPairing a F : ℂ)) ↔
      (ccmPublishedRestrictedWeilPairing a F : ℂ) =
        cOneExtendedPairing t d hd v :=
  tendsto_cOnePrimeArchPacketSource_iff_eq_extendedPairing
    hzhalf hwhalf hsep hd hconv _

/-- Matrix-family form of the same connector: every literal published CCM matrix entry is covered,
including both tent-cosine diagonals and divided-difference sine off-diagonals. -/
theorem tendsto_cOnePrimeArchPacketSource_to_publishedMatrix_iff_connector
    {sn : ℕ → Finset ℂ} {cn : ℕ → ℂ → ℂ} {t : Finset ℂ} {d : ℂ → ℂ}
    (hzhalf : ∀ n, ∀ z ∈ sn n, 1 < (1 / 2 + z * I).re)
    (hwhalf : ∀ w ∈ t, 1 < (1 / 2 + (starRingEnd ℂ) w * I).re)
    (hsep : ∀ n, ∀ z ∈ sn n, ∀ w ∈ t, z ≠ (starRingEnd ℂ) w)
    (hd : XiWeilSquareSummable (xiWeilCauchyPacket t d))
    {v : lp (fun _ : XiZeroCopy => ℂ) 2}
    (hconv : Tendsto
      (fun n => xiAbsoluteCauchyPacketEvaluation (sn n) (cn n) (hzhalf n))
      atTop (nhds v)) (a : ℝ) (N : ℕ) (i j : Fin (2 * N + 1)) :
    Tendsto (fun n => cOnePrimeArchPacketSource (sn n) (cn n) t d) atTop
        (nhds (ccmPublishedRestrictedWeilMatrix a N i j : ℂ)) ↔
      (ccmPublishedRestrictedWeilMatrix a N i j : ℂ) =
        cOneExtendedPairing t d hd v :=
  tendsto_cOnePrimeArchPacketSource_iff_eq_extendedPairing
    hzhalf hwhalf hsep hd hconv _

/-- Every explicit rectangular profile lies in the closed C1 Cauchy core. -/
theorem xiRectangularTwoEdgeEvaluation_mem_cOneClosedCore (L a : ℝ) :
    xiWeilEvaluationLp (xiRectangularTwoEdgeTransform L a)
        (xiRectangularTwoEdgeTransform_squareSummable L a) ∈
      xiWeilCauchyHilbertSubspace :=
  xiWeilEvaluationLp_mem_xiWeilCauchyHilbertSubspace _ _

/-- On absolute-domain packets, the source pairing is exactly the Xi spectral polarization. -/
theorem xiWeilPolarization_cauchyPacket_eq_cOnePrimeArchPacketSource
    {s t : Finset ℂ} {c d : ℂ → ℂ}
    (hzhalf : ∀ z ∈ s, 1 < (1 / 2 + z * I).re)
    (hwhalf : ∀ w ∈ t, 1 < (1 / 2 + (starRingEnd ℂ) w * I).re)
    (hsep : ∀ z ∈ s, ∀ w ∈ t, z ≠ (starRingEnd ℂ) w) :
    xiWeilPolarization (xiWeilCauchyPacket s c) (xiWeilCauchyPacket t d) =
      cOnePrimeArchPacketSource s c t d := by
  exact xiWeilPolarization_cauchyPacket_eq_primeArchSource hzhalf hwhalf hsep

/-- **Unconditional witness transport on the closed packet class.**  Arithmetic and spectral
real-part negativity are equivalent for every absolute-domain separated packet pair. -/
theorem cOnePrimeArchPacketSource_re_lt_zero_iff_polarization
    {s t : Finset ℂ} {c d : ℂ → ℂ}
    (hzhalf : ∀ z ∈ s, 1 < (1 / 2 + z * I).re)
    (hwhalf : ∀ w ∈ t, 1 < (1 / 2 + (starRingEnd ℂ) w * I).re)
    (hsep : ∀ z ∈ s, ∀ w ∈ t, z ≠ (starRingEnd ℂ) w) :
    (cOnePrimeArchPacketSource s c t d).re < 0 ↔
      (xiWeilPolarization (xiWeilCauchyPacket s c)
        (xiWeilCauchyPacket t d)).re < 0 := by
  rw [xiWeilPolarization_cauchyPacket_eq_cOnePrimeArchPacketSource hzhalf hwhalf hsep]

end

end RHTower
