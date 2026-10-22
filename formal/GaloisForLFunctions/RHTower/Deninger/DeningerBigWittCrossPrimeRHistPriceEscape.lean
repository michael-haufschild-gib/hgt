import GaloisForLFunctions.RHTower.Deninger.DeningerBigWittCrossPrimeHarmonicSingularGraphSource
import GaloisForLFunctions.RHTower.XiSourceHistoryPriceEscape

/-!
# Price escape of the literal Big-Witt cross-prime dark source

The canonical prime-two Big-Witt row is a genuine finite, pre-divisor cross-prime source.
Normalizing it by its divergent algebraic trace sends its ambient Calderón--Witt Hilbert packet
to zero while retaining unit singular trace.  Therefore it is an actual norm-dark source history.

This file tests that concrete history against RHist's positive response--price law.  Every
continuous real observer with nonnegative responses and a fixed positive response-times-price gap
forces the source price to escape to infinity.  The row can support singular one-leg observation,
but it cannot be a finite-price RHist producer through an ambient continuous observer.
-/

open Filter Topology

namespace RHTower

noncomputable section

open GaloisForLFunctions

/-- Ambient Calderón--Witt realization of the canonical trace-normalized finite Big-Witt row. -/
abbrev crossPrimeNormalizedPacket (n : ℕ) :
    DeningerCalderonWittCrossPrimePacketHilbert :=
  deningerBigWittCrossPairFinitePacketAdmission
    (deningerBigWittPrimeTwoRightEdgeNormalizedPacket n)

/-- The literal normalized cross-prime source row becomes norm-dark in the ambient Hilbert
carrier. -/
theorem tendsto_crossPrimeNormalizedPacket_zero :
    Tendsto crossPrimeNormalizedPacket atTop (nhds 0) :=
  tendsto_deningerBigWittCrossPairFinitePacketAdmission_primeTwoRightEdgeNormalizedPacket

/-- **Literal cross-prime RHist price escape.** A continuous positive observer cannot retain a
fixed response--price gap along the norm-dark Big-Witt source row at any finite price scale. -/
theorem crossPrimeNormalizedPacket_positiveResponse_forces_price_escape
    (φ : DeningerCalderonWittCrossPrimePacketHilbert →L[ℝ] ℝ)
    (price : ℕ → ℝ) {κ : ℝ} (hκ : 0 < κ)
    (hresponse : ∀ n, 0 ≤ φ (crossPrimeNormalizedPacket n))
    (hprice : ∀ n, 0 ≤ price n)
    (hreciprocal : ∀ n, κ ≤ φ (crossPrimeNormalizedPacket n) * price n) :
    Tendsto price atTop atTop := by
  let F : ℕ → Finset ℕ := fun n => {n}
  let mu : ℕ → ℕ → ℝ := fun n i => if i = n then 1 else 0
  have hmu : ∀ n i, i ∈ F n → 0 ≤ mu n i := by
    intro n i hi
    have : i = n := by simpa [F] using hi
    simp [mu, this]
  have hmass : ∀ n, ∑ i ∈ F n, mu n i = 1 := by
    intro n
    simp [F, mu]
  have hdark : Tendsto
      (fun n => ‖∑ i ∈ F n, mu n i • crossPrimeNormalizedPacket i‖)
      atTop (nhds 0) := by
    have h := tendsto_crossPrimeNormalizedPacket_zero.norm
    simpa [F, mu] using h
  have hresponse' : ∀ n i, i ∈ F n → 0 ≤ φ (crossPrimeNormalizedPacket i) := by
    intro n i hi
    have : i = n := by simpa [F] using hi
    simpa [this] using hresponse n
  have hprice' : ∀ n i, i ∈ F n → 0 ≤ price i := by
    intro n i hi
    have : i = n := by simpa [F] using hi
    simpa [this] using hprice n
  have hreciprocal' : ∀ n i, i ∈ F n →
      κ ≤ φ (crossPrimeNormalizedPacket i) * price i := by
    intro n i hi
    have : i = n := by simpa [F] using hi
    simpa [this] using hreciprocal n
  have hescape := GaloisForLFunctions.HTGeometry.coalitional_darkHistory_positiveGap_forces_price_escape
    F mu crossPrimeNormalizedPacket price φ hκ hmu hresponse' hprice' hmass hdark hreciprocal'
  simpa [F, mu] using hescape

end

end RHTower
