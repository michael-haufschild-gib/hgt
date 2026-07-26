import GaloisForLFunctions.HTGeometry.DirectionalVandermondePhaseJet
import GaloisForLFunctions.RHTower.PrimeIsingTreeFixedModalClosureNoGo

/-!
# Prime-Ising collision-free spectral-depth universality

The exact balanced prime-Ising spectral packet already gives a modal upper bound.  When its
frequencies are collision-free, directional Vandermonde nonflatness supplies the missing lower
statement: some derivative below packet cardinality is nonzero at every base point.
-/

namespace GaloisForLFunctions.RHTower

open Complex

noncomputable section

/-- Exact upper and lower spectral-depth data for a collision-free balanced prime-Ising packet. -/
structure PrimeIsingCollisionFreeSpectralDepthCertificate (T : PrimeIsingTree) : Prop where
  frequencyInjective :
    Function.Injective (fun i : Fin (balancedPrimeIsingTreeSpectralPacket T).length =>
      ((balancedPrimeIsingTreeSpectralPacket T).get i).frequency)
  exactCardinality :
    (balancedPrimeIsingTreeSpectralPacket T).length =
      2 ^ primeIsingTreeVertexCount T
  exactRepresentation :
    balancedPrimeIsingTreePartition T =
      primeIsingSpectralPacketEval (balancedPrimeIsingTreeSpectralPacket T)
  modalUpperBound : ∀ z : ℂ,
    HTGeometry.FiniteModalWidthAtMost (2 ^ primeIsingTreeVertexCount T)
      (fun k => iteratedDeriv k (balancedPrimeIsingTreePartition T) z)
  nonflatBelowPacketDepth : ∀ z : ℂ,
    ∃ k : Fin (balancedPrimeIsingTreeSpectralPacket T).length,
      iteratedDeriv (k : ℕ) (balancedPrimeIsingTreePartition T) z ≠ 0

/-- The amplitude vector of every exact balanced packet is nonzero: otherwise its evaluation at
the unit-normalized origin would vanish. -/
theorem balancedPrimeIsingTreeSpectralPacket_amplitudeVector_ne_zero
    (T : PrimeIsingTree) :
    (fun i : Fin (balancedPrimeIsingTreeSpectralPacket T).length =>
      ((balancedPrimeIsingTreeSpectralPacket T).get i).amplitude) ≠ 0 := by
  let packet := balancedPrimeIsingTreeSpectralPacket T
  let c : Fin packet.length → ℂ := fun i => (packet.get i).amplitude
  let lam : Fin packet.length → ℂ := fun i => (packet.get i).frequency
  have hphase :
      HTGeometry.phasePolynomial lam c = primeIsingSpectralPacketEval packet := by
    rw [primeIsingSpectralPacketEval_eq_fin_sum]
    rfl
  intro hc
  have hc' : c = 0 := by
    simpa only [c, packet] using hc
  have hphaseZero : HTGeometry.phasePolynomial lam c 0 = 0 := by
    simp [HTGeometry.phasePolynomial, hc']
  have hbalancedZero : balancedPrimeIsingTreePartition T 0 = 0 := by
    rw [balancedPrimeIsingTreePartition_eq_spectralPacketEval]
    change primeIsingSpectralPacketEval packet 0 = 0
    rw [← hphase]
    exact hphaseZero
  rw [balancedPrimeIsingTreePartition_zero] at hbalancedZero
  exact one_ne_zero hbalancedZero

/-- A collision-free balanced prime-Ising packet has a nonzero derivative below packet cardinality
at every base point. -/
theorem balancedPrimeIsingTreePartition_nonflatBelowPacketDepth
    (T : PrimeIsingTree)
    (hfrequency :
      Function.Injective (fun i : Fin (balancedPrimeIsingTreeSpectralPacket T).length =>
        ((balancedPrimeIsingTreeSpectralPacket T).get i).frequency))
    (z : ℂ) :
    ∃ k : Fin (balancedPrimeIsingTreeSpectralPacket T).length,
      iteratedDeriv (k : ℕ) (balancedPrimeIsingTreePartition T) z ≠ 0 := by
  let packet := balancedPrimeIsingTreeSpectralPacket T
  let c : Fin packet.length → ℂ := fun i => (packet.get i).amplitude
  let lam : Fin packet.length → ℂ := fun i => (packet.get i).frequency
  have hfrequency' : Function.Injective lam := by
    simpa only [lam, packet] using hfrequency
  have hc : c ≠ 0 := by
    simpa only [c, packet] using
      balancedPrimeIsingTreeSpectralPacket_amplitudeVector_ne_zero T
  have hphase :
      HTGeometry.phasePolynomial lam c = primeIsingSpectralPacketEval packet := by
    rw [primeIsingSpectralPacketEval_eq_fin_sum]
    rfl
  obtain ⟨k, hk⟩ := HTGeometry.phaseJet_exists_ne_zero hfrequency' hc z
  refine ⟨k, ?_⟩
  rw [hphase] at hk
  change iteratedDeriv (k : ℕ)
    (primeIsingSpectralPacketEval (balancedPrimeIsingTreeSpectralPacket T)) z ≠ 0 at hk
  rwa [← balancedPrimeIsingTreePartition_eq_spectralPacketEval] at hk

/-- **Prime-Ising collision-free spectral-depth universality law.**  Exact cardinality,
representation, modal upper bound, and base-point-uniform nonflatness form one certificate. -/
theorem primeIsingCollisionFree_spectralDepthUniversality
    (T : PrimeIsingTree)
    (hfrequency :
      Function.Injective (fun i : Fin (balancedPrimeIsingTreeSpectralPacket T).length =>
        ((balancedPrimeIsingTreeSpectralPacket T).get i).frequency)) :
    PrimeIsingCollisionFreeSpectralDepthCertificate T where
  frequencyInjective := hfrequency
  exactCardinality := length_balancedPrimeIsingTreeSpectralPacket T
  exactRepresentation := balancedPrimeIsingTreePartition_eq_spectralPacketEval T
  modalUpperBound :=
    finiteModalWidthAtMost_iteratedDeriv_balancedPrimeIsingTreePartition T
  nonflatBelowPacketDepth :=
    balancedPrimeIsingTreePartition_nonflatBelowPacketDepth T hfrequency

end

end GaloisForLFunctions.RHTower
