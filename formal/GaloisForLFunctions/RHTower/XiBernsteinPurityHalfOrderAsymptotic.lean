import GaloisForLFunctions.RHTower.AtomicBernsteinMaximalPacketAsymptotic
import GaloisForLFunctions.RHTower.XiBernsteinMaximalPacketAsymptotic
import GaloisForLFunctions.RHTower.XiBernsteinAtomicPacket

/-!
# Sharp half-order asymptotic of the complete Xi Bernstein purity

The source-defined endpoint purity is the square energy of the full absolutely summable Xi atomic
packet.  Under failure of RH, finite maximal-coordinate diagonal terms have a positive half-order
limit, mixed maximal terms are strictly gapped, and the complete nonmaximal complement is
exponentially smaller.  Thus the full source coefficients—not merely a finite model—have a
positive `B^(2n)/sqrt(n)` leading term.
-/

open Complex Filter Topology
open scoped BigOperators Real

namespace RHTower

noncomputable section

/-- The source-defined endpoint purity is exactly the square energy of its atomic Xi packet. -/
theorem primeArchEndpointBernsteinPurity_eq_atomicBernsteinPacketSquareEnergy
    (n : ℕ) :
    primeArchEndpointBernsteinPurity n =
      atomicBernsteinPacketSquareEnergy xiZeroCopyReciprocalSquare
        xiEndpointNormalizedReciprocalSquare n := by
  rw [primeArchEndpointBernsteinPurity, bernsteinCoefficientPurity,
    atomicBernsteinPacketSquareEnergy, finiteComplexPacketSquareEnergy,
    ← primeArchEndpointBernsteinPacket_eq_atomic]
  apply Finset.sum_congr rfl
  intro k hk
  rw [primeArchEndpointBernsteinPacket, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- **Sharp positive half-order asymptotic of the complete Xi Bernstein purity under failure of
RH.**  The source-defined coefficients, not merely a finite model, have a positive
`B^(2n)/sqrt(n)` leading term. -/
theorem exists_positive_halfOrder_primeArchEndpointBernsteinPurity_of_not_rh
    (hRH : ¬ RiemannHypothesis) :
    ∃ D : Finset XiZeroCopy, ∃ B beta L : ℝ,
      1 < B ∧ 1 < beta ∧ beta < B ∧ D.Nonempty ∧
      (∀ q ∈ D, xiEndpointBernsteinAtomAmplitudeBase q = B) ∧
      (∀ q ∉ D, xiEndpointBernsteinAtomAmplitudeBase q ≤ beta) ∧
      L = ∑ u ∈ xiEndpointCoordinateSet D,
        ‖xiEndpointCoordinateWeight D u‖ ^ (2 : ℕ) *
          bernsteinAffineRowHalfOrderConstant u ∧
      0 < L ∧
      Tendsto
        (fun n : ℕ => Real.sqrt n * primeArchEndpointBernsteinPurity n /
          (B ^ (2 : ℕ)) ^ n)
        atTop (nhds L) := by
  obtain ⟨D, B, beta, hB, hbeta1, hbeta, hDne, hD, hDsub,
      hmax, hLpos⟩ :=
    exists_positive_halfOrder_maximalXiBernsteinCoordinatePacket_of_not_rh hRH
  let L : ℝ := ∑ u ∈ xiEndpointCoordinateSet D,
    ‖xiEndpointCoordinateWeight D u‖ ^ (2 : ℕ) *
      bernsteinAffineRowHalfOrderConstant u
  have hfull :=
    tendsto_atomicBernsteinPacketSquareEnergy_of_finiteCoordinatePacket
      D xiZeroCopyReciprocalSquare xiEndpointNormalizedReciprocalSquare
      summable_xiZeroCopyReciprocalSquare
      (lt_trans zero_lt_one hB) (zero_le_one.trans hbeta1.le) hbeta
      (fun q hq => (hD q hq).le) hDsub (by
        exact hmax)
  have hpurity : Tendsto
      (fun n : ℕ => Real.sqrt n * primeArchEndpointBernsteinPurity n /
        (B ^ (2 : ℕ)) ^ n)
      atTop (nhds L) := by
    apply hfull.congr'
    exact Eventually.of_forall fun n => by
      change Real.sqrt n *
          atomicBernsteinPacketSquareEnergy xiZeroCopyReciprocalSquare
            xiEndpointNormalizedReciprocalSquare n / (B ^ (2 : ℕ)) ^ n =
        Real.sqrt n * primeArchEndpointBernsteinPurity n / (B ^ (2 : ℕ)) ^ n
      rw [primeArchEndpointBernsteinPurity_eq_atomicBernsteinPacketSquareEnergy]
  exact ⟨D, B, beta, L, hB, hbeta1, hbeta, hDne, hD, hDsub,
    rfl, hLpos, hpurity⟩

end

end RHTower
