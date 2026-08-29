import GaloisForLFunctions.RHTower.MobiusThetaAdaptiveGreenDoubleLogResidueWeld
import GaloisForLFunctions.RHTower.MobiusThetaPhysicalSourceToXiLanding

/-!
# Continuous coface-annihilator no-go for the complete physical Möbius--theta source

The complete exponent cofaces of the physical Möbius--theta source are absolutely summable.
Their finite codiagonals were already known to converge strongly to the canonical theta source.
We identify the Banach sum itself with that source and use continuity to close a source-weld
no-go.

Any continuous linear map that annihilates every exact physical coface also annihilates the
theta generator.  Consequently, away from the critical line, no such map can land the theta
generator on the nonzero actual adaptive Green codiagonal.  Equivalently, every continuous
coefficient-faithful off-wall landing detects at least one physical coface.

This retires continuous same-`L²` coface annihilation as the missing source differential behind
the adaptive Green/double-log RH chain.  A surviving producer must change topology, pass through
a nontrivial quotient, or become divisor-dependent before completion.
-/

open Complex Filter
open scoped Topology

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry
open DeningerMeyerGaussianGreen

/-- Absolute Banach codiagonal of all complete physical exponent cofaces is exactly the
canonical theta source. -/
theorem tsum_mobiusThetaCompletePhysicalChannel_three_eq_thetaSource :
    (∑' j : ℕ, mobiusThetaCompletePhysicalChannel 3 j) = xiThetaSourceL2 := by
  have hsum : Tendsto
      (fun N : ℕ =>
        ∑ j ∈ Finset.range (N + 1), mobiusThetaCompletePhysicalChannel 3 j)
      atTop (nhds (∑' j : ℕ, mobiusThetaCompletePhysicalChannel 3 j)) := by
    have h := summable_mobiusThetaCompletePhysicalChannel_three.hasSum.tendsto_sum_nat
    exact (h.comp (tendsto_add_atTop_nat 1)).congr'
      (Filter.Eventually.of_forall fun _N => rfl)
  exact tendsto_nhds_unique hsum
    (tendsto_sum_range_mobiusThetaCompletePhysicalChannel 3)

/-- A continuous source differential killing every complete physical exponent coface must also
kill their nonzero total theta-source class. -/
theorem continuousLinearMap_thetaSource_eq_zero_of_annihilates_completePhysicalCofaces
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (D : MobiusThetaSourceL2 →L[ℂ] E)
    (hcoface : ∀ j : ℕ, D (mobiusThetaCompletePhysicalChannel 3 j) = 0) :
    D xiThetaSourceL2 = 0 := by
  calc
    D xiThetaSourceL2 = D (∑' j : ℕ, mobiusThetaCompletePhysicalChannel 3 j) := by
      rw [tsum_mobiusThetaCompletePhysicalChannel_three_eq_thetaSource]
    _ = ∑' j : ℕ, D (mobiusThetaCompletePhysicalChannel 3 j) :=
      D.map_tsum summable_mobiusThetaCompletePhysicalChannel_three
    _ = 0 := by simp [hcoface]

/-- Off the critical line, continuous same-completion coface annihilation cannot land the theta
generator on the actual adaptive Green codiagonal. -/
theorem not_exists_continuous_completePhysicalCofaceAnnihilator_landing_actualGreenCodiagonal
    (p : Nat.Primes) (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2) :
    ¬ ∃ D : MobiusThetaSourceL2 →L[ℂ] AdaptiveArithmeticL1,
      (∀ j : ℕ, D (mobiusThetaCompletePhysicalChannel 3 j) = 0) ∧
        D xiThetaSourceL2 =
          resolvedDefectCodiagonal (R := ℂ)
            (adaptivePrimeNormalActualGreenResolvedLineComparison p q) := by
  rintro ⟨D, hcoface, hlanding⟩
  have hsource : D xiThetaSourceL2 = 0 :=
    continuousLinearMap_thetaSource_eq_zero_of_annihilates_completePhysicalCofaces
      D hcoface
  have hcodiagonal :
      resolvedDefectCodiagonal (R := ℂ)
          (adaptivePrimeNormalActualGreenResolvedLineComparison p q) = 0 := by
    rw [← hlanding, hsource]
  exact hoff
    ((adaptivePrimeNormalActualGreenResolvedLineComparison_codiagonal_eq_zero_iff
      p q).1 hcodiagonal)

/-- Positive survivor: every continuous off-wall landing that faithfully sends the theta source
to the actual Green codiagonal detects at least one exact physical exponent coface. -/
theorem exists_completePhysicalCoface_detected_of_landing_actualGreenCodiagonal_offLine
    (p : Nat.Primes) (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2)
    (D : MobiusThetaSourceL2 →L[ℂ] AdaptiveArithmeticL1)
    (hlanding : D xiThetaSourceL2 =
      resolvedDefectCodiagonal (R := ℂ)
        (adaptivePrimeNormalActualGreenResolvedLineComparison p q)) :
    ∃ j : ℕ, D (mobiusThetaCompletePhysicalChannel 3 j) ≠ 0 := by
  by_contra hnone
  have hcoface : ∀ j : ℕ,
      D (mobiusThetaCompletePhysicalChannel 3 j) = 0 := by
    intro j
    by_contra hj
    exact hnone ⟨j, hj⟩
  exact not_exists_continuous_completePhysicalCofaceAnnihilator_landing_actualGreenCodiagonal
    p q hoff ⟨D, hcoface, hlanding⟩

/-- Global classification of the proposed source weld.  Such continuous coface annihilators can
land the theta generator on every actual Green codiagonal exactly under RH; under RH the zero map
is the certificate.  Thus constructing these maps cannot be an independent source proof step. -/
theorem all_exists_continuous_completePhysicalCofaceAnnihilator_landing_actualGreenCodiagonal_iff_rh
    (p : Nat.Primes) :
    (∀ q : XiZeroCopy,
      ∃ D : MobiusThetaSourceL2 →L[ℂ] AdaptiveArithmeticL1,
        (∀ j : ℕ, D (mobiusThetaCompletePhysicalChannel 3 j) = 0) ∧
          D xiThetaSourceL2 =
            resolvedDefectCodiagonal (R := ℂ)
              (adaptivePrimeNormalActualGreenResolvedLineComparison p q)) ↔
      RiemannHypothesis := by
  constructor
  · intro hsource
    apply (adaptivePrimeNormalActualGreenCodiagonal_all_zero_iff_riemannHypothesis p).1
    intro q
    obtain ⟨D, hcoface, hlanding⟩ := hsource q
    rw [← hlanding]
    exact continuousLinearMap_thetaSource_eq_zero_of_annihilates_completePhysicalCofaces
      D hcoface
  · intro hRH q
    refine ⟨0, by simp, ?_⟩
    have hcodiagonal :=
      (adaptivePrimeNormalActualGreenCodiagonal_all_zero_iff_riemannHypothesis p).2 hRH q
    simp [hcodiagonal]

end

end RHTower
