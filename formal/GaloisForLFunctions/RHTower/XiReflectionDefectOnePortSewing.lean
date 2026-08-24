import GaloisForLFunctions.RHTower.SourceHorizontalSharedReservoirStokesObstruction
import GaloisForLFunctions.RHTower.RouteRHarmonicQuantumGapCriterion

/-!
# Reflection-defect one-port sewing

This module packages the source-first global object exposed by the shared-reservoir/Stokes
obstruction.  Every Xi divisor copy retains its own multiplicity and provenance, and the forward
and reflected three-prime packets may have different landing maps.  What is shared is the
coefficient-generated global Stokes carrier and its unique physical-rank port.

The package is deliberately stronger than separate pointwise realizations: one carrier is fixed
before any divisor copy is read.  If such a sewing exists, an off-line copy would force at least
two negative source directions into a carrier with at most one negative port.  Hence every copy
lies on the critical line and RH follows.

No sewing is constructed here.  The remaining source theorem must build this object from the
Euler--Gamma completion without selecting zeros or assigning independent reflected reservoirs.
-/

open GaloisForLFunctions

namespace RHTower

noncomputable section

namespace ReflectionDefectOnePortSewing

open GaloisForLFunctions.IrregularStokes.GlobalPuiseuxWitt

/--
One coefficient-generated Stokes carrier receiving every multiplicity-labelled Xi defect and its
reflection.  The local prime packet is part of the source datum, while the two landing maps retain
orientation.  Only the global carrier is required to be common.
-/
structure XiGlobalOnePortSewing where
  markedPointDepth : ℕ
  orbitCount : Fin (markedPointDepth + 1) → ℕ
  fiberRank : Fin (markedPointDepth + 1) → ℕ
  coverDegree : Fin (markedPointDepth + 1) → ℕ
  jetDepth : Fin (markedPointDepth + 1) → ℕ
  genus : ℕ
  localData : LocalData markedPointDepth orbitCount fiberRank coverDegree jetDepth
  primes : Fin 3 → Nat.Primes
  forward :
    (q : XiZeroCopy) →
      (Fin 3 → ℝ) →ₗ[ℝ] compatibleCharges localData
  reflected :
    (q : XiZeroCopy) →
      (Fin 3 → ℝ) →ₗ[ℝ] compatibleCharges localData
  forward_preserves : ∀ q x,
    (sourceZeroHorizontalSharedReservoirMatrix q primes).toQuadraticForm' x =
      globalWittForm genus localData (forward q x)
  reflected_preserves : ∀ q x,
    (sourceZeroHorizontalSharedReservoirMatrix
      (xiZeroCopyLineConjEquiv q) primes).toQuadraticForm' x =
        globalWittForm genus localData (reflected q x)

/-- One global one-port sewing forces an arbitrary Xi divisor point onto the critical line. -/
theorem xiDivisorSupport_re_eq_half_of_globalOnePortSewing
    (S : XiGlobalOnePortSewing) (rho : XiDivisorSupport) :
    (rho : ℂ).re = 1 / 2 := by
  let q : XiZeroCopy := xiFirstZeroCopy rho
  by_contra hoff
  have hqoff : (q.1 : ℂ).re ≠ 1 / 2 := by
    simpa [q] using hoff
  exact
    (GlobalPuiseuxWittLanding.not_both_sourceZeroHorizontal_orientations_land_in_globalWitt
      (m := 3) (by norm_num) q hqoff S.primes S.genus S.localData
      (S.forward q) (S.reflected q))
      ⟨S.forward_preserves q, S.reflected_preserves q⟩

/--
Global defect-budget endpoint.  A source construction of one common coefficient-generated Stokes
carrier for all forward/reflected three-prime defect packets proves RH without erasing divisor
cores, multiplicities, or prime provenance.
-/
theorem riemannHypothesis_of_globalOnePortSewing
    (S : XiGlobalOnePortSewing) : RiemannHypothesis := by
  apply riemannHypothesis_of_forall_xiDivisorSupport_re_eq_half
  exact xiDivisorSupport_re_eq_half_of_globalOnePortSewing S

end ReflectionDefectOnePortSewing

end

end RHTower
