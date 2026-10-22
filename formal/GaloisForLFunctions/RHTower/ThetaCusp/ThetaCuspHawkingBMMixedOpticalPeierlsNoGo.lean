import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingCubicPeierlsPolarization
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMMixedHorizonCausalOpticalProducer

/-!
# Peierls obstruction to the one-channel BM mixed optical landing

The existing conditional Birmingham--Mokhtari optical producer assumes that the `+-` response
jump carries the cubic causal cut while the sourced `++` jump vanishes. Those assumptions cannot
describe an off-critical causal cut of one cyclic variational theory.

Indeed, cyclicity turns the projected mixed contribution into the causal self-pairing of its own
quadratic source. Peierls skewness kills that term. If the `++` sourced jump also vanishes, the
complete cut is zero. The conditional mixed optical landing instead makes the same cut nonzero at
every off-critical Xi fibre. Hence its response-incidence, zero-`++`, and positive reciprocity
hypotheses cannot simultaneously weld to an augmented action pairing and Peierls propagator.
-/

open Complex

namespace RHTower

noncomputable section

variable {X Y : Type*}
  [AddCommGroup X] [Module ℂ X]
  [AddCommGroup Y] [Module ℂ Y]

/-- In a cyclic variational theory, a vanishing `++` sourced jump makes the complete cubic cut
zero: the remaining mixed term is a Peierls self-pairing. -/
theorem d4GaugeFixedTeukolskyCokernelCausalCut_eq_zero_of_Peierls_of_ppJump_eq_zero
    (pairing : X →ₗ[ℂ] Y →ₗ[ℂ] ℂ)
    (B : X →ₗ[ℂ] X →ₗ[ℂ] Y)
    (C : X →ₗ[ℂ] X →ₗ[ℂ] X →ₗ[ℂ] Y)
    (Delta : Y →ₗ[ℂ] X)
    (RppRet RpmRet RppAdv RpmAdv : Y →ₗ[ℂ] X) (p m : X)
    (hB : ∀ x y, B x y = B y x)
    (hcyclic : ∀ x y z, pairing x (B y z) = pairing z (B x y))
    (hRpm : RpmRet - RpmAdv = Delta)
    (hskew : ∀ f g, d4GaugeFixedTeukolskyPeierlsSourcePairing pairing Delta f g =
      -d4GaugeFixedTeukolskyPeierlsSourcePairing pairing Delta g f)
    (hpp : (RppRet - RppAdv)
      (d4GaugeFixedTeukolskyQuadraticPlusPlusResidual B p) = 0) :
    d4GaugeFixedTeukolskyTotalPlusPlusMinusCokernelCausalCut
        (pairing m) B C RppRet RpmRet RppAdv RpmAdv p m = 0 := by
  rw [d4GaugeFixedTeukolskyTotalPlusPlusMinusCokernelCausalCut_eq,
    hRpm, hpp,
    d4GaugeFixedTeukolskyPeierls_mixed_self_eq_zero
      pairing B Delta p m hB hcyclic hskew]
  simp

/-- The existing one-channel mixed optical landing cannot be the causal cut of a cyclic
variational theory with a skew Peierls propagator at an off-critical Xi fibre. -/
theorem d4BMXiMixedHorizonOpticalLanding_not_Peierls_of_offCritical
    (pairing : X →ₗ[ℂ] Y →ₗ[ℂ] ℂ)
    (B : X →ₗ[ℂ] X →ₗ[ℂ] Y)
    (C : X →ₗ[ℂ] X →ₗ[ℂ] X →ₗ[ℂ] Y)
    (Delta : Y →ₗ[ℂ] X)
    (RppRet RpmRet RppAdv RpmAdv : Y →ₗ[ℂ] X) (p m u : X)
    {amplitude : ℂ} (ha : amplitude ≠ 0)
    (n k : ℕ) (orthogonalMixing : ℂ) (q : XiZeroCopy)
    (hoff : (q.1 : ℂ).re ≠ 1 / 2)
    (hB : ∀ x y, B x y = B y x)
    (hcyclic : ∀ x y z, pairing x (B y z) = pairing z (B x y))
    (hRpm : RpmRet - RpmAdv = Delta)
    (hskew : ∀ f g, d4GaugeFixedTeukolskyPeierlsSourcePairing pairing Delta f g =
      -d4GaugeFixedTeukolskyPeierlsSourcePairing pairing Delta g f)
    (hpm : (RpmRet - RpmAdv)
      (d4GaugeFixedTeukolskyQuadraticPlusMinusResidual B p m) =
        d4BMXiMixedHorizonComplexMonodromyJump n k q • u)
    (hpp : (RppRet - RppAdv)
      (d4GaugeFixedTeukolskyQuadraticPlusPlusResidual B p) = 0)
    (hreciprocity : pairing m (B p u) =
      Complex.normSq
        (d4BMMixedHorizonOpticalSourceProjection amplitude orthogonalMixing q)) :
    False := by
  have hcutzero :=
    d4GaugeFixedTeukolskyCokernelCausalCut_eq_zero_of_Peierls_of_ppJump_eq_zero
      pairing B C Delta RppRet RpmRet RppAdv RpmAdv p m
        hB hcyclic hRpm hskew hpp
  have hoptical := d4BMXiMixedHorizon_totalCokernelCausalCut_eq_opticalSection
    (pairing m) B C RppRet RpmRet RppAdv RpmAdv p m u n k
      amplitude orthogonalMixing q hpm hpp hreciprocity
  have hopticalzero :
      d4BMXiMixedHorizonCausalOpticalSection
        n k amplitude orthogonalMixing q = 0 := by
    rw [← hoptical, hcutzero]
  exact hoff ((d4BMXiMixedHorizonCausalOpticalSection_eq_zero_iff
    ha n k orthogonalMixing q).mp hopticalzero)

end

end RHTower
