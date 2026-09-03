import GaloisForLFunctions.RHTower.XiOrderedPrimeTraceClassRelocation
import GaloisForLFunctions.RHTower.ArithmeticDilationTraceClass

/-!
# Paired relative-trace cancellation for ordered Xi/RVM relocation

The ordered-Xi relocation operator and its smooth Riemann--von Mangoldt skeleton
have a trace-class difference.  This module computes its ordinary trace exactly.
The positive and negative marked-prime sectors carry opposite copies of every
diagonal relocation coefficient, so the relative trace is zero.

Consequently this concrete relative-completion candidate cannot carry the unit
charge required by a strict-right escape class.  The obstruction is structural:
it does not depend on an estimate or on the location of any Xi zero.
-/

open scoped BigOperators InnerProductSpace

namespace RHTower

noncomputable section

/-- The trace-class ordered-Xi/RVM relocation has exactly zero ordinary trace. -/
theorem opTrace_xiOrderedSignedPrimeRVMCorrection_eq_zero :
    ContinuousLinearMap.opTrace xiOrderedSignedPrimeRVMCorrection = 0 := by
  rw [opTrace_eq_tsum_basis_of_memSchattenClass_one
    xiOrderedSignedPrimeRVMCorrection_memSchattenClass_one
    (HTGeometry.ellTwoCoordinateBasis RouteKSignedPrimeIndex)]
  have hdiag : ∀ i : RouteKSignedPrimeIndex,
      inner ℂ
          (HTGeometry.ellTwoCoordinateBasis RouteKSignedPrimeIndex i)
          (xiOrderedSignedPrimeRVMCorrection
            (HTGeometry.ellTwoCoordinateBasis RouteKSignedPrimeIndex i)) =
        (xiOrderedSignedPrimeRVMCorrectionMultiplier i : ℂ) := by
    intro i
    have hact : xiOrderedSignedPrimeRVMCorrection
          (HTGeometry.ellTwoCoordinateBasis RouteKSignedPrimeIndex i) =
        (xiOrderedSignedPrimeRVMCorrectionMultiplier i : ℂ) •
          HTGeometry.ellTwoCoordinateBasis RouteKSignedPrimeIndex i := by
      apply Subtype.ext
      funext j
      unfold xiOrderedSignedPrimeRVMCorrection
      rw [GaloisForLFunctions.HTGeometry.realSummableDiagonalOperator_apply]
      change
        (xiOrderedSignedPrimeRVMCorrectionMultiplier j : ℂ) *
            (HTGeometry.ellTwoCoordinateBasis RouteKSignedPrimeIndex i) j =
          (xiOrderedSignedPrimeRVMCorrectionMultiplier i : ℂ) *
            (HTGeometry.ellTwoCoordinateBasis RouteKSignedPrimeIndex i) j
      by_cases hji : j = i
      · subst j
        rfl
      · simp [HTGeometry.ellTwoCoordinateBasis_apply, lp.single_apply, hji]
    rw [hact]
    simp
  simp_rw [hdiag]
  have hsumC : Summable (fun i : RouteKSignedPrimeIndex =>
      (xiOrderedSignedPrimeRVMCorrectionMultiplier i : ℂ)) := by
    apply Summable.of_norm
    simpa [Complex.norm_real, Real.norm_eq_abs] using
      summable_abs_xiOrderedSignedPrimeRVMCorrectionMultiplier
  have hinl : Summable ((fun i : RouteKSignedPrimeIndex =>
      (xiOrderedSignedPrimeRVMCorrectionMultiplier i : ℂ)) ∘ Sum.inl) :=
    hsumC.comp_injective Sum.inl_injective
  have hinr : Summable ((fun i : RouteKSignedPrimeIndex =>
      (xiOrderedSignedPrimeRVMCorrectionMultiplier i : ℂ)) ∘ Sum.inr) :=
    hsumC.comp_injective Sum.inr_injective
  rw [Summable.tsum_sum hinl hinr]
  have hpair : ∀ p : Nat.Primes,
      (xiOrderedSignedPrimeRVMCorrectionMultiplier (Sum.inr p) : ℂ) =
        -(xiOrderedSignedPrimeRVMCorrectionMultiplier (Sum.inl p) : ℂ) := by
    intro p
    simp [xiOrderedSignedPrimeRVMCorrectionMultiplier]
  calc
    (∑' p : Nat.Primes,
        (xiOrderedSignedPrimeRVMCorrectionMultiplier (Sum.inl p) : ℂ)) +
        ∑' p : Nat.Primes,
          (xiOrderedSignedPrimeRVMCorrectionMultiplier (Sum.inr p) : ℂ) =
      (∑' p : Nat.Primes,
        (xiOrderedSignedPrimeRVMCorrectionMultiplier (Sum.inl p) : ℂ)) +
        ∑' p : Nat.Primes,
          -(xiOrderedSignedPrimeRVMCorrectionMultiplier (Sum.inl p) : ℂ) := by
        congr 1
        exact tsum_congr hpair
    _ = 0 := by rw [tsum_neg]; exact add_neg_cancel _

/-- The literal relative difference between ordered Xi data and its RVM skeleton
also has exactly zero ordinary trace. -/
theorem opTrace_xiOrderedSignedPrimeOperator_sub_routeKSignedPrimeRVMOperator_eq_zero :
    ContinuousLinearMap.opTrace
        (xiOrderedSignedPrimeOperator - routeKSignedPrimeRVMOperator) = 0 := by
  rw [xiOrderedSignedPrimeOperator_sub_routeKSignedPrimeRVMOperator]
  exact opTrace_xiOrderedSignedPrimeRVMCorrection_eq_zero

/-- Closed no-go: the concrete relative-completion trace cannot equal a unit
escape charge. -/
theorem opTrace_xiOrderedSignedPrimeOperator_sub_routeKSignedPrimeRVMOperator_ne_one :
    ContinuousLinearMap.opTrace
        (xiOrderedSignedPrimeOperator - routeKSignedPrimeRVMOperator) ≠ 1 := by
  rw [opTrace_xiOrderedSignedPrimeOperator_sub_routeKSignedPrimeRVMOperator_eq_zero]
  exact zero_ne_one

end

end RHTower
