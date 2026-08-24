import GaloisForLFunctions.RHTower.XiOrderedPositiveRVMRelocation
import GaloisForLFunctions.RHTower.PrimeIndexedRVMSignedSkeleton
import GaloisForLFunctions.HTGeometry.CountableSeparableInteractionOperatorLaw

open scoped BigOperators InnerProductSpace Nat.Prime

namespace RHTower

noncomputable section

def xiOrderedPrimeReciprocal (p : Nat.Primes) : ℝ :=
  (xiOrderedPositiveOrdinate (routeKPrimeRVMIndex p))⁻¹

theorem xiOrderedPrimeReciprocal_pos (p : Nat.Primes) :
    0 < xiOrderedPrimeReciprocal p := by
  exact inv_pos.mpr (xiOrderedPositiveOrdinate_pos _)

theorem xiOrderedPrimeReciprocal_le_zero (p : Nat.Primes) :
    xiOrderedPrimeReciprocal p ≤ xiOrderedPrimeReciprocal (nthPrimeEquiv 0) := by
  rw [xiOrderedPrimeReciprocal, xiOrderedPrimeReciprocal,
    show routeKPrimeRVMIndex (nthPrimeEquiv 0) = 0 by
      simpa [nthPrimeEquiv] using routeKPrimeRVMIndex_nthPrimeSubtype 0]
  exact (inv_le_inv₀ (xiOrderedPositiveOrdinate_pos _)
    (xiOrderedPositiveOrdinate_pos _)).2
      (xiOrderedPositiveOrdinate_monotone (Nat.zero_le _))

def xiOrderedSignedPrimeMultiplier : RouteKSignedPrimeIndex → ℂ
  | Sum.inl p => (xiOrderedPrimeReciprocal p : ℂ)
  | Sum.inr p => -(xiOrderedPrimeReciprocal p : ℂ)

theorem norm_xiOrderedSignedPrimeMultiplier_le_zero
    (i : RouteKSignedPrimeIndex) :
    ‖xiOrderedSignedPrimeMultiplier i‖ ≤
      xiOrderedPrimeReciprocal (nthPrimeEquiv 0) := by
  cases i with
  | inl p =>
      simpa [xiOrderedSignedPrimeMultiplier, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (xiOrderedPrimeReciprocal_pos p)] using
        xiOrderedPrimeReciprocal_le_zero p
  | inr p =>
      simpa [xiOrderedSignedPrimeMultiplier, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (xiOrderedPrimeReciprocal_pos p)] using
        xiOrderedPrimeReciprocal_le_zero p

/-- Target-fed, multiplicity-ordered signed reciprocal-zero operator on marked prime sectors. -/
def xiOrderedSignedPrimeOperator :
    RouteKSignedPrimeHilbert →L[ℂ] RouteKSignedPrimeHilbert :=
  HTGeometry.ellTwoDiagonal xiOrderedSignedPrimeMultiplier
    norm_xiOrderedSignedPrimeMultiplier_le_zero

theorem xiOrderedSignedPrimeOperator_basis_inl (p : Nat.Primes) :
    xiOrderedSignedPrimeOperator
        (HTGeometry.ellTwoCoordinateBasis
          RouteKSignedPrimeIndex (Sum.inl p)) =
      (xiOrderedPrimeReciprocal p : ℂ) •
        HTGeometry.ellTwoCoordinateBasis
          RouteKSignedPrimeIndex (Sum.inl p) := by
  simpa [xiOrderedSignedPrimeOperator, xiOrderedSignedPrimeMultiplier] using
    HTGeometry.ellTwoDiagonal_coordinateBasis
      xiOrderedSignedPrimeMultiplier norm_xiOrderedSignedPrimeMultiplier_le_zero
      (Sum.inl p)

theorem xiOrderedSignedPrimeOperator_basis_inr (p : Nat.Primes) :
    xiOrderedSignedPrimeOperator
        (HTGeometry.ellTwoCoordinateBasis
          RouteKSignedPrimeIndex (Sum.inr p)) =
      -(xiOrderedPrimeReciprocal p : ℂ) •
        HTGeometry.ellTwoCoordinateBasis
          RouteKSignedPrimeIndex (Sum.inr p) := by
  simpa [xiOrderedSignedPrimeOperator, xiOrderedSignedPrimeMultiplier] using
    HTGeometry.ellTwoDiagonal_coordinateBasis
      xiOrderedSignedPrimeMultiplier norm_xiOrderedSignedPrimeMultiplier_le_zero
      (Sum.inr p)

theorem xiOrderedSignedPrimeOperator_selfAdjoint :
    ContinuousLinearMap.adjoint xiOrderedSignedPrimeOperator =
      xiOrderedSignedPrimeOperator := by
  rw [xiOrderedSignedPrimeOperator,
    HTGeometry.adjoint_ellTwoDiagonal]
  ext f i
  rw [HTGeometry.ellTwoDiagonal_apply,
    HTGeometry.ellTwoDiagonal_apply]
  cases i <;> simp [xiOrderedSignedPrimeMultiplier]

def xiOrderedSignedPrimeRVMCorrectionMultiplier :
    RouteKSignedPrimeIndex → ℝ
  | Sum.inl p => xiOrderedPrimeReciprocal p - routeKPrimeRVMReciprocal p
  | Sum.inr p => -(xiOrderedPrimeReciprocal p - routeKPrimeRVMReciprocal p)

theorem summable_abs_xiOrderedPrimeReciprocal_sub_routeKPrimeRVMReciprocal :
    Summable (fun p : Nat.Primes =>
      |xiOrderedPrimeReciprocal p - routeKPrimeRVMReciprocal p|) := by
  apply nthPrimeEquiv.summable_iff.mp
  simpa [Function.comp_def, xiOrderedPrimeReciprocal, routeKPrimeRVMReciprocal,
    nthPrimeEquiv, routeKPrimeRVMIndex_nthPrimeSubtype] using
    summable_abs_xiOrderedPositiveOrdinate_inv_sub_routeKRVMQuantile_inv

theorem summable_abs_xiOrderedSignedPrimeRVMCorrectionMultiplier :
    Summable (fun i : RouteKSignedPrimeIndex =>
      |xiOrderedSignedPrimeRVMCorrectionMultiplier i|) := by
  apply Summable.sum
  · simpa [Function.comp_def, xiOrderedSignedPrimeRVMCorrectionMultiplier] using
      summable_abs_xiOrderedPrimeReciprocal_sub_routeKPrimeRVMReciprocal
  · simpa [Function.comp_def, xiOrderedSignedPrimeRVMCorrectionMultiplier,
      abs_sub_comm] using
      summable_abs_xiOrderedPrimeReciprocal_sub_routeKPrimeRVMReciprocal

/-- Trace-class diagonal relocating smooth RVM atoms to actual ordered Xi ordinates. -/
def xiOrderedSignedPrimeRVMCorrection :
    RouteKSignedPrimeHilbert →L[ℂ] RouteKSignedPrimeHilbert :=
  GaloisForLFunctions.HTGeometry.realSummableDiagonalOperator
    xiOrderedSignedPrimeRVMCorrectionMultiplier
    summable_abs_xiOrderedSignedPrimeRVMCorrectionMultiplier

theorem xiOrderedSignedPrimeRVMCorrection_memSchattenClass_one :
    MemSchattenClass 1 xiOrderedSignedPrimeRVMCorrection := by
  exact GaloisForLFunctions.HTGeometry.realSummableDiagonalOperator_memSchattenClass_one
      xiOrderedSignedPrimeRVMCorrectionMultiplier
      summable_abs_xiOrderedSignedPrimeRVMCorrectionMultiplier

theorem xiOrderedSignedPrimeRVMCorrection_isSelfAdjoint :
    IsSelfAdjoint xiOrderedSignedPrimeRVMCorrection := by
  exact GaloisForLFunctions.HTGeometry.realSummableDiagonalOperator_isSelfAdjoint
      xiOrderedSignedPrimeRVMCorrectionMultiplier
      summable_abs_xiOrderedSignedPrimeRVMCorrectionMultiplier

theorem xiOrderedSignedPrimeOperator_sub_routeKSignedPrimeRVMOperator :
    xiOrderedSignedPrimeOperator - routeKSignedPrimeRVMOperator =
      xiOrderedSignedPrimeRVMCorrection := by
  apply ContinuousLinearMap.ext
  intro f
  rw [sub_apply]
  apply Subtype.ext
  funext i
  have hA : xiOrderedSignedPrimeOperator f i =
      xiOrderedSignedPrimeMultiplier i * f i := by
    rw [xiOrderedSignedPrimeOperator, HTGeometry.ellTwoDiagonal_apply]
  have hQ : routeKSignedPrimeRVMOperator f i =
      routeKSignedPrimeRVMMultiplier i * f i := by
    rw [routeKSignedPrimeRVMOperator, HTGeometry.ellTwoDiagonal_apply]
  have hK : xiOrderedSignedPrimeRVMCorrection f i =
      (xiOrderedSignedPrimeRVMCorrectionMultiplier i : ℂ) * f i := by
    exact GaloisForLFunctions.HTGeometry.realSummableDiagonalOperator_apply
      xiOrderedSignedPrimeRVMCorrectionMultiplier
      summable_abs_xiOrderedSignedPrimeRVMCorrectionMultiplier f i
  change xiOrderedSignedPrimeOperator f i - routeKSignedPrimeRVMOperator f i =
    xiOrderedSignedPrimeRVMCorrection f i
  rw [hA, hQ, hK]
  cases i <;>
    simp [xiOrderedSignedPrimeMultiplier, routeKSignedPrimeRVMMultiplier,
      xiOrderedSignedPrimeRVMCorrectionMultiplier] <;> ring

/-- Exact prime-indexed trace-class reciprocal-divisor relocation. -/
theorem xiOrderedSignedPrimeOperator_sub_routeKSignedPrimeRVMOperator_memSchattenClass_one :
    MemSchattenClass 1
      (xiOrderedSignedPrimeOperator - routeKSignedPrimeRVMOperator) := by
  rw [xiOrderedSignedPrimeOperator_sub_routeKSignedPrimeRVMOperator]
  exact xiOrderedSignedPrimeRVMCorrection_memSchattenClass_one

end

end RHTower
