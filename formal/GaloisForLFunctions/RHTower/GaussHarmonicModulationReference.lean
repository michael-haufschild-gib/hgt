import GaloisForLFunctions.RHTower.IndexedDiagonalWeakSchatten
import GaloisForLFunctions.RHTower.SchattenCriticalAsymptotic
import GaloisForLFunctions.RHTower.SuzukiDiagonalResolventInstantiation
import GaloisForLFunctions.RHTower.EulerSquarefreeDyadicAffineProjection
import GaloisForLFunctions.HTGeometry.CompactOperatorDiscreteSpectrum
import Mathlib.Analysis.Fourier.AddCircle

/-!
# Harmonic reference operator for the Gauss quasi-inner endpoint

This module transports the explicit harmonic diagonal `diag (1 / (n + 1))` to the circle through
the Fourier basis and the standard reindexing `ℤ ≃ ℕ`.  The resulting operator is the concrete
positive compact reference used by the weak-modulation route at the depth-one endpoint.  Its
approximation numbers and logarithmic residue are exact; no modulation comparison is asserted.
-/

namespace RHTower

open Filter Topology MeasureTheory ContinuousLinearMap GaloisForLFunctions.RHTower

noncomputable section

/-- The harmonic multiplier is antitone. -/
theorem harmonicMultiplier_antitone :
    ∀ {i j : ℕ}, i ≤ j → harmonicMultiplier j ≤ harmonicMultiplier i := by
  intro i j hij
  dsimp [harmonicMultiplier]
  gcongr

/-- Exact approximation numbers of the harmonic diagonal operator. -/
theorem approxNumber_harmonicDiagonalOperator (n : ℕ) :
    approxNumber harmonicDiagonalOperator n = harmonicMultiplier n := by
  let hbound : ∀ k, ‖(((harmonicMultiplier k : ℝ) : ℂ))‖ ≤ harmonicMultiplier 0 :=
    fun k => by
      simpa [Real.norm_eq_abs, abs_of_nonneg (harmonicMultiplier_nonneg k)] using
        harmonicMultiplier_antitone (Nat.zero_le k)
  have hop : harmonicDiagonalOperator =
      diagonalOperator (fun k => ((harmonicMultiplier k : ℝ) : ℂ)) hbound := by
    ext f k
    rfl
  rw [hop]
  exact approxNumber_diagonalOperator_eq harmonicMultiplier_nonneg
    harmonicMultiplier_antitone n

/-- Critical approximation-number asymptotic of the harmonic diagonal. -/
theorem tendsto_harmonicDiagonalOperator_approxNumber_mul_succ :
    Tendsto
      (fun n : ℕ => approxNumber harmonicDiagonalOperator n ^ (1 : ℝ) * ((n : ℝ) + 1))
      atTop (nhds 1) := by
  have hfun :
      (fun n : ℕ => approxNumber harmonicDiagonalOperator n ^ (1 : ℝ) * ((n : ℝ) + 1)) =
        fun _ : ℕ => (1 : ℝ) := by
    funext n
    rw [approxNumber_harmonicDiagonalOperator, Real.rpow_one]
    dsimp [harmonicMultiplier]
    field_simp
  rw [hfun]
  exact tendsto_const_nhds

/-- Fourier/reindexing unitary from the harmonic sequence model to the circle. -/
def gaussHarmonicReferenceUnitary :
    EllTwo ≃ₗᵢ[ℂ] Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) :=
  (lpReindexEquiv Equiv.intEquivNat.symm).trans
    (fourierBasis (T := (1 : ℝ))).repr.symm

/-- Positive harmonic reference on the circle. -/
def gaussHarmonicReference :
    Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) →L[ℂ]
      Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) :=
  unitaryPush gaussHarmonicReferenceUnitary harmonicDiagonalOperator

/-- Exact approximation-number law for the circle reference. -/
theorem approxNumber_gaussHarmonicReference (n : ℕ) :
    approxNumber gaussHarmonicReference n = 1 / ((n : ℝ) + 1) := by
  rw [gaussHarmonicReference, approxNumber_unitaryPush,
    approxNumber_harmonicDiagonalOperator]
  rfl

/-- The harmonic circle reference belongs to weak `S₁`. -/
theorem memWeakSchattenClass_gaussHarmonicReference :
    MemWeakSchattenClass 1 gaussHarmonicReference :=
  (memWeakSchattenClass_of_tendsto_mul_succ
    tendsto_harmonicDiagonalOperator_approxNumber_mul_succ).unitaryPush
      gaussHarmonicReferenceUnitary

/-- The harmonic circle reference has exact logarithmic residue one. -/
theorem hasSchattenLogResidue_gaussHarmonicReference :
    HasSchattenLogResidue 1 gaussHarmonicReference 1 :=
  (hasSchattenLogResidue_of_tendsto_mul_succ
    tendsto_harmonicDiagonalOperator_approxNumber_mul_succ).unitaryPush
      gaussHarmonicReferenceUnitary

/-- The harmonic circle reference is injective. -/
theorem gaussHarmonicReference_injective : Function.Injective gaussHarmonicReference := by
  intro x y hxy
  apply gaussHarmonicReferenceUnitary.symm.injective
  apply injective_harmonicDiagonalOperator
  have h := congrArg gaussHarmonicReferenceUnitary.symm hxy
  simpa [gaussHarmonicReference, unitaryPush] using h

/-- The harmonic circle reference is self-adjoint. -/
theorem gaussHarmonicReference_isSelfAdjoint : IsSelfAdjoint gaussHarmonicReference := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  change inner ℂ
      (gaussHarmonicReferenceUnitary
        (harmonicDiagonalOperator (gaussHarmonicReferenceUnitary.symm x))) y =
    inner ℂ x
      (gaussHarmonicReferenceUnitary
        (harmonicDiagonalOperator (gaussHarmonicReferenceUnitary.symm y)))
  calc
    _ = inner ℂ (harmonicDiagonalOperator (gaussHarmonicReferenceUnitary.symm x))
        (gaussHarmonicReferenceUnitary.symm y) := by
          rw [← gaussHarmonicReferenceUnitary.inner_map_map]
          simp
    _ = inner ℂ (gaussHarmonicReferenceUnitary.symm x)
        (harmonicDiagonalOperator (gaussHarmonicReferenceUnitary.symm y)) := by
          exact ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
            isSelfAdjoint_harmonicDiagonalOperator _ _
    _ = _ := by
          rw [← gaussHarmonicReferenceUnitary.inner_map_map]
          simp

/-- The harmonic circle reference has dense range. -/
theorem gaussHarmonicReference_denseRange : DenseRange gaussHarmonicReference :=
  GaloisForLFunctions.HTGeometry.denseRange_of_isSelfAdjoint_of_injective
    gaussHarmonicReference_isSelfAdjoint gaussHarmonicReference_injective

/-- The harmonic circle reference is nonnegative in the bounded-operator order. -/
theorem gaussHarmonicReference_nonneg : (0 : _ →L[ℂ] _) ≤ gaussHarmonicReference := by
  rw [ContinuousLinearMap.le_def, sub_zero]
  have hbase : harmonicDiagonalOperator.IsPositive :=
    isPositive_diagonalOperator_ofReal harmonicMultiplier norm_harmonicMultiplier_le
      harmonicMultiplier_nonneg
  constructor
  · intro x y
    change inner ℂ
        (gaussHarmonicReferenceUnitary
          (harmonicDiagonalOperator (gaussHarmonicReferenceUnitary.symm x))) y =
      inner ℂ x
        (gaussHarmonicReferenceUnitary
          (harmonicDiagonalOperator (gaussHarmonicReferenceUnitary.symm y)))
    calc
      _ = inner ℂ
          (harmonicDiagonalOperator (gaussHarmonicReferenceUnitary.symm x))
          (gaussHarmonicReferenceUnitary.symm y) := by
            rw [← gaussHarmonicReferenceUnitary.inner_map_map]
            simp
      _ = inner ℂ (gaussHarmonicReferenceUnitary.symm x)
          (harmonicDiagonalOperator (gaussHarmonicReferenceUnitary.symm y)) :=
            hbase.1 _ _
      _ = _ := by
            rw [← gaussHarmonicReferenceUnitary.inner_map_map]
            simp
  · intro x
    change 0 ≤ (inner ℂ
      (gaussHarmonicReferenceUnitary
        (harmonicDiagonalOperator (gaussHarmonicReferenceUnitary.symm x))) x).re
    have hi : inner ℂ
        (gaussHarmonicReferenceUnitary
          (harmonicDiagonalOperator (gaussHarmonicReferenceUnitary.symm x))) x =
        inner ℂ (harmonicDiagonalOperator (gaussHarmonicReferenceUnitary.symm x))
          (gaussHarmonicReferenceUnitary.symm x) := by
      simpa using gaussHarmonicReferenceUnitary.inner_map_map
        (harmonicDiagonalOperator (gaussHarmonicReferenceUnitary.symm x))
        (gaussHarmonicReferenceUnitary.symm x)
    rw [hi]
    exact hbase.2 (gaussHarmonicReferenceUnitary.symm x)

/-- The harmonic circle reference is compact. -/
theorem isCompactOperator_gaussHarmonicReference :
    IsCompactOperator gaussHarmonicReference :=
  IsCompactOperator.unitaryPush gaussHarmonicReferenceUnitary harmonicDiagonalOperator
    isCompactOperator_harmonicDiagonalOperator

end

end RHTower
