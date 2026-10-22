import GaloisForLFunctions.RHTower.Deninger.DeningerHankelGlobalSecantPrime
import GaloisForLFunctions.RHTower.Deninger.DeningerHazewinkelPrimeReduction
import GaloisForLFunctions.RHTower.Deninger.DeningerHazewinkelLeadingLocalization
import GaloisForLFunctions.HTGeometry.MvPolynomialProjectiveChartPrime

/-!
# Integral Hazewinkel saturation from the homogeneous Hankel secant

The normalized Hazewinkel coefficient ring has zeroth moment `a₀ = 1`, whereas the generic
Hankel secant uses a homogeneous variable `a₀`.  This module constructs the exact projective
chart connecting them.  The homogeneous generic secant ideal is prime over `ℤ`, avoids `a₀`,
and therefore remains prime after setting `a₀` to one.  Its affine-chart image is proved
generator-for-generator to be the Hazewinkel ideal.

This repairs the exponent-descent gap in Hazewinkel's printed saturation argument without
dividing inside a restricted coefficient algebra.  Consequences include all-stage integral
primeness, exact leading-determinant saturation, reduced universal pair quotients, and corrected
finite-Hankel-rank multiplication over arbitrary commutative target rings, including rings with
nilpotents.
-/

namespace RHTower
noncomputable section

open MvPolynomial
open scoped BigOperators

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Reindex the generic zeroth moment as the distinguished projective coordinate. -/
def deningerNatHeadEquiv : ℕ ≃ Option ℕ where
  toFun
    | 0 => none
    | n + 1 => some n
  invFun
    | none => 0
    | some n => n + 1
  left_inv n := by cases n <;> rfl
  right_inv n := by cases n <;> rfl

@[simp] theorem deningerNatHeadEquiv_zero : deningerNatHeadEquiv 0 = none := rfl

@[simp] theorem deningerNatHeadEquiv_succ (n : ℕ) :
    deningerNatHeadEquiv (n + 1) = some n := rfl

/-- Homogeneous reindexing from generic moments to a head coordinate plus affine tail. -/
def deningerHankelProjectiveRename :
    MvPolynomial ℕ ℤ →+* MvPolynomial (Option ℕ) ℤ :=
  (MvPolynomial.renameEquiv ℤ deningerNatHeadEquiv).toRingEquiv.toRingHom

/-- Normalize a generic moment polynomial by reindexing and setting `a₀ = 1`. -/
def deningerHankelNormalize : MvPolynomial ℕ ℤ →+* MvPolynomial ℕ ℤ :=
  GaloisForLFunctions.optionHeadDehomogenize.comp deningerHankelProjectiveRename

@[simp] theorem deningerHankelNormalize_X (n : ℕ) :
    deningerHankelNormalize (MvPolynomial.X n) =
      deningerHazewinkelUniversalCoeff n := by
  cases n <;>
    simp [deningerHankelNormalize, deningerHankelProjectiveRename,
      deningerHazewinkelUniversalCoeff]

/-- Homogeneous projective closure of the rank-`n` generic Hankel secant. -/
def deningerHankelProjectiveIdeal (n : ℕ) :
    Ideal (MvPolynomial (Option ℕ) ℤ) :=
  Ideal.map deningerHankelProjectiveRename (deningerGenericHankelIdeal ℤ n)

/-- Reindexing preserves integral primeness of the homogeneous Hankel secant ideal. -/
theorem deningerHankelProjectiveIdeal_isPrime (n : ℕ) :
    (deningerHankelProjectiveIdeal n).IsPrime := by
  letI : (deningerGenericHankelIdeal ℤ n).IsPrime :=
    deningerGenericHankelIdeal_int_isPrime n
  apply Ideal.map_isPrime_of_surjective
  · exact (MvPolynomial.renameEquiv ℤ deningerNatHeadEquiv).surjective
  · intro P hP
    have hPzero : P = 0 := by
      apply (MvPolynomial.renameEquiv ℤ deningerNatHeadEquiv).injective
      exact RingHom.mem_ker.mp hP
    rw [hPzero]
    exact (deningerGenericHankelIdeal ℤ n).zero_mem

/-- The reindexed generic secant ideal remains homogeneous. -/
theorem deningerHankelProjectiveIdeal_isHomogeneous (n : ℕ) :
    (deningerHankelProjectiveIdeal n).IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Option ℕ) ℤ) := by
  rw [deningerHankelProjectiveIdeal, deningerGenericHankelIdeal,
    deningerMatrixMinorIdeal, Ideal.map_span]
  apply Ideal.homogeneous_span
  intro P hP
  obtain ⟨Q, ⟨rows, cols, rfl⟩, rfl⟩ := hP
  refine ⟨n + 1, ?_⟩
  simpa [deningerHankelProjectiveRename, MvPolynomial.renameEquiv_apply] using
    (deningerGenericHankelMinor_isHomogeneous ℤ n rows cols).rename_isHomogeneous

/-- At positive rank, the homogenizing coordinate survives on the projective secant. -/
theorem deningerHankelProjectiveIdeal_X_none_not_mem (n : ℕ) (hn : 0 < n) :
    MvPolynomial.X (none : Option ℕ) ∉ deningerHankelProjectiveIdeal n := by
  intro hX
  obtain ⟨P, hP, hPeq⟩ :=
    (Ideal.mem_map_iff_of_surjective deningerHankelProjectiveRename
      (MvPolynomial.renameEquiv ℤ deningerNatHeadEquiv).surjective).mp hX
  have hrenameX : deningerHankelProjectiveRename (MvPolynomial.X 0) =
      MvPolynomial.X (none : Option ℕ) := by
    simp [deningerHankelProjectiveRename, MvPolynomial.renameEquiv_apply]
  have hPX : P = MvPolynomial.X 0 := by
    apply (MvPolynomial.renameEquiv ℤ deningerNatHeadEquiv).injective
    exact hPeq.trans hrenameX.symm
  exact deningerGenericHankel_X_zero_not_mem n hn (hPX ▸ hP)

/-- The affine chart `a₀ = 1` of the homogeneous integral Hankel secant is prime. -/
theorem deningerHankelProjectiveAffineIdeal_isPrime (n : ℕ) (hn : 0 < n) :
    (Ideal.map GaloisForLFunctions.optionHeadDehomogenize
      (deningerHankelProjectiveIdeal n)).IsPrime :=
  GaloisForLFunctions.Ideal.IsPrime.map_optionHeadDehomogenize
    (deningerHankelProjectiveIdeal n) (deningerHankelProjectiveIdeal_isPrime n)
      (deningerHankelProjectiveIdeal_isHomogeneous n)
        (deningerHankelProjectiveIdeal_X_none_not_mem n hn)

/-- Normalization sends every generic Hankel minor to the corresponding Hazewinkel minor. -/
theorem deningerHankelNormalize_genericMinor
    (n : ℕ) (rows cols : Fin (n + 1) → ℕ) :
    deningerHankelNormalize
        (((deningerGenericMomentHankel ℤ).submatrix rows cols).det) =
      (deningerHazewinkelUniversalHankel.submatrix rows cols).det := by
  rw [deningerHankelNormalize.map_det]
  congr 1
  ext i j
  simp [Matrix.submatrix_apply, deningerGenericMomentHankel,
    deningerHazewinkelUniversalHankel]

/-- Generator-level identification of normalized generic and Hazewinkel Hankel ideals. -/
theorem deningerHankelNormalize_genericIdeal (n : ℕ) :
    Ideal.map deningerHankelNormalize (deningerGenericHankelIdeal ℤ n) =
      deningerHazewinkelIdeal n := by
  rw [deningerGenericHankelIdeal, deningerHazewinkelIdeal,
    deningerMatrixMinorIdeal, Ideal.map_span]
  congr 1
  ext P
  constructor
  · rintro ⟨Q, ⟨rows, cols, rfl⟩, rfl⟩
    exact ⟨rows, cols, deningerHankelNormalize_genericMinor n rows cols⟩
  · rintro ⟨rows, cols, rfl⟩
    exact ⟨((deningerGenericMomentHankel ℤ).submatrix rows cols).det,
      ⟨rows, cols, rfl⟩, deningerHankelNormalize_genericMinor n rows cols⟩

/-- The projective affine chart is exactly the normalized Hazewinkel ideal. -/
theorem deningerHankelProjectiveAffineIdeal_eq_hazewinkel (n : ℕ) :
    Ideal.map GaloisForLFunctions.optionHeadDehomogenize
        (deningerHankelProjectiveIdeal n) = deningerHazewinkelIdeal n := by
  rw [deningerHankelProjectiveIdeal, Ideal.map_map]
  exact deningerHankelNormalize_genericIdeal n

/-- **Integral Hazewinkel primeness.** Every positive normalized Hankel stage ideal is prime. -/
theorem deningerHazewinkelIdeal_isPrime (n : ℕ) (hn : 0 < n) :
    (deningerHazewinkelIdeal n).IsPrime := by
  rw [← deningerHankelProjectiveAffineIdeal_eq_hazewinkel n]
  exact deningerHankelProjectiveAffineIdeal_isPrime n hn

/-- **Exact saturation.** Multiplication by the leading determinant has no kernel modulo `Jₙ`. -/
theorem deningerHazewinkelIdeal_colon_leading_eq (n : ℕ) (hn : 0 < n) :
    (deningerHazewinkelIdeal n).colon
        (Ideal.span {deningerHazewinkelLeadingDeterminant n}) =
      deningerHazewinkelIdeal n := by
  ext P
  constructor
  · intro hP
    have hmul : P * deningerHazewinkelLeadingDeterminant n ∈
        deningerHazewinkelIdeal n :=
      Ideal.mem_colon_span_singleton.mp hP
    rcases (deningerHazewinkelIdeal_isPrime n hn).mem_or_mem hmul with hP | hD
    · exact hP
    · exact (deningerHazewinkelLeadingDeterminant_not_mem n hn hD).elim
  · intro hP
    apply Ideal.mem_colon_span_singleton.mpr
    exact (deningerHazewinkelIdeal n).mul_mem_right
      (deningerHazewinkelLeadingDeterminant n) hP

/-- Universal tensors of two positive Hazewinkel stages are reduced. -/
theorem deningerHazewinkelStageTensor_isReduced
    (n m : ℕ) (hn : 0 < n) (hm : 0 < m) :
    IsReduced (DeningerHazewinkelStageTensor n m) :=
  deningerHazewinkelStageTensor_isReduced_of_isPrime n m hn hm
    (deningerHazewinkelIdeal_isPrime n hn) (deningerHazewinkelIdeal_isPrime m hm)

/-- Universal pair quotients for two positive Hazewinkel stages are reduced. -/
theorem deningerHazewinkelPairQuotient_isReduced
    (n m : ℕ) (hn : 0 < n) (hm : 0 < m) :
    IsReduced (DeningerHazewinkelPairQuotient n m) :=
  deningerHazewinkelPairQuotient_isReduced_of_isPrime n m hn hm
    (deningerHazewinkelIdeal_isPrime n hn) (deningerHazewinkelIdeal_isPrime m hm)

/-- **Unconditional corrected finite-rank multiplication.** Canonical big-Witt multiplication
obeys the corrected Hazewinkel stage bound over every commutative ring, including targets with
nilpotents. -/
theorem deninger_hankelRankLT_mul_corrected
    {A : Type*} [CommRing A] {n m : ℕ}
    (hn : 0 < n) (hm : 0 < m)
    {u v : DeningerBigWittAdditive A}
    (hu : DeningerBigWittHankelRankLT (n + 1) u)
    (hv : DeningerBigWittHankelRankLT (m + 1) v) :
    DeningerBigWittHankelRankLT
      (deningerCorrectedWittMulStageBound n m + 1)
      (deningerBigWittMul u v) :=
  deninger_hankelRankLT_mul_corrected_of_hazewinkel_isPrime
    hn hm (deningerHazewinkelIdeal_isPrime n hn)
      (deningerHazewinkelIdeal_isPrime m hm) hu hv

end
end RHTower
