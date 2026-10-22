import GaloisForLFunctions.HTGeometry.Critical.Schur.SourceCoordinates
import GaloisForLFunctions.HTGeometry.LocalizationAtPrimeDivisorDVR
import GaloisForLFunctions.HTGeometry.PrimeDivisorOrder
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-!
# The actual rectangular-Schur prime divisor

In the Schur-coordinate presentation of the actual source field, the ramification polynomial is
irreducible.  Hence it cuts out a height-one prime divisor.  Its local ring is a DVR and the Schur
polynomial itself is a uniformizer, so its divisorial order is exactly one.  This is the reduced
codimension-one source divisor used by the later inertia calculation.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open IsDiscreteValuationRing

set_option synthInstance.maxHeartbeats 100000

/-- Coordinate ring of the actual critical source in Schur coordinates. -/
abbrev criticalSchurSourceRing (K : Type*) [Field K] (m n : ℕ) :=
  MvPolynomial (Fin (m + n - 1 + 1)) K

/-- Principal ideal of the actual rectangular-Schur ramification polynomial. -/
noncomputable def criticalSchurRamificationIdeal
    (K : Type*) [Field K] (m n : ℕ) : Ideal (criticalSchurSourceRing K m n) :=
  Ideal.span {criticalSourceSchurRamificationPolynomial K m n}

theorem criticalSchurRamificationIdeal_isPrime
    (K : Type*) [Field K] {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    (criticalSchurRamificationIdeal K m n).IsPrime := by
  classical
  rw [criticalSchurRamificationIdeal]
  exact (Ideal.span_singleton_prime
    (irreducible_criticalSourceSchurRamificationPolynomial K hm hn).ne_zero).mpr
      (irreducible_criticalSourceSchurRamificationPolynomial K hm hn).prime

theorem criticalSchurRamificationIdeal_height
    (K : Type*) [Field K] {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    (criticalSchurRamificationIdeal K m n).height = 1 := by
  classical
  rw [criticalSchurRamificationIdeal]
  let p := criticalSourceSchurRamificationPolynomial K m n
  have hp := irreducible_criticalSourceSchurRamificationPolynomial K hm hn
  exact Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_of_ne_zero hp.ne_zero) hp.not_isUnit

/-- The actual rectangular-Schur divisor in the rational source presentation. -/
noncomputable def criticalSchurPrimeDivisor
    (K : Type*) [Field K] {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    PrimeDivisor (criticalSchurSourceRing K m n) :=
  ⟨criticalSchurRamificationIdeal K m n,
    criticalSchurRamificationIdeal_isPrime K hm hn,
    criticalSchurRamificationIdeal_height K hm hn⟩

@[simp] theorem criticalSchurPrimeDivisor_val
    (K : Type*) [Field K] {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    (criticalSchurPrimeDivisor K hm hn).1 = criticalSchurRamificationIdeal K m n :=
  rfl

/-- The Schur polynomial maps to a uniformizer in the local ring at its divisor. -/
theorem irreducible_algebraMap_criticalSourceSchurRamificationPolynomial
    (K : Type*) [Field K] {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    Irreducible
      (algebraMap (criticalSchurSourceRing K m n)
        (Localization.AtPrime (criticalSchurPrimeDivisor K hm hn).1)
        (criticalSourceSchurRamificationPolynomial K m n)) := by
  classical
  refine (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr ?_
  have h := IsLocalization.AtPrime.map_eq_maximalIdeal
    (criticalSchurPrimeDivisor K hm hn).1
    (Localization.AtPrime (criticalSchurPrimeDivisor K hm hn).1)
  refine h.symm.trans ?_
  show Ideal.map
      (algebraMap (criticalSchurSourceRing K m n)
        (Localization.AtPrime (criticalSchurPrimeDivisor K hm hn).1))
      (criticalSchurRamificationIdeal K m n) = _
  rw [criticalSchurRamificationIdeal, Ideal.map_span, Set.image_singleton]

/-- **The actual rectangular-Schur divisor is reduced:** its defining polynomial has order one at
its own generic point. -/
theorem orderAt_criticalSchurPrimeDivisor_ramificationPolynomial
    (K : Type*) [Field K] {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    orderAt (criticalSchurPrimeDivisor K hm hn)
      (criticalSourceSchurRamificationPolynomial K m n) = 1 :=
  addVal_uniformizer
    (irreducible_algebraMap_criticalSourceSchurRamificationPolynomial K hm hn)

end

end GaloisForLFunctions.HTGeometry
