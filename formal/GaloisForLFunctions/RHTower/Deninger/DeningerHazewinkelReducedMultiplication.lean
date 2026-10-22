import GaloisForLFunctions.RHTower.Deninger.DeningerKroneckerFieldStage
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Nilpotent.Lemmas

/-!
# Corrected Hazewinkel multiplication over reduced rings

The field-valued Kronecker theorem descends through every prime quotient.  It
shows, over an arbitrary commutative ring, that every corrected-size Hankel
minor of a Witt product is nilpotent.  Reducedness then gives the exact
corrected multiplicative stage bound.

This separates the unconditional reduced-ring theorem from the genuinely
stronger arbitrary-ring ideal-containment problem.  Nilpotents are not silently
discarded: their precise residue after primewise descent is recorded.
-/

namespace RHTower
noncomputable section

/-- If two big Witt vectors have Hankel stages `n` and `m`, then every output
minor at the corrected resultant bound is nilpotent over any commutative ring.
-/
theorem deninger_hankelRankLT_mul_corrected_minor_isNilpotent
    {A : Type*} [CommRing A] {n m : ℕ}
    {u v : DeningerBigWittAdditive A}
    (hu : DeningerBigWittHankelRankLT (n + 1) u)
    (hv : DeningerBigWittHankelRankLT (m + 1) v)
    (rows cols : Fin (deningerCorrectedWittMulStageBound n m + 1) → ℕ) :
    IsNilpotent
      (((deningerBigWittHankel (deningerBigWittMul u v)).submatrix rows cols).det) := by
  rw [nilpotent_iff_mem_prime]
  intro p hp
  letI : p.IsPrime := hp
  let D := A ⧸ p
  let K := FractionRing D
  let q : A →+* D := Ideal.Quotient.mk p
  let ι : D →+* K := algebraMap D K
  let f : A →+* K := ι.comp q
  have huK : DeningerBigWittHankelRankLT (n + 1) (deningerBigWittMap f u) :=
    hu.map f
  have hvK : DeningerBigWittHankelRankLT (m + 1) (deningerBigWittMap f v) :=
    hv.map f
  have hout := deningerField_hankelRankLT_mul_corrected huK hvK
  have hout' : DeningerBigWittHankelRankLT
      (deningerCorrectedWittMulStageBound n m + 1)
      (deningerBigWittMap f (deningerBigWittMul u v)) := by
    rw [deningerBigWittMul_natural]
    exact hout
  have hdet := hout' rows cols
  have hmapped : f
      (((deningerBigWittHankel (deningerBigWittMul u v)).submatrix rows cols).det) = 0 := by
    rw [f.map_det]
    have heq : f.mapMatrix
          ((deningerBigWittHankel (deningerBigWittMul u v)).submatrix rows cols) =
        (deningerBigWittHankel
          (deningerBigWittMap f (deningerBigWittMul u v))).submatrix rows cols := by
      ext i j
      simp only [Matrix.submatrix_apply, deningerBigWittHankel_map]
      rfl
    rw [heq]
    exact hdet
  have hquot : q
      (((deningerBigWittHankel (deningerBigWittMul u v)).submatrix rows cols).det) = 0 := by
    apply (IsFractionRing.injective D K)
    simpa [f, ι] using hmapped
  exact Ideal.Quotient.eq_zero_iff_mem.mp hquot

/-- Corrected Hazewinkel multiplicative closure over every reduced commutative
ring. -/
theorem deningerReduced_hankelRankLT_mul_corrected
    {A : Type*} [CommRing A] [IsReduced A] {n m : ℕ}
    {u v : DeningerBigWittAdditive A}
    (hu : DeningerBigWittHankelRankLT (n + 1) u)
    (hv : DeningerBigWittHankelRankLT (m + 1) v) :
    DeningerBigWittHankelRankLT
      (deningerCorrectedWittMulStageBound n m + 1)
      (deningerBigWittMul u v) := by
  intro rows cols
  exact (deninger_hankelRankLT_mul_corrected_minor_isNilpotent
    hu hv rows cols).eq_zero

end
end RHTower
