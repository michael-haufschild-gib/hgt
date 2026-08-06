import GaloisForLFunctions.HTGeometry.MilnorWittGradedIso
import GaloisForLFunctions.HTGeometry.MilnorWittGradedNegative
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Milnor--Witt K-theory of an algebraically closed field

An algebraically closed field is quadratically closed: the polynomial `X² - a` has a root.  The
Milnor--Witt collapse over a quadratically closed field therefore applies verbatim, giving
`K_n^{MW}(F) ≅ K_n^M(F)` for `n ≥ 0`, `ℤ` in degree zero, `Fˣ` in degree one, and `ℤ/2` in every
negative degree.

* `GaloisForLFunctions.HTGeometry.isSquare_of_isAlgClosed` : every element is a square.
* `GaloisForLFunctions.HTGeometry.mwForgetEquivAlgClosed` : the forgetful isomorphism in every
  nonnegative degree.
* `GaloisForLFunctions.HTGeometry.mwForgetEquivZeroAlgClosed`,
  `GaloisForLFunctions.HTGeometry.mwForgetEquivOneAlgClosed` : degrees zero and one.
* `GaloisForLFunctions.HTGeometry.mwNegDegreeEquivAlgClosed` : the negative degrees.
-/

namespace GaloisForLFunctions.HTGeometry

section AlgClosed

variable {F : Type*} [Field F] [IsAlgClosed F]

/-- **An algebraically closed field is quadratically closed.** -/
theorem isSquare_of_isAlgClosed (x : F) : ∃ y : F, x = y * y := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq x (n := 2) (by norm_num)
  exact ⟨z, by rw [← hz]; ring⟩

/-- **`K_n^{MW}(F) ≅ K_n^M(F)` over an algebraically closed field**, for every `n ≥ 0`. -/
def mwForgetEquivAlgClosed (n : ℕ) : MilnorWittKDeg F (n : ℤ) ≃+ MilnorKDeg F n :=
  mwForgetEquiv isSquare_of_isAlgClosed n

/-- **`K_0^{MW}(F) ≅ ℤ` over an algebraically closed field**, by rank. -/
def mwForgetEquivZeroAlgClosed : MilnorWittKDeg F ((0 : ℕ) : ℤ) ≃+ ℤ :=
  mwForgetEquivZero isSquare_of_isAlgClosed

/-- **`K_1^{MW}(F) ≅ Fˣ` over an algebraically closed field.** -/
def mwForgetEquivOneAlgClosed : MilnorWittKDeg F ((1 : ℕ) : ℤ) ≃+ Additive Fˣ :=
  mwForgetEquivOne isSquare_of_isAlgClosed

/-- **`K_n^{MW}(F) ≅ ℤ/2` in every negative degree over an algebraically closed field.** -/
noncomputable def mwNegDegreeEquivAlgClosed {n : ℤ} (hn : n ≤ -1) :
    MilnorWittKDeg F n ≃+ ZMod 2 :=
  mwNegDegreeEquiv isSquare_of_isAlgClosed hn

end AlgClosed

end GaloisForLFunctions.HTGeometry
