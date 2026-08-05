import GaloisForLFunctions.HTGeometry.MovingEvenCanonicalSurgery

/-!
# Separated surgery pole families exist

The even canonical surgery inserts, for each parameter, the parameter itself and its sign
conjugate.  Separation of the resulting `2k` poles is assumed and never produced.

It is exactly two conditions on the parameters: they are distinct, and no parameter is the sign
conjugate of another.  A half-plane condition supplies the second one outright — sign conjugation
reverses the real part, so a family with strictly positive real parts is automatically disjoint
from its own sign conjugate.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex

/-- **A distinct family in the right half plane has separated surgery poles.**  Sign conjugation
reverses the real part, so the two halves of the pole packet cannot meet. -/
theorem evenSurgeryPoleSeparated_of_injective_of_re_pos {k : ℕ} {t : Fin k → ℂ}
    (hinj : Function.Injective t) (hre : ∀ i, 0 < (t i).re) :
    EvenSurgeryPoleSeparated t := by
  have hsum : Function.Injective (Sum.elim t (fun i => -star (t i))) := by
    rintro (a | a) (b | b) hab
    · exact congrArg Sum.inl (hinj hab)
    · exfalso
      have hre' : (t a).re = -(t b).re := by
        have := congrArg Complex.re hab
        simpa [Complex.neg_re, Complex.star_def, Complex.conj_re] using this
      have := hre a
      have := hre b
      linarith [hre a, hre b, hre'.symm ▸ hre a]
    · exfalso
      have hre' : -(t a).re = (t b).re := by
        have := congrArg Complex.re hab
        simpa [Complex.neg_re, Complex.star_def, Complex.conj_re] using this
      linarith [hre a, hre b]
    · refine congrArg Sum.inr (hinj ?_)
      have : star (t a) = star (t b) := by
        have := hab
        simpa using neg_injective this
      simpa using congrArg star this
  have hcomp : movingEvenCanonicalSurgeryPoleFamily t
      = (Sum.elim t (fun i => -star (t i))) ∘ finSumFinEquiv.symm := rfl
  rw [EvenSurgeryPoleSeparated, hcomp]
  exact hsum.comp finSumFinEquiv.symm.injective

end GaloisForLFunctions.HTGeometry
