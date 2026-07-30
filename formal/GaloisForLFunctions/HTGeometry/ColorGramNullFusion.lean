import GaloisForLFunctions.HTGeometry.ColorGramMinkowskiCone
import Mathlib.Analysis.Matrix.Order

/-!
# Independent null roots fuse to a timelike colour-Gram future

Two row-supported `3 × 2` complex events individually have rank-one, Lorentz-null Gram records.
This file proves that if their two-component roots are linearly independent, the sum of those
records is positive definite and therefore timelike.

This is the exact rank-two null-fusion property behind strict convexity of the
`H₂(ℂ)` positive cone. It does not prove that a physical event uses this cone as spacetime,
derive the roots from a source law, or establish gravity.
-/

open Matrix
open scoped ComplexOrder Matrix

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- Put two two-component roots into the first two colour rows. -/
def twoNullRootEvent (u v : Fin 2 → ℂ) : ColorEventMatrix :=
  fun i j =>
    Fin.cases (u j)
      (fun i' => Fin.cases (v j) (fun _ => 0) i') i

/-- The Gram record of two roots is the sum of their two individual null records. -/
theorem twoNullRootEvent_gram_eq_add
    (u v : Fin 2 → ℂ) :
    colorGramMatrix (twoNullRootEvent u v) =
      colorGramMatrix (singleColorEvent u) +
        colorGramMatrix (singleColorEvent v) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [colorGramMatrix, twoNullRootEvent, singleColorEvent,
      Matrix.mul_apply, Fin.sum_univ_succ]

/-- The first maximal minor is the alternating determinant of the two roots. -/
theorem twoNullRootEvent_minor01
    (u v : Fin 2 → ℂ) :
    colorMinor01 (twoNullRootEvent u v) =
      u 0 * v 1 - v 0 * u 1 := by
  change u 0 * v 1 - v 0 * u 1 = u 0 * v 1 - v 0 * u 1
  rfl

/-- The other two maximal minors vanish because the third colour row is zero. -/
theorem twoNullRootEvent_minor02
    (u v : Fin 2 → ℂ) :
    colorMinor02 (twoNullRootEvent u v) = 0 := by
  change u 0 * 0 - 0 * u 1 = 0
  ring

/-- The other two maximal minors vanish because the third colour row is zero. -/
theorem twoNullRootEvent_minor12
    (u v : Fin 2 → ℂ) :
    colorMinor12 (twoNullRootEvent u v) = 0 := by
  change v 0 * 0 - 0 * v 1 = 0
  ring

/-- Independent two-component roots have a strictly timelike combined Gram record. -/
theorem twoNullRootEvent_lorentzMassSq_pos
    (u v : Fin 2 → ℂ)
    (hindependent : u 0 * v 1 - v 0 * u 1 ≠ 0) :
    0 < colorGramLorentzMassSq (twoNullRootEvent u v) := by
  rw [colorGramLorentzMassSq_pos_iff]
  exact Or.inl <| by
    simpa [twoNullRootEvent_minor01] using hindependent

/--
Two independent Lorentz-null square roots fuse to a positive-definite future record.

Each summand is the Gram record of a one-row event and hence Lorentz-null. Independence of the
roots makes the combined `2 × 2` determinant strictly positive.
-/
theorem independent_nullRoot_gram_add_posDef
    (u v : Fin 2 → ℂ)
    (hindependent : u 0 * v 1 - v 0 * u 1 ≠ 0) :
    (colorGramMatrix (singleColorEvent u) +
      colorGramMatrix (singleColorEvent v)).PosDef := by
  let X := twoNullRootEvent u v
  have hGram :
      colorGramMatrix X =
        colorGramMatrix (singleColorEvent u) +
          colorGramMatrix (singleColorEvent v) :=
    twoNullRootEvent_gram_eq_add u v
  have hpsd :
      (colorGramMatrix (singleColorEvent u) +
        colorGramMatrix (singleColorEvent v)).PosSemidef := by
    rw [← hGram]
    exact colorGramMatrix_posSemidef X
  apply hpsd.posDef_iff_det_ne_zero.mpr
  rw [← hGram, colorGramMatrix_det]
  exact_mod_cast ne_of_gt
    (twoNullRootEvent_lorentzMassSq_pos u v hindependent)

end GaloisForLFunctions.HTGeometry
