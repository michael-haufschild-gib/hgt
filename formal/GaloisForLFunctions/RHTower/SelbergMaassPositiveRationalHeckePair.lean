import GaloisForLFunctions.RHTower.SelbergMaassRationalTrace
import Mathlib.NumberTheory.HeckeRing.Defs

/-!
# Positive rational Hecke pair for principal Maass sources

The positive-determinant rational matrices, embedded in `GL(2, ℝ)`, form the
arithmetic correspondence monoid of a principal-congruence Maass source.
They contain the source group and commensurate it, hence form a genuine
Mathlib Hecke pair.  This supplies the exact double-coset carrier for the
already constructed rational finite traces.  It deliberately does not assert
that those traces factor through double cosets or preserve convolution; that
is the next source-attached finite-place theorem.
-/

namespace GaloisForLFunctions.RHTower

open Matrix SpecialLinearGroup GeneralLinearGroup Subgroup
open scoped MatrixGroups Pointwise

noncomputable section

/-- Positive-real rational matrices, viewed as a correspondence submonoid of
`GL(2, ℝ)`. -/
def positiveRationalGLRealImage : Submonoid (GL (Fin 2) ℝ) where
  carrier := {x | ∃ q : GL (Fin 2) ℚ,
    q.map (algebraMap ℚ ℝ) = x ∧ 0 < (q.map (algebraMap ℚ ℝ)).val.det}
  one_mem' := by
    refine ⟨1, ?_, ?_⟩
    · simp
    · norm_num
  mul_mem' := by
    rintro x y ⟨q, hq, hqpos⟩ ⟨r, hr, hrpos⟩
    refine ⟨q * r, ?_, rationalGL_map_det_mul_pos q r hqpos hrpos⟩
    rw [Matrix.GeneralLinearGroup.map_mul, hq, hr]

/-- Every principal-congruence source transformation belongs to the positive
rational correspondence monoid. -/
theorem principalCongruenceGL_le_positiveRationalGLRealImage (N : ℕ) :
    (principalCongruenceGL N).toSubmonoid ≤ positiveRationalGLRealImage := by
  intro x hx
  have hx' : x ∈ rationalConjugateGroup N (1 : GL (Fin 2) ℚ) := by
    simpa [rationalConjugateGroup, rationalPullbackConjugateGroup] using hx
  let x' : rationalConjugateGroup N (1 : GL (Fin 2) ℚ) := ⟨x, hx'⟩
  obtain ⟨q, hq, hqpos⟩ :=
    rationalConjugateGroup_exists_positive_rational_lift N (1 : GL (Fin 2) ℚ) x'
  exact ⟨q, hq, hqpos⟩

/-- Every positive rational correspondence commensurates the principal source
group. -/
theorem positiveRationalGLRealImage_le_commensurator_principalCongruenceGL (N : ℕ) :
    positiveRationalGLRealImage ≤
      (Subgroup.Commensurable.commensurator (principalCongruenceGL N)).toSubmonoid := by
  rintro x ⟨q, hq, hqpos⟩
  rw [← hq]
  exact rationalGL_mem_commensurator_principalCongruenceGL N q

/-- The principal Maass source and positive rational correspondence monoid are
a Hecke pair in Mathlib's exact sense. -/
theorem principalCongruenceGL_isHeckeTriple_positiveRational (N : ℕ) :
    IsHeckeTriple positiveRationalGLRealImage
      (principalCongruenceGL N) (principalCongruenceGL N) :=
  IsHeckeTriple.of_diagonal
    (principalCongruenceGL_le_positiveRationalGLRealImage N)
    (positiveRationalGLRealImage_le_commensurator_principalCongruenceGL N)

/-- A positive rational matrix supplies an element of the source Hecke-pair
monoid. -/
def positiveRationalHeckeElement (g : GL (Fin 2) ℚ)
    (hg : 0 < (g.map (algebraMap ℚ ℝ)).val.det) : positiveRationalGLRealImage :=
  ⟨g.map (algebraMap ℚ ℝ), g, rfl, hg⟩

end

end GaloisForLFunctions.RHTower
