/-
# Chen--Gupta--Li Lemma 4.5 diagonal Poisson factor

Separates the all-equal row triples in CGL's cubic trace and identifies them
with the cube of the Lemma 4.4 Ramanujan/Poisson mass.  The proof handles the
empty packet directly and cancels the nonzero finite row count otherwise.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiLemma45FrequencySplit
import GaloisForLFunctions.RHTower.ChenGuptaLiHZeroTraceReality
import GaloisForLFunctions.RHTower.ChenGuptaLiWeightedCubicDiagonal

open Matrix
open scoped BigOperators FourierTransform

noncomputable section

namespace RHTower

/-- The one-coordinate Ramanujan/Poisson mass whose cube is CGL Lemma 4.5's
all-equal-row contribution. -/
def cglLemma45DiagonalPoissonMass
    (w : CGLRealSmoothBump) (N : CGLPositiveLength) (Q : CGLPositiveModulus) : ℂ :=
  ∑' ell : ℤ, cglRamanujanAdditiveSum Q (ell : ZMod Q.value) *
    ((cglAffineFourierScale N Q : ℂ) *
      𝓕 (fun u => w.toCGLSmoothBump.value u * w.toCGLSmoothBump.value u)
        (cglAffineFourierScale N Q * (ell : ℝ)))

/-- **CGL Lemma 4.5, all-equal-row factor.** The cubic diagonal is the row
count times the cube of the source's Lemma 4.4 Poisson mass. -/
theorem cglLemma45_cubicDiagonal_eq_card_mul_diagonalPoissonMass_cube
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (Q : CGLPositiveModulus) (R : ℕ)
    (rows : Fin R → CGLCharacterDyadicRowData Q.value) :
    cglCharacterDyadicWeightedGramCubicDiagonal N.value Q.value R
      (cglSmoothBumpDyadicWeight w.toCGLSmoothBump N) rows =
      (R : ℂ) * cglLemma45DiagonalPoissonMass w N Q ^ (3 : ℕ) := by
  by_cases hR : R = 0
  · subst R
    simp [cglCharacterDyadicWeightedGramCubicDiagonal_eq_card_mul_unitWeightMass_cube]
  · have hR0 : (R : ℂ) ≠ 0 := by
      exact_mod_cast hR
    have htraceMass :=
      cglCharacterDyadicWeighted_trace_self_mul_conjTranspose_eq_card_mul_unitWeightMass
        N.value Q.value R (cglSmoothBumpDyadicWeight w.toCGLSmoothBump N) rows
    have htracePoisson :
        (cglCharacterDyadicWeightedEvaluationMatrix N.value Q.value R
          (cglSmoothBumpDyadicWeight w.toCGLSmoothBump N) rows *
          (cglCharacterDyadicWeightedEvaluationMatrix N.value Q.value R
            (cglSmoothBumpDyadicWeight w.toCGLSmoothBump N) rows)ᴴ).trace =
          (R : ℂ) * cglLemma45DiagonalPoissonMass w N Q := by
      simpa only [cglLemma45DiagonalPoissonMass] using
        cglRealSmoothBumpDyadicWeighted_trace_self_mul_conjTranspose_eq_card_mul_ramanujanFourier
          w N Q R rows
    have hmass : (cglCharacterDyadicWeightedUnitWeightMass N.value Q.value
        (cglSmoothBumpDyadicWeight w.toCGLSmoothBump N) : ℂ) =
        cglLemma45DiagonalPoissonMass w N Q := by
      apply mul_left_cancel₀ hR0
      exact htraceMass.symm.trans htracePoisson
    rw [cglCharacterDyadicWeightedGramCubicDiagonal_eq_card_mul_unitWeightMass_cube, hmass]

/-- **CGL Lemma 4.5, exact diagonal/off-diagonal trace split.** The source
diagonal Poisson factor is separated from the literal non-all-equal cubic
trace, with no spacing or analytic premise. -/
theorem cglLemma45_cubicTrace_eq_diagonalPoisson_add_offDiagonal
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (Q : CGLPositiveModulus) (R : ℕ)
    (rows : Fin R → CGLCharacterDyadicRowData Q.value) :
    cglCharacterDyadicWeightedGramCubicTrace N.value Q.value R
      (cglSmoothBumpDyadicWeight w.toCGLSmoothBump N) rows =
      (R : ℂ) * cglLemma45DiagonalPoissonMass w N Q ^ (3 : ℕ) +
        cglCharacterDyadicWeightedGramCubicOffDiagonal N.value Q.value R
          (cglSmoothBumpDyadicWeight w.toCGLSmoothBump N) rows := by
  rw [cglCharacterDyadicWeightedGramCubicTrace_eq_diagonal_add_offDiagonal,
    cglLemma45_cubicDiagonal_eq_card_mul_diagonalPoissonMass_cube]

end RHTower
