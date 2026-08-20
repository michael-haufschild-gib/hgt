/-
# Chen--Gupta--Li class-I dyadic detector block

Literal `c_n χ(n)n^{it}` coefficient vector on one source dyadic block,
connected to the existing character large-value matrix.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiCharacterLargeValues
import GaloisForLFunctions.RHTower.ChenGuptaLiTailCoefficientBounds

namespace RHTower

noncomputable section

/-- The unscaled source coefficient vector on the dyadic interval
`N + {1, …, N}`. -/
def cglClassIDyadicDetectorCoefficients (X N : ℕ) :
    EuclideanSpace ℂ (Fin N) :=
  WithLp.toLp 2 (fun j : Fin N =>
    (zeroDetectionMobiusCoefficient X (N + j.1 + 1) : ℂ))

/-- The literal class-I detector polynomial in the existing character-row
coordinates. -/
def cglClassIDyadicDetectorPolynomial (X N q : ℕ)
    (w : CGLCharacterDyadicRowData q) : ℂ :=
  cglCharacterDyadicPolynomial N q w (cglClassIDyadicDetectorCoefficients X N)

/-- Expansion of the class-I block as the source's dyadic coefficient sum. -/
theorem cglClassIDyadicDetectorPolynomial_expand (X N q : ℕ)
    (w : CGLCharacterDyadicRowData q) :
    cglClassIDyadicDetectorPolynomial X N q w =
      ∑ j, (zeroDetectionMobiusCoefficient X (N + j.1 + 1) : ℂ) *
        w.character (cglCharacterDyadicIndex N j) * cglCharacterDyadicPhase N w.time j := by
  unfold cglClassIDyadicDetectorPolynomial cglCharacterDyadicPolynomial
  simp only [cglClassIDyadicDetectorCoefficients, cglCharacterDyadicIndex]

/-- Each actual class-I detector coefficient is controlled by its literal
divisor count. -/
theorem norm_cglClassIDyadicDetectorCoefficient_le_divisors (X N : ℕ)
    (j : Fin N) :
    ‖(cglClassIDyadicDetectorCoefficients X N) j‖ ≤
      ((N + j.1 + 1).divisors.card : ℝ) := by
  simpa only [cglClassIDyadicDetectorCoefficients] using
    norm_zeroDetectionMobiusCoefficient_le_card_divisors X (N + j.1 + 1)

end

end RHTower
