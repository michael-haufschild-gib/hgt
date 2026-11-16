import GaloisForLFunctions.HilbertMetric.Spectral.ClippedThreshold
import GaloisForLFunctions.HeckeKreinToeplitz.HyperbolicPairsAndTheIndexFormula

/-!
# Clipped energy under a hyperbolic character pair

A character pair vanishes on the kernel of one evaluation functional, so its
positive index is at most one. The clipped threshold inequality therefore pays
only `c²` for adding the pair to an arbitrary Gram matrix. Neither the character
nor its weight needs a unitarity or sign condition.
-/

open Matrix
open scoped ComplexOrder
open GaloisForLFunctions.HTGeometry
namespace GaloisForLFunctions.HeckeKreinToeplitz
open HilbertMetric.Clipped
noncomputable section
variable {G ι κ : Type*} [Group G] [Fintype ι] [DecidableEq ι] [Fintype κ]

/-- A hyperbolic pair carries at most one positive square as well as one negative square. -/
theorem pairKernel_positive_index_le_one (χ : G →* ℂ) (ω : ℂ) (x : ι → G) :
    RiemannGaussian.HermitianRankTrace.posIndex
      (gram_isHermitian (isHermKernel_pairKernel χ ω) x) ≤ 1 := by
  have hi := ArithmeticCastelnuovoSeveri.negIndex_le_card_of_nonneg_on_ker
    (-(gram (pairKernel χ ω) x)) (fun _ : Fin 1 => charEval χ x) (fun c hc => by
      rw [hermQuad_neg, hermQuad_gram_pairKernel, hc 0]
      simp)
  simp only [hermNegIndex, neg_neg, Fintype.card_fin] at hi
  rw [posIndex_eq_card_pos_eigenvalues (gram_isHermitian (isHermKernel_pairKernel χ ω) x)] at hi
  exact hi

theorem pairKernel_trace (χ : G →* ℂ) (ω : ℂ) (x : ι → G) :
    (trace (gram (pairKernel χ ω) x)).re = 2 * Fintype.card ι * ω.re := by
  simp [trace, diag, gram, pairKernel, reflectChar, mul_add]
  ring

/-- Adding a character pair costs one clipping penalty, independently of its displacement. -/
theorem pairKernel_clipped_threshold (A : Matrix κ ι ℂ) (χ : G →* ℂ)
    (ω : ℂ) (x : ι → G) (c : ℝ) :
    energy c (Aᴴ * A) + 4 * c * Fintype.card ι * ω.re - c ^ 2 ≤
      (trace ((Aᴴ * A + gram (pairKernel χ ω) x) *
        (Aᴴ * A + gram (pairKernel χ ω) x))).re := by
  have ht := threshold (Matrix.posSemidef_conjTranspose_mul_self A)
    (gram_isHermitian (isHermKernel_pairKernel χ ω) x) c
  rw [pairKernel_trace] at ht
  have hi : (RiemannGaussian.HermitianRankTrace.posIndex
      (gram_isHermitian (isHermKernel_pairKernel χ ω) x) : ℝ) ≤ 1 := by
    exact_mod_cast pairKernel_positive_index_le_one χ ω x
  have hp := mul_le_mul_of_nonneg_left hi (sq_nonneg c)
  nlinarith only [ht, hp]

#print axioms pairKernel_positive_index_le_one
#print axioms pairKernel_clipped_threshold

end
end GaloisForLFunctions.HeckeKreinToeplitz
