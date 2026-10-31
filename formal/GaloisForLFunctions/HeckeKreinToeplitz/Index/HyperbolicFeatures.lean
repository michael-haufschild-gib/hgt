import GaloisForLFunctions.HeckeKreinToeplitz.FiniteIndexIsPositiveMinusFiniteRank

/-!
# One negative square per hyperbolic feature pair

A group kernel expressed as a sum of `m` Hermitian cross-feature pairs has negative index
at most `m`. Adding the squares of the feature differences leaves the sum of their individual
squares, so the bound holds on every finite Gram matrix.
-/

open Complex Finset Matrix
open scoped ComplexConjugate
open GaloisForLFunctions.HTGeometry
noncomputable section
namespace GaloisForLFunctions.HeckeKreinToeplitz

private def featureOuterGram {ι : Type*} (z : ι → ℂ) : Matrix ι ι ℂ :=
  fun a b => conj (z a) * z b

private theorem hermQuad_featureOuterGram {ι : Type*} [Fintype ι] (z c : ι → ℂ) :
    hermQuad (featureOuterGram z) c = normSq (∑ a, c a * z a) := by
  have he : (normSq (∑ a, c a * z a) : ℂ) =
      ∑ a, ∑ b, conj (c a) * (conj (z a) * z b * c b) := by
    rw [Complex.normSq_eq_conj_mul_self]
    simp only [map_sum, Finset.sum_mul_sum, map_mul]
    exact sum_congr rfl fun a _ => sum_congr rfl fun b _ => by ring
  simp only [hermQuad, featureOuterGram, dotProduct, mulVec, Pi.star_apply,
    Finset.mul_sum, Complex.star_def]
  rw [← he, Complex.ofReal_re]

private theorem hermQuad_sum_features {ι J : Type*} [Fintype ι] [Fintype J]
    (M : J → Matrix ι ι ℂ) (c : ι → ℂ) :
    hermQuad (∑ j, M j) c = ∑ j, hermQuad (M j) c := by
  simp only [hermQuad, Matrix.sum_mulVec, dotProduct_sum, Complex.re_sum]

/-- Each hyperbolic feature pair costs at most one negative square. -/
theorem negIndex_le_of_hyperbolic_features {G : Type*} [Group G] {k : G → ℂ}
    {m : ℕ} (F B : Fin m → G → ℂ)
    (h : ∀ a b, k (a⁻¹ * b) =
      ∑ j, (conj (F j a) * B j b + conj (B j a) * F j b)) :
    negIndex k ≤ m := by
  refine negIndex_le_of_rank (fun j a => F j a - B j a) fun n x c => ?_
  have hm : gram k x + ∑ j, featureOuterGram (fun a => F j (x a) - B j (x a)) =
      ∑ j, (featureOuterGram (fun a => F j (x a)) +
        featureOuterGram (fun a => B j (x a))) := by
    ext a b
    simp only [Matrix.add_apply, Matrix.sum_apply, featureOuterGram, gram, h]
    rw [← Finset.sum_add_distrib]
    apply sum_congr rfl
    intro j _
    rw [map_sub]
    ring
  have he := congrArg (fun M => hermQuad M c) hm
  simp only [hermQuad_add, hermQuad_sum_features, hermQuad_featureOuterGram] at he
  rw [he]
  exact sum_nonneg fun j _ => add_nonneg (normSq_nonneg _) (normSq_nonneg _)

#print axioms negIndex_le_of_hyperbolic_features
end GaloisForLFunctions.HeckeKreinToeplitz
