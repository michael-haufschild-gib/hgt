import GaloisForLFunctions.HeckeKreinToeplitz.Index.NullSubgroupRank
import GaloisForLFunctions.AdelicKreinGeometry.ThePontryaginExtensionsOfWeilsCorrelation
import GaloisForLFunctions.ArithmeticPositiveDuality.TheExtremalsOfTheHeckeLawAreTwistedHaarStates

/-!
# Finite rank of affine kernels with zero axis readings

A Hermitian kernel on `Aff(ℚ)` with at most `r` negative squares, vanishing on all
translations and dilations, has column-space dimension at most `r²`. The translation
subgroup is normal, and every affine map is a translation followed by a dilation.
-/

open Complex
open GaloisForLFunctions.HeckeKreinToeplitz
open GaloisForLFunctions.ArithmeticPositiveDuality

noncomputable section
namespace GaloisForLFunctions.AdelicKreinGeometry

private theorem zero_on_slopeUnit_ker {k : AffineGroupQ → ℂ}
    (ht : ∀ b : ℚ, k (translation b) = 0) : ∀ g ∈ slopeUnit.ker, k g = 0 := by
  intro g hg
  change slopeUnit g = 1 at hg
  have hs : affSlope g = 1 := by
    have he := congrArg (fun u : ℚˣ => (u : ℚ)) hg
    change affSlope g = 1 at he
    exact he
  have he : g = translation (affShift g) :=
    affine_ext (by rw [affSlope_translation, hs]) (affShift_translation _).symm
  rw [he]
  exact ht _

private theorem affine_axes_product (g : AffineGroupQ) :
    ∃ h ∈ slopeUnit.ker, ∃ d ∈ dilation.range, g = h * d := by
  refine ⟨translation (affShift g), ?_, dilation (slopeUnit g), ⟨slopeUnit g, rfl⟩, ?_⟩
  · change slopeUnit (translation (affShift g)) = 1
    exact Units.ext (affSlope_translation _)
  · exact eq_translation_mul_dilation g

/-- A finite-index affine kernel with zero axis readings has a finite column space. -/
theorem finite_columnSpan_of_zero_axes {k : AffineGroupQ → ℂ} (hk : IsHermKernel k)
    {r : ℕ} (hi : negIndex k ≤ r)
    (ht : ∀ b : ℚ, k (translation b) = 0) (hd : ∀ u : ℚˣ, k (dilation u) = 0) :
    Module.Finite ℂ (kernelColumnSpan k) ∧ Module.finrank ℂ (kernelColumnSpan k) ≤ r * r :=
  finite_columnSpan_of_zero_subgroups hk hi slopeUnit.ker dilation.range inferInstance
    (zero_on_slopeUnit_ker ht) (by rintro _ ⟨u, rfl⟩; exact hd u) affine_axes_product

/-- Every finite Gram matrix of an affine kernel with zero axis readings has rank at most `r²`. -/
theorem rank_gram_le_square_of_zero_axes {k : AffineGroupQ → ℂ} (hk : IsHermKernel k)
    {r : ℕ} (hi : negIndex k ≤ r)
    (ht : ∀ b : ℚ, k (translation b) = 0) (hd : ∀ u : ℚˣ, k (dilation u) = 0)
    {ι : Type*} [Fintype ι] (x : ι → AffineGroupQ) : (gram k x).rank ≤ r * r :=
  rank_gram_le_square_of_zero_subgroups hk hi slopeUnit.ker dilation.range inferInstance
    (zero_on_slopeUnit_ker ht) (by rintro _ ⟨u, rfl⟩; exact hd u) affine_axes_product x

#print axioms finite_columnSpan_of_zero_axes
#print axioms rank_gram_le_square_of_zero_axes
end GaloisForLFunctions.AdelicKreinGeometry
