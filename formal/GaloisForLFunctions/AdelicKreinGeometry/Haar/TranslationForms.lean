import GaloisForLFunctions.AdelicKreinGeometry.Haar.GeneralOrbits
import GaloisForLFunctions.AdelicKreinGeometry.Haar.TranslationMovingPositivity
import GaloisForLFunctions.AdelicKreinGeometry.Haar.TranslationProjections
import GaloisForLFunctions.HeckeKreinToeplitz.Index.HermitianFiniteSums
import GaloisForLFunctions.HeckeKreinToeplitz.Index.ProjectionOrder

/-!
# Nonnegative cyclic translation forms

The moving projection defines a nonnegative Hermitian form. Its values increase when the cyclic subgroup grows and remain uniformly bounded on the algebraic column space.
-/

open Complex Module Finset
open GaloisForLFunctions.ArithmeticPositiveDuality
open GaloisForLFunctions.BiarithmeticGeometry
open GaloisForLFunctions.HeckeKreinToeplitz
open GaloisForLFunctions.HTGeometry
noncomputable section
namespace GaloisForLFunctions.AdelicKreinGeometry

/-- The projection onto rational translation differences. -/
def translationMovingProjection (k : AffineGroupQ → ℂ)
    (hp : ∀ g, k (g * translation 1) = k g) (b : ℚ) : End ℂ (kernelColumnSpan k) :=
  1 + (-1 : ℂ) • translationFixedProjection k hp b

theorem translationMovingProjection_apply_eq_sub (k : AffineGroupQ → ℂ)
    (hp : ∀ g, k (g * translation 1) = k g) (b : ℚ) (x : kernelColumnSpan k) :
    translationMovingProjection k hp b x = x - translationFixedProjection k hp b x := by
  apply Subtype.ext
  funext g
  change (x : AffineGroupQ → ℂ) g + (-1 : ℂ) *
    (translationFixedProjection k hp b x : AffineGroupQ → ℂ) g =
      (x : AffineGroupQ → ℂ) g - (translationFixedProjection k hp b x : AffineGroupQ → ℂ) g
  ring

/-- The moving column form, with the first argument linear. -/
def translationMovingForm (k : AffineGroupQ → ℂ)
    (hp : ∀ g, k (g * translation 1) = k g) (b : ℚ)
    (x y : kernelColumnSpan k) : ℂ :=
  kernelColumnPairing k (translationMovingProjection k hp b y)
    (translationMovingProjection k hp b x)

theorem translationMovingForm_hermitian {k : AffineGroupQ → ℂ} (hk : IsHermKernel k)
    (hp : ∀ g, k (g * translation 1) = k g) (b : ℚ) :
    IsHermitianForm (translationMovingForm k hp b) := by
  let S := translationMovingProjection k hp b
  refine ⟨?_, ?_, ?_⟩
  · intro x y z
    change kernelColumnPairing k (S z) (S (x + y)) =
      kernelColumnPairing k (S z) (S x) + kernelColumnPairing k (S z) (S y)
    rw [map_add, map_add]
  · intro a x y
    change kernelColumnPairing k (S y) (S (a • x)) =
      a * kernelColumnPairing k (S y) (S x)
    rw [map_smul, map_smul, smul_eq_mul]
  · intro x y
    exact kernelColumnPairing_conj_symm hk (S x) (S y)

/-- Reversing the cyclic step leaves its moving form unchanged. -/
theorem translationMovingForm_neg (k : AffineGroupQ → ℂ)
    (hp : ∀ g, k (g * translation 1) = k g) (b : ℚ) :
    translationMovingForm k hp (-b) = translationMovingForm k hp b := by
  funext x y
  simp only [translationMovingForm, translationMovingProjection, translationFixedProjection_neg]

/-- Affine transport rescales the moving form's cyclic step. -/
theorem translationMovingForm_affine {k : AffineGroupQ → ℂ} (hk : IsHermKernel k)
    (hp : ∀ g, k (g * translation 1) = k g) (b : ℚ) (g : AffineGroupQ)
    (x y : kernelColumnSpan k) :
    translationMovingForm k hp b (kernelColumnRepresentation k g x)
      (kernelColumnRepresentation k g y) = translationMovingForm k hp (b / affSlope g) x y := by
  have hm (v : kernelColumnSpan k) :
      translationMovingProjection k hp b (kernelColumnRepresentation k g v) =
        kernelColumnRepresentation k g (translationMovingProjection k hp (b / affSlope g) v) := by
    simp only [translationMovingProjection, LinearMap.add_apply, LinearMap.smul_apply,
      Module.End.one_apply, translationFixedProjection_affine, map_add, map_smul]
  simp only [translationMovingForm, hm, kernelColumnPairing_invariant hk]

/-- Subtracting the moving form leaves precisely the fixed-projection pairing. -/
theorem columnPairing_sub_translationMovingForm {k : AffineGroupQ → ℂ} (hk : IsHermKernel k)
    (hp : ∀ g, k (g * translation 1) = k g) (b : ℚ) (x y : kernelColumnSpan k) :
    kernelColumnPairing k y x - translationMovingForm k hp b x y =
      kernelColumnPairing k (translationFixedProjection k hp b y) (translationFixedProjection k hp b x) := by
  apply sub_eq_iff_eq_add.mpr
  have h := kernelColumnPairing_projection_decomposition hk (translation b)
    (kernel_translation_locally_periodic hp b) y x
  simpa only [translationMovingForm, translationMovingProjection_apply_eq_sub,
    translationFixedProjection] using h

theorem translationMovingForm_nonneg {k : AffineGroupQ → ℂ}
    (hk : IsHermKernel k) {r : ℕ} (hi : negIndex k ≤ r)
    (hp : ∀ g, k (g * translation 1) = k g) (b : ℚ) (x : kernelColumnSpan k) :
    0 ≤ (translationMovingForm k hp b x x).re := by
  apply translation_moving_subspace_nonnegative hk hi hp b
  exact add_neg_locallyPeriodicProjection_mem_range _ (kernel_translation_locally_periodic hp b) x

/-- Every column has moving norm at most one, uniformly over rational steps. -/
theorem translationMovingForm_point_le_one {k : AffineGroupQ → ℂ}
    (hk : IsHermKernel k) (hs : HasIntegerSuccessor k)
    (hp : ∀ g, k (g * translation 1) = k g) (b : ℚ) (g : AffineGroupQ) :
    (translationMovingForm k hp b (kernelColumnPoint k g) (kernelColumnPoint k g)).re ≤ 1 := by
  have hdiag : kernelColumnPairing k (kernelColumnPoint k g) (kernelColumnPoint k g) = 1 := by
    rw [kernelColumnPairing_point_left hk]
    change k (g⁻¹ * g) = 1
    rw [inv_mul_cancel, hasIntegerSuccessor_one hs]
  have hP := integer_successor_affine_projection_pairing hk hs hp b g
  have he := congrArg Complex.re (columnPairing_sub_translationMovingForm hk hp b
    (kernelColumnPoint k g) (kernelColumnPoint k g))
  rw [hdiag, Complex.sub_re, Complex.one_re, hP] at he
  have hreal : (((b / affSlope g).den : ℂ)⁻¹).re = ((b / affSlope g).den : ℝ)⁻¹ := by
    simpa only [Complex.ofReal_inv, Complex.ofReal_natCast] using
      Complex.ofReal_re (((b / affSlope g).den : ℝ)⁻¹)
  rw [hreal] at he
  have hpos : (0 : ℝ) ≤ ((b / affSlope g).den : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  linarith only [he, hpos]

/-- Positive moving forms are uniformly bounded on every vector in the algebraic column space. -/
theorem translationMovingForm_bddAbove {k : AffineGroupQ → ℂ}
    (hk : IsHermKernel k) {r : ℕ} (hi : negIndex k ≤ r) (hs : HasIntegerSuccessor k)
    (hp : ∀ g, k (g * translation 1) = k g) (x : kernelColumnSpan k) :
    BddAbove (Set.range (fun b : ℚ => (translationMovingForm k hp b x x).re)) := by
  obtain ⟨n, g, c, rfl⟩ := exists_kernelColumnPoint_fin_sum k x
  refine ⟨(∑ i, ‖c i‖) ^ 2, ?_⟩
  rintro a ⟨b, rfl⟩
  exact positiveHermitianForm_fin_sum_re_le (translationMovingForm_hermitian hk hp b)
    (translationMovingForm_nonneg hk hi hp b) (fun i => kernelColumnPoint k (g i))
    (fun i => translationMovingForm_point_le_one hk hs hp b (g i)) c

/-- Moving forms increase under enlargement of a cyclic translation subgroup. -/
theorem translationMovingForm_re_le_nat_multiple {k : AffineGroupQ → ℂ}
    (hk : IsHermKernel k) {r : ℕ} (hi : negIndex k ≤ r)
    (hp : ∀ g, k (g * translation 1) = k g) (b : ℚ) (n : ℕ) (x : kernelColumnSpan k) :
    (translationMovingForm k hp ((n : ℚ) * b) x x).re ≤
      (translationMovingForm k hp b x x).re := by
  have he : translation ((n : ℚ) * b) = (translation b) ^ n := by
    simpa only [MonoidHom.id_apply] using
      (rational_affine_translation_pow (MonoidHom.id AffineGroupQ) b n).symm
  have h := kernelColumnPairing_moving_re_le_of_power hk _ _ n he
    (kernel_translation_locally_periodic hp ((n : ℚ) * b))
    (kernel_translation_locally_periodic hp b)
    (translation_moving_subspace_nonnegative hk hi hp b) x
  simpa only [translationMovingForm, translationMovingProjection_apply_eq_sub,
    translationFixedProjection] using h

#print axioms translationMovingForm_nonneg
#print axioms translationMovingForm_bddAbove
#print axioms translationMovingForm_re_le_nat_multiple
end GaloisForLFunctions.AdelicKreinGeometry
