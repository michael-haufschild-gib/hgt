import GaloisForLFunctions.BiarithmeticGeometry.Affine.ParsellVinogradovHomogeneousMoments
import GaloisForLFunctions.BiarithmeticGeometry.Affine.MixedCoordinateVolume

/-!
# The additive group of homogeneous physical shears

Power vectors at distinct real nodes form a Vandermonde basis. Equality on
the moment curve therefore determines a matrix. The physical action on
moments proves the shear group law, and its unit determinant reduces the
volume of two sheared sets to their relative shear.
-/

open MeasureTheory Matrix
open scoped ENNReal

namespace GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
noncomputable section

private theorem matrix_eq_of_power_vectors (m : ℕ) (M N : Matrix (Fin m) (Fin m) ℝ)
    (h : ∀ z : ℝ, M *ᵥ (fun i => z ^ i.val) = N *ᵥ (fun i => z ^ i.val)) : M = N := by
  let V : Matrix (Fin m) (Fin m) ℝ :=
    (Matrix.vandermonde (fun i : Fin m => (i.val : ℝ))).transpose
  have hd : V.det ≠ 0 := by
    change (Matrix.vandermonde (fun i : Fin m => (i.val : ℝ))).transpose.det ≠ 0
    rw [Matrix.det_transpose]
    apply Matrix.det_vandermonde_ne_zero_iff.mpr
    intro i j hij
    exact Fin.ext (Nat.cast_injective hij)
  have hprod : M * V = N * V := by
    ext i j
    simp only [Matrix.mul_apply, V, Matrix.transpose_apply, Matrix.vandermonde_apply]
    exact congrFun (h (j.val : ℝ)) i
  calc
    M = (M * V) * V⁻¹ := by rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv V
      (isUnit_iff_ne_zero.mpr hd), mul_one]
    _ = (N * V) * V⁻¹ := by rw [hprod]
    _ = N := by rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv V
      (isUnit_iff_ne_zero.mpr hd), mul_one]

private theorem shearBlock_power_vector (m : ℕ) (θ z : ℝ) :
    shearBlock m θ *ᵥ (fun i => z ^ i.val) = fun i => (z + θ) ^ i.val := by
  cases m with
  | zero => funext i; exact Fin.elim0 i
  | succ d =>
    have hv (w : ℝ) : homogeneousMoment d 1 w = (fun i => w ^ i.val) := by
      funext i
      simp only [homogeneousMoment, one_pow, one_mul]
    simpa only [hv, mul_one] using
      shearBlock_mul_homogeneousMoment d θ 1 z

/-- Homogeneous physical shears compose by addition of their parameters. -/
theorem shearBlock_mul (m : ℕ) (θ φ : ℝ) :
    shearBlock m θ * shearBlock m φ = shearBlock m (θ + φ) := by
  apply matrix_eq_of_power_vectors
  intro z
  rw [← Matrix.mulVec_mulVec, shearBlock_power_vector, shearBlock_power_vector,
    shearBlock_power_vector]
  funext i
  congr 1
  ring

/-- Zero shear is the identity matrix in every block size. -/
theorem shearBlock_zero (m : ℕ) : shearBlock m 0 = 1 := by
  apply matrix_eq_of_power_vectors
  intro z
  rw [shearBlock_power_vector, Matrix.one_mulVec, add_zero]

/-- Composition on ambient vectors, not only on the moment curve. -/
theorem shearLinear_comp_apply (m : ℕ) (θ φ : ℝ) (x : Fin m → ℝ) :
    Matrix.toLin' (shearBlock m θ) (Matrix.toLin' (shearBlock m φ) x) =
      Matrix.toLin' (shearBlock m (θ + φ)) x := by
  simp only [Matrix.toLin'_apply, Matrix.mulVec_mulVec, shearBlock_mul]

theorem shearLinear_zero_apply (m : ℕ) (x : Fin m → ℝ) :
    Matrix.toLin' (shearBlock m 0) x = x := by
  rw [Matrix.toLin'_apply, shearBlock_zero, Matrix.one_mulVec]

/-- Negating the shear parameter interchanges images and inverse images. -/
theorem shearLinear_image_eq_preimage_neg (m : ℕ) (θ : ℝ) (S : Set (Fin m → ℝ)) :
    (Matrix.toLin' (shearBlock m θ)) '' S =
      (Matrix.toLin' (shearBlock m (-θ))) ⁻¹' S := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa only [Set.mem_preimage, shearLinear_comp_apply, neg_add_cancel,
      shearLinear_zero_apply] using hx
  · intro hy
    refine ⟨Matrix.toLin' (shearBlock m (-θ)) y, hy, ?_⟩
    rw [shearLinear_comp_apply, add_neg_cancel, shearLinear_zero_apply]

/-- The actual homogeneous shears preserve outer volume on every set. -/
theorem volume_shearLinear_image (m : ℕ) (θ : ℝ) (S : Set (Fin m → ℝ)) :
    volume ((Matrix.toLin' (shearBlock m θ)) '' S) = volume S := by
  simpa only [LinearMap.det_toLin', det_shearBlock, abs_one, ENNReal.ofReal_one, one_mul] using
    Measure.addHaar_image_linearMap volume (Matrix.toLin' (shearBlock m θ)) S

/-- Two sheared sets have exactly the overlap volume of the relative shear. -/
theorem volume_two_shearLinear_images (m : ℕ) (θ φ : ℝ) (A B : Set (Fin m → ℝ)) :
    volume ((Matrix.toLin' (shearBlock m θ)) '' A ∩ (Matrix.toLin' (shearBlock m φ)) '' B) =
      volume (A ∩ (Matrix.toLin' (shearBlock m (θ - φ))) ⁻¹' B) := by
  have hi : Function.Injective (Matrix.toLin' (shearBlock m θ)) := by
    apply Function.LeftInverse.injective (g := Matrix.toLin' (shearBlock m (-θ)))
    intro x
    rw [shearLinear_comp_apply, neg_add_cancel, shearLinear_zero_apply]
  have hc : (fun x => Matrix.toLin' (shearBlock m θ)
      (Matrix.toLin' (shearBlock m (φ - θ)) x)) = Matrix.toLin' (shearBlock m φ) := by
    funext x
    rw [shearLinear_comp_apply, show θ + (φ - θ) = φ by ring]
  have hset : (Matrix.toLin' (shearBlock m θ)) ''
      (A ∩ (Matrix.toLin' (shearBlock m (φ - θ))) '' B) =
      (Matrix.toLin' (shearBlock m θ)) '' A ∩ (Matrix.toLin' (shearBlock m φ)) '' B := by
    rw [Set.image_inter hi, Set.image_image, hc]
  rw [← hset, volume_shearLinear_image, shearLinear_image_eq_preimage_neg,
    show -(φ - θ) = θ - φ by ring]

#print axioms shearBlock_mul
#print axioms shearBlock_zero
#print axioms shearLinear_comp_apply
#print axioms shearLinear_image_eq_preimage_neg
#print axioms volume_shearLinear_image
#print axioms volume_two_shearLinear_images

end
end GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
