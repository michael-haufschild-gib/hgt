import GaloisForLFunctions.HTGeometry.SignedEulerianTopFiberCurvature
import GaloisForLFunctions.RHTower.PrimeSieveBooleanFirstTraceConnection

/-!
# Source curvature and the signed-Eulerian Pluecker lift

The first-trace Boolean connection retains order as a nonzero two-face curvature, while every
completed-face scalar realization kills it.  The same loss occurs in the Visontai--Williams
top-signature fibre containing `3142` and `3241`.

A rank-two Hermitian pencil gives the exact finite repair: its determinant is the squared
four-label curvature times `z * w`, hence is nonvanishing when both variables lie in the open
upper half-plane.  The associated univariate Gram determinant has curvature square as its
quadratic coefficient and no nonnegative real root.
-/

namespace RHTower

section FirstTracePaths

variable {R A B : Type*}
  [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]

/-- Corrected first-trace path adjoining face `e` and then face `f`. -/
def firstTracePathEF (x e f : A) (r t : R) : A :=
  firstTraceCorrectedEdge x e r +
    firstTraceCorrectedEdge ((1 - r) • (x * e)) f t

/-- Corrected first-trace path adjoining face `f` and then face `e`. -/
def firstTracePathFE (x e f : A) (r t : R) : A :=
  firstTraceCorrectedEdge x f t +
    firstTraceCorrectedEdge ((1 - t) • (x * f)) e r

/-- Path difference is exactly the corrected square curvature. -/
theorem firstTracePathEF_sub_firstTracePathFE
    (x e f : A) (r t : R) :
    firstTracePathEF x e f r t - firstTracePathFE x e f r t =
      firstTraceCorrectedSquareCurvature x e f r t := by
  simp only [firstTracePathEF, firstTracePathFE, firstTraceCorrectedSquareCurvature]
  abel

/-- Every scalar realization completing both faces identifies the two insertion paths. -/
theorem map_firstTracePathEF_eq_firstTracePathFE
    (φ : A →ₐ[R] B) (x e f : A) (r t : R)
    (he : φ e = 1) (hf : φ f = 1) :
    φ (firstTracePathEF x e f r t) = φ (firstTracePathFE x e f r t) := by
  apply sub_eq_zero.mp
  rw [← map_sub]
  rw [firstTracePathEF_sub_firstTracePathFE]
  exact map_firstTraceCorrectedSquareCurvature_eq_zero φ x e f r t he hf

/-- On a face witness with `e = 1` and `f = 0`, the source curvature is `-r x`. -/
theorem firstTraceSquareCurvature_one_zero
    (x : A) (r t : R) :
    firstTraceCorrectedSquareCurvature x 1 0 r t = -(r • x) := by
  rw [firstTraceCorrectedSquareCurvature_eq]
  simp

/-- A nonzero reciprocal source edge separates the two insertion histories before scalarization. -/
theorem firstTracePathEF_ne_firstTracePathFE_of_faceWitness
    (x : A) (r t : R) (hrx : r • x ≠ 0) :
    firstTracePathEF x 1 0 r t ≠ firstTracePathFE x 1 0 r t := by
  intro h
  have hzero : firstTracePathEF x 1 0 r t - firstTracePathFE x 1 0 r t = 0 :=
    sub_eq_zero.mpr h
  rw [firstTracePathEF_sub_firstTracePathFE,
    firstTraceSquareCurvature_one_zero] at hzero
  exact hrx (neg_eq_zero.mp hzero)

/-- Closed nonzero two-face witness. -/
theorem concrete_firstTracePathEF_ne_firstTracePathFE :
    firstTracePathEF (R := ℝ) (1 : ℝ) 1 0 1 1 ≠
      firstTracePathFE (R := ℝ) (1 : ℝ) 1 0 1 1 := by
  exact firstTracePathEF_ne_firstTracePathFE_of_faceWitness 1 1 1 (by norm_num)

end FirstTracePaths

end RHTower

namespace GaloisForLFunctions.HTGeometry

/-- A pair of distinct source histories cannot map faithfully to the common scalar top weight of
the `3142`/`3241` signature fibre. -/
theorem not_injective_of_distinct_histories_realize_topFiber
    {A R : Type*} [CommMonoid R]
    (φ : A → R) (source3142 source3241 : A)
    (hsource : source3142 ≠ source3241)
    (x y : ℕ → R) (q : R)
    (h3142 : φ source3142 = typeBTopWeight x y q signedWord3142)
    (h3241 : φ source3241 = typeBTopWeight x y q signedWord3241) :
    ¬Function.Injective φ := by
  intro hinjective
  apply hsource
  apply hinjective
  calc
    φ source3142 = typeBTopWeight x y q signedWord3142 := h3142
    _ = typeBTopWeight x y q signedWord3241 :=
      typeBTopWeight_signedWord3142_eq_signedWord3241 x y q
    _ = φ source3241 := h3241.symm

/-- Multiplicative four-label curvature of a descent-edge kernel. -/
def signedEulerianFourLabelCurvature (κ : ℕ → ℕ → ℝ) : ℝ :=
  κ 3 1 * κ 4 2 - κ 3 2 * κ 4 1

/-- Determinant of a real `2 x 2` curvature kernel. -/
def curvatureMinor (a b c d : ℝ) : ℝ := a * d - b * c

/-- Rank-two Hermitian pencil whose columns are `(a,c)` and `(b,d)`. -/
def curvaturePluckerPencil (a b c d : ℝ) (z w : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![z * (a : ℂ) ^ 2 + w * (b : ℂ) ^ 2,
      z * (a : ℂ) * c + w * (b : ℂ) * d;
     z * (a : ℂ) * c + w * (b : ℂ) * d,
      z * (c : ℂ) ^ 2 + w * (d : ℂ) ^ 2]

/-- The pencil determinant is the squared Pluecker curvature. -/
theorem det_curvaturePluckerPencil
    (a b c d : ℝ) (z w : ℂ) :
    (curvaturePluckerPencil a b c d z w).det =
      (curvatureMinor a b c d : ℂ) ^ 2 * z * w := by
  simp [curvaturePluckerPencil, curvatureMinor, Matrix.det_fin_two]
  ring

/-- Nonzero curvature gives an upper-half-plane-stable rank-two pencil determinant. -/
theorem det_curvaturePluckerPencil_ne_zero_of_im_pos
    {a b c d : ℝ} (hcurv : curvatureMinor a b c d ≠ 0)
    {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.im) :
    (curvaturePluckerPencil a b c d z w).det ≠ 0 := by
  rw [det_curvaturePluckerPencil]
  apply mul_ne_zero (mul_ne_zero (pow_ne_zero 2 ?_) ?_) ?_
  · exact_mod_cast hcurv
  · intro hz0
    subst z
    norm_num at hz
  · intro hw0
    subst w
    norm_num at hw

/-- Gram determinant `det(I + u K K^T)` for `K = [[a,b],[c,d]]`. -/
def curvatureGramDet (a b c d u : ℝ) : ℝ :=
  (!![1 + u * (a ^ 2 + b ^ 2), u * (a * c + b * d);
      u * (a * c + b * d), 1 + u * (c ^ 2 + d ^ 2)] :
    Matrix (Fin 2) (Fin 2) ℝ).det

/-- Gram energy, the linear coefficient of the normalized determinant. -/
def curvatureEnergy (a b c d : ℝ) : ℝ := a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2

/-- Exact normalized Gram polynomial. -/
theorem curvatureGramDet_eq
    (a b c d u : ℝ) :
    curvatureGramDet a b c d u =
      1 + curvatureEnergy a b c d * u + curvatureMinor a b c d ^ 2 * u ^ 2 := by
  simp [curvatureGramDet, curvatureEnergy, curvatureMinor, Matrix.det_fin_two]
  ring

/-- The Gram quadratic coefficient is positive exactly when four-label curvature is nonzero. -/
theorem curvatureGram_quadraticCoefficient_pos_iff
    (a b c d : ℝ) :
    0 < curvatureMinor a b c d ^ 2 ↔ curvatureMinor a b c d ≠ 0 := by
  exact sq_pos_iff

/-- Sum-of-squares factorization of the Gram-polynomial discriminant. -/
theorem curvatureGram_discriminant_eq
    (a b c d : ℝ) :
    curvatureEnergy a b c d ^ 2 - 4 * curvatureMinor a b c d ^ 2 =
      ((a - d) ^ 2 + (b + c) ^ 2) * ((a + d) ^ 2 + (b - c) ^ 2) := by
  simp [curvatureEnergy, curvatureMinor]
  ring

/-- The normalized Gram polynomial has nonnegative discriminant. -/
theorem curvatureGram_discriminant_nonneg
    (a b c d : ℝ) :
    0 ≤ curvatureEnergy a b c d ^ 2 - 4 * curvatureMinor a b c d ^ 2 := by
  rw [curvatureGram_discriminant_eq]
  positivity

/-- Every real zero of the normalized Gram determinant is strictly negative. -/
theorem curvatureGramDet_root_neg
    {a b c d u : ℝ} (hroot : curvatureGramDet a b c d u = 0) :
    u < 0 := by
  rw [curvatureGramDet_eq] at hroot
  by_contra hnot
  have hu : 0 ≤ u := le_of_not_gt hnot
  have henergy : 0 ≤ curvatureEnergy a b c d := by
    simp [curvatureEnergy]
    positivity
  have hcurv : 0 ≤ curvatureMinor a b c d ^ 2 := sq_nonneg _
  have hu2 : 0 ≤ u ^ 2 := sq_nonneg _
  nlinarith [mul_nonneg henergy hu, mul_nonneg hcurv hu2]

/-- The signed-Eulerian four-label curvature is the Pluecker minor of its edge kernel. -/
theorem signedEulerianFourLabelCurvature_eq_curvatureMinor
    (κ : ℕ → ℕ → ℝ) :
    signedEulerianFourLabelCurvature κ =
      curvatureMinor (κ 3 1) (κ 3 2) (κ 4 1) (κ 4 2) := by
  rfl

/-- The curvature-preserving pencil attached directly to a signed-Eulerian edge kernel. -/
theorem det_signedEulerian_curvaturePencil
    (κ : ℕ → ℕ → ℝ) (z w : ℂ) :
    (curvaturePluckerPencil (κ 3 1) (κ 3 2) (κ 4 1) (κ 4 2) z w).det =
      (signedEulerianFourLabelCurvature κ : ℂ) ^ 2 * z * w := by
  rw [det_curvaturePluckerPencil, signedEulerianFourLabelCurvature_eq_curvatureMinor]

end GaloisForLFunctions.HTGeometry
