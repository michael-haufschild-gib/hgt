import GaloisForLFunctions.HTGeometry.LpFiniteProductUnitary

/-!
# Bounded operators in one finite-product coordinate

Splitting one coordinate gives a bounded fibre operator on the full product
space. Its action on a complete product basis is the literal local action
times the remaining mode coefficients.
-/

noncomputable section

open scoped Classical InnerProductSpace

namespace GaloisForLFunctions.HTGeometry

variable {I A B : Type}

/-- Place the selected coordinate after all the complementary coordinates. -/
def lpCoordinateSplitEquiv (i : I) : (I → B) ≃ ({j : I // j ≠ i} → B) × B :=
  (Equiv.funSplitAt i B).trans (Equiv.prodComm _ _)

theorem lpCoordinateSplitEquiv_apply (i : I) (x : I → B) :
    lpCoordinateSplitEquiv i x = (fun j : {j : I // j ≠ i} => x j, x i) := rfl

theorem lpCoordinateSplitEquiv_symm_at (i : I)
    (p : ({j : I // j ≠ i} → B) × B) :
    (lpCoordinateSplitEquiv i).symm p i = p.2 :=
  congrArg Prod.snd ((lpCoordinateSplitEquiv i).apply_symm_apply p)

theorem lpCoordinateSplitEquiv_symm_other (i : I)
    (p : ({j : I // j ≠ i} → B) × B) (j : {j : I // j ≠ i}) :
    (lpCoordinateSplitEquiv i).symm p j = p.1 j :=
  congrArg (fun x => x.1 j) ((lpCoordinateSplitEquiv i).apply_symm_apply p)

/-- Splitting a product mode gives a pure tensor of its complementary and local modes. -/
theorem lpCoordinateSplit_productBasis [Fintype I]
    (b : I → HilbertBasis A ℂ (lp (fun _ : B => ℂ) 2)) (e : I → A) (i : I) :
    lpReindexEquiv (lpCoordinateSplitEquiv i) (lpFiniteProductBasis I b e) =
      lpTensorProductVector
        (lpFiniteProductBasis {j : I // j ≠ i} (fun j => b j) (fun j => e j))
        (b i (e i)) := by
  apply lp.ext
  funext p
  rw [lpReindexEquiv_apply, lpFiniteProductBasis_apply, lpTensorProductVector_apply,
    lpFiniteProductBasis_apply, Fintype.prod_eq_mul_prod_subtype_ne _ i]
  simp only [lpCoordinateSplitEquiv_symm_at, lpCoordinateSplitEquiv_symm_other]
  ring

/-- The actual bounded lift of one local operator to all finite-product coordinates. -/
def lpCoordinateOperator (i : I)
    (T : lp (fun _ : B => ℂ) 2 →L[ℂ] lp (fun _ : B => ℂ) 2) :
    lp (fun _ : I → B => ℂ) 2 →L[ℂ] lp (fun _ : I → B => ℂ) 2 :=
  (lpReindexEquiv (lpCoordinateSplitEquiv i)).symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
    lpProductRightOperator T ∘L
      (lpReindexEquiv (lpCoordinateSplitEquiv i)).toContinuousLinearEquiv.toContinuousLinearMap

theorem lpCoordinateOperator_apply (i : I)
    (T : lp (fun _ : B => ℂ) 2 →L[ℂ] lp (fun _ : B => ℂ) 2)
    (v : lp (fun _ : I → B => ℂ) 2) (x : I → B) :
    lpCoordinateOperator i T v x =
      lpProductRightOperator T (lpReindexEquiv (lpCoordinateSplitEquiv i) v)
        (fun j => x j, x i) := rfl

/-- Each complete product mode sees the local operator in exactly one factor. -/
theorem lpCoordinateOperator_productBasis_apply [Fintype I] (i : I)
    (T : lp (fun _ : B => ℂ) 2 →L[ℂ] lp (fun _ : B => ℂ) 2)
    (b : I → HilbertBasis A ℂ (lp (fun _ : B => ℂ) 2)) (e : I → A) (x : I → B) :
    lpCoordinateOperator i T (lpFiniteProductBasis I b e) x =
      (∏ j : {j : I // j ≠ i}, b j (e j) (x j)) * T (b i (e i)) (x i) := by
  rw [lpCoordinateOperator_apply, lpCoordinateSplit_productBasis,
    lpProductRightOperator_tensor, lpTensorProductVector_apply, lpFiniteProductBasis_apply]

/-- A local pointwise multiplier relation lifts to the complete product mode. -/
theorem lpCoordinateOperator_productBasis_multiplier [Fintype I] (i : I)
    (T : lp (fun _ : B => ℂ) 2 →L[ℂ] lp (fun _ : B => ℂ) 2)
    (b : I → HilbertBasis A ℂ (lp (fun _ : B => ℂ) 2))
    (e : I → A) (r : B → ℂ) (h : ∀ n, T (b i (e i)) n = r n * b i (e i) n)
    (x : I → B) :
    lpCoordinateOperator i T (lpFiniteProductBasis I b e) x =
      r (x i) * lpFiniteProductBasis I b e x := by
  rw [lpCoordinateOperator_productBasis_apply, h, lpFiniteProductBasis_apply,
    Fintype.prod_eq_mul_prod_subtype_ne _ i]
  ring

/-- Matrix entries of a lifted operator vanish unless every other coordinate agrees. -/
theorem lpCoordinateOperator_single_apply (i : I)
    (T : lp (fun _ : B => ℂ) 2 →L[ℂ] lp (fun _ : B => ℂ) 2)
    (e x : I → B) :
    lpCoordinateOperator i T (lp.single 2 e (1 : ℂ)) x =
      (if (fun j : {j : I // j ≠ i} => x j) = (fun j : {j : I // j ≠ i} => e j)
        then 1 else 0) * T (lp.single 2 (e i) (1 : ℂ)) (x i) := by
  rw [lpCoordinateOperator_apply, lpReindexEquiv_single]
  change lpProductRightOperator T
    (lp.single 2 ((fun j : {j : I // j ≠ i} => e j), e i) (1 : ℂ))
      ((fun j : {j : I // j ≠ i} => x j), x i) = _
  rw [← lpTensorProductVector_single, lpProductRightOperator_tensor,
    lpTensorProductVector_apply]
  simp only [lp.single_apply, Pi.single_apply]

theorem lpCoordinateOperator_isSelfAdjoint (i : I)
    (T : lp (fun _ : B => ℂ) 2 →L[ℂ] lp (fun _ : B => ℂ) 2)
    (hT : IsSelfAdjoint T) : IsSelfAdjoint (lpCoordinateOperator i T) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro x y
  let U := lpReindexEquiv (lpCoordinateSplitEquiv (B := B) i)
  let F := lpProductRightOperator (I := {j : I // j ≠ i} → B) T
  have hF := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    (lpProductRightOperator_isSelfAdjoint (I := {j : I // j ≠ i} → B) T hT)
  change inner ℂ (U.symm (F (U x))) y = inner ℂ x (U.symm (F (U y)))
  calc
    inner ℂ (U.symm (F (U x))) y = inner ℂ (F (U x)) (U y) := by
      simpa only [U.symm_apply_apply] using U.symm.inner_map_map (F (U x)) (U y)
    _ = inner ℂ (U x) (F (U y)) := hF _ _
    _ = inner ℂ x (U.symm (F (U y))) := by
      simpa only [U.symm_apply_apply] using (U.symm.inner_map_map (U x) (F (U y))).symm

end GaloisForLFunctions.HTGeometry
