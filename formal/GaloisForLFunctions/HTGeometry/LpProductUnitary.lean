import GaloisForLFunctions.HTGeometry.LpTwoCurry
import GaloisForLFunctions.HTGeometry.LpFamilyIsometry
import GaloisForLFunctions.HTGeometry.WoldThermofieldStandardForm
import Mathlib.Analysis.Normed.Lp.lpHolder

/-!
# Product unitaries on square-summable coordinates

Regrouping into coordinate fibres lets bounded maps and unitaries act on one
factor. Tensor products of complete coefficient bases follow by unitary transport.
-/

noncomputable section

open scoped InnerProductSpace

namespace GaloisForLFunctions.HTGeometry

variable {I J A B : Type*}

/-- A family of surjective isometries acts unitarily on the square-summable sum. -/
def lpFamilyUnitary {E F : I → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℂ (E i)]
    [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace ℂ (F i)]
    (U : ∀ i, E i ≃ₗᵢ[ℂ] F i) : lp E 2 ≃ₗᵢ[ℂ] lp F 2 where
  toFun := lpFamilyIsometry (by norm_num) (fun i => (U i).toLinearIsometry)
  invFun := lpFamilyIsometry (by norm_num) (fun i => (U i).symm.toLinearIsometry)
  left_inv x := by
    apply lp.ext
    funext i
    exact (U i).symm_apply_apply (x i)
  right_inv x := by
    apply lp.ext
    funext i
    exact (U i).apply_symm_apply (x i)
  map_add' := (lpFamilyIsometry (by norm_num) (fun i => (U i).toLinearIsometry)).map_add
  map_smul' := (lpFamilyIsometry (by norm_num) (fun i => (U i).toLinearIsometry)).map_smul
  norm_map' := (lpFamilyIsometry (by norm_num) (fun i => (U i).toLinearIsometry)).norm_map

@[simp] theorem lpFamilyUnitary_apply {E F : I → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℂ (E i)]
    [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace ℂ (F i)]
    (U : ∀ i, E i ≃ₗᵢ[ℂ] F i) (x : lp E 2) (i : I) :
    lpFamilyUnitary U x i = U i (x i) := rfl

/-- A unitary acting in the second factor of a square-summable product. -/
def lpProductRightUnitary
    (V : lp (fun _ : J => ℂ) 2 ≃ₗᵢ[ℂ] lp (fun _ : B => ℂ) 2) :
    lp (fun _ : I × J => ℂ) 2 ≃ₗᵢ[ℂ] lp (fun _ : I × B => ℂ) 2 :=
  (lpTwoCurry (I := I) (J := J)).trans
    ((lpFamilyUnitary (fun _ : I => V)).trans (lpTwoCurry (I := I) (J := B)).symm)

theorem lpProductRightUnitary_apply
    (V : lp (fun _ : J => ℂ) 2 ≃ₗᵢ[ℂ] lp (fun _ : B => ℂ) 2)
    (x : lp (fun _ : I × J => ℂ) 2) (i : I) (j : B) :
    lpProductRightUnitary V x (i, j) = V (lpTwoCurry x i) j := rfl

theorem lpTwoCurry_tensor (x : lp (fun _ : I => ℂ) 2)
    (y : lp (fun _ : J => ℂ) 2) (i : I) :
    lpTwoCurry (lpTensorProductVector x y) i = x i • y := by
  apply lp.ext
  funext j
  rfl

theorem lpProductRightUnitary_tensor
    (V : lp (fun _ : J => ℂ) 2 ≃ₗᵢ[ℂ] lp (fun _ : B => ℂ) 2)
    (x : lp (fun _ : I => ℂ) 2) (y : lp (fun _ : J => ℂ) 2) :
    lpProductRightUnitary V (lpTensorProductVector x y) = lpTensorProductVector x (V y) := by
  apply lp.ext
  funext p
  rw [lpProductRightUnitary_apply, lpTwoCurry_tensor, map_smul]
  rfl

theorem lpReindexEquiv_swap_tensor
    (x : lp (fun _ : I => ℂ) 2) (y : lp (fun _ : J => ℂ) 2) :
    lpReindexEquiv (Equiv.prodComm I J) (lpTensorProductVector x y) =
      lpTensorProductVector y x := by
  apply lp.ext
  funext p
  change x p.2 * y p.1 = y p.1 * x p.2
  ring

/-- The tensor product of two coefficient unitaries on the actual product carrier. -/
def lpProductUnitary
    (U : lp (fun _ : I => ℂ) 2 ≃ₗᵢ[ℂ] lp (fun _ : A => ℂ) 2)
    (V : lp (fun _ : J => ℂ) 2 ≃ₗᵢ[ℂ] lp (fun _ : B => ℂ) 2) :
    lp (fun _ : I × J => ℂ) 2 ≃ₗᵢ[ℂ] lp (fun _ : A × B => ℂ) 2 :=
  (lpProductRightUnitary V).trans
    ((lpReindexEquiv (Equiv.prodComm I B)).trans
      ((lpProductRightUnitary U).trans (lpReindexEquiv (Equiv.prodComm B A))))

theorem lpProductUnitary_tensor
    (U : lp (fun _ : I => ℂ) 2 ≃ₗᵢ[ℂ] lp (fun _ : A => ℂ) 2)
    (V : lp (fun _ : J => ℂ) 2 ≃ₗᵢ[ℂ] lp (fun _ : B => ℂ) 2)
    (x : lp (fun _ : I => ℂ) 2) (y : lp (fun _ : J => ℂ) 2) :
    lpProductUnitary U V (lpTensorProductVector x y) =
      lpTensorProductVector (U x) (V y) := by
  simp only [lpProductUnitary, LinearIsometryEquiv.trans_apply,
    lpProductRightUnitary_tensor, lpReindexEquiv_swap_tensor]

/-- The tensor product of complete coefficient Hilbert bases is complete. -/
def lpProductBasis
    (b : HilbertBasis I ℂ (lp (fun _ : A => ℂ) 2))
    (c : HilbertBasis J ℂ (lp (fun _ : B => ℂ) 2)) :
    HilbertBasis (I × J) ℂ (lp (fun _ : A × B => ℂ) 2) :=
  HilbertBasis.ofRepr (lpProductUnitary b.repr.symm c.repr.symm).symm

theorem lpTensorProductVector_single [DecidableEq I] [DecidableEq J] (i : I) (j : J) :
    lpTensorProductVector (lp.single 2 i (1 : ℂ)) (lp.single 2 j (1 : ℂ)) =
      lp.single 2 (i, j) (1 : ℂ) := by
  classical
  apply lp.ext
  funext p
  simp only [lpTensorProductVector_apply, lp.single_apply, Pi.single_apply]
  by_cases hi : p.1 = i <;> by_cases hj : p.2 = j <;> simp [hi, hj, Prod.ext_iff]

theorem lpReindexEquiv_single [DecidableEq I] [DecidableEq J] (e : I ≃ J) (i : I) :
    lpReindexEquiv e (lp.single 2 i (1 : ℂ)) = lp.single 2 (e i) (1 : ℂ) := by
  classical
  apply lp.ext
  funext j
  rw [lpReindexEquiv_apply]
  simp only [lp.single_apply]
  by_cases h : j = e i
  · subst j
    simp
  · have he : e.symm j ≠ i := fun hji => h (by rw [← hji, e.apply_symm_apply])
    simp [h, he]

theorem lpProductUnitary_single_apply [DecidableEq I] [DecidableEq J]
    (U : lp (fun _ : I => ℂ) 2 ≃ₗᵢ[ℂ] lp (fun _ : A => ℂ) 2)
    (V : lp (fun _ : J => ℂ) 2 ≃ₗᵢ[ℂ] lp (fun _ : B => ℂ) 2)
    (i : I) (j : J) (a : A) (b : B) :
    lpProductUnitary U V (lp.single 2 (i, j) (1 : ℂ)) (a, b) =
      U (lp.single 2 i (1 : ℂ)) a * V (lp.single 2 j (1 : ℂ)) b := by
  rw [← lpTensorProductVector_single, lpProductUnitary_tensor, lpTensorProductVector_apply]

theorem lpProductBasis_apply
    (b : HilbertBasis I ℂ (lp (fun _ : A => ℂ) 2))
    (c : HilbertBasis J ℂ (lp (fun _ : B => ℂ) 2)) (i : I) (j : J) :
    lpProductBasis b c (i, j) = lpTensorProductVector (b i) (c j) := by
  classical
  rw [← (lpProductBasis b c).repr_symm_single (i, j)]
  change lpProductUnitary b.repr.symm c.repr.symm (lp.single 2 (i, j) (1 : ℂ)) = _
  rw [← lpTensorProductVector_single, lpProductUnitary_tensor,
    b.repr_symm_single, c.repr_symm_single]

/-- A bounded operator acts on the second coordinate fibre. -/
def lpProductRightOperator
    (T : lp (fun _ : J => ℂ) 2 →L[ℂ] lp (fun _ : B => ℂ) 2) :
    lp (fun _ : I × J => ℂ) 2 →L[ℂ] lp (fun _ : I × B => ℂ) 2 :=
  (lpTwoCurry (I := I) (J := B)).symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
    lp.mapCLM 2 (fun _ : I => T) (norm_nonneg T) (fun _ => le_rfl) ∘L
      (lpTwoCurry (I := I) (J := J)).toContinuousLinearEquiv.toContinuousLinearMap

theorem lpProductRightOperator_apply
    (T : lp (fun _ : J => ℂ) 2 →L[ℂ] lp (fun _ : B => ℂ) 2)
    (x : lp (fun _ : I × J => ℂ) 2) (i : I) (j : B) :
    lpProductRightOperator T x (i, j) = T (lpTwoCurry x i) j := rfl

theorem lpProductRightOperator_tensor
    (T : lp (fun _ : J => ℂ) 2 →L[ℂ] lp (fun _ : B => ℂ) 2)
    (x : lp (fun _ : I => ℂ) 2) (y : lp (fun _ : J => ℂ) 2) :
    lpProductRightOperator T (lpTensorProductVector x y) =
      lpTensorProductVector x (T y) := by
  apply lp.ext
  funext p
  rw [lpProductRightOperator_apply, lpTwoCurry_tensor, map_smul]
  rfl

/-- A self-adjoint fibre operator stays self-adjoint on the product carrier. -/
theorem lpProductRightOperator_isSelfAdjoint
    (T : lp (fun _ : J => ℂ) 2 →L[ℂ] lp (fun _ : J => ℂ) 2)
    (hT : IsSelfAdjoint T) : IsSelfAdjoint (lpProductRightOperator (I := I) T) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric] at hT ⊢
  intro x y
  calc
    inner ℂ (lpProductRightOperator T x) y =
        inner ℂ (lpTwoCurry (lpProductRightOperator T x)) (lpTwoCurry y) :=
      ((lpTwoCurry (I := I) (J := J)).inner_map_map _ _).symm
    _ = inner ℂ (lpTwoCurry x) (lpTwoCurry (lpProductRightOperator T y)) := by
      rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
      apply tsum_congr
      intro i
      exact hT (lpTwoCurry x i) (lpTwoCurry y i)
    _ = inner ℂ x (lpProductRightOperator T y) :=
      (lpTwoCurry (I := I) (J := J)).inner_map_map _ _

end GaloisForLFunctions.HTGeometry
