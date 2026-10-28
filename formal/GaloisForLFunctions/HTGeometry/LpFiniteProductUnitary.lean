import GaloisForLFunctions.HTGeometry.LpProductUnitary
import Mathlib.Data.Fintype.Option

/-!
# Finite products of coefficient unitaries

The product of finitely many unitary coefficient matrices is unitary on the
actual square-summable function carrier. The proof joins one factor at a time.
-/

noncomputable section

open scoped Classical

namespace GaloisForLFunctions.HTGeometry

variable {A B : Type}

/-- Finite products of local unitary matrices have a unitary realization on
the product coordinate space, with the exact product columns. -/
theorem exists_lpFiniteProductUnitary (I : Type) [Fintype I]
    (U : I → (lp (fun _ : A => ℂ) 2 ≃ₗᵢ[ℂ] lp (fun _ : B => ℂ) 2)) :
    ∃ V : lp (fun _ : I → A => ℂ) 2 ≃ₗᵢ[ℂ] lp (fun _ : I → B => ℂ) 2,
      ∀ (a : I → A) (b : I → B),
        V (lp.single 2 a (1 : ℂ)) b = ∏ i, U i (lp.single 2 (a i) (1 : ℂ)) (b i) := by
  classical
  let P : ∀ (I : Type) [Fintype I], Prop := fun I _ =>
    ∀ U : I → (lp (fun _ : A => ℂ) 2 ≃ₗᵢ[ℂ] lp (fun _ : B => ℂ) 2),
      ∃ V : lp (fun _ : I → A => ℂ) 2 ≃ₗᵢ[ℂ] lp (fun _ : I → B => ℂ) 2,
        ∀ (a : I → A) (b : I → B),
          V (lp.single 2 a (1 : ℂ)) b = ∏ i, U i (lp.single 2 (a i) (1 : ℂ)) (b i)
  apply Fintype.induction_empty_option (P := P)
  · intro I J _ e h U
    letI : Fintype I := Fintype.ofEquiv J e.symm
    obtain ⟨V, hV⟩ := h (fun i => U (e i))
    let eA : (I → A) ≃ (J → A) := Equiv.arrowCongr e (Equiv.refl A)
    let eB : (I → B) ≃ (J → B) := Equiv.arrowCongr e (Equiv.refl B)
    refine ⟨(lpReindexEquiv eA.symm).trans (V.trans (lpReindexEquiv eB)), ?_⟩
    intro a b
    simp only [LinearIsometryEquiv.trans_apply, lpReindexEquiv_single, lpReindexEquiv_apply]
    rw [hV]
    change (∏ i : I, U (e i) (lp.single 2 (a (e i)) (1 : ℂ)) (b (e i))) = _
    exact Fintype.prod_equiv e _ _ (fun _ => rfl)
  · intro U
    let e : (PEmpty → A) ≃ (PEmpty → B) :=
      { toFun := fun _ x => PEmpty.elim x
        invFun := fun _ x => PEmpty.elim x
        left_inv := by intro f; funext x; exact PEmpty.elim x
        right_inv := by intro f; funext x; exact PEmpty.elim x }
    refine ⟨lpReindexEquiv e, ?_⟩
    intro a b
    rw [lpReindexEquiv_single]
    have hb : b = e a := Subsingleton.elim _ _
    subst b
    simp
  · intro I _ h U
    obtain ⟨V, hV⟩ := h (fun i => U (some i))
    let eA : (Option I → A) ≃ A × (I → A) := Equiv.piOptionEquivProd
    let eB : (Option I → B) ≃ B × (I → B) := Equiv.piOptionEquivProd
    refine ⟨(lpReindexEquiv eA).trans
      ((lpProductUnitary (U none) V).trans (lpReindexEquiv eB.symm)), ?_⟩
    intro a b
    simp only [LinearIsometryEquiv.trans_apply, lpReindexEquiv_single, lpReindexEquiv_apply]
    change lpProductUnitary (U none) V
      (lp.single 2 (a none, fun i => a (some i)) (1 : ℂ))
        (b none, fun i => b (some i)) = _
    rw [lpProductUnitary_single_apply, hV, Fintype.prod_option]
/-- The complete finite tensor unitary with its literal product coefficients. -/
def lpFiniteProductUnitary (I : Type) [Fintype I]
    (U : I → (lp (fun _ : A => ℂ) 2 ≃ₗᵢ[ℂ] lp (fun _ : B => ℂ) 2)) :
    lp (fun _ : I → A => ℂ) 2 ≃ₗᵢ[ℂ] lp (fun _ : I → B => ℂ) 2 :=
  Classical.choose (exists_lpFiniteProductUnitary I U)

theorem lpFiniteProductUnitary_single_apply (I : Type) [Fintype I]
    (U : I → (lp (fun _ : A => ℂ) 2 ≃ₗᵢ[ℂ] lp (fun _ : B => ℂ) 2))
    (a : I → A) (b : I → B) :
    lpFiniteProductUnitary I U (lp.single 2 a (1 : ℂ)) b =
      ∏ i, U i (lp.single 2 (a i) (1 : ℂ)) (b i) :=
  Classical.choose_spec (exists_lpFiniteProductUnitary I U) a b

/-- A complete finite tensor basis on scalar product coordinates. -/
def lpFiniteProductBasis (I : Type) [Fintype I]
    (b : I → HilbertBasis A ℂ (lp (fun _ : B => ℂ) 2)) :
    HilbertBasis (I → A) ℂ (lp (fun _ : I → B => ℂ) 2) :=
  HilbertBasis.ofRepr (lpFiniteProductUnitary I (fun i => (b i).repr.symm)).symm

theorem lpFiniteProductBasis_apply (I : Type) [Fintype I]
    (b : I → HilbertBasis A ℂ (lp (fun _ : B => ℂ) 2))
    (a : I → A) (x : I → B) :
    lpFiniteProductBasis I b a x = ∏ i, b i (a i) (x i) := by
  classical
  rw [← (lpFiniteProductBasis I b).repr_symm_single a]
  change lpFiniteProductUnitary I (fun i => (b i).repr.symm)
    (lp.single 2 a (1 : ℂ)) x = _
  rw [lpFiniteProductUnitary_single_apply]
  apply Finset.prod_congr rfl
  intro i _
  rw [(b i).repr_symm_single]

end GaloisForLFunctions.HTGeometry
