import GaloisForLFunctions.HTGeometry.CoerciveInnerProductRenorm
import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
# Compact spectral vanishing in a coercive form norm

Transport a compact operator to the equivalent Hilbert norm supplied by a
coercive metric. Symmetry for that metric and absence of nonzero eigenvectors
force the operator to vanish. This permits spectral arguments on a positive
form quotient without assuming symmetry in the original ambient norm.
-/

open Complex
open scoped InnerProduct
noncomputable section
namespace CoerciveInnerProductRenorm
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def toOldCLM (D : Datum H) : Carrier D →L[ℂ] H :=
  (toOld D).toLinearMap.mkContinuous 1 fun x => by
    simpa only [one_mul] using old_norm_le D x

def fromOldCLM (D : Datum H) : H →L[ℂ] Carrier D :=
  (toOld D).symm.toLinearMap.mkContinuous (‖D.op‖+1) fun x => by
    simpa only [LinearEquiv.apply_symm_apply] using norm_le D ((toOld D).symm x)

theorem toOldCLM_apply (D : Datum H) (x : Carrier D) :
    toOldCLM D x = toOld D x := rfl

theorem fromOldCLM_apply (D : Datum H) (x : H) :
    fromOldCLM D x = (toOld D).symm x := rfl

/-- Spectral vanishing remains valid when self-adjointness holds only for an
equivalent coercive Hilbert form. -/
theorem compact_eq_zero_of_no_nonzero_eigenvectors (D : Datum H)
    (T : H →L[ℂ] H) (hT : IsCompactOperator T)
    (hsym : ∀ x y : H, inner ℂ (D.op (T x)) y = inner ℂ (D.op x) (T y))
    (hno : ∀ μ : ℂ, μ ≠ 0 → ∀ x : H, T x = μ • x → x = 0) : T = 0 := by
  let S : Carrier D →L[ℂ] Carrier D := (fromOldCLM D).comp (T.comp (toOldCLM D))
  have hS (x : Carrier D) : toOld D (S x) = T (toOld D x) := by
    simp only [S,ContinuousLinearMap.comp_apply,toOldCLM_apply,fromOldCLM_apply,
      LinearEquiv.apply_symm_apply]
  have hc : IsCompactOperator S := (hT.comp_clm (toOldCLM D)).clm_comp (fromOldCLM D)
  have hs : S.IsSymmetric := by
    intro x y
    rw [inner_def,inner_def,hS,hS]
    exact hsym _ _
  have hz : S = 0 := (ContinuousLinearMap.eq_zero_of_forall_hasEigenvalue_eq_zero hc hs).mp
    (by
      intro μ hμ
      by_contra hn
      obtain ⟨x,hx,hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hμ
      apply hne
      apply (toOld D).injective
      rw [map_zero]
      apply hno μ hn
      have he := congrArg (toOld D) (Module.End.mem_eigenspace_iff.mp hx)
      simpa only [hS,map_smul] using he)
  ext x
  have he := hS ((toOld D).symm x)
  simpa only [hz,ContinuousLinearMap.zero_apply,map_zero,LinearEquiv.apply_symm_apply] using he.symm

end CoerciveInnerProductRenorm
