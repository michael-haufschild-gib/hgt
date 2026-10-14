import GaloisForLFunctions.HTGeometry.FiniteSupportOperatorFredholm
import GaloisForLFunctions.HTGeometry.FredholmDeterminantTracePowers
import GaloisForLFunctions.RHTower.TraceNormLimit
import Mathlib.Tactic.NoncommRing

/-! # Actual Fredholm multiplication on a common finite coordinate block

The existing coordinate-composition and zero-extension identities make the
finite block an exact operator algebra. Multiplicativity of the actual operator
Fredholm determinant then follows from the ordinary matrix determinant law.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open HilbertSchmidt _root_.ContinuousLinearMap _root_.RHTower

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*} [DecidableEq ι]

private theorem coordinate_comp_eq_ofBlock (b : HilbertBasis ι ℂ H)
    (S T : H →L[ℂ] H) (s : Finset ι)
    (hS : ∀ p, p ∉ s ×ˢ s → coordMatrix b S p = 0)
    (hT : ∀ p, p ∉ s ×ˢ s → coordMatrix b T p = 0) :
    coordMatrix b (S ∘L T) =
      ofBlock (blockMatrix (coordMatrix b S) s * blockMatrix (coordMatrix b T) s) := by
  have hKS : coordMatrix b S = ofBlock (blockMatrix (coordMatrix b S) s) :=
    (truncKernel_eq_self_of_support hS).symm.trans (truncKernel_eq_ofBlock _ _)
  have hKT : coordMatrix b T = ofBlock (blockMatrix (coordMatrix b T) s) :=
    (truncKernel_eq_self_of_support hT).symm.trans (truncKernel_eq_ofBlock _ _)
  exact (hsComp_coordMatrix b S T).symm.trans
    ((congrArg₂ hsComp hKS hKT).trans (hsComp_ofBlock _ _))

theorem coordMatrix_comp_support (b : HilbertBasis ι ℂ H)
    (S T : H →L[ℂ] H) (s : Finset ι)
    (hS : ∀ p, p ∉ s ×ˢ s → coordMatrix b S p = 0)
    (hT : ∀ p, p ∉ s ×ˢ s → coordMatrix b T p = 0) :
    ∀ p, p ∉ s ×ˢ s → coordMatrix b (S ∘L T) p = 0 := by
  intro p hp
  rw [coordinate_comp_eq_ofBlock b S T s hS hT]
  apply dif_neg
  simpa only [Finset.mem_product] using hp

theorem blockMatrix_coordMatrix_comp (b : HilbertBasis ι ℂ H)
    (S T : H →L[ℂ] H) (s : Finset ι)
    (hS : ∀ p, p ∉ s ×ˢ s → coordMatrix b S p = 0)
    (hT : ∀ p, p ∉ s ×ˢ s → coordMatrix b T p = 0) :
    blockMatrix (coordMatrix b (S ∘L T)) s =
      blockMatrix (coordMatrix b S) s * blockMatrix (coordMatrix b T) s := by
  rw [coordinate_comp_eq_ofBlock b S T s hS hT]
  ext i j
  exact ofBlock_apply_of_mem _ i.property j.property

omit [CompleteSpace H] in
private theorem blockMatrix_add (b : HilbertBasis ι ℂ H)
    (S T : H →L[ℂ] H) (s : Finset ι) :
    blockMatrix (coordMatrix b (S + T)) s =
      blockMatrix (coordMatrix b S) s + blockMatrix (coordMatrix b T) s := by
  ext i j
  simp only [blockMatrix, Matrix.add_apply, coordMatrix_apply, add_apply, inner_add_right]

theorem fredholmDetOp_finite_product (b : HilbertBasis ι ℂ H)
    (S T : H →L[ℂ] H) (hS1 : MemSchattenClass 1 S) (hT1 : MemSchattenClass 1 T)
    (s : Finset ι)
    (hS : ∀ p, p ∉ s ×ˢ s → coordMatrix b S p = 0)
    (hT : ∀ p, p ∉ s ×ˢ s → coordMatrix b T p = 0) :
    fredholmDetOp b (S + T + S ∘L T) = fredholmDetOp b S * fredholmDetOp b T := by
  have hST := coordMatrix_comp_support b S T s hS hT
  have hsum : ∀ p, p ∉ s ×ˢ s → coordMatrix b (S + T + S ∘L T) p = 0 := by
    intro p hp
    have hadd : coordMatrix b (S + T + S ∘L T) p =
        coordMatrix b S p + coordMatrix b T p + coordMatrix b (S ∘L T) p := by
      simp only [coordMatrix_apply, add_apply, inner_add_right]
    rw [hadd, hS p hp, hT p hp, hST p hp, add_zero, add_zero]
  have hsum1 := (hS1.one_add hT1).one_add (memSchattenClass_one_comp_left hT1 S)
  rw [fredholmDetOp_eq_det_block_of_support b hsum1 s hsum,
    fredholmDetOp_eq_det_block_of_support b hS1 s hS,
    fredholmDetOp_eq_det_block_of_support b hT1 s hT,
    blockMatrix_add, blockMatrix_add, blockMatrix_coordMatrix_comp b S T s hS hT]
  rw [show 1 + (blockMatrix (coordMatrix b S) s + blockMatrix (coordMatrix b T) s +
      blockMatrix (coordMatrix b S) s * blockMatrix (coordMatrix b T) s) =
      (1 + blockMatrix (coordMatrix b S) s) * (1 + blockMatrix (coordMatrix b T) s) by noncomm_ring,
    Matrix.det_mul]

end
end GaloisForLFunctions.HTGeometry
