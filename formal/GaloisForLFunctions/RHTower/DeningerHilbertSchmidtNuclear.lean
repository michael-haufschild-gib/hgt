import GaloisForLFunctions.RHTower.DeningerNuclearSchattenBridge
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# A composite of Hilbert–Schmidt maps is nuclear

A map between Hilbert spaces is Hilbert–Schmidt relative to a Hilbert basis of its domain when the
images of the basis vectors are square-summable.  Expanding a vector in a Hilbert basis of the
middle space writes a composite `B ∘ A` as the sum of the rank-one maps built from the adjoint of
the first factor and the images of the second, and the norms of those rank-one maps are the
products of two square-summable families, hence summable.

So a composite of Hilbert–Schmidt maps is nuclear.  This is the bridge on which the permanence
theory of nuclear spaces rests, since Hilbert space quotients are complemented.

* `DeningerIsHilbertSchmidtOn` : the Hilbert–Schmidt condition on a Hilbert basis.
* `deningerSummable_mul_of_sq` : a product of square-summable families is summable.
* `deningerIsNuclear_comp_of_hilbertSchmidt` : a composite of Hilbert–Schmidt maps is nuclear.
-/

namespace RHTower

open ContinuousLinearMap

section Summability

/-- **A product of square-summable nonnegative families is summable**, by the arithmetic-geometric
mean inequality. -/
theorem deningerSummable_mul_of_sq {κ : Type*} {f g : κ → ℝ}
    (hf : Summable fun i => f i ^ 2) (hg : Summable fun i => g i ^ 2)
    (hfn : ∀ i, 0 ≤ f i) (hgn : ∀ i, 0 ≤ g i) : Summable fun i => f i * g i := by
  refine Summable.of_nonneg_of_le (fun i => mul_nonneg (hfn i) (hgn i)) (fun i => ?_)
    ((hf.add hg).mul_left (1 / 2))
  have h := sq_nonneg (f i - g i)
  nlinarith [h]

end Summability

section HilbertSchmidt

/-- **The Hilbert–Schmidt condition on a Hilbert basis**: the images of the basis vectors are
square-summable. -/
def DeningerIsHilbertSchmidtOn {ι : Type} {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (b : HilbertBasis ι ℂ E) (A : E →L[ℂ] F) : Prop :=
  Summable fun i => ‖A (b i)‖ ^ 2

variable {ι : Type} {H₁ H₂ H₃ : Type*}
variable [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
variable [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]
variable [NormedAddCommGroup H₃] [InnerProductSpace ℂ H₃]

/-- **A composite of Hilbert–Schmidt maps is nuclear.**  Expanding in a Hilbert basis of the
middle space, the composite is the sum of the rank-one maps pairing the adjoint of the first factor
against the images of the second. -/
theorem deningerIsNuclear_comp_of_hilbertSchmidt (c : HilbertBasis ι ℂ H₂)
    (A : H₁ →L[ℂ] H₂) (B : H₂ →L[ℂ] H₃)
    (hA : DeningerIsHilbertSchmidtOn c (ContinuousLinearMap.adjoint A))
    (hB : DeningerIsHilbertSchmidtOn c B) :
    DeningerIsNuclear (B.comp A) := by
  refine ⟨ι, fun j => innerSL ℂ (ContinuousLinearMap.adjoint A (c j)), fun j => B (c j),
    ?_, ?_⟩
  · have hnorm : (fun j => ‖innerSL ℂ (ContinuousLinearMap.adjoint A (c j))‖ * ‖B (c j)‖)
        = fun j => ‖ContinuousLinearMap.adjoint A (c j)‖ * ‖B (c j)‖ := by
      funext j
      rw [innerSL_apply_norm]
    rw [hnorm]
    exact deningerSummable_mul_of_sq hA hB (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  · intro x
    have h1 : HasSum (fun j => (c.repr (A x)) j • c j) (A x) := c.hasSum_repr (A x)
    have h2 := B.hasSum h1
    have heq : (fun j => (innerSL ℂ (ContinuousLinearMap.adjoint A (c j))) x • B (c j))
        = fun j => B ((c.repr (A x)) j • c j) := by
      funext j
      rw [map_smul]
      congr 1
      show (inner ℂ (ContinuousLinearMap.adjoint A (c j)) x : ℂ) = (c.repr (A x)) j
      rw [c.repr_apply_apply, ContinuousLinearMap.adjoint_inner_left]
    rw [heq]
    exact h2

end HilbertSchmidt

section TraceClass

variable {ι : Type} {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **A composite of Hilbert–Schmidt operators is trace class.** -/
theorem deningerMemSchattenClass_one_comp_of_hilbertSchmidt (c : HilbertBasis ι ℂ H)
    (A B : H →L[ℂ] H)
    (hA : DeningerIsHilbertSchmidtOn c (ContinuousLinearMap.adjoint A))
    (hB : DeningerIsHilbertSchmidtOn c B) :
    MemSchattenClass 1 (B.comp A) :=
  (deningerIsNuclear_comp_of_hilbertSchmidt c A B hA hB).memSchattenClass_one

end TraceClass

end RHTower

