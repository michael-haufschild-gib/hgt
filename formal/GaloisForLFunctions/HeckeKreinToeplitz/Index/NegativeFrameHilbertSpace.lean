import GaloisForLFunctions.HeckeKreinToeplitz.Index.NegativeColumnFrames
import GaloisForLFunctions.HeckeKreinToeplitz.Index.FiniteNegativeDirections
import Mathlib.Analysis.InnerProductSpace.Completion

/-!
# Hilbert geometry from a maximal negative frame

A normalized negative frame with nonnegative orthogonal complement splits
the column space into a positive inner product space and a finite negative
Euclidean factor. The projection is the original vector plus its pairings
against the negative frame.
-/

noncomputable section
set_option autoImplicit false
open Complex Finset
open scoped ComplexConjugate InnerProductSpace

namespace GaloisForLFunctions.HeckeKreinToeplitz.NegativeFrame

variable {G : Type*} [Group G] {k : G → ℂ} {m : ℕ}

/-- Orthogonal complement of a finite column frame. -/
def complement (e : Fin m → kernelColumnSpan k) : Submodule ℂ (kernelColumnSpan k) :=
  ⨅ i, (kernelColumnPairing k (e i)).ker

/-- The complement carries the positive column inner product. -/
def Space (_hk : IsHermKernel k) (e : Fin m → kernelColumnSpan k)
    (_he : IsNegativeColumnFrame e)
    (_hp : ∀ v : kernelColumnSpan k, (∀ i, kernelColumnPairing k (e i) v = 0) →
      0 ≤ (kernelColumnPairing k v v).re) := ↥(complement e)

variable (hk : IsHermKernel k) (e : Fin m → kernelColumnSpan k)
    (he : IsNegativeColumnFrame e)
    (hp : ∀ v : kernelColumnSpan k, (∀ i, kernelColumnPairing k (e i) v = 0) →
      0 ≤ (kernelColumnPairing k v v).re)

instance : AddCommGroup (Space hk e he hp) := inferInstanceAs (AddCommGroup ↥(complement e))
instance : Module ℂ (Space hk e he hp) := inferInstanceAs (Module ℂ ↥(complement e))

/-- Inclusion of the positive complement into the column space. -/
def inclusion : Space hk e he hp →ₗ[ℂ] kernelColumnSpan k := (complement e).subtype

theorem orthogonal (v : Space hk e he hp) (i : Fin m) :
    kernelColumnPairing k (e i) (inclusion hk e he hp v) = 0 :=
  (Submodule.mem_iInf _).mp v.property i

instance core : InnerProductSpace.Core ℂ (Space hk e he hp) where
  inner v w := kernelColumnPairing k (inclusion hk e he hp v) (inclusion hk e he hp w)
  conj_inner_symm v w := (kernelColumnPairing_conj_symm hk _ _).symm
  re_inner_nonneg v := hp _ (orthogonal hk e he hp v)
  add_left v w z := kernelColumnPairing_add_left hk _ _ _
  smul_left v w c := kernelColumnPairing_smul_left hk c _ _
  definite v hv := by
    apply Subtype.ext
    exact kernelColumnPairing_definite_on_frame_complement hk he hp
      (orthogonal hk e he hp v) hv

instance : NormedAddCommGroup (Space hk e he hp) :=
  (core hk e he hp).toNormedAddCommGroup
instance : InnerProductSpace ℂ (Space hk e he hp) := InnerProductSpace.ofCore _

theorem inner_def (v w : Space hk e he hp) : inner ℂ v w =
    kernelColumnPairing k (inclusion hk e he hp v) (inclusion hk e he hp w) := rfl

/-- Projection along the negative frame onto its positive complement. -/
def projection : kernelColumnSpan k →ₗ[ℂ] Space hk e he hp where
  toFun v := ⟨v + ∑ i, kernelColumnPairing k (e i) v • e i, by
    apply (Submodule.mem_iInf _).mpr
    intro i
    change kernelColumnPairing k (e i) (v + ∑ j, kernelColumnPairing k (e j) v • e j) = 0
    rw [map_add, he.pairing_sum]
    exact add_neg_cancel _⟩
  map_add' v w := by
    apply Subtype.ext
    change (v + w) + ∑ i, kernelColumnPairing k (e i) (v + w) • e i =
      (v + ∑ i, kernelColumnPairing k (e i) v • e i) +
      (w + ∑ i, kernelColumnPairing k (e i) w • e i)
    simp only [map_add, add_smul, Finset.sum_add_distrib]
    abel
  map_smul' c v := by
    apply Subtype.ext
    change c • v + ∑ i, kernelColumnPairing k (e i) (c • v) • e i =
      c • (v + ∑ i, kernelColumnPairing k (e i) v • e i)
    simp only [map_smul, smul_add, Finset.smul_sum, smul_smul, smul_eq_mul]

/-- Negative coordinates are the negatives of the frame pairings. -/
def coordinates : kernelColumnSpan k →ₗ[ℂ] EuclideanSpace ℂ (Fin m) :=
  (WithLp.linearEquiv 2 ℂ (Fin m → ℂ)).symm.toLinearMap.comp
    (LinearMap.pi fun i => -(kernelColumnPairing k (e i)))

theorem coordinates_apply (v : kernelColumnSpan k) (i : Fin m) :
    coordinates e v i = -kernelColumnPairing k (e i) v := rfl

/-- Orthogonal splitting into the positive complement and the negative Euclidean factor. -/
def splitting : kernelColumnSpan k ≃ₗ[ℂ] (Space hk e he hp × EuclideanSpace ℂ (Fin m)) where
  toFun v := (projection hk e he hp v, coordinates e v)
  invFun v := inclusion hk e he hp v.1 + ∑ i, v.2 i • e i
  left_inv v := by
    change (v + ∑ i, kernelColumnPairing k (e i) v • e i) +
      (∑ i, (-kernelColumnPairing k (e i) v) • e i) = v
    rw [add_assoc, ← Finset.sum_add_distrib]
    simp only [← add_smul, add_neg_cancel, zero_smul, sum_const_zero, add_zero]
  right_inv v := by
    have h (i : Fin m) : kernelColumnPairing k (e i)
        (inclusion hk e he hp v.1 + ∑ j, v.2 j • e j) = -v.2 i := by
      rw [map_add, orthogonal, he.pairing_sum, zero_add]
    apply Prod.ext
    · apply Subtype.ext
      change (inclusion hk e he hp v.1 + ∑ j, v.2 j • e j) +
        (∑ i, kernelColumnPairing k (e i)
          (inclusion hk e he hp v.1 + ∑ j, v.2 j • e j) • e i) =
        inclusion hk e he hp v.1
      simp only [h]
      rw [add_assoc, ← Finset.sum_add_distrib]
      simp only [← add_smul, add_neg_cancel, zero_smul, sum_const_zero, add_zero]
    · apply (WithLp.linearEquiv 2 ℂ (Fin m → ℂ)).injective
      funext i
      change -kernelColumnPairing k (e i)
        (inclusion hk e he hp v.1 + ∑ j, v.2 j • e j) = v.2 i
      rw [h, neg_neg]
  map_add' v w := Prod.ext (map_add _ v w) (map_add _ v w)
  map_smul' c v := Prod.ext (map_smul _ c v) (map_smul _ c v)

theorem pairing_inclusion_sum (v : Space hk e he hp) (c : Fin m → ℂ) :
    kernelColumnPairing k (inclusion hk e he hp v) (∑ i, c i • e i) = 0 := by
  have ho (i : Fin m) : kernelColumnPairing k (inclusion hk e he hp v) (e i) = 0 := by
    rw [kernelColumnPairing_conj_symm hk, orthogonal, map_zero]
  simp only [map_sum, map_smul, ho, smul_zero, sum_const_zero]

include hk he in
theorem pairing_sum_sum (a b : EuclideanSpace ℂ (Fin m)) :
    kernelColumnPairing k (∑ i, a i • e i) (∑ i, b i • e i) = -inner ℂ a b := by
  change kernelColumnPairing k (kernelColumnSynthesis e fun i => a i) (∑ i, b i • e i) = _
  rw [kernelColumnPairing_synthesis hk]
  simp only [he.pairing_sum, mul_neg, sum_neg_distrib, PiLp.inner_apply, RCLike.inner_apply']

/-- The column form becomes the difference of the positive and negative Hilbert forms. -/
theorem pairing_splitting_symm
    (v w : Space hk e he hp × EuclideanSpace ℂ (Fin m)) :
    kernelColumnPairing k ((splitting hk e he hp).symm v)
      ((splitting hk e he hp).symm w) = FiniteNegative.pairing v w := by
  have hleft : kernelColumnPairing k (∑ i, v.2 i • e i) (inclusion hk e he hp w.1) = 0 := by
    rw [kernelColumnPairing_conj_symm hk, pairing_inclusion_sum, map_zero]
  change kernelColumnPairing k (inclusion hk e he hp v.1 + ∑ i, v.2 i • e i)
    (inclusion hk e he hp w.1 + ∑ i, w.2 i • e i) = _
  rw [kernelColumnPairing_add_left hk, map_add, map_add, pairing_inclusion_sum,
    hleft, pairing_sum_sum hk e he]
  simp only [add_zero, zero_add]
  rfl

theorem pairing_splitting (v w : kernelColumnSpan k) :
    FiniteNegative.pairing (splitting hk e he hp v) (splitting hk e he hp w) =
      kernelColumnPairing k v w := by
  simpa only [LinearEquiv.symm_apply_apply] using
    (pairing_splitting_symm hk e he hp (splitting hk e he hp v) (splitting hk e he hp w)).symm

#print axioms pairing_splitting

end GaloisForLFunctions.HeckeKreinToeplitz.NegativeFrame
