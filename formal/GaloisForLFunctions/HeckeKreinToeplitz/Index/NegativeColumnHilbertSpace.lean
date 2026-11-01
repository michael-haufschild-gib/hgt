import GaloisForLFunctions.HeckeKreinToeplitz.Index.NegativeColumnComplement
import GaloisForLFunctions.HeckeKreinToeplitz.Index.OneNegativeDirection
import Mathlib.Analysis.InnerProductSpace.Completion

/-!
# Hilbert completion of the positive column complement

Splitting off a column of square `-1` identifies the column form with one
negative scalar direction and a positive inner product. Completing only the
positive part gives a dense, form-preserving realization in a complete
index-one space.
-/

noncomputable section
set_option autoImplicit false
open Complex UniformSpace
open scoped ComplexConjugate InnerProductSpace

namespace GaloisForLFunctions.HeckeKreinToeplitz.NegativeColumn

variable {G : Type*} [Group G] {k : G → ℂ}

/-- Positive orthogonal complement, equipped below with its column inner product. -/
def Space (_hk : IsHermKernel k) (_hi : negIndex k ≤ 1)
    (e : kernelColumnSpan k) (_he : kernelColumnPairing k e e = -1) :=
  ↥(kernelColumnPairing k e).ker

variable (hk : IsHermKernel k) (hi : negIndex k ≤ 1)
    (e : kernelColumnSpan k) (he : kernelColumnPairing k e e = -1)

instance : AddCommGroup (Space hk hi e he) :=
  inferInstanceAs (AddCommGroup ↥(kernelColumnPairing k e).ker)

instance : Module ℂ (Space hk hi e he) :=
  inferInstanceAs (Module ℂ ↥(kernelColumnPairing k e).ker)

/-- Inclusion into the algebraic column space. -/
def inclusion : Space hk hi e he →ₗ[ℂ] kernelColumnSpan k :=
  (kernelColumnPairing k e).ker.subtype

theorem orthogonal (v : Space hk hi e he) :
    kernelColumnPairing k e (inclusion hk hi e he v) = 0 := v.property

instance core : InnerProductSpace.Core ℂ (Space hk hi e he) where
  inner v w := kernelColumnPairing k (inclusion hk hi e he v) (inclusion hk hi e he w)
  conj_inner_symm v w := (kernelColumnPairing_conj_symm hk _ _).symm
  re_inner_nonneg v := kernelColumnPairing_nonneg_of_orthogonal_negative hk hi
    (by rw [he]; norm_num) (orthogonal hk hi e he v)
  add_left v w z := kernelColumnPairing_add_left hk _ _ _
  smul_left v w c := kernelColumnPairing_smul_left hk c _ _
  definite v hv := by
    apply Subtype.ext
    exact kernelColumnPairing_definite_on_negative_complement hk hi he
      (orthogonal hk hi e he v) hv

instance : NormedAddCommGroup (Space hk hi e he) :=
  (core hk hi e he).toNormedAddCommGroup

instance : InnerProductSpace ℂ (Space hk hi e he) := InnerProductSpace.ofCore _

theorem inner_def (v w : Space hk hi e he) :
    inner ℂ v w = kernelColumnPairing k (inclusion hk hi e he v)
      (inclusion hk hi e he w) := rfl

/-- Orthogonal projection onto the positive complement. -/
def projection : kernelColumnSpan k →ₗ[ℂ] Space hk hi e he where
  toFun v := ⟨v + kernelColumnPairing k e v • e, by
    change kernelColumnPairing k e (v + kernelColumnPairing k e v • e) = 0
    rw [map_add, map_smul, smul_eq_mul, he]
    ring⟩
  map_add' v w := by
    apply Subtype.ext
    change (v + w) + kernelColumnPairing k e (v + w) • e =
      (v + kernelColumnPairing k e v • e) + (w + kernelColumnPairing k e w • e)
    rw [map_add, add_smul]
    abel
  map_smul' c v := by
    apply Subtype.ext
    change c • v + kernelColumnPairing k e (c • v) • e =
      c • (v + kernelColumnPairing k e v • e)
    simp only [map_smul, smul_add, smul_smul, smul_eq_mul]

/-- Algebraic orthogonal splitting into a positive space and one negative coordinate. -/
def splitting : kernelColumnSpan k ≃ₗ[ℂ] (Space hk hi e he × ℂ) where
  toFun v := (projection hk hi e he v, -kernelColumnPairing k e v)
  invFun v := inclusion hk hi e he v.1 + v.2 • e
  left_inv v := by
    change (v + kernelColumnPairing k e v • e) + (-kernelColumnPairing k e v) • e = v
    rw [add_assoc, ← add_smul, add_neg_cancel, zero_smul, add_zero]
  right_inv v := by
    have h : kernelColumnPairing k e (inclusion hk hi e he v.1 + v.2 • e) = -v.2 := by
      rw [map_add, map_smul, orthogonal, smul_eq_mul, he]
      ring
    apply Prod.ext
    · apply Subtype.ext
      change (inclusion hk hi e he v.1 + v.2 • e) +
        kernelColumnPairing k e (inclusion hk hi e he v.1 + v.2 • e) • e =
          inclusion hk hi e he v.1
      rw [h, add_assoc, ← add_smul, add_neg_cancel, zero_smul, add_zero]
    · change -kernelColumnPairing k e (inclusion hk hi e he v.1 + v.2 • e) = v.2
      rw [h, neg_neg]
  map_add' v w := by
    apply Prod.ext
    · exact map_add _ v w
    · exact (map_add (-(kernelColumnPairing k e)) v w)
  map_smul' c v := by
    apply Prod.ext
    · exact map_smul _ c v
    · exact (map_smul (-(kernelColumnPairing k e)) c v)

theorem pairing_splitting_symm (v w : Space hk hi e he × ℂ) :
    kernelColumnPairing k ((splitting hk hi e he).symm v)
      ((splitting hk hi e he).symm w) = IndexOne.pairing v w := by
  have hv : kernelColumnPairing k (inclusion hk hi e he v.1) e = 0 := by
    rw [kernelColumnPairing_conj_symm hk, orthogonal, map_zero]
  change kernelColumnPairing k (inclusion hk hi e he v.1 + v.2 • e)
    (inclusion hk hi e he w.1 + w.2 • e) = _
  rw [kernelColumnPairing_add_left hk, kernelColumnPairing_smul_left hk,
    map_add, map_smul, map_add, map_smul, orthogonal, hv, he]
  simp only [smul_eq_mul, mul_zero, add_zero, zero_add, mul_neg, mul_one]
  rfl

theorem pairing_splitting (v w : kernelColumnSpan k) :
    IndexOne.pairing (splitting hk hi e he v) (splitting hk hi e he w) =
      kernelColumnPairing k v w := by
  simpa only [LinearEquiv.symm_apply_apply] using
    (pairing_splitting_symm hk hi e he (splitting hk hi e he v)
      (splitting hk hi e he w)).symm

end GaloisForLFunctions.HeckeKreinToeplitz.NegativeColumn
