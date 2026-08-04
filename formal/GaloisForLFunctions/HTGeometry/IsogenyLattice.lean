import GaloisForLFunctions.HTGeometry.IsogenyRegular
import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient

/-!
# Isogenies of lattices

A finite free `ℤ`-module is isogeny-regular, and an endomorphism of it is an isogeny exactly when
its determinant is nonzero.  In that case the kernel is trivial and the cokernel has order
`|det|`, so the degree of the isogeny is `1 / |det|`.

The reciprocal is not an artefact of a bad convention: lattices carry isogenies contravariantly,
and the general degree `|ker| / |coker|` assigns the reciprocal weight to an injection exactly so
that it composes correctly against the surjective convention used for tori and abelian varieties.

The rank of a lattice is recovered from the degree of multiplication by `n`, which is
`n ^ (-rank)`.  Since that degree is an isogeny invariant, isogenous lattices have equal rank.
-/

open Module

variable {L L₁ L₂ : Type*} [AddCommGroup L] [Module.Free ℤ L] [Module.Finite ℤ L]
  [AddCommGroup L₁] [Module.Free ℤ L₁] [Module.Finite ℤ L₁]
  [AddCommGroup L₂] [Module.Free ℤ L₂] [Module.Finite ℤ L₂]

namespace LinearMap

/-- An endomorphism of a finite free `ℤ`-module with nonzero determinant is injective. -/
theorem injective_of_det_ne_zero {φ : L →ₗ[ℤ] L} (hφ : LinearMap.det φ ≠ 0) :
    Function.Injective φ := by
  rw [← LinearMap.ker_eq_bot]
  by_contra h
  exact hφ (LinearMap.det_eq_zero_iff_ker_ne_bot.2 h)

/-- The cokernel of an injective endomorphism of a finite free `ℤ`-module has order `|det|`. -/
theorem card_quotient_range_eq_natAbs_det {φ : L →ₗ[ℤ] L} (hinj : Function.Injective φ) :
    Nat.card (L ⧸ LinearMap.range φ) = (LinearMap.det φ).natAbs := by
  have key := Submodule.natAbs_det_equiv (LinearMap.range φ) (LinearEquiv.ofInjective φ hinj)
  have heq : (LinearMap.range φ).subtype ∘ₗ
      AddMonoidHom.toIntLinearMap ((LinearEquiv.ofInjective φ hinj : L ≃ₗ[ℤ] _) : L →+ _) = φ := by
    ext x
    simp
  rw [heq] at key
  exact key.symm

omit [Module.Free ℤ L₁] [Module.Finite ℤ L₁] [Module.Free ℤ L₂] [Module.Finite ℤ L₂] in
/-- The additive range of a `ℤ`-linear map is the additive subgroup underlying its linear
range. -/
theorem toAddMonoidHom_range (φ : L₁ →ₗ[ℤ] L₂) :
    (φ.toAddMonoidHom).range = (LinearMap.range φ).toAddSubgroup := by
  ext x
  simp [LinearMap.mem_range, AddMonoidHom.mem_range]

/-- The kernel of an endomorphism with nonzero determinant is trivial. -/
theorem kerCard_toAddMonoidHom_of_det_ne_zero {φ : L →ₗ[ℤ] L} (hφ : LinearMap.det φ ≠ 0) :
    (φ.toAddMonoidHom).kerCard = 1 := by
  rw [AddMonoidHom.kerCard, (AddMonoidHom.ker_eq_bot_iff _).2 (injective_of_det_ne_zero hφ)]
  simp

/-- The cokernel of an endomorphism with nonzero determinant has order `|det|`. -/
theorem cokerCard_toAddMonoidHom_of_det_ne_zero {φ : L →ₗ[ℤ] L} (hφ : LinearMap.det φ ≠ 0) :
    (φ.toAddMonoidHom).cokerCard = (LinearMap.det φ).natAbs := by
  rw [AddMonoidHom.cokerCard_eq_card_quotient, toAddMonoidHom_range]
  exact card_quotient_range_eq_natAbs_det (injective_of_det_ne_zero hφ)

/-- **An endomorphism of a lattice is an isogeny exactly when its determinant is nonzero.** -/
theorem isAddIsogeny_toAddMonoidHom_of_det_ne_zero {φ : L →ₗ[ℤ] L} (hφ : LinearMap.det φ ≠ 0) :
    IsAddIsogeny (φ.toAddMonoidHom) := by
  refine ⟨?_, ?_⟩
  · rw [(AddMonoidHom.ker_eq_bot_iff _).2 (injective_of_det_ne_zero hφ)]
    infer_instance
  · rw [toAddMonoidHom_range]
    refine Nat.finite_of_card_ne_zero ?_
    rw [show Nat.card (L ⧸ (LinearMap.range φ).toAddSubgroup)
        = Nat.card (L ⧸ LinearMap.range φ) from rfl,
      card_quotient_range_eq_natAbs_det (injective_of_det_ne_zero hφ)]
    simpa using hφ

/-- The degree of a lattice isogeny is the reciprocal of the absolute determinant. -/
theorem isogenyDegree_toAddMonoidHom_of_det_ne_zero {φ : L →ₗ[ℤ] L} (hφ : LinearMap.det φ ≠ 0) :
    (φ.toAddMonoidHom).isogenyDegree = 1 / ((LinearMap.det φ).natAbs : ℚ) := by
  rw [AddMonoidHom.isogenyDegree, kerCard_toAddMonoidHom_of_det_ne_zero hφ,
    cokerCard_toAddMonoidHom_of_det_ne_zero hφ]
  norm_num

end LinearMap

namespace IsogenyLattice

omit [Module.Free ℤ L] [Module.Finite ℤ L] in
/-- Multiplication by `n` on a lattice is the scalar endomorphism `n • id`. -/
theorem nsmulAddMonoidHom_eq (n : ℕ) :
    (nsmulAddMonoidHom n : L →+ L) = (((n : ℤ) • LinearMap.id : L →ₗ[ℤ] L)).toAddMonoidHom := by
  ext x
  simp

omit [Module.Finite ℤ L] in
/-- The determinant of multiplication by `n` on a lattice is `n ^ rank`. -/
theorem det_nsmul (n : ℕ) :
    LinearMap.det (((n : ℤ) • LinearMap.id : L →ₗ[ℤ] L)) = (n : ℤ) ^ finrank ℤ L := by
  rw [LinearMap.det_smul, LinearMap.det_id, mul_one]

/-- Lattices are isogeny-regular. -/
instance (priority := 100) isAddIsogenyRegular : IsAddIsogenyRegular L where
  isogeny_nsmul n hn := by
    rw [nsmulAddMonoidHom_eq n]
    refine LinearMap.isAddIsogeny_toAddMonoidHom_of_det_ne_zero ?_
    rw [det_nsmul n]
    exact pow_ne_zero _ (by exact_mod_cast hn.ne')

/-- The degree of multiplication by `n` on a lattice is `n ^ (-rank)`. -/
theorem isogenyDegree_nsmulAddMonoidHom (n : ℕ) (hn : 0 < n) :
    (nsmulAddMonoidHom n : L →+ L).isogenyDegree = 1 / ((n ^ finrank ℤ L : ℕ) : ℚ) := by
  have hdet : LinearMap.det (((n : ℤ) • LinearMap.id : L →ₗ[ℤ] L)) ≠ 0 := by
    rw [det_nsmul n]
    exact pow_ne_zero _ (by exact_mod_cast hn.ne')
  rw [nsmulAddMonoidHom_eq n, LinearMap.isogenyDegree_toAddMonoidHom_of_det_ne_zero hdet,
    det_nsmul n]
  norm_num

/-- **Isogenous lattices have equal rank.**  The rank is read off from the degree of
multiplication by `2`, which is an isogeny invariant. -/
theorem finrank_eq_of_isAddIsogeny {f : L₁ →+ L₂} (hf : IsAddIsogeny f) :
    finrank ℤ L₁ = finrank ℤ L₂ := by
  have hinv := AddMonoidHom.isogenyDegree_nsmul_eq_of_isogeny (G := L₁) (H := L₂) hf 2 two_pos
  rw [isogenyDegree_nsmulAddMonoidHom 2 two_pos, isogenyDegree_nsmulAddMonoidHom 2 two_pos] at hinv
  have hpos₁ : (0 : ℚ) < ((2 ^ finrank ℤ L₁ : ℕ) : ℚ) := by positivity
  have hpos₂ : (0 : ℚ) < ((2 ^ finrank ℤ L₂ : ℕ) : ℚ) := by positivity
  have hEq : ((2 ^ finrank ℤ L₂ : ℕ) : ℚ) = ((2 ^ finrank ℤ L₁ : ℕ) : ℚ) := by
    field_simp at hinv
    linarith [hinv]
  have : (2 : ℕ) ^ finrank ℤ L₂ = 2 ^ finrank ℤ L₁ := by exact_mod_cast hEq
  exact (Nat.pow_right_injective le_rfl this).symm

end IsogenyLattice
