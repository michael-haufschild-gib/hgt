/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisNormQuotientTransition

/-!
# Norm quotients and valuations descend through finite Galois towers

Norm transitivity gives a surjective projection from the norm quotient of a top field onto the
norm quotient of every intermediate field.  Thus finiteness, norm-surjectivity on valuation-zero
units, and the unramified norm-valuation formula all descend from one common finite top extension.

These facts let compatible finite local `H²` layers be constructed inside one extension, instead
of choosing unrelated cyclic extensions degree by degree.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

noncomputable section

/-- Every norm from the top of a finite scalar tower is already a norm from its middle field. -/
theorem cyclicGaloisH2BaseNormImage_tower_le
    (K L M : Type) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional L M] [FiniteDimensional K M] :
    cyclicGaloisH2BaseNormImage K M ≤ cyclicGaloisH2BaseNormImage K L := by
  intro a ha
  rcases ha with ⟨x, rfl⟩
  refine ⟨Additive.ofMul (Units.map (Algebra.norm L) (Additive.toMul x)), ?_⟩
  apply Additive.toMul.injective
  change cyclicGaloisNormUnits K L
      (Units.map (Algebra.norm L) (Additive.toMul x)) =
    cyclicGaloisNormUnits K M (Additive.toMul x)
  apply Units.ext
  change Algebra.norm K (Algebra.norm L ((Additive.toMul x : Mˣ) : M)) =
    Algebra.norm K ((Additive.toMul x : Mˣ) : M)
  exact Algebra.norm_norm (R := K) (S := L)

/-- Natural projection from a finer norm quotient to a coarser norm quotient. -/
noncomputable def cyclicGaloisH2BaseNormQuotientProjection
    (K L M : Type) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional L M] [FiniteDimensional K M] :
    Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K M →+
      Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K L :=
  QuotientAddGroup.lift (cyclicGaloisH2BaseNormImage K M)
    (QuotientAddGroup.mk' (cyclicGaloisH2BaseNormImage K L)) (by
      intro a ha
      rw [AddMonoidHom.mem_ker]
      exact (QuotientAddGroup.eq_zero_iff _).mpr
        (cyclicGaloisH2BaseNormImage_tower_le K L M ha))

theorem cyclicGaloisH2BaseNormQuotientProjection_surjective
    (K L M : Type) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional L M] [FiniteDimensional K M] :
    Function.Surjective (cyclicGaloisH2BaseNormQuotientProjection K L M) := by
  intro q
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk'_surjective
    (cyclicGaloisH2BaseNormImage K L) q
  exact ⟨QuotientAddGroup.mk a, rfl⟩

/-- Finiteness of the top norm quotient descends to every intermediate layer. -/
theorem cyclicGaloisH2BaseNormQuotient_finite_of_tower
    (K L M : Type) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional L M] [FiniteDimensional K M]
    [Finite (Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K M)] :
    Finite (Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K L) :=
  Finite.of_surjective (cyclicGaloisH2BaseNormQuotientProjection K L M)
    (cyclicGaloisH2BaseNormQuotientProjection_surjective K L M)

/-- Galois invariance of a top-field valuation descends to a normal intermediate field. -/
theorem valuation_comap_gal_invariant_of_tower
    (K L M Γ₀ : Type) [Field K] [Field L] [Field M]
    [LinearOrderedCommGroupWithZero Γ₀]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    [Normal K L] [Normal K M]
    (vM : Valuation M Γ₀)
    (hM : ∀ (σ : Gal(M/K)) (x : M), vM (σ x) = vM x) :
    ∀ (σ : Gal(L/K)) (x : L),
      vM.comap (algebraMap L M) (σ x) =
        vM.comap (algebraMap L M) x := by
  intro σ x
  obtain ⟨τ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective M σ
  rw [Valuation.comap_apply, Valuation.comap_apply]
  have hrestrict : algebraMap L M ((AlgEquiv.restrictNormalHom L τ) x) =
      τ (algebraMap L M x) :=
    AlgEquiv.restrictNormal_commutes τ L x
  rw [hrestrict]
  exact hM τ (algebraMap L M x)

/-- Norm-valuation formula on a normal intermediate field, inherited from an invariant top
valuation and its restriction to the base. -/
theorem tameValHom_norm_eq_pow_of_top_gal_invariant
    (K L M : Type) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    [FiniteDimensional K L] [IsGalois K L] [Normal K M]
    (vK : Valuation K (WithZero (Multiplicative ℤ)))
    (vM : Valuation M (WithZero (Multiplicative ℤ)))
    (hbase : ∀ x : K, vM (algebraMap K M x) = vK x)
    (hM : ∀ (σ : Gal(M/K)) (x : M), vM (σ x) = vM x)
    (x : Lˣ) :
    tameValHom vK (Units.map (Algebra.norm K) x) =
      (tameValHom (vM.comap (algebraMap L M)) x) ^ Module.finrank K L := by
  apply tameValHom_norm_eq_pow_of_valuation
  have hnorm := valuation_algebraMap_norm_eq_pow_of_gal_invariant
    (vM.comap (algebraMap L M))
    (valuation_comap_gal_invariant_of_tower K L M
      (WithZero (Multiplicative ℤ)) vM hM) (x : L)
  calc
    vK (Algebra.norm K (x : L)) =
        vM (algebraMap K M (Algebra.norm K (x : L))) :=
      (hbase (Algebra.norm K (x : L))).symm
    _ = vM (algebraMap L M (algebraMap K L (Algebra.norm K (x : L)))) := by
      rw [IsScalarTower.algebraMap_apply K L M]
    _ = (vM.comap (algebraMap L M) (x : L)) ^ Module.finrank K L := hnorm

/-- Norm surjectivity on any chosen set of base units descends from a finite top field to every
intermediate field. -/
theorem cyclicGaloisNormUnits_exists_of_tower
    (K L M : Type) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional L M] [FiniteDimensional K M]
    (a : Kˣ) (ha : ∃ x : Mˣ, cyclicGaloisNormUnits K M x = a) :
    ∃ y : Lˣ, cyclicGaloisNormUnits K L y = a := by
  obtain ⟨x, hx⟩ := ha
  refine ⟨Units.map (Algebra.norm L) x, ?_⟩
  apply Units.ext
  change Algebra.norm K (Algebra.norm L (x : M)) = (a : K)
  rw [Algebra.norm_norm]
  exact congrArg Units.val hx

/-- Surjectivity of the norm on valuation-zero units descends through a finite scalar tower. -/
theorem tameValHom_norm_zero_surjective_of_tower
    (K L M : Type) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional L M] [FiniteDimensional K M]
    (vK : Valuation K (WithZero (Multiplicative ℤ)))
    (hzeroM : ∀ a : Kˣ, tameValHom vK a = 1 →
      ∃ b : Mˣ, Units.map (Algebra.norm K) b = a) :
    ∀ a : Kˣ, tameValHom vK a = 1 →
      ∃ b : Lˣ, Units.map (Algebra.norm K) b = a := by
  intro a ha
  exact cyclicGaloisNormUnits_exists_of_tower K L M a (hzeroM a ha)

end


end GaloisForLFunctions.HTGeometry.ABHN
