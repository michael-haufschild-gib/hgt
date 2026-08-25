/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisH2CarryNormQuotient

/-!
# Genuine inflation in carry-cocycle coordinates

For finite cyclic norm quotients, every degree-two class has an explicit carry-cocycle
representative.  The explicit carry computation therefore upgrades from a formula on selected
classes to equality of genuine group-cohomological inflation with the orientation-corrected
norm-quotient transition.

Under split valuation coordinates this is finite-torsion inclusion, twisted only by the unit
recording the chosen-generator orientation.  Consequently actual ordinary and continuous
inflation are injective.  These are the directed-system facts needed before an unramified local
`H²` colimit can be compared with the full local Brauer group.
-/

open CategoryTheory Representation

namespace GaloisForLFunctions.HTGeometry.ABHN

noncomputable section

/-- Orientation-corrected norm-quotient transition in literal carry-cocycle coordinates. -/
noncomputable def cyclicGaloisH2OrientedCarryNormQuotientTransition
    (K L M : Type) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional L M] [FiniteDimensional K M]
    [IsGalois K L] [IsGalois K M]
    [IsCyclic Gal(L/K)] [IsCyclic Gal(M/K)]
    [Finite (Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K L)]
    [Finite (Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K M)] :
    cyclicGaloisH2 K L →+ cyclicGaloisH2 K M :=
  (cyclicGaloisRestrictionOrientation K L M).val •
    cyclicGaloisH2CarryNormQuotientTransition K L M

@[simp] theorem cyclicGaloisH2OrientedCarryNormQuotientTransition_carryClass
    (K L M : Type) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional L M] [FiniteDimensional K M]
    [IsGalois K L] [IsGalois K M]
    [IsCyclic Gal(L/K)] [IsCyclic Gal(M/K)]
    [Finite (Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K L)]
    [Finite (Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K M)]
    (a : Additive Kˣ) :
    cyclicGaloisH2OrientedCarryNormQuotientTransition K L M
        (cyclicGaloisCarryH2Class K L a) =
      cyclicGaloisCarryH2Class K M
        (((cyclicGaloisRestrictionOrientation K L M).val * Module.finrank L M) • a) := by
  change (cyclicGaloisRestrictionOrientation K L M).val •
      cyclicGaloisH2CarryNormQuotientTransition K L M
        (cyclicGaloisCarryH2Class K L a) = _
  rw [cyclicGaloisH2CarryNormQuotientTransition_carryClass]
  change (cyclicGaloisRestrictionOrientation K L M).val •
      cyclicGaloisCarryH2ClassHom K M (Module.finrank L M • a) =
    cyclicGaloisCarryH2ClassHom K M
      (((cyclicGaloisRestrictionOrientation K L M).val * Module.finrank L M) • a)
  rw [← map_nsmul, mul_nsmul]
  rw [smul_smul, smul_smul, Nat.mul_comm]

/-- Genuine group-cohomological inflation is the orientation-corrected transition in literal
carry-cocycle coordinates. -/
theorem cyclicGaloisH2Inflation_eq_orientedCarryNormQuotientTransition
    (K L M : Type) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional L M] [FiniteDimensional K M]
    [IsGalois K L] [IsGalois K M]
    [IsCyclic Gal(L/K)] [IsCyclic Gal(M/K)]
    [Finite (Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K L)]
    [Finite (Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K M)] :
    (groupCohomology.map
        (AlgEquiv.restrictNormalHom (F := K) (K₁ := M) L)
        (galoisTowerUnitsRepresentationHom K L M) 2).hom.toAddMonoidHom =
      cyclicGaloisH2OrientedCarryNormQuotientTransition K L M := by
  apply AddMonoidHom.ext
  intro z
  obtain ⟨a, rfl⟩ := cyclicGaloisCarryH2Class_surjective K L z
  change (groupCohomology.map
      (AlgEquiv.restrictNormalHom (F := K) (K₁ := M) L)
      (galoisTowerUnitsRepresentationHom K L M) 2).hom
        (cyclicGaloisCarryH2Class K L a) = _
  rw [cyclicGaloisCarryH2Class_inflation,
    cyclicGaloisH2OrientedCarryNormQuotientTransition_carryClass]

/-- Carry-normalized split-valuation coordinates send norm-quotient refinement to canonical
finite-torsion inclusion. -/
theorem cyclicGaloisCarryH2SplitValuationEquiv_transition
    (K L M : Type) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional L M] [FiniteDimensional K M]
    [IsGalois K L] [IsGalois K M]
    [IsCyclic Gal(L/K)] [IsCyclic Gal(M/K)]
    [Finite (Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K L)]
    [Finite (Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K M)]
    (vK : Valuation K (WithZero (Multiplicative ℤ)))
    (vL : Valuation L (WithZero (Multiplicative ℤ)))
    (vM : Valuation M (WithZero (Multiplicative ℤ))) (u : Kˣ)
    (hu : Multiplicative.toAdd (tameValHom vK u) = 1)
    (hvalKL : ∀ x : Lˣ,
      tameValHom vK (Units.map (Algebra.norm K) x) =
        (tameValHom vL x) ^ Module.finrank K L)
    (hzeroKL : ∀ a : Kˣ, tameValHom vK a = 1 →
      ∃ b : Lˣ, Units.map (Algebra.norm K) b = a)
    (hvalKM : ∀ x : Mˣ,
      tameValHom vK (Units.map (Algebra.norm K) x) =
        (tameValHom vM x) ^ Module.finrank K M)
    (hzeroKM : ∀ a : Kˣ, tameValHom vK a = 1 →
      ∃ b : Mˣ, Units.map (Algebra.norm K) b = a) :
    (cyclicGaloisCarryH2SplitValuationEquiv K M vK vM
      (Module.finrank K M) u hu rfl hvalKM hzeroKM).toAddMonoidHom.comp
        (cyclicGaloisH2CarryNormQuotientTransition K L M) =
      (zmodRatModIntTransition Module.finrank_pos.ne' Module.finrank_pos.ne'
        ⟨Module.finrank L M, (Module.finrank_mul_finrank K L M).symm⟩).comp
        (cyclicGaloisCarryH2SplitValuationEquiv K L vK vL
          (Module.finrank K L) u hu rfl hvalKL hzeroKL).toAddMonoidHom := by
  apply AddMonoidHom.ext
  intro z
  obtain ⟨a, rfl⟩ := cyclicGaloisCarryH2Class_surjective K L z
  rw [AddMonoidHom.comp_apply, cyclicGaloisH2CarryNormQuotientTransition_carryClass]
  change cyclicGaloisCarryH2SplitValuationEquiv K M vK vM
      (Module.finrank K M) u hu rfl hvalKM hzeroKM
        (cyclicGaloisCarryH2Class K M (Module.finrank L M • a)) =
    zmodRatModIntTransition Module.finrank_pos.ne' Module.finrank_pos.ne'
      ⟨Module.finrank L M, (Module.finrank_mul_finrank K L M).symm⟩
      (cyclicGaloisCarryH2SplitValuationEquiv K L vK vL
        (Module.finrank K L) u hu rfl hvalKL hzeroKL
          (cyclicGaloisCarryH2Class K L a))
  rw [cyclicGaloisCarryH2SplitValuationEquiv_apply,
    cyclicGaloisCarryH2SplitValuationEquiv_apply]
  rw [map_nsmul]
  change Module.finrank L M •
      (((Multiplicative.toAdd (tameValHom vK (Additive.toMul a)) : ℤ)) :
        ZMod (Module.finrank K M)) =
    zmodRatModIntTransition Module.finrank_pos.ne' Module.finrank_pos.ne'
      ⟨Module.finrank L M, (Module.finrank_mul_finrank K L M).symm⟩
      (((Multiplicative.toAdd (tameValHom vK (Additive.toMul a)) : ℤ)) :
        ZMod (Module.finrank K L))
  rw [zmodRatModIntTransition_intCast Module.finrank_pos.ne'
    Module.finrank_pos.ne' (Module.finrank_mul_finrank K L M)]
  simp [nsmul_eq_mul]

/-- Genuine inflation is orientation multiplication followed by finite-torsion inclusion in
carry-normalized split-valuation coordinates. -/
theorem cyclicGaloisH2Inflation_carrySplitValuationInvariant
    (K L M : Type) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional L M] [FiniteDimensional K M]
    [IsGalois K L] [IsGalois K M]
    [IsCyclic Gal(L/K)] [IsCyclic Gal(M/K)]
    (vK : Valuation K (WithZero (Multiplicative ℤ)))
    (vL : Valuation L (WithZero (Multiplicative ℤ)))
    (vM : Valuation M (WithZero (Multiplicative ℤ))) (u : Kˣ)
    (hu : Multiplicative.toAdd (tameValHom vK u) = 1)
    (hvalKL : ∀ x : Lˣ,
      tameValHom vK (Units.map (Algebra.norm K) x) =
        (tameValHom vL x) ^ Module.finrank K L)
    (hzeroKL : ∀ a : Kˣ, tameValHom vK a = 1 →
      ∃ b : Lˣ, Units.map (Algebra.norm K) b = a)
    (hvalKM : ∀ x : Mˣ,
      tameValHom vK (Units.map (Algebra.norm K) x) =
        (tameValHom vM x) ^ Module.finrank K M)
    (hzeroKM : ∀ a : Kˣ, tameValHom vK a = 1 →
      ∃ b : Mˣ, Units.map (Algebra.norm K) b = a)
    (z : cyclicGaloisH2 K L) :
    cyclicGaloisCarryH2SplitValuationEquiv K M vK vM
        (Module.finrank K M) u hu rfl hvalKM hzeroKM
        ((groupCohomology.map
          (AlgEquiv.restrictNormalHom (F := K) (K₁ := M) L)
          (galoisTowerUnitsRepresentationHom K L M) 2).hom z) =
      (cyclicGaloisRestrictionOrientation K L M).val •
        zmodRatModIntTransition Module.finrank_pos.ne' Module.finrank_pos.ne'
          ⟨Module.finrank L M, (Module.finrank_mul_finrank K L M).symm⟩
          (cyclicGaloisCarryH2SplitValuationEquiv K L vK vL
            (Module.finrank K L) u hu rfl hvalKL hzeroKL z) := by
  letI : NeZero (Module.finrank K L) :=
    ⟨Nat.ne_of_gt (Module.finrank_pos (R := K) (M := L))⟩
  letI : NeZero (Module.finrank K M) :=
    ⟨Nat.ne_of_gt (Module.finrank_pos (R := K) (M := M))⟩
  let qEquivL := cyclicGaloisH2BaseNormQuotientSplitValuationEquiv
    K L vK vL (Module.finrank K L) u hu rfl hvalKL hzeroKL
  let qEquivM := cyclicGaloisH2BaseNormQuotientSplitValuationEquiv
    K M vK vM (Module.finrank K M) u hu rfl hvalKM hzeroKM
  letI : Finite (Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K L) :=
    Finite.of_injective qEquivL qEquivL.injective
  letI : Finite (Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K M) :=
    Finite.of_injective qEquivM qEquivM.injective
  rw [show (groupCohomology.map
      (AlgEquiv.restrictNormalHom (F := K) (K₁ := M) L)
      (galoisTowerUnitsRepresentationHom K L M) 2).hom z =
        cyclicGaloisH2OrientedCarryNormQuotientTransition K L M z by
    exact congrArg (fun f : cyclicGaloisH2 K L →+ cyclicGaloisH2 K M => f z)
      (cyclicGaloisH2Inflation_eq_orientedCarryNormQuotientTransition K L M)]
  change cyclicGaloisCarryH2SplitValuationEquiv K M vK vM
      (Module.finrank K M) u hu rfl hvalKM hzeroKM
      ((cyclicGaloisRestrictionOrientation K L M).val •
        cyclicGaloisH2CarryNormQuotientTransition K L M z) = _
  rw [map_nsmul]
  congr 1
  have h := congrArg
    (fun f : cyclicGaloisH2 K L →+ ZMod (Module.finrank K M) => f z)
    (cyclicGaloisCarryH2SplitValuationEquiv_transition K L M vK vL vM u hu
      hvalKL hzeroKL hvalKM hzeroKM)
  exact h

/-- Actual group-cohomological inflation is injective for split-valuation cyclic layers. -/
theorem cyclicGaloisH2Inflation_injective_of_splitValuation
    (K L M : Type) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional L M] [FiniteDimensional K M]
    [IsGalois K L] [IsGalois K M]
    [IsCyclic Gal(L/K)] [IsCyclic Gal(M/K)]
    (vK : Valuation K (WithZero (Multiplicative ℤ)))
    (vL : Valuation L (WithZero (Multiplicative ℤ)))
    (vM : Valuation M (WithZero (Multiplicative ℤ))) (u : Kˣ)
    (hu : Multiplicative.toAdd (tameValHom vK u) = 1)
    (hvalKL : ∀ x : Lˣ,
      tameValHom vK (Units.map (Algebra.norm K) x) =
        (tameValHom vL x) ^ Module.finrank K L)
    (hzeroKL : ∀ a : Kˣ, tameValHom vK a = 1 →
      ∃ b : Lˣ, Units.map (Algebra.norm K) b = a)
    (hvalKM : ∀ x : Mˣ,
      tameValHom vK (Units.map (Algebra.norm K) x) =
        (tameValHom vM x) ^ Module.finrank K M)
    (hzeroKM : ∀ a : Kˣ, tameValHom vK a = 1 →
      ∃ b : Mˣ, Units.map (Algebra.norm K) b = a) :
    Function.Injective
      (groupCohomology.map
        (AlgEquiv.restrictNormalHom (F := K) (K₁ := M) L)
        (galoisTowerUnitsRepresentationHom K L M) 2).hom := by
  letI : NeZero (Module.finrank K L) :=
    ⟨Nat.ne_of_gt (Module.finrank_pos (R := K) (M := L))⟩
  let eL := cyclicGaloisCarryH2SplitValuationEquiv K L vK vL
    (Module.finrank K L) u hu rfl hvalKL hzeroKL
  let eM := cyclicGaloisCarryH2SplitValuationEquiv K M vK vM
    (Module.finrank K M) u hu rfl hvalKM hzeroKM
  let t := zmodRatModIntTransition Module.finrank_pos.ne' Module.finrank_pos.ne'
    ⟨Module.finrank L M, (Module.finrank_mul_finrank K L M).symm⟩
  intro x y hxy
  apply eL.injective
  have hx := cyclicGaloisH2Inflation_carrySplitValuationInvariant
    K L M vK vL vM u hu hvalKL hzeroKL hvalKM hzeroKM x
  have hy := cyclicGaloisH2Inflation_carrySplitValuationInvariant
    K L M vK vL vM u hu hvalKL hzeroKL hvalKM hzeroKM y
  have htarget :
      (cyclicGaloisRestrictionOrientation K L M).val • t (eL x) =
        (cyclicGaloisRestrictionOrientation K L M).val • t (eL y) :=
    hx.symm.trans ((congrArg eM hxy).trans hy)
  have htarget' :
      t ((cyclicGaloisRestrictionOrientation K L M).val • eL x) =
        t ((cyclicGaloisRestrictionOrientation K L M).val • eL y) := by
    simpa only [map_nsmul] using htarget
  have hsource := zmodRatModIntTransition_injective Module.finrank_pos.ne'
    Module.finrank_pos.ne'
    ⟨Module.finrank L M, (Module.finrank_mul_finrank K L M).symm⟩ htarget'
  have horientation :
      IsUnit (((cyclicGaloisRestrictionOrientation K L M).val : ℕ) :
        ZMod (Module.finrank K L)) := by
    rw [ZMod.natCast_zmod_val]
    exact cyclicGaloisRestrictionOrientation_isUnit K L M
  apply horientation.mul_left_cancel
  simpa [nsmul_eq_mul] using hsource

/-- Actual finite continuous inflation is injective for split-valuation cyclic layers. -/
theorem finiteGaloisContinuousH2Inflation_injective_of_splitValuation
    (K L M : Type) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional L M] [FiniteDimensional K M]
    [IsGalois K L] [IsGalois K M]
    [IsCyclic Gal(L/K)] [IsCyclic Gal(M/K)]
    (vK : Valuation K (WithZero (Multiplicative ℤ)))
    (vL : Valuation L (WithZero (Multiplicative ℤ)))
    (vM : Valuation M (WithZero (Multiplicative ℤ))) (u : Kˣ)
    (hu : Multiplicative.toAdd (tameValHom vK u) = 1)
    (hvalKL : ∀ x : Lˣ,
      tameValHom vK (Units.map (Algebra.norm K) x) =
        (tameValHom vL x) ^ Module.finrank K L)
    (hzeroKL : ∀ a : Kˣ, tameValHom vK a = 1 →
      ∃ b : Lˣ, Units.map (Algebra.norm K) b = a)
    (hvalKM : ∀ x : Mˣ,
      tameValHom vK (Units.map (Algebra.norm K) x) =
        (tameValHom vM x) ^ Module.finrank K M)
    (hzeroKM : ∀ a : Kˣ, tameValHom vK a = 1 →
      ∃ b : Mˣ, Units.map (Algebra.norm K) b = a) :
    Function.Injective (finiteGaloisContinuousH2Inflation K L M) := by
  intro x y hxy
  apply (finiteGaloisContinuousH2ToOrdinaryH2AddEquiv K L).injective
  apply cyclicGaloisH2Inflation_injective_of_splitValuation
    K L M vK vL vM u hu hvalKL hzeroKL hvalKM hzeroKM
  rw [← finiteGaloisContinuousH2Inflation_toOrdinary_apply,
    ← finiteGaloisContinuousH2Inflation_toOrdinary_apply, hxy]

/-- Orientation-corrected carry transition transported to finite continuous Galois `H²`. -/
noncomputable def finiteGaloisContinuousH2OrientedCarryNormQuotientTransition
    (K L M : Type) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional L M] [FiniteDimensional K M]
    [IsGalois K L] [IsGalois K M]
    [IsCyclic Gal(L/K)] [IsCyclic Gal(M/K)]
    [Finite (Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K L)]
    [Finite (Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K M)] :
    continuousGaloisH2 K L →+ continuousGaloisH2 K M :=
  (finiteGaloisContinuousH2ToOrdinaryH2AddEquiv K M).symm.toAddMonoidHom.comp
    ((cyclicGaloisH2OrientedCarryNormQuotientTransition K L M).comp
      (finiteGaloisContinuousH2ToOrdinaryH2AddEquiv K L).toAddMonoidHom)

/-- Ordinary coordinates of the orientation-corrected continuous carry transition. -/
theorem finiteGaloisContinuousH2OrientedCarryNormQuotientTransition_toOrdinary_apply
    (K L M : Type) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional L M] [FiniteDimensional K M]
    [IsGalois K L] [IsGalois K M]
    [IsCyclic Gal(L/K)] [IsCyclic Gal(M/K)]
    [Finite (Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K L)]
    [Finite (Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K M)]
    (z : continuousGaloisH2 K L) :
    finiteGaloisContinuousH2ToOrdinaryH2AddEquiv K M
        (finiteGaloisContinuousH2OrientedCarryNormQuotientTransition K L M z) =
      cyclicGaloisH2OrientedCarryNormQuotientTransition K L M
        (finiteGaloisContinuousH2ToOrdinaryH2AddEquiv K L z) := by
  exact (finiteGaloisContinuousH2ToOrdinaryH2AddEquiv K M).apply_symm_apply _

/-- Genuine finite continuous inflation is exactly the orientation-corrected transition in
literal carry-cocycle coordinates. -/
theorem finiteGaloisContinuousH2Inflation_eq_orientedCarryNormQuotientTransition
    (K L M : Type) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional L M] [FiniteDimensional K M]
    [IsGalois K L] [IsGalois K M]
    [IsCyclic Gal(L/K)] [IsCyclic Gal(M/K)]
    [Finite (Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K L)]
    [Finite (Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K M)] :
    finiteGaloisContinuousH2Inflation K L M =
      finiteGaloisContinuousH2OrientedCarryNormQuotientTransition K L M := by
  apply AddMonoidHom.ext
  intro z
  apply (finiteGaloisContinuousH2ToOrdinaryH2AddEquiv K M).injective
  rw [finiteGaloisContinuousH2Inflation_toOrdinary_apply,
    finiteGaloisContinuousH2OrientedCarryNormQuotientTransition_toOrdinary_apply]
  exact congrArg
    (fun f : cyclicGaloisH2 K L →+ cyclicGaloisH2 K M =>
      f (finiteGaloisContinuousH2ToOrdinaryH2AddEquiv K L z))
    (cyclicGaloisH2Inflation_eq_orientedCarryNormQuotientTransition K L M)

/-- Orientation-corrected carry transitions compose because they are genuine inflation. -/
theorem finiteGaloisContinuousH2OrientedCarryNormQuotientTransition_comp
    (K L M N : Type) [Field K] [Field L] [Field M] [Field N]
    [Algebra K L] [Algebra K M] [Algebra K N]
    [Algebra L M] [Algebra L N] [Algebra M N]
    [IsScalarTower K L M] [IsScalarTower K L N]
    [IsScalarTower K M N] [IsScalarTower L M N]
    [FiniteDimensional K L] [FiniteDimensional K M] [FiniteDimensional K N]
    [FiniteDimensional L M] [FiniteDimensional L N] [FiniteDimensional M N]
    [IsGalois K L] [IsGalois K M] [IsGalois K N]
    [IsCyclic Gal(L/K)] [IsCyclic Gal(M/K)] [IsCyclic Gal(N/K)]
    [Finite (Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K L)]
    [Finite (Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K M)]
    [Finite (Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K N)] :
    (finiteGaloisContinuousH2OrientedCarryNormQuotientTransition K M N).comp
        (finiteGaloisContinuousH2OrientedCarryNormQuotientTransition K L M) =
      finiteGaloisContinuousH2OrientedCarryNormQuotientTransition K L N := by
  rw [← finiteGaloisContinuousH2Inflation_eq_orientedCarryNormQuotientTransition K L M,
    ← finiteGaloisContinuousH2Inflation_eq_orientedCarryNormQuotientTransition K M N,
    ← finiteGaloisContinuousH2Inflation_eq_orientedCarryNormQuotientTransition K L N]
  exact finiteGaloisContinuousH2Inflation_comp K L M N

end

end GaloisForLFunctions.HTGeometry.ABHN
