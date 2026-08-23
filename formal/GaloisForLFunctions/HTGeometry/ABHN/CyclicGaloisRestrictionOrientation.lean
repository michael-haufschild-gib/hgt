/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.ContinuousGaloisH2NormQuotientTransition

/-!
# Generator orientation in cyclic Galois H² inflation

Periodic cyclic-group resolutions depend on a chosen generator.  In a Galois tower, independently
chosen generators need not be compatible with restriction.  This file records the missing
orientation: the restriction of the chosen generator of `Gal(M/K)` is the chosen generator of
`Gal(L/K)` raised to a unit `q mod [L:K]`.

The orientation is a unit, is one on an identity tower, and obeys a multiplicative tower law.
Consequently the generator-oriented norm-quotient transition sends a base parameter `a` to
`a ^ (q * [M:L])`, not in general to `a ^ [M:L]`.  We transport this corrected transition to
continuous `H²` and reduce its comparison with genuine group-cohomological inflation to the
corrected base-unit formula.  No inflation comparison is assumed or asserted.
-/

open CategoryTheory Representation

namespace GaloisForLFunctions.HTGeometry.ABHN

noncomputable section

/-- Coordinate modulo `[L : K]` of the restricted chosen generator of `Gal(M/K)`, measured with
respect to the independently chosen generator of `Gal(L/K)`. -/
def cyclicGaloisRestrictionOrientation
    (K L M : Type) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional L M] [FiniteDimensional K M]
    [IsGalois K L] [IsGalois K M]
    [IsCyclic Gal(L/K)] [IsCyclic Gal(M/K)] :
    ZMod (Module.finrank K L) :=
  Multiplicative.toAdd
    ((zmodMulEquivOfGenerator
      (cyclicGaloisGenerator_spec K L)
      (IsGalois.card_aut_eq_finrank K L)).symm
      (AlgEquiv.restrictNormalHom (F := K) (K₁ := M) L
        (cyclicGaloisGenerator K M)))

/-- Restriction sends the chosen upper generator to the lower generator raised to the orientation
coordinate. -/
theorem cyclicGaloisRestrictionOrientation_spec
    (K L M : Type) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional L M] [FiniteDimensional K M]
    [IsGalois K L] [IsGalois K M]
    [IsCyclic Gal(L/K)] [IsCyclic Gal(M/K)] :
    AlgEquiv.restrictNormalHom (F := K) (K₁ := M) L
        (cyclicGaloisGenerator K M) =
      cyclicGaloisGenerator K L ^ (cyclicGaloisRestrictionOrientation K L M).val := by
  letI : NeZero (Module.finrank K L) :=
    ⟨Nat.ne_of_gt (Module.finrank_pos (R := K) (M := L))⟩
  let e := zmodMulEquivOfGenerator
      (cyclicGaloisGenerator_spec K L)
      (IsGalois.card_aut_eq_finrank K L)
  have h := e.apply_symm_apply
    (AlgEquiv.restrictNormalHom (F := K) (K₁ := M) L
      (cyclicGaloisGenerator K M))
  change e (Multiplicative.ofAdd (cyclicGaloisRestrictionOrientation K L M)) = _ at h
  calc
    _ = e (Multiplicative.ofAdd (cyclicGaloisRestrictionOrientation K L M)) := h.symm
    _ = e (Multiplicative.ofAdd (((cyclicGaloisRestrictionOrientation K L M).val : ℤ) : ZMod _)) := by
      rw [Int.cast_natCast, ZMod.natCast_zmod_val]
    _ = cyclicGaloisGenerator K L ^ ((cyclicGaloisRestrictionOrientation K L M).val : ℤ) :=
      zmodMulEquivOfGenerator_apply_ofAdd_intCast _ _ _
    _ = cyclicGaloisGenerator K L ^ (cyclicGaloisRestrictionOrientation K L M).val := by
      rw [zpow_natCast]

/-- Surjectivity of Galois restriction forces the orientation coordinate to be a unit modulo the
lower extension degree. -/
theorem cyclicGaloisRestrictionOrientation_isUnit
    (K L M : Type) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional L M] [FiniteDimensional K M]
    [IsGalois K L] [IsGalois K M]
    [IsCyclic Gal(L/K)] [IsCyclic Gal(M/K)] :
    IsUnit (cyclicGaloisRestrictionOrientation K L M) := by
  letI : NeZero (Module.finrank K L) :=
    ⟨Nat.ne_of_gt (Module.finrank_pos (R := K) (M := L))⟩
  let f := AlgEquiv.restrictNormalHom (F := K) (K₁ := M) L
  have hsurj : Function.Surjective f :=
    AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := L) (E := M)
  have htopM : Subgroup.zpowers (cyclicGaloisGenerator K M) = ⊤ :=
    (Subgroup.eq_top_iff' _).2 (cyclicGaloisGenerator_spec K M)
  have htopL : Subgroup.zpowers (f (cyclicGaloisGenerator K M)) = ⊤ := by
    rw [← MonoidHom.map_zpowers, htopM]
    exact Subgroup.map_top_of_surjective f hsurj
  have horder : orderOf (f (cyclicGaloisGenerator K M)) = Module.finrank K L := by
    rw [orderOf_eq_card_of_forall_mem_zpowers ((Subgroup.eq_top_iff' _).1 htopL)]
    exact IsGalois.card_aut_eq_finrank K L
  rw [cyclicGaloisRestrictionOrientation_spec, orderOf_pow, cyclicGaloisGenerator_orderOf] at horder
  have hgcd : Nat.gcd (Module.finrank K L) (cyclicGaloisRestrictionOrientation K L M).val = 1 := by
    rw [Nat.div_eq_self] at horder
    rcases horder with hzero | hgcd
    · exact (Nat.ne_of_gt (Module.finrank_pos (R := K) (M := L)) hzero).elim
    · exact hgcd
  rw [← ZMod.natCast_zmod_val (cyclicGaloisRestrictionOrientation K L M), ZMod.isUnit_iff_coprime]
  rw [Nat.coprime_iff_gcd_eq_one, Nat.gcd_comm]
  exact hgcd

/-- Identity towers have orientation one. -/
theorem cyclicGaloisRestrictionOrientation_self
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)] :
    cyclicGaloisRestrictionOrientation K L L = 1 := by
  simp only [cyclicGaloisRestrictionOrientation]
  rw [AlgEquiv.restrictNormalHom_id]
  exact congrArg Multiplicative.toAdd
    (zmodMulEquivOfGenerator_symm_apply_generator
      (cyclicGaloisGenerator_spec K L) (IsGalois.card_aut_eq_finrank K L))

/-- The degree of a lower field in a finite tower divides the degree of every upper field. -/
theorem cyclicGaloisFinrank_dvd
    (K L M : Type) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional L M] [FiniteDimensional K M] :
    Module.finrank K L ∣ Module.finrank K M := by
  refine ⟨Module.finrank L M, ?_⟩
  exact (Module.finrank_mul_finrank K L M).symm

/-- Natural scalar multiplication depends only on a residue class modulo any annihilator of the
element. -/
theorem nsmul_eq_nsmul_of_zmod_natCast_eq {A : Type*} [AddCommGroup A]
    (n a b : ℕ) (x : A) (hab : (a : ZMod n) = (b : ZMod n)) (hx : n • x = 0) :
    a • x = b • x := by
  have hmod : a ≡ b [MOD n] := (ZMod.natCast_eq_natCast_iff a b n).mp hab
  obtain ⟨k, hk⟩ := (Nat.modEq_iff_dvd.mp hmod)
  have hdiff : ((b : ℤ) - (a : ℤ)) • x = 0 := by
    rw [hk]
    rw [mul_zsmul, zsmul_comm, natCast_zsmul, hx, smul_zero]
  have heq : (b : ℤ) • x = (a : ℤ) • x := by
    have hdiff' : (b : ℤ) • x + -((a : ℤ) • x) = 0 := by
      simpa only [sub_zsmul] using hdiff
    calc
      (b : ℤ) • x = (b : ℤ) • x + (-((a : ℤ) • x) + (a : ℤ) • x) := by simp
      _ = ((b : ℤ) • x + -((a : ℤ) • x)) + (a : ℤ) • x := by rw [add_assoc]
      _ = (a : ℤ) • x := by rw [hdiff', zero_add]
  simpa only [natCast_zsmul] using heq.symm

/-- Orientations multiply in a tower, after reducing the upper orientation modulo the lower
degree. -/
theorem cyclicGaloisRestrictionOrientation_comp
    (K L M N : Type) [Field K] [Field L] [Field M] [Field N]
    [Algebra K L] [Algebra K M] [Algebra K N]
    [Algebra L M] [Algebra L N] [Algebra M N]
    [IsScalarTower K L M] [IsScalarTower K L N]
    [IsScalarTower K M N] [IsScalarTower L M N]
    [FiniteDimensional K L] [FiniteDimensional K M] [FiniteDimensional K N]
    [FiniteDimensional L M] [FiniteDimensional L N] [FiniteDimensional M N]
    [IsGalois K L] [IsGalois K M] [IsGalois K N]
    [IsCyclic Gal(L/K)] [IsCyclic Gal(M/K)] [IsCyclic Gal(N/K)] :
    cyclicGaloisRestrictionOrientation K L N =
      cyclicGaloisRestrictionOrientation K L M *
        ZMod.castHom (cyclicGaloisFinrank_dvd K L M) (ZMod (Module.finrank K L))
          (cyclicGaloisRestrictionOrientation K M N) := by
  letI : NeZero (Module.finrank K L) :=
    ⟨Nat.ne_of_gt (Module.finrank_pos (R := K) (M := L))⟩
  letI : NeZero (Module.finrank K M) :=
    ⟨Nat.ne_of_gt (Module.finrank_pos (R := K) (M := M))⟩
  let eL := zmodMulEquivOfGenerator
    (cyclicGaloisGenerator_spec K L) (IsGalois.card_aut_eq_finrank K L)
  apply Multiplicative.ofAdd.injective
  apply eL.injective
  rw [show eL (Multiplicative.ofAdd (cyclicGaloisRestrictionOrientation K L N)) =
      AlgEquiv.restrictNormalHom (F := K) (K₁ := N) L
        (cyclicGaloisGenerator K N) by
      exact eL.apply_symm_apply _]
  rw [IsScalarTower.AlgEquiv.restrictNormalHom_comp K L M N]
  rw [MonoidHom.comp_apply]
  rw [cyclicGaloisRestrictionOrientation_spec K M N, map_pow]
  rw [cyclicGaloisRestrictionOrientation_spec K L M, ← pow_mul]
  rw [show eL (Multiplicative.ofAdd
      (cyclicGaloisRestrictionOrientation K L M *
        ZMod.castHom (cyclicGaloisFinrank_dvd K L M) (ZMod (Module.finrank K L))
          (cyclicGaloisRestrictionOrientation K M N))) =
      cyclicGaloisGenerator K L ^
        ((cyclicGaloisRestrictionOrientation K L M).val * (cyclicGaloisRestrictionOrientation K M N).val) by
    have hcast :
        ZMod.castHom (cyclicGaloisFinrank_dvd K L M) (ZMod (Module.finrank K L))
            (cyclicGaloisRestrictionOrientation K M N) =
          ((cyclicGaloisRestrictionOrientation K M N).val : ZMod (Module.finrank K L)) := by
      calc
        _ = ZMod.castHom (cyclicGaloisFinrank_dvd K L M)
              (ZMod (Module.finrank K L))
              ((cyclicGaloisRestrictionOrientation K M N).val : ZMod (Module.finrank K M)) := by
            rw [ZMod.natCast_zmod_val]
        _ = _ := by rw [map_natCast]
    have hproduct :
        cyclicGaloisRestrictionOrientation K L M *
            ZMod.castHom (cyclicGaloisFinrank_dvd K L M) (ZMod (Module.finrank K L))
              (cyclicGaloisRestrictionOrientation K M N) =
          (((cyclicGaloisRestrictionOrientation K L M).val * (cyclicGaloisRestrictionOrientation K M N).val : ℕ) :
            ZMod (Module.finrank K L)) := by
      calc
        _ = cyclicGaloisRestrictionOrientation K L M *
              ((cyclicGaloisRestrictionOrientation K M N).val : ZMod (Module.finrank K L)) := by rw [hcast]
        _ = ((cyclicGaloisRestrictionOrientation K L M).val : ZMod (Module.finrank K L)) *
              ((cyclicGaloisRestrictionOrientation K M N).val : ZMod (Module.finrank K L)) := by
            rw [ZMod.natCast_zmod_val]
        _ = _ := by rw [Nat.cast_mul]
    rw [hproduct]
    change eL (Multiplicative.ofAdd
      (((cyclicGaloisRestrictionOrientation K L M).val * (cyclicGaloisRestrictionOrientation K M N).val : ℕ) : ZMod _)) = _
    calc
      _ = eL (Multiplicative.ofAdd
          ((((cyclicGaloisRestrictionOrientation K L M).val * (cyclicGaloisRestrictionOrientation K M N).val : ℕ) : ℤ) : ZMod _)) := by
        rw [Int.cast_natCast]
      _ = _ := by
        rw [zmodMulEquivOfGenerator_apply_ofAdd_intCast, zpow_natCast]]

/-- Norm-quotient transition corrected by the generator orientation of Galois restriction. -/
noncomputable def cyclicGaloisH2OrientedNormQuotientTransition
    (K L M : Type) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional L M] [FiniteDimensional K M]
    [IsGalois K L] [IsGalois K M]
    [IsCyclic Gal(L/K)] [IsCyclic Gal(M/K)] :
    cyclicGaloisH2 K L →+ cyclicGaloisH2 K M :=
  (cyclicGaloisRestrictionOrientation K L M).val • cyclicGaloisH2NormQuotientTransition K L M

/-- The oriented transition is orientation multiplication after the norm-defined transition. -/
theorem cyclicGaloisH2OrientedNormQuotientTransition_apply
    (K L M : Type) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional L M] [FiniteDimensional K M]
    [IsGalois K L] [IsGalois K M]
    [IsCyclic Gal(L/K)] [IsCyclic Gal(M/K)] (z : cyclicGaloisH2 K L) :
    cyclicGaloisH2OrientedNormQuotientTransition K L M z =
      (cyclicGaloisRestrictionOrientation K L M).val • cyclicGaloisH2NormQuotientTransition K L M z := rfl

/-- A base parameter is raised to `orientation * [M : L]` by the oriented transition. -/
theorem cyclicGaloisH2OrientedNormQuotientTransition_baseProjection
    (K L M : Type) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional L M] [FiniteDimensional K M]
    [IsGalois K L] [IsGalois K M]
    [IsCyclic Gal(L/K)] [IsCyclic Gal(M/K)] (a : Additive Kˣ) :
    cyclicGaloisH2OrientedNormQuotientTransition K L M (cyclicGaloisH2BaseProjection K L a) =
      cyclicGaloisH2BaseProjection K M
        (((cyclicGaloisRestrictionOrientation K L M).val * Module.finrank L M) • a) := by
  rw [cyclicGaloisH2OrientedNormQuotientTransition_apply,
    cyclicGaloisH2NormQuotientTransition_baseProjection, ← map_nsmul, mul_nsmul]
  rw [smul_smul, smul_smul, Nat.mul_comm]

/-- The oriented transition on an identity tower is the identity, including the degree-one case
where `ZMod 1` has zero as its sole representative. -/
theorem cyclicGaloisH2OrientedNormQuotientTransition_self
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)] :
    cyclicGaloisH2OrientedNormQuotientTransition K L L = AddMonoidHom.id _ := by
  apply AddMonoidHom.ext
  intro z
  by_cases hdegree : Module.finrank K L = 1
  · have hz : z = 0 := by
      have hzero := cyclicGaloisH2_finrank_nsmul_eq_zero K L z
      rwa [hdegree, one_nsmul] at hzero
    rw [hz, map_zero, map_zero]
  · rw [cyclicGaloisH2OrientedNormQuotientTransition_apply, cyclicGaloisH2NormQuotientTransition_self,
      AddMonoidHom.id_apply, cyclicGaloisRestrictionOrientation_self, ZMod.val_one'' hdegree, one_nsmul]

/-- Oriented norm-quotient transitions compose through every finite cyclic Galois tower. -/
theorem cyclicGaloisH2OrientedNormQuotientTransition_comp
    (K L M N : Type) [Field K] [Field L] [Field M] [Field N]
    [Algebra K L] [Algebra K M] [Algebra K N]
    [Algebra L M] [Algebra L N] [Algebra M N]
    [IsScalarTower K L M] [IsScalarTower K L N]
    [IsScalarTower K M N] [IsScalarTower L M N]
    [FiniteDimensional K L] [FiniteDimensional K M] [FiniteDimensional K N]
    [FiniteDimensional L M] [FiniteDimensional L N] [FiniteDimensional M N]
    [IsGalois K L] [IsGalois K M] [IsGalois K N]
    [IsCyclic Gal(L/K)] [IsCyclic Gal(M/K)] [IsCyclic Gal(N/K)] :
    (cyclicGaloisH2OrientedNormQuotientTransition K M N).comp
        (cyclicGaloisH2OrientedNormQuotientTransition K L M) =
      cyclicGaloisH2OrientedNormQuotientTransition K L N := by
  apply AddMonoidHom.ext
  intro z
  rw [AddMonoidHom.comp_apply, cyclicGaloisH2OrientedNormQuotientTransition_apply,
    cyclicGaloisH2OrientedNormQuotientTransition_apply,
    cyclicGaloisH2OrientedNormQuotientTransition_apply, map_nsmul]
  have hcomp := congrArg
    (fun f : cyclicGaloisH2 K L →+ cyclicGaloisH2 K N => f z)
    (cyclicGaloisH2NormQuotientTransition_comp K L M N)
  change cyclicGaloisH2NormQuotientTransition K M N
      (cyclicGaloisH2NormQuotientTransition K L M z) =
    cyclicGaloisH2NormQuotientTransition K L N z at hcomp
  rw [hcomp, smul_smul]
  let w := cyclicGaloisH2NormQuotientTransition K L N z
  have hw : Module.finrank K L • w = 0 := by
    change Module.finrank K L • cyclicGaloisH2NormQuotientTransition K L N z = 0
    rw [← map_nsmul, cyclicGaloisH2_finrank_nsmul_eq_zero, map_zero]
  let q := cyclicGaloisRestrictionOrientation K L M
  let r := cyclicGaloisRestrictionOrientation K M N
  let s := cyclicGaloisRestrictionOrientation K L N
  letI : NeZero (Module.finrank K L) :=
    ⟨Nat.ne_of_gt (Module.finrank_pos (R := K) (M := L))⟩
  letI : NeZero (Module.finrank K M) :=
    ⟨Nat.ne_of_gt (Module.finrank_pos (R := K) (M := M))⟩
  have hcast :
      ZMod.castHom (cyclicGaloisFinrank_dvd K L M) (ZMod (Module.finrank K L)) r =
        (r.val : ZMod (Module.finrank K L)) := by
    calc
      _ = ZMod.castHom (cyclicGaloisFinrank_dvd K L M)
          (ZMod (Module.finrank K L)) (r.val : ZMod (Module.finrank K M)) := by
        rw [ZMod.natCast_zmod_val]
      _ = _ := by rw [map_natCast]
  have hmod : ((r.val * q.val : ℕ) : ZMod (Module.finrank K L)) = s := by
    calc
      _ = (r.val : ZMod (Module.finrank K L)) *
          (q.val : ZMod (Module.finrank K L)) := by rw [Nat.cast_mul]
      _ = (q.val : ZMod (Module.finrank K L)) *
          (r.val : ZMod (Module.finrank K L)) := mul_comm _ _
      _ = q * ZMod.castHom (cyclicGaloisFinrank_dvd K L M)
          (ZMod (Module.finrank K L)) r := by
        rw [ZMod.natCast_zmod_val, hcast]
      _ = s := (cyclicGaloisRestrictionOrientation_comp K L M N).symm
  exact nsmul_eq_nsmul_of_zmod_natCast_eq (Module.finrank K L)
    (r.val * q.val) s.val w (hmod.trans (ZMod.natCast_zmod_val s).symm) hw

/-- Genuine group-cohomological inflation equals the oriented norm transition exactly when it has
the corrected formula on all base-unit representatives. -/
theorem cyclicGaloisH2Inflation_eq_orientedNormQuotientTransition_iff
    (K L M : Type) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional L M] [FiniteDimensional K M]
    [IsGalois K L] [IsGalois K M]
    [IsCyclic Gal(L/K)] [IsCyclic Gal(M/K)] :
    (groupCohomology.map
        (AlgEquiv.restrictNormalHom (F := K) (K₁ := M) L)
        (galoisTowerUnitsRepresentationHom K L M) 2).hom.toAddMonoidHom =
      cyclicGaloisH2OrientedNormQuotientTransition K L M ↔
      ∀ a : Additive Kˣ,
        (groupCohomology.map
          (AlgEquiv.restrictNormalHom (F := K) (K₁ := M) L)
          (galoisTowerUnitsRepresentationHom K L M) 2).hom
            (cyclicGaloisH2BaseProjection K L a) =
          cyclicGaloisH2BaseProjection K M
            (((cyclicGaloisRestrictionOrientation K L M).val * Module.finrank L M) • a) := by
  constructor
  · intro h a
    have ha := congrArg
      (fun f : cyclicGaloisH2 K L →+ cyclicGaloisH2 K M =>
        f (cyclicGaloisH2BaseProjection K L a)) h
    rw [cyclicGaloisH2OrientedNormQuotientTransition_baseProjection] at ha
    exact ha
  · intro h
    apply AddMonoidHom.ext
    intro z
    change (groupCohomology.map
        (AlgEquiv.restrictNormalHom (F := K) (K₁ := M) L)
        (galoisTowerUnitsRepresentationHom K L M) 2).hom z =
      cyclicGaloisH2OrientedNormQuotientTransition K L M z
    obtain ⟨a, rfl⟩ := cyclicGaloisH2BaseProjection_surjective K L z
    rw [h, cyclicGaloisH2OrientedNormQuotientTransition_baseProjection]

/-- The oriented and unoriented norm transitions coincide exactly when the orientation unit acts
trivially on every transitioned base parameter. -/
theorem cyclicGaloisH2OrientedNormQuotientTransition_eq_normQuotientTransition_iff
    (K L M : Type) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional L M] [FiniteDimensional K M]
    [IsGalois K L] [IsGalois K M]
    [IsCyclic Gal(L/K)] [IsCyclic Gal(M/K)] :
    cyclicGaloisH2OrientedNormQuotientTransition K L M = cyclicGaloisH2NormQuotientTransition K L M ↔
      ∀ a : Additive Kˣ,
        cyclicGaloisH2BaseProjection K M
            (((cyclicGaloisRestrictionOrientation K L M).val * Module.finrank L M) • a) =
          cyclicGaloisH2BaseProjection K M (Module.finrank L M • a) := by
  constructor
  · intro h a
    have ha := congrArg
      (fun f : cyclicGaloisH2 K L →+ cyclicGaloisH2 K M =>
        f (cyclicGaloisH2BaseProjection K L a)) h
    rw [cyclicGaloisH2OrientedNormQuotientTransition_baseProjection,
      cyclicGaloisH2NormQuotientTransition_baseProjection] at ha
    exact ha
  · intro h
    apply AddMonoidHom.ext
    intro z
    obtain ⟨a, rfl⟩ := cyclicGaloisH2BaseProjection_surjective K L z
    rw [cyclicGaloisH2OrientedNormQuotientTransition_baseProjection,
      cyclicGaloisH2NormQuotientTransition_baseProjection, h]

/-- Oriented norm transition transported to finite continuous Galois `H²`. -/
noncomputable def finiteGaloisContinuousH2OrientedNormQuotientTransition
    (K L M : Type) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional L M] [FiniteDimensional K M]
    [IsGalois K L] [IsGalois K M]
    [IsCyclic Gal(L/K)] [IsCyclic Gal(M/K)] :
    continuousGaloisH2 K L →+ continuousGaloisH2 K M :=
  (finiteGaloisContinuousH2ToOrdinaryH2AddEquiv K M).symm.toAddMonoidHom.comp
    ((cyclicGaloisH2OrientedNormQuotientTransition K L M).comp
      (finiteGaloisContinuousH2ToOrdinaryH2AddEquiv K L).toAddMonoidHom)

/-- Ordinary coordinates of the continuous oriented transition. -/
theorem finiteGaloisContinuousH2OrientedNormQuotientTransition_toOrdinary_apply
    (K L M : Type) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional L M] [FiniteDimensional K M]
    [IsGalois K L] [IsGalois K M]
    [IsCyclic Gal(L/K)] [IsCyclic Gal(M/K)] (z : continuousGaloisH2 K L) :
    finiteGaloisContinuousH2ToOrdinaryH2AddEquiv K M
        (finiteGaloisContinuousH2OrientedNormQuotientTransition K L M z) =
      cyclicGaloisH2OrientedNormQuotientTransition K L M
        (finiteGaloisContinuousH2ToOrdinaryH2AddEquiv K L z) := by
  exact (finiteGaloisContinuousH2ToOrdinaryH2AddEquiv K M).apply_symm_apply _

/-- Continuous inflation equals the oriented transition exactly when their ordinary cyclic `H²`
coordinates agree. -/
theorem finiteGaloisContinuousH2Inflation_eq_orientedNormQuotientTransition_iff_ordinary
    (K L M : Type) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional L M] [FiniteDimensional K M]
    [IsGalois K L] [IsGalois K M]
    [IsCyclic Gal(L/K)] [IsCyclic Gal(M/K)] :
    finiteGaloisContinuousH2Inflation K L M = finiteGaloisContinuousH2OrientedNormQuotientTransition K L M ↔
      (groupCohomology.map
        (AlgEquiv.restrictNormalHom (F := K) (K₁ := M) L)
        (galoisTowerUnitsRepresentationHom K L M) 2).hom.toAddMonoidHom =
          cyclicGaloisH2OrientedNormQuotientTransition K L M := by
  constructor
  · intro h
    apply AddMonoidHom.ext
    intro z
    let c : continuousGaloisH2 K L :=
      (finiteGaloisContinuousH2ToOrdinaryH2AddEquiv K L).symm z
    have hz := congrArg
      (fun f : continuousGaloisH2 K L →+ continuousGaloisH2 K M => f c) h
    have hz' := congrArg (finiteGaloisContinuousH2ToOrdinaryH2AddEquiv K M) hz
    rw [finiteGaloisContinuousH2Inflation_toOrdinary_apply,
      finiteGaloisContinuousH2OrientedNormQuotientTransition_toOrdinary_apply] at hz'
    change (groupCohomology.map
        (AlgEquiv.restrictNormalHom (F := K) (K₁ := M) L)
        (galoisTowerUnitsRepresentationHom K L M) 2).hom
          (finiteGaloisContinuousH2ToOrdinaryH2AddEquiv K L c) =
      cyclicGaloisH2OrientedNormQuotientTransition K L M
        (finiteGaloisContinuousH2ToOrdinaryH2AddEquiv K L c) at hz'
    change (groupCohomology.map
        (AlgEquiv.restrictNormalHom (F := K) (K₁ := M) L)
        (galoisTowerUnitsRepresentationHom K L M) 2).hom
          ((finiteGaloisContinuousH2ToOrdinaryH2AddEquiv K L)
            ((finiteGaloisContinuousH2ToOrdinaryH2AddEquiv K L).symm z)) =
      cyclicGaloisH2OrientedNormQuotientTransition K L M
        ((finiteGaloisContinuousH2ToOrdinaryH2AddEquiv K L)
          ((finiteGaloisContinuousH2ToOrdinaryH2AddEquiv K L).symm z)) at hz'
    rw [(finiteGaloisContinuousH2ToOrdinaryH2AddEquiv K L).apply_symm_apply] at hz'
    exact hz'
  · intro h
    apply AddMonoidHom.ext
    intro z
    apply (finiteGaloisContinuousH2ToOrdinaryH2AddEquiv K M).injective
    rw [finiteGaloisContinuousH2Inflation_toOrdinary_apply,
      finiteGaloisContinuousH2OrientedNormQuotientTransition_toOrdinary_apply]
    change (groupCohomology.map
        (AlgEquiv.restrictNormalHom (F := K) (K₁ := M) L)
        (galoisTowerUnitsRepresentationHom K L M) 2).hom.toAddMonoidHom
          (finiteGaloisContinuousH2ToOrdinaryH2AddEquiv K L z) =
      cyclicGaloisH2OrientedNormQuotientTransition K L M
        (finiteGaloisContinuousH2ToOrdinaryH2AddEquiv K L z)
    exact congrArg
      (fun f : cyclicGaloisH2 K L →+ cyclicGaloisH2 K M =>
        f (finiteGaloisContinuousH2ToOrdinaryH2AddEquiv K L z)) h

/-- Corrected base-unit criterion for continuous inflation to equal the oriented norm transition. -/
theorem finiteGaloisContinuousH2Inflation_eq_orientedNormQuotientTransition_iff_baseProjection
    (K L M : Type) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional L M] [FiniteDimensional K M]
    [IsGalois K L] [IsGalois K M]
    [IsCyclic Gal(L/K)] [IsCyclic Gal(M/K)] :
    finiteGaloisContinuousH2Inflation K L M = finiteGaloisContinuousH2OrientedNormQuotientTransition K L M ↔
      ∀ a : Additive Kˣ,
        (groupCohomology.map
          (AlgEquiv.restrictNormalHom (F := K) (K₁ := M) L)
          (galoisTowerUnitsRepresentationHom K L M) 2).hom
            (cyclicGaloisH2BaseProjection K L a) =
          cyclicGaloisH2BaseProjection K M
            (((cyclicGaloisRestrictionOrientation K L M).val * Module.finrank L M) • a) :=
  (finiteGaloisContinuousH2Inflation_eq_orientedNormQuotientTransition_iff_ordinary K L M).trans
    (cyclicGaloisH2Inflation_eq_orientedNormQuotientTransition_iff K L M)

/-- The continuous oriented transition on an identity tower is the identity. -/
theorem finiteGaloisContinuousH2OrientedNormQuotientTransition_self
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)] :
    finiteGaloisContinuousH2OrientedNormQuotientTransition K L L = AddMonoidHom.id _ := by
  apply AddMonoidHom.ext
  intro z
  apply (finiteGaloisContinuousH2ToOrdinaryH2AddEquiv K L).injective
  rw [finiteGaloisContinuousH2OrientedNormQuotientTransition_toOrdinary_apply,
    cyclicGaloisH2OrientedNormQuotientTransition_self]
  rfl

/-- Continuous oriented transitions compose through every finite cyclic Galois tower. -/
theorem finiteGaloisContinuousH2OrientedNormQuotientTransition_comp
    (K L M N : Type) [Field K] [Field L] [Field M] [Field N]
    [Algebra K L] [Algebra K M] [Algebra K N]
    [Algebra L M] [Algebra L N] [Algebra M N]
    [IsScalarTower K L M] [IsScalarTower K L N]
    [IsScalarTower K M N] [IsScalarTower L M N]
    [FiniteDimensional K L] [FiniteDimensional K M] [FiniteDimensional K N]
    [FiniteDimensional L M] [FiniteDimensional L N] [FiniteDimensional M N]
    [IsGalois K L] [IsGalois K M] [IsGalois K N]
    [IsCyclic Gal(L/K)] [IsCyclic Gal(M/K)] [IsCyclic Gal(N/K)] :
    (finiteGaloisContinuousH2OrientedNormQuotientTransition K M N).comp
        (finiteGaloisContinuousH2OrientedNormQuotientTransition K L M) =
      finiteGaloisContinuousH2OrientedNormQuotientTransition K L N := by
  apply AddMonoidHom.ext
  intro z
  apply (finiteGaloisContinuousH2ToOrdinaryH2AddEquiv K N).injective
  rw [AddMonoidHom.comp_apply,
    finiteGaloisContinuousH2OrientedNormQuotientTransition_toOrdinary_apply,
    finiteGaloisContinuousH2OrientedNormQuotientTransition_toOrdinary_apply,
    finiteGaloisContinuousH2OrientedNormQuotientTransition_toOrdinary_apply]
  exact congrArg
    (fun f : cyclicGaloisH2 K L →+ cyclicGaloisH2 K N =>
      f (finiteGaloisContinuousH2ToOrdinaryH2AddEquiv K L z))
    (cyclicGaloisH2OrientedNormQuotientTransition_comp K L M N)

end
end GaloisForLFunctions.HTGeometry.ABHN
