import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.SUnitRank
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.PowerIndexOfAbelianGroup
import Mathlib.LinearAlgebra.Dimension.Torsion.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity

/-! The power index of S-units combines the S-unit rank with the roots
of unity in the underlying number field. -/

noncomputable section

open NumberField IsDedekindDomain Module

namespace GaloisForLFunctions

variable (K : Type*) [Field K] [NumberField K] (G : Type*) [Group G] [MulSemiringAction G K]
attribute [local instance] primeMulAction
variable (S : SubMulAction G (HeightOneSpectrum (𝓞 K)))

local notation "U" => (sUnits K G S)
local notation "H" => (Multiplicative ↥U)

private theorem ordAt_eq_zero_of_finite_order (x : Kˣ) (hx : IsOfFinOrder x)
    (w : HeightOneSpectrum (𝓞 K)) : ordAt K w (Additive.ofMul x) = 0 := by
  obtain ⟨m, hm, hpow⟩ := isOfFinOrder_iff_pow_eq_one.mp hx
  have hz := congrArg (ordAt K w) (show m • Additive.ofMul x = 0 from hpow)
  rw [map_nsmul, map_zero, nsmul_eq_mul] at hz
  exact (mul_eq_zero.mp hz).resolve_left (Nat.cast_ne_zero.mpr hm.ne')

private theorem dvd_card_torsion_sUnits (n : ℕ) [NeZero n] [HasEnoughRootsOfUnity K n] :
    n ∣ Nat.card (CommGroup.torsion H) := by
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K n
  let u : Kˣ := (hζ.isUnit (NeZero.ne n)).unit
  have hu : IsPrimitiveRoot u n := IsPrimitiveRoot.coe_units_iff.mp hζ
  have hfin : IsOfFinOrder u := by
    rw [← orderOf_pos_iff, ← hu.eq_orderOf]
    exact NeZero.pos n
  let v : H := ⟨Additive.ofMul u, fun w _ => ordAt_eq_zero_of_finite_order K u hfin w⟩
  let j : H →* Kˣ := (U).subtype.toMultiplicative
  have hj : Function.Injective j := Subtype.val_injective
  have hv : orderOf v = n := (orderOf_injective j hj v).symm.trans hu.eq_orderOf.symm
  let t : CommGroup.torsion H := ⟨v, orderOf_pos_iff.mp (hv.symm ▸ NeZero.pos n)⟩
  have ht : orderOf t = n :=
    (orderOf_injective (CommGroup.torsion H).subtype Subtype.val_injective t).symm.trans hv
  rw [← ht]
  exact orderOf_dvd_natCard t

/-- The n-th power subgroup of the S-units has index n to the number
of infinite and specified finite places, when all n-th roots are present. -/
theorem index_power_sUnits [Fintype S] (n : ℕ) [NeZero n] [HasEnoughRootsOfUnity K n] :
    (powMonoidHom n : H →* H).range.index = n ^ (Fintype.card (InfinitePlace K) + Fintype.card S) := by
  letI : Module.Finite ℤ U := finite_sUnits K G S
  letI : Group.FG H := by
    rw [Group.fg_iff_monoid_fg, Monoid.fg_iff_add_fg, ← AddGroup.fg_iff_addMonoid_fg,
      ← Module.Finite.iff_addGroup_fg]
    change Module.Finite ℤ U
    exact finite_sUnits K G S
  haveI : Module.Finite ℤ (Additive (CommGroup.torsion H)) := by
    change Module.Finite ℤ (AddSubgroup.toIntSubmodule (AddCommGroup.torsion U))
    exact Module.Finite.iff_fg.mpr (IsNoetherian.noetherian _)
  haveI : Group.FG (CommGroup.torsion H) :=
    GroupFG.iff_add_fg.mpr (Module.Finite.iff_addGroup_fg.mp inferInstance)
  haveI : Finite (CommGroup.torsion H) :=
    CommGroup.finite_of_fg_torsion _ CommMonoid.torsion.isTorsion
  let f : CommGroup.torsion H →* K :=
    (Units.coeHom K).comp ((U).subtype.toMultiplicative.comp (CommGroup.torsion H).subtype)
  haveI : IsCyclic (CommGroup.torsion H) :=
    isCyclic_of_injective_ringHom f (Units.val_injective.comp
      (Subtype.val_injective.comp Subtype.val_injective))
  have hr : finrank ℤ (Additive (H ⧸ CommGroup.torsion H)) = Units.rank K + Fintype.card S :=
    (finrank_quotient_torsion_eq (M := Additive H)).trans (finrank_sUnits K G S)
  rw [index_range_powMonoidHom_eq_pow_mul (NeZero.ne n), hr, IsCyclic.index_powMonoidHom_range,
    Nat.gcd_eq_right (dvd_card_torsion_sUnits K G S n), ← pow_succ,
    Units.rank, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces]
  have hpos : 0 < InfinitePlace.nrRealPlaces K + InfinitePlace.nrComplexPlaces K := by
    rw [← InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces]
    exact Fintype.card_pos
  congr 1
  omega

end GaloisForLFunctions
