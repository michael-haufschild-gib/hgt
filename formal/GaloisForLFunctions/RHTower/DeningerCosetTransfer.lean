import GaloisForLFunctions.RHTower.DeningerPermutationSum

/-!
# Projection and transfer between permutation representations

For a subgroup contained in another, the cosets of the smaller project onto the cosets of the
larger, and when the index is finite the projection has a transfer running the other way, summing a
coset of the larger over the cosets of the smaller inside it.  The projection after the transfer is
multiplication by the index, so over a ring in which the index is invertible the projection is a
split epimorphism of representations.

* `deningerCosetProj` : the projection.
* `deningerCosetTransfer` : the transfer.
* `deningerCosetProj_transfer` : the composite is the index.
-/

namespace RHTower

open Monoid CategoryTheory

universe u

variable {G : Type u} [Group G] (k : Type u) [CommRing k] {H B : Subgroup G} (hHB : H ≤ B)

/-- The projection of coset spaces attached to an inclusion of subgroups. -/
def deningerCosetProjMap (x : G ⧸ H) : G ⧸ B :=
  Quotient.liftOn' x (fun g => (QuotientGroup.mk g : G ⧸ B)) (by
    intro a b hab
    exact QuotientGroup.eq.2 (hHB (QuotientGroup.leftRel_apply.1 hab)))

@[simp] theorem deningerCosetProjMap_mk (g : G) :
    deningerCosetProjMap hHB (QuotientGroup.mk g : G ⧸ H) = (QuotientGroup.mk g : G ⧸ B) := rfl

theorem deningerCosetProjMap_smul (g : G) (x : G ⧸ H) :
    deningerCosetProjMap hHB (g • x) = g • deningerCosetProjMap hHB x := by
  induction x using QuotientGroup.induction_on with
  | H a => rfl

/-- **The projection of permutation representations.** -/
noncomputable def deningerCosetProj :
    Rep.ofMulAction k G (G ⧸ H) ⟶ Rep.ofMulAction k G (G ⧸ B) :=
  deningerPermHom k (fun x => MonoidAlgebra.single (deningerCosetProjMap hHB x) (1 : k)) (by
    intro g x
    rw [Representation.ofMulAction_single, deningerCosetProjMap_smul])

section Transfer

variable [Fintype (↥B ⧸ H.subgroupOf B)]

/-- The coset of `g * z`, as a function of the class of `z` in the fibre. -/
def deningerFiberMap (g : G) (c : ↥B ⧸ H.subgroupOf B) : G ⧸ H :=
  Quotient.liftOn' c (fun z : B => (QuotientGroup.mk (g * (z : G)) : G ⧸ H)) (by
    intro z z' hzz'
    have h1 : (z : B)⁻¹ * z' ∈ H.subgroupOf B := QuotientGroup.leftRel_apply.1 hzz'
    rw [Subgroup.mem_subgroupOf] at h1
    refine QuotientGroup.eq.2 ?_
    have hcalc : (g * (z : G))⁻¹ * (g * (z' : G)) = ((z : G))⁻¹ * (z' : G) := by group
    rw [hcalc]
    exact h1)

omit [Fintype (↥B ⧸ H.subgroupOf B)] in
theorem deningerFiberMap_mk (g : G) (z : B) :
    deningerFiberMap (H := H) g (QuotientGroup.mk z) =
      (QuotientGroup.mk (g * (z : G)) : G ⧸ H) := rfl

omit [Fintype (↥B ⧸ H.subgroupOf B)] in
theorem deningerFiberMap_smul (g x : G) (c : ↥B ⧸ H.subgroupOf B) :
    deningerFiberMap (H := H) (x * g) c = x • deningerFiberMap (H := H) g c := by
  induction c using Quotient.inductionOn' with
  | h z =>
    show (QuotientGroup.mk (x * g * (z : G)) : G ⧸ H) =
      x • (QuotientGroup.mk (g * (z : G)) : G ⧸ H)
    rw [mul_assoc]
    rfl

/-- Shifting the fibre by an element of the larger subgroup. -/
def deningerFiberShift (b₀ : B) : (↥B ⧸ H.subgroupOf B) ≃ (↥B ⧸ H.subgroupOf B) where
  toFun := Quotient.map' (fun z => b₀ * z) (by
    intro z z' hzz'
    rw [QuotientGroup.leftRel_apply] at hzz' ⊢
    have hcalc : (b₀ * z)⁻¹ * (b₀ * z') = z⁻¹ * z' := by group
    rw [hcalc]
    exact hzz')
  invFun := Quotient.map' (fun z => b₀⁻¹ * z) (by
    intro z z' hzz'
    rw [QuotientGroup.leftRel_apply] at hzz' ⊢
    have hcalc : (b₀⁻¹ * z)⁻¹ * (b₀⁻¹ * z') = z⁻¹ * z' := by group
    rw [hcalc]
    exact hzz')
  left_inv := by
    rintro c
    induction c using Quotient.inductionOn' with
    | h z =>
      show (Quotient.mk'' (b₀⁻¹ * (b₀ * z)) : ↥B ⧸ H.subgroupOf B) = Quotient.mk'' z
      rw [← mul_assoc, inv_mul_cancel, one_mul]
  right_inv := by
    rintro c
    induction c using Quotient.inductionOn' with
    | h z =>
      show (Quotient.mk'' (b₀ * (b₀⁻¹ * z)) : ↥B ⧸ H.subgroupOf B) = Quotient.mk'' z
      rw [← mul_assoc, mul_inv_cancel, one_mul]

omit [Fintype (↥B ⧸ H.subgroupOf B)] in
theorem deningerFiberMap_shift (g : G) (b₀ : B) (c : ↥B ⧸ H.subgroupOf B) :
    deningerFiberMap (H := H) (g * (b₀ : G)) c =
      deningerFiberMap (H := H) g (deningerFiberShift b₀ c) := by
  induction c using Quotient.inductionOn' with
  | h z =>
    show (QuotientGroup.mk (g * (b₀ : G) * (z : G)) : G ⧸ H) =
      deningerFiberMap (H := H) g (Quotient.mk'' (b₀ * z))
    show _ = (QuotientGroup.mk (g * ((b₀ * z : B) : G)) : G ⧸ H)
    rw [Subgroup.coe_mul, mul_assoc]

/-- The transfer of coset spaces: a coset of the larger subgroup is sent to the sum of the cosets
of the smaller subgroup inside it. -/
noncomputable def deningerCosetTransferMap (x : G ⧸ B) : MonoidAlgebra k (G ⧸ H) :=
  Quotient.liftOn' x
    (fun g => ∑ c : ↥B ⧸ H.subgroupOf B,
      MonoidAlgebra.single (deningerFiberMap (H := H) g c) (1 : k))
    (by
      intro a b hab
      have hmem : a⁻¹ * b ∈ B := QuotientGroup.leftRel_apply.1 hab
      set b₀ : B := ⟨a⁻¹ * b, hmem⟩ with hb₀
      have hb : b = a * (b₀ : G) := by rw [hb₀]; group
      rw [hb]
      exact (Fintype.sum_equiv (deningerFiberShift b₀) _ _
        (fun c => by rw [deningerFiberMap_shift])).symm)

theorem deningerCosetTransferMap_mk (g : G) :
    deningerCosetTransferMap (H := H) k (QuotientGroup.mk g : G ⧸ B) =
      ∑ c : ↥B ⧸ H.subgroupOf B,
        MonoidAlgebra.single (deningerFiberMap (H := H) g c) (1 : k) := rfl

theorem deningerCosetTransferMap_smul (x : G) (y : G ⧸ B) :
    deningerCosetTransferMap (H := H) k (x • y) =
      Representation.ofMulAction k G (G ⧸ H) x (deningerCosetTransferMap (H := H) k y) := by
  induction y using QuotientGroup.induction_on with
  | H g =>
    show deningerCosetTransferMap (H := H) k (QuotientGroup.mk (x * g) : G ⧸ B) = _
    rw [deningerCosetTransferMap_mk, deningerCosetTransferMap_mk, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Representation.ofMulAction_single, deningerFiberMap_smul]

/-- **The transfer of permutation representations.** -/
noncomputable def deningerCosetTransfer :
    Rep.ofMulAction k G (G ⧸ B) ⟶ Rep.ofMulAction k G (G ⧸ H) :=
  deningerPermHom k (fun x => deningerCosetTransferMap (H := H) k x)
    (fun g x => deningerCosetTransferMap_smul k g x)

/-- **The projection after the transfer is the index.** -/
theorem deningerCosetProj_transfer (x : G ⧸ B) :
    (deningerCosetProj k hHB).hom (deningerCosetTransferMap (H := H) k x) =
      (Fintype.card (↥B ⧸ H.subgroupOf B)) • MonoidAlgebra.single x (1 : k) := by
  induction x using QuotientGroup.induction_on with
  | H g =>
    rw [deningerCosetTransferMap_mk, map_sum]
    have hterm : ∀ c : ↥B ⧸ H.subgroupOf B,
        (deningerCosetProj k hHB).hom
            (MonoidAlgebra.single (deningerFiberMap (H := H) g c) (1 : k)) =
          MonoidAlgebra.single (QuotientGroup.mk g : G ⧸ B) (1 : k) := by
      intro c
      induction c using Quotient.inductionOn' with
      | h z =>
        rw [deningerCosetProj, deningerPermHom_single, one_smul]
        show MonoidAlgebra.single
          (deningerCosetProjMap hHB (QuotientGroup.mk (g * (z : G)) : G ⧸ H)) (1 : k) = _
        rw [deningerCosetProjMap_mk]
        congr 1
        exact QuotientGroup.eq.2 (by simp)
    rw [Finset.sum_congr rfl (fun c _ => hterm c), Finset.sum_const, Finset.card_univ]

end Transfer

end RHTower
