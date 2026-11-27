import GaloisForLFunctions.RHTower.Artin.ArtinLocalEulerPolynomialOfAnInducedCharacter
import GaloisForLFunctions.RHTower.Artin.ArtinVirtualFrobeniusReciprocity
import Mathlib.GroupTheory.DoubleCoset
import Mathlib.RingTheory.IntegralDomain

/-! The self-pairing of an induced linear character counts the double cosets
on which the two characters agree on the subgroup intersection. -/

noncomputable section
open scoped Classical

namespace GaloisForLFunctions

variable {G : Type*} [Group G] (H : Subgroup G)

/-- Conjugation by this representative preserves the character on the overlap. -/
def LinearCharacter.Intertwines (χ : LinearCharacter H) (x : G) : Prop :=
  ∀ u : H, ∀ h : x⁻¹ * (u : G) * x ∈ H, χ ⟨x⁻¹ * (u : G) * x, h⟩ = χ u

private theorem intertwines_mul (χ : LinearCharacter H) {x : G}
    (hx : χ.Intertwines H x) (a b : H) : χ.Intertwines H ((a : G) * x * b) := by
  intro u hu
  let v := a⁻¹ * u * a
  let y := (a : G) * x * b
  have e : (b : G) * (y⁻¹ * (u : G) * y) * (b : G)⁻¹ =
      x⁻¹ * (v : G) * x := by
    change (b : G) * (((a : G) * x * b)⁻¹ * (u : G) * ((a : G) * x * b)) * (b : G)⁻¹ =
      x⁻¹ * ((a : G)⁻¹ * (u : G) * a) * x
    group
  let w : H := ⟨x⁻¹ * (v : G) * x, e ▸ H.mul_mem (H.mul_mem b.2 hu) (H.inv_mem b.2)⟩
  have hw : (⟨y⁻¹ * (u : G) * y, hu⟩ : H) = b⁻¹ * w * b := by
    apply Subtype.ext
    change y⁻¹ * (u : G) * y = (b : G)⁻¹ * (x⁻¹ * (v : G) * x) * b
    rw [← e]
    group
  have hχ (r s : H) : χ (r⁻¹ * s * r) = χ s := by
    rw [map_mul, map_mul, map_inv, mul_comm (χ r)⁻¹, mul_assoc, inv_mul_cancel, mul_one]
  change χ (⟨y⁻¹ * (u : G) * y, hu⟩ : H) = χ u
  exact (congrArg χ hw).trans ((hχ b w).trans ((hx v w.2).trans (hχ a u)))

/-- The overlap condition is invariant under the double coset relation. -/
theorem LinearCharacter.intertwines_doubleCoset (χ : LinearCharacter H) {x y : G}
    (h : DoubleCoset.mk H H x = DoubleCoset.mk H H y) :
    χ.Intertwines H x ↔ χ.Intertwines H y := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (DoubleCoset.eq H H x y).mp h
  refine ⟨fun hx => intertwines_mul H χ hx ⟨a, ha⟩ ⟨b, hb⟩, fun hy => ?_⟩
  have e : a⁻¹ * (a * x * b) * b⁻¹ = x := by group
  exact e ▸ intertwines_mul H χ hy (⟨a, ha⟩ : H)⁻¹ (⟨b, hb⟩ : H)⁻¹

private abbrev overlap (x : G) : Subgroup H :=
  (H.map (MulAut.conj x).toMonoidHom).subgroupOf H

private theorem mem_overlap (x : G) (u : H) :
    u ∈ overlap H x ↔ x⁻¹ * (u : G) * x ∈ H := by
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

private def overlapConj (x : G) : overlap H x →* H where
  toFun u := ⟨x⁻¹ * ((u : H) : G) * x, (mem_overlap H x u).mp u.2⟩
  map_one' := Subtype.ext (by
    change x⁻¹ * 1 * x = 1
    group)
  map_mul' u v := Subtype.ext (by
    change x⁻¹ * (((u : H) : G) * ((v : H) : G)) * x =
      (x⁻¹ * ((u : H) : G) * x) * (x⁻¹ * ((v : H) : G) * x)
    group)

variable [Fintype G]

/-- Enumerate the double cosets by the surjection from the finite group. -/
abbrev doubleCosetFintype : Fintype (DoubleCoset.Quotient (H : Set G) H) :=
  Fintype.ofSurjective (DoubleCoset.mk H H) fun q => ⟨q.out, DoubleCoset.out_eq' H H q⟩

private theorem sum_pair_over_overlap (χ : LinearCharacter H) (x : G) :
    (∑ u : H, ((χ u : ℂ)⁻¹) * extendByZero H (fun v => (χ v : ℂ)) (x⁻¹ * (u : G) * x)) =
      if χ.Intertwines H x then (Nat.card (overlap H x) : ℂ) else 0 := by
  let f (u : H) := ((χ u : ℂ)⁻¹) * extendByZero H (fun v => (χ v : ℂ)) (x⁻¹ * (u : G) * x)
  let ρ : LinearCharacter (overlap H x) := (χ.comp (overlap H x).subtype)⁻¹ * χ.comp (overlapConj H x)
  let r : overlap H x →* ℂ := (Units.coeHom ℂ).comp ρ
  have he : r = 1 ↔ χ.Intertwines H x := by
    constructor
    · intro h u hu
      have e : (χ u)⁻¹ * χ ⟨x⁻¹ * (u : G) * x, hu⟩ = 1 :=
        Units.ext (DFunLike.congr_fun h (⟨u, (mem_overlap H x u).mpr hu⟩ : overlap H x))
      exact (inv_mul_eq_one.mp e).symm
    · intro h
      ext u
      change (((χ (u : H))⁻¹ * χ (overlapConj H x u) : ℂˣ) : ℂ) = 1
      have hu : χ (overlapConj H x u) = χ (u : H) :=
        h (u : H) ((mem_overlap H x u).mp u.2)
      rw [hu, inv_mul_cancel, Units.val_one]
  calc
    (∑ u : H, f u) = ∑ u ∈ Finset.univ.filter (fun u => u ∈ overlap H x), f u := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun u _ => ?_
      split_ifs with h
      · rfl
      · dsimp only [f]
        rw [extendByZero_of_notMem H _ (fun hu => h ((mem_overlap H x u).mpr hu)), mul_zero]
    _ = ∑ u : overlap H x, r u := by
      rw [Finset.sum_subtype _ (p := fun u => u ∈ overlap H x) (fun u => by simp)]
      refine Finset.sum_congr rfl fun u _ => ?_
      dsimp only [f]
      rw [extendByZero_of_mem H _ ((mem_overlap H x u).mp u.2)]
      exact (congrArg (· * (χ (overlapConj H x u) : ℂ))
        (Units.val_inv_eq_inv_val (χ (u : H)))).symm
    _ = _ := by
      rw [sum_hom_units, Nat.card_eq_fintype_card, Nat.cast_ite, Nat.cast_zero]
      exact if_congr he rfl rfl

/-- Each compatible double coset contributes one to Frobenius reciprocity
for the restriction of an induced linear character. -/
theorem inducedLinearCharacter_restriction_pairing (χ : LinearCharacter H) :
    letI := doubleCosetFintype H
    (Nat.card H : ℂ)⁻¹ * ∑ u : H, (χ u : ℂ)⁻¹ *
      inducedFunction H (fun v => (χ v : ℂ)) (u : G) =
      ∑ q : DoubleCoset.Quotient (H : Set G) H, if χ.Intertwines H q.out then (1 : ℂ) else 0 := by
  let Q := DoubleCoset.Quotient (H : Set G) H
  letI : Fintype Q := doubleCosetFintype H
  let p := DoubleCoset.mk H H
  let c := (Nat.card H : ℂ)
  let w (x : G) := (Nat.card (overlap H x) : ℂ)
  let F (u : H) (x : G) :=
    (χ u : ℂ)⁻¹ * extendByZero H (fun v => (χ v : ℂ)) (x⁻¹ * (u : G) * x)
  have hu (u : H) :
      (χ u : ℂ)⁻¹ * inducedFunction H (fun v => (χ v : ℂ)) (u : G) = c⁻¹ * ∑ x, F u x := by
    unfold inducedFunction
    rw [← Equiv.sum_comp (Equiv.inv G), mul_left_comm, Finset.mul_sum]
    simp only [Equiv.inv_apply, inv_inv, F, c]
  have hw (q : Q) : (∑ x : G, if p x = q then w x else 0) = c * c := by
    change _ = (Nat.card H : ℂ) * Nat.card H
    rw [← Nat.cast_mul, ← sum_card_decomposition_doubleCoset H H q.out, Nat.cast_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Nat.cast_ite, Nat.cast_zero]
    refine if_congr ?_ rfl rfl
    have hpq : p q.out = q := DoubleCoset.out_eq' H H q
    exact ⟨fun e => (DoubleCoset.eq H H _ _).mp (hpq.trans e.symm),
      fun e => ((DoubleCoset.eq H H _ _).mpr e).symm.trans hpq⟩
  have hw' (q : Q) (v : ℂ) :
      (∑ x : G, if p x = q then w x * v else 0) = (c * c) * v := by
    rw [← hw q, Finset.sum_mul]
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs with h
    · rfl
    · exact (zero_mul v).symm
  have hx (x : G) :
      (if χ.Intertwines H x then w x else 0) =
        ∑ q : Q, if p x = q then w x * (if χ.Intertwines H q.out then 1 else 0) else 0 := by
    rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]
    have h := (χ.intertwines_doubleCoset H (DoubleCoset.out_eq' H H (p x)).symm)
    rw [h]
    split_ifs
    · rw [mul_one]
    · rw [mul_zero]
  have hc : c ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  calc
    _ = c⁻¹ * (c⁻¹ * ∑ x : G, ∑ u : H, F u x) := by
      simp_rw [hu, ← Finset.mul_sum]
      rw [Finset.sum_comm (s := (Finset.univ : Finset H)) (t := (Finset.univ : Finset G))]
    _ = c⁻¹ * (c⁻¹ * ∑ x : G, if χ.Intertwines H x then w x else 0) := by
      simp only [F, sum_pair_over_overlap, w]
    _ = ∑ q : Q, if χ.Intertwines H q.out then (1 : ℂ) else 0 := by
      simp only [hx]
      rw [Finset.sum_comm, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [hw', ← mul_assoc c⁻¹ (c * c), ← mul_assoc c⁻¹ c c, inv_mul_cancel₀ hc,
        one_mul, ← mul_assoc c⁻¹ c, inv_mul_cancel₀ hc, one_mul]

/-- The normalized self-pairing of the induced character is the number of compatible cosets. -/
theorem characterPairing_inducedLinear_eq (χ : LinearCharacter H) :
    letI := doubleCosetFintype H
    characterPairing G (inducedFunction H (fun v => (χ v : ℂ)))
        (inducedFunction H (fun v => (χ v : ℂ))) =
      ∑ q : DoubleCoset.Quotient (H : Set G) H, if χ.Intertwines H q.out then (1 : ℂ) else 0 := by
  let ρ := monomialVirtualCharacter G H χ
  have hr : ρ.val = inducedFunction H (fun v => (χ v : ℂ)) := by
    funext g
    change (monomialVirtualCharacter G H χ).val g = _
    rw [monomialVirtualCharacter_apply, induced_character_eq_inducedFunction]
    congr 1
    funext u
    exact linearCharacterRepresentation_character χ u
  have h := virtualCharacter_monomial_pairing_restriction G H χ ρ
  change characterPairing G ρ.val ρ.val =
    characterPairing H (fun u : H => ρ.val (u : G)) (linearVirtualCharacter H χ).val at h
  rw [← hr, h, characterPairing_comm H, hr]
  calc
    _ = (Nat.card H : ℂ)⁻¹ * ∑ u : H, (χ u : ℂ)⁻¹ *
        inducedFunction H (fun v => (χ v : ℂ)) (u : G) := by
      unfold characterPairing
      refine congrArg ((Nat.card H : ℂ)⁻¹ * ·) (Finset.sum_congr rfl fun u _ => ?_)
      rw [linearVirtualCharacter_apply, map_inv, Units.val_inv_eq_inv_val, mul_comm]
    _ = _ := inducedLinearCharacter_restriction_pairing H χ

end GaloisForLFunctions
