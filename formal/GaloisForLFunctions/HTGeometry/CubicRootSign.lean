import GaloisForLFunctions.HTGeometry.CubicGaloisGroup
import GaloisForLFunctions.HTGeometry.VandermondeFixed

/-!
# Cubic root permutations and their discriminant signs

An arbitrary ordering of the three roots gives a Vandermonde discriminant
radical. Its transformation law identifies even and odd root permutations
inside any common normal splitting field.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry
open Polynomial
variable {F L : Type*} [Field F] [Field L] [Algebra F L]

theorem vandermondeProd_three (v : Fin 3 → L) :
    vandermondeProd v = (v 1 - v 0) * (v 2 - v 0) * (v 2 - v 1) := by
  classical
  have h0 : Finset.Ioi (0 : Fin 3) = {1, 2} := by ext i; fin_cases i <;> simp
  have h1 : Finset.Ioi (1 : Fin 3) = {2} := by ext i; fin_cases i <;> simp
  have h2 : Finset.Ioi (2 : Fin 3) = ∅ := by ext i; fin_cases i <;> simp
  simp [vandermondeProd, Fin.prod_univ_three, h0, h1, h2]

theorem cubic_roots_eq_enum (P : Cubic F) (hsep : P.toPoly.Separable)
    (e : P.toPoly.rootSet L ≃ Fin 3) :
    (P.map (algebraMap F L)).roots =
      {(e.symm 0 : L), (e.symm 1 : L), (e.symm 2 : L)} := by
  classical
  rw [Cubic.map_roots]
  apply (Multiset.Nodup.ext (Polynomial.nodup_roots hsep.map) ?_).mpr
  · intro x
    have hm : x ∈ (P.toPoly.map (algebraMap F L)).roots ↔ x ∈ P.toPoly.rootSet L := by
      simp only [rootSet, Finset.mem_coe, Multiset.mem_toFinset, aroots_def]
    rw [hm]
    constructor
    · intro hx
      obtain ⟨k, hk⟩ := e.symm.surjective ⟨x, hx⟩
      have hk' := congrArg Subtype.val hk
      fin_cases k <;> simp_all
    · intro hx
      simp at hx
      rcases hx with hx | hx | hx <;> rw [hx] <;> exact (e.symm _).property
  · simp
    exact ⟨⟨e.symm.injective.ne (by decide), e.symm.injective.ne (by decide)⟩,
      e.symm.injective.ne (by decide)⟩

/-- The Vandermonde in an arbitrary ordering of the cubic roots is its discriminant radical. -/
def cubicOrderedDiscriminantRoot (P : Cubic F) (e : P.toPoly.rootSet L ≃ Fin 3) : L :=
  algebraMap F L P.a ^ 2 * vandermondeProd (fun k => (e.symm k : L))

theorem cubicOrderedDiscriminantRoot_sq (P : Cubic F) (ha : P.a ≠ 0)
    (hsep : P.toPoly.Separable) (e : P.toPoly.rootSet L ≃ Fin 3) :
    cubicOrderedDiscriminantRoot P e * cubicOrderedDiscriminantRoot P e =
      algebraMap F L P.discr := by
  rw [Cubic.discr_eq_prod_three_roots ha (cubic_roots_eq_enum P hsep e),
    cubicOrderedDiscriminantRoot, vandermondeProd_three]
  ring

/-- Root permutations in the common ambient field, with an explicit ordering. -/
def cubicOrderedRootAction (P : Cubic F)
    [Fact ((P.toPoly.map (algebraMap F L)).Splits)]
    (e : P.toPoly.rootSet L ≃ Fin 3) : (L ≃ₐ[F] L) →* Equiv.Perm (Fin 3) :=
  e.permCongrHom.toMonoidHom.comp
    ((Gal.galActionHom P.toPoly L).comp (Gal.restrict P.toPoly L))

theorem cubicOrderedRootAction_apply (P : Cubic F)
    [Fact ((P.toPoly.map (algebraMap F L)).Splits)]
    (e : P.toPoly.rootSet L ≃ Fin 3) (σ : L ≃ₐ[F] L) (k : Fin 3) :
    (e.symm (cubicOrderedRootAction P e σ k) : L) = σ (e.symm k) := by
  change (e.symm (e (Gal.galActionHom P.toPoly L (Gal.restrict P.toPoly L σ)
    (e.symm k))) : L) = _
  rw [e.symm_apply_apply]
  exact Gal.galActionHom_restrict P.toPoly L σ (e.symm k)

theorem cubicOrderedDiscriminantRoot_map (P : Cubic F)
    [Fact ((P.toPoly.map (algebraMap F L)).Splits)]
    (e : P.toPoly.rootSet L ≃ Fin 3) (σ : L ≃ₐ[F] L) :
    σ (cubicOrderedDiscriminantRoot P e) =
      (Equiv.Perm.sign (cubicOrderedRootAction P e σ) : ℤ) •
        cubicOrderedDiscriminantRoot P e := by
  rw [cubicOrderedDiscriminantRoot, map_mul, map_pow, σ.commutes, map_vandermondeProd]
  have hcomp : (fun k => σ (e.symm k : L)) =
      (fun k => (e.symm k : L)) ∘ cubicOrderedRootAction P e σ := by
    funext k
    exact (cubicOrderedRootAction_apply P e σ k).symm
  rw [hcomp, vandermondeProd_comp]
  simp only [zsmul_eq_mul]
  ring

/-- Each nonsquare irreducible cubic gives every permutation in any normal splitting ambient field. -/
theorem cubicOrderedRootAction_surjective [CharZero F] [Normal F L]
    (P : Cubic F) (ha : P.a ≠ 0) (hirr : Irreducible P.toPoly)
    (hns : ¬ IsSquare P.discr) [Fact ((P.toPoly.map (algebraMap F L)).Splits)]
    (e : P.toPoly.rootSet L ≃ Fin 3) : Function.Surjective (cubicOrderedRootAction P e) := by
  classical
  have hcard : Nat.card (Equiv.Perm (P.toPoly.rootSet L)) = 6 := by
    rw [Nat.card_perm, Nat.card_congr e]
    norm_num
  have hbij : Function.Bijective (Gal.galActionHom P.toPoly L) := by
    apply (Gal.galActionHom_injective P.toPoly L).bijective_of_nat_card_le
    rw [hcard, cubic_galois_card_eq_six P ha hirr hns]
  exact e.permCongrHom.surjective.comp
    (hbij.2.comp (Gal.restrict_surjective P.toPoly L))

/-- Fixing the discriminant radical is equivalent to even root permutation. -/
theorem cubicOrderedRootAction_sign_eq_one_iff [CharZero L]
    (P : Cubic F) [Fact ((P.toPoly.map (algebraMap F L)).Splits)]
    (e : P.toPoly.rootSet L ≃ Fin 3) (σ : L ≃ₐ[F] L)
    (hr : cubicOrderedDiscriminantRoot P e ≠ 0) :
    Equiv.Perm.sign (cubicOrderedRootAction P e σ) = 1 ↔
      σ (cubicOrderedDiscriminantRoot P e) = cubicOrderedDiscriminantRoot P e := by
  have hm := cubicOrderedDiscriminantRoot_map P e σ
  constructor
  · intro h
    simpa [h] using hm
  · intro h
    rcases Int.units_eq_one_or (Equiv.Perm.sign (cubicOrderedRootAction P e σ)) with he | he
    · exact he
    · have hn : σ (cubicOrderedDiscriminantRoot P e) = -cubicOrderedDiscriminantRoot P e := by
        simpa [he] using hm
      exact (hr (CharZero.eq_neg_self_iff.mp (h.symm.trans hn))).elim

/-- Negating the discriminant radical is equivalent to odd root permutation. -/
theorem cubicOrderedRootAction_sign_eq_neg_one_iff [CharZero L]
    (P : Cubic F) [Fact ((P.toPoly.map (algebraMap F L)).Splits)]
    (e : P.toPoly.rootSet L ≃ Fin 3) (σ : L ≃ₐ[F] L)
    (hr : cubicOrderedDiscriminantRoot P e ≠ 0) :
    Equiv.Perm.sign (cubicOrderedRootAction P e σ) = -1 ↔
      σ (cubicOrderedDiscriminantRoot P e) = -cubicOrderedDiscriminantRoot P e := by
  have hm := cubicOrderedDiscriminantRoot_map P e σ
  constructor
  · intro h
    simpa [h] using hm
  · intro h
    rcases Int.units_eq_one_or (Equiv.Perm.sign (cubicOrderedRootAction P e σ)) with he | he
    · have hp : σ (cubicOrderedDiscriminantRoot P e) = cubicOrderedDiscriminantRoot P e := by
        simpa [he] using hm
      exact (hr (CharZero.eq_neg_self_iff.mp (hp.symm.trans h))).elim
    · exact he

end GaloisForLFunctions.HTGeometry
