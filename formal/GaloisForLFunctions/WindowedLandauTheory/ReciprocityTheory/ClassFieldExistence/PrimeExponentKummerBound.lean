import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.KummerRadicalPairing
import Mathlib.GroupTheory.FiniteAbelian.Duality

/-! A finite abelian extension of exponent dividing n lies in the field of
all n-th radicals. A cyclic character detects each nontrivial
automorphism through a simple Kummer subextension. -/

noncomputable section

open IntermediateField
open scoped IsMulCommutative

namespace GlobalTheory.Kummer

variable {F E : Type*} [Field F] [Field E] [Algebra F E]
  [FiniteDimensional F E] [IsAbelianGalois F E]
  {p : ℕ} [NeZero p] [HasEnoughRootsOfUnity F p]

local notation "G" => Gal(E/F)

local instance : CommGroup G :=
  { (inferInstance : Group G) with mul_comm := IsMulCommutative.is_comm.comm }

/-- Each nontrivial automorphism moves a p-th root of a scalar. -/
theorem exists_moved_radical_of_exponent
    (hpow : ∀ σ : G, σ ^ p = 1) {σ : G} (hσ : σ ≠ 1) :
    ∃ (a : Fˣ) (x : E), x ^ p = algebraMap F E (a : F) ∧ σ x ≠ x := by
  letI : HasEnoughRootsOfUnity F (Monoid.exponent G) :=
    HasEnoughRootsOfUnity.of_dvd F ((Monoid.exponent_dvd_iff_forall_pow_eq_one).mpr hpow)
  obtain ⟨χ, hχ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity G F hσ
  let ψ := χ.codRestrict (rootsOfUnity p F) fun g => by
    rw [mem_rootsOfUnity, ← map_pow, hpow, map_one]
  have hψ : ψ σ ≠ 1 := fun h => hχ (congrArg Subtype.val h)
  let T := fixedField ψ.ker
  letI : IsAbelianGalois F T := IsAbelianGalois.of_algHom T.val
  let r : G →* Gal(T/F) := AlgEquiv.restrictNormalHom T
  have hr : r.ker = ψ.ker := T.restrictNormalHom_ker.trans (fixingSubgroup_fixedField _)
  let e := (QuotientGroup.quotientKerEquivOfSurjective r
    (AlgEquiv.restrictNormalHom_surjective (F := F) (K₁ := T) (E := E))).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hr).trans (QuotientGroup.quotientKerEquivRange ψ))
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot F p
  have hd : Nat.card ψ.range ∣ p :=
    (Subgroup.card_subgroup_dvd_card ψ.range).trans (dvd_of_eq hζ.card_rootsOfUnity)
  let d := Nat.card ψ.range
  letI : NeZero d := ⟨Nat.card_pos.ne'⟩
  letI : HasEnoughRootsOfUnity F d := HasEnoughRootsOfUnity.of_dvd F hd
  letI : IsCyclic (rootsOfUnity p F) := rootsOfUnity.isCyclic F p
  letI : IsCyclic Gal(T/F) := isCyclic_of_injective e.toMonoidHom e.injective
  have hT : Module.finrank F T = d := by
    rw [← IsGalois.card_aut_eq_finrank, Nat.card_congr e.toEquiv]
  have hroot : (primitiveRoots (Module.finrank F T) F).Nonempty := by
    rw [hT]
    obtain ⟨ζ', hζ'⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot F d
    exact ⟨ζ', (mem_primitiveRoots (NeZero.pos d)).mpr hζ'⟩
  obtain ⟨x, ⟨a, ha⟩, hx⟩ := exists_root_adjoin_eq_top_of_isCyclic F T hroot
  rw [hT] at ha
  have hmove : r σ x ≠ x := by
    intro h
    have hT' : Algebra.adjoin F {x} = ⊤ := by
      rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
        (IsAlgebraic.of_finite F x), hx, IntermediateField.top_toSubalgebra]
    have hfix : r σ = 1 := by
      have heq : (r σ).toAlgHom = (1 : Gal(T/F)).toAlgHom :=
        AlgHom.ext_of_adjoin_eq_top hT' (fun _ hx => Set.mem_singleton_iff.mp hx ▸ h)
      exact AlgEquiv.ext fun y => DFunLike.congr_fun heq y
    apply hψ
    apply MonoidHom.mem_ker.mp
    rw [← hr]
    exact hfix
  have ha0 : a ≠ 0 := by
    intro h
    have hx0 : x = 0 := by
      rw [h, map_zero] at ha
      by_contra hne
      exact pow_ne_zero d hne ha.symm
    apply hmove
    rw [hx0, map_zero]
  obtain ⟨m, hm⟩ := hd
  refine ⟨(Units.mk0 a ha0) ^ m, x.val, ?_, ?_⟩
  · have he : x.val ^ d = algebraMap F E a := (congrArg Subtype.val ha).symm
    rw [hm, pow_mul, he, Units.val_pow_eq_pow_val, Units.val_mk0, map_pow]
  · intro h
    apply hmove
    apply Subtype.ext
    exact (σ.restrictNormal_commutes T x).trans h

theorem le_radicalField_top_of_exponent
    {Ω : Type*} [Field Ω] [Algebra F Ω] [IsAlgClosed Ω] (j : E →ₐ[F] Ω)
    (hpow : ∀ σ : G, σ ^ p = 1) :
    j.fieldRange ≤ radicalField (Ω := Ω) (⊤ : Subgroup (PowerClasses F p)) := by
  let L := radicalField (Ω := Ω) (⊤ : Subgroup (PowerClasses F p))
  let T := L.comap j
  have ht : T.fixingSubgroup = ⊥ := by
    apply le_antisymm _ bot_le
    intro σ hσ
    rw [Subgroup.mem_bot]
    by_contra hne
    obtain ⟨a, x, hx, hmove⟩ := exists_moved_radical_of_exponent hpow hne
    have hxT : x ∈ T :=
      mem_radicalField (a := a) (Subgroup.mem_top _) (by rw [← map_pow, hx]; exact j.commutes (a : F))
    exact hmove (hσ ⟨x, hxT⟩)
  have hT : T = ⊤ := by
    rw [← IsGalois.fixedField_fixingSubgroup T, ht, fixedField_bot]
  rintro _ ⟨x, rfl⟩
  have hx : x ∈ T := hT.symm ▸ IntermediateField.mem_top
  exact hx

theorem finrank_le_card_powerClasses_of_exponent
    [CharZero F] [Finite (PowerClasses F p)] (hpow : ∀ σ : G, σ ^ p = 1) :
    Module.finrank F E ≤ Nat.card (PowerClasses F p) := by
  let Ω := AlgebraicClosure F
  let j : E →ₐ[F] Ω := IsAlgClosed.lift
  let L := radicalField (Ω := Ω) (⊤ : Subgroup (PowerClasses F p))
  have h : j.fieldRange ≤ L := le_radicalField_top_of_exponent j hpow
  letI : FiniteDimensional F L := radicalField_finiteDimensional Ω _
  calc
    Module.finrank F E = Module.finrank F j.fieldRange := j.equivFieldRange.toLinearEquiv.finrank_eq
    _ ≤ Module.finrank F L :=
      LinearMap.finrank_le_finrank_of_injective (f := (IntermediateField.inclusion h).toLinearMap)
        (IntermediateField.inclusion h).injective
    _ = Nat.card (PowerClasses F p) := by
      change Module.finrank F (radicalField (Ω := Ω) (⊤ : Subgroup (PowerClasses F p))) = _
      rw [finrank_radicalField, Nat.card_congr Subgroup.topEquiv.toEquiv]

theorem exists_moved_radical_of_prime_exponent [Fact p.Prime]
    (hpow : ∀ σ : G, σ ^ p = 1) {σ : G} (hσ : σ ≠ 1) :
    ∃ (a : Fˣ) (x : E), x ^ p = algebraMap F E (a : F) ∧ σ x ≠ x :=
  exists_moved_radical_of_exponent hpow hσ

theorem le_radicalField_top_of_prime_exponent [Fact p.Prime]
    {Ω : Type*} [Field Ω] [Algebra F Ω] [IsAlgClosed Ω] (j : E →ₐ[F] Ω)
    (hpow : ∀ σ : G, σ ^ p = 1) :
    j.fieldRange ≤ radicalField (Ω := Ω) (⊤ : Subgroup (PowerClasses F p)) :=
  le_radicalField_top_of_exponent j hpow

theorem finrank_le_card_powerClasses_of_prime_exponent [Fact p.Prime]
    [CharZero F] [Finite (PowerClasses F p)] (hpow : ∀ σ : G, σ ^ p = 1) :
    Module.finrank F E ≤ Nat.card (PowerClasses F p) :=
  finrank_le_card_powerClasses_of_exponent hpow

end GlobalTheory.Kummer

#print axioms GlobalTheory.Kummer.exists_moved_radical_of_exponent
#print axioms GlobalTheory.Kummer.le_radicalField_top_of_exponent
#print axioms GlobalTheory.Kummer.finrank_le_card_powerClasses_of_exponent
