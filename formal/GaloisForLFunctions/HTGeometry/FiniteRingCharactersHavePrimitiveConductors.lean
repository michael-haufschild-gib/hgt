import GaloisForLFunctions.HTGeometry.PrimitiveFiniteRingCharactersHaveGaussTransforms
import Mathlib.Data.SetLike.Fintype
import Mathlib.Algebra.Ring.Prod

/-!
# Conductors of characters of finite commutative rings

A unit congruent to one modulo a sum of ideals splits into units in the
two congruence kernels. Hence the sum of all character-descent ideals is
itself a descent ideal. It is the unique greatest such ideal, and the
unique character it induces on the quotient is primitive. The kernel
criterion also identifies primitive characters on any isomorphic quotient.
-/

noncomputable section
open scoped Classical
namespace GaloisForLFunctions.FiniteRing

variable {R C : Type*} [CommRing R] [Finite R] [CommMonoidWithZero C]

/-- Units congruent to one modulo a sum of ideals split into the two congruence kernels. -/
theorem exists_unit_congruence_decomposition (I J : Ideal R) (u : Rˣ)
    (hu : (u : R) - 1 ∈ I ⊔ J) :
    ∃ v w : Rˣ, (v : R) - 1 ∈ I ∧ (w : R) - 1 ∈ J ∧ u = v * w := by
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp hu
  let f := (Ideal.Quotient.mk I).prod (Ideal.Quotient.mk J)
  have hI : Ideal.Quotient.mk I (1 + y) = Ideal.Quotient.mk I (u : R) := by
    apply Ideal.Quotient.eq.mpr
    have he : 1 + y - (u : R) = -x := by linear_combination hxy
    rw [he]
    exact I.neg_mem hx
  have hJ : Ideal.Quotient.mk J (1 + y) = 1 := by
    rw [map_add, map_one, Ideal.Quotient.eq_zero_iff_mem.mpr hy, add_zero]
  have hf : IsUnit (f (1 + y)) := by
    apply Prod.isUnit_iff.mpr
    change IsUnit (Ideal.Quotient.mk I (1 + y)) ∧ IsUnit (Ideal.Quotient.mk J (1 + y))
    rw [hI, hJ]
    exact ⟨u.isUnit.map _, isUnit_one⟩
  obtain ⟨w, hw⟩ := exists_unit_map_eq f (1 + y) hf
  have hwI : Ideal.Quotient.mk I (w : R) = Ideal.Quotient.mk I (u : R) :=
    (congrArg Prod.fst hw).trans hI
  have hwJ : Ideal.Quotient.mk J (w : R) = 1 := (congrArg Prod.snd hw).trans hJ
  refine ⟨u * w⁻¹, w, ?_, ?_, by simp⟩
  · apply Ideal.Quotient.eq.mp
    rw [map_one, Units.val_mul, map_mul, ← hwI, ← map_mul, Units.mul_inv, map_one]
  · apply Ideal.Quotient.eq.mp
    simpa only [map_one] using hwJ

theorem FactorsThrough.bot (χ : MulChar R C) : FactorsThrough χ ⊥ := by
  apply (factorsThrough_iff χ ⊥).mpr
  intro u hu
  have hu' : (u : R) = 1 := sub_eq_zero.mp (show (u : R) - 1 = 0 from hu)
  rw [hu', map_one]

theorem FactorsThrough.of_le {χ : MulChar R C} {I J : Ideal R}
    (hχ : FactorsThrough χ J) (hIJ : I ≤ J) : FactorsThrough χ I :=
  (factorsThrough_iff χ I).mpr fun u hu => (factorsThrough_iff χ J).mp hχ u (hIJ hu)

/-- Descent ideals are closed under sums. -/
theorem FactorsThrough.sup {χ : MulChar R C} {I J : Ideal R}
    (hI : FactorsThrough χ I) (hJ : FactorsThrough χ J) : FactorsThrough χ (I ⊔ J) := by
  apply (factorsThrough_iff χ (I ⊔ J)).mpr
  intro u hu
  obtain ⟨v, w, hv, hw, rfl⟩ := exists_unit_congruence_decomposition I J u hu
  rw [Units.val_mul, map_mul, (factorsThrough_iff χ I).mp hI v hv,
    (factorsThrough_iff χ J).mp hJ w hw, one_mul]

theorem FactorsThrough.finset_sup (χ : MulChar R C) (s : Finset (Ideal R))
    (hs : ∀ I ∈ s, FactorsThrough χ I) : FactorsThrough χ (s.sup id) := by
  induction s using Finset.induction_on with
  | empty => simpa using FactorsThrough.bot χ
  | @insert I s hIs ih =>
    rw [Finset.sup_insert]
    exact (hs I (Finset.mem_insert_self _ _)).sup
      (ih fun J hJ => hs J (Finset.mem_insert_of_mem hJ))

/-- The largest ideal through which the unit character descends. -/
def conductorIdeal (χ : MulChar R C) : Ideal R :=
  letI := Fintype.ofFinite (Ideal R)
  (Finset.univ.filter (FactorsThrough χ)).sup id

theorem factorsThrough_conductorIdeal (χ : MulChar R C) :
    FactorsThrough χ (conductorIdeal χ) := by
  letI := Fintype.ofFinite (Ideal R)
  exact FactorsThrough.finset_sup χ _ fun I hI => (Finset.mem_filter.mp hI).2

theorem factorsThrough_iff_le_conductorIdeal (χ : MulChar R C) (I : Ideal R) :
    FactorsThrough χ I ↔ I ≤ conductorIdeal χ := by
  constructor
  · intro hI
    letI := Fintype.ofFinite (Ideal R)
    exact Finset.le_sup (f := id) (Finset.mem_filter.mpr ⟨Finset.mem_univ I, hI⟩)
  · exact (factorsThrough_conductorIdeal χ).of_le

theorem isPrimitive_iff_conductorIdeal_eq_bot (χ : MulChar R C) :
    IsPrimitive χ ↔ conductorIdeal χ = ⊥ := by
  constructor
  · intro hχ
    exact hχ _ (factorsThrough_conductorIdeal χ)
  · intro hχ I hI
    apply le_bot_iff.mp
    simpa only [hχ] using (factorsThrough_iff_le_conductorIdeal χ I).mp hI

theorem factorsThrough_ker_iff {S : Type*} [CommRing S] (f : R →+* S)
    (χ : MulChar R C) :
    FactorsThrough χ (RingHom.ker f) ↔
      (Units.map f.toMonoidHom).ker ≤ χ.toUnitHom.ker := by
  rw [factorsThrough_iff]
  constructor
  · intro h u hu
    apply MonoidHom.mem_ker.mpr
    apply Units.ext
    apply h
    change f ((u : R) - 1) = 0
    rw [map_sub, map_one, sub_eq_zero]
    exact congrArg Units.val (MonoidHom.mem_ker.mp hu)
  · intro h u hu
    change f ((u : R) - 1) = 0 at hu
    rw [map_sub, map_one, sub_eq_zero] at hu
    have hq : Units.map f.toMonoidHom u = 1 := Units.ext hu
    exact congrArg Units.val (h (MonoidHom.mem_ker.mpr hq))

/-- Descent through any surjective ring map is decided by the conductor ideal. -/
theorem exists_inflateChar_eq_iff_ker_le_conductorIdeal {S : Type*} [CommRing S]
    (f : R →+* S) (hf : Function.Surjective f) (χ : MulChar R C) :
    (∃ χ' : MulChar S C, inflateChar f χ' = χ) ↔
      RingHom.ker f ≤ conductorIdeal χ := by
  rw [exists_inflateChar_eq_iff f hf, ← factorsThrough_ker_iff,
    factorsThrough_iff_le_conductorIdeal]

/-- A character induced from a quotient with conductor kernel is primitive on that quotient. -/
theorem isPrimitive_of_ker_eq_conductorIdeal {S : Type*} [CommRing S]
    (f : R →+* S) (hf : Function.Surjective f) (χ : MulChar R C) (χ' : MulChar S C)
    (hχ' : inflateChar f χ' = χ) (hker : RingHom.ker f = conductorIdeal χ) :
    IsPrimitive χ' := by
  letI : Finite S := Finite.of_surjective f hf
  intro J hJ
  have hχf (u : Rˣ) : χ' (f (u : R)) = χ (u : R) := by
    exact (inflateChar_unit _ _ u).symm.trans (DFunLike.congr_fun hχ' (u : R))
  have hdesc : FactorsThrough χ (Ideal.comap f J) := by
    apply (factorsThrough_iff χ _).mpr
    intro u hu
    rw [← hχf]
    apply (factorsThrough_iff χ' J).mp hJ (Units.map f.toMonoidHom u)
    change f (u : R) - 1 ∈ J
    simpa only [Ideal.mem_comap, map_sub, map_one] using hu
  have hle : Ideal.comap f J ≤ RingHom.ker f := by
    rw [hker]
    exact (factorsThrough_iff_le_conductorIdeal χ _).mp hdesc
  apply le_bot_iff.mp
  intro y hy
  obtain ⟨r, hr⟩ := hf y
  have hrJ : r ∈ Ideal.comap f J := by
    change f r ∈ J
    rwa [hr]
  exact show y = 0 from hr.symm.trans (hle hrJ)

/-- The unique character on the conductor quotient inducing the original character. -/
def conductorCharacter (χ : MulChar R C) : MulChar (R ⧸ conductorIdeal χ) C :=
  Classical.choose (factorsThrough_conductorIdeal χ)

theorem inflate_conductorCharacter (χ : MulChar R C) :
    inflateChar (Ideal.Quotient.mk (conductorIdeal χ)) (conductorCharacter χ) = χ :=
  Classical.choose_spec (factorsThrough_conductorIdeal χ)

theorem conductorCharacter_unique (χ : MulChar R C)
    (χ' : MulChar (R ⧸ conductorIdeal χ) C)
    (hχ' : inflateChar (Ideal.Quotient.mk (conductorIdeal χ)) χ' = χ) :
    χ' = conductorCharacter χ :=
  inflateChar_injective _ Ideal.Quotient.mk_surjective
    (hχ'.trans (inflate_conductorCharacter χ).symm)

/-- Any further quotient descent would contradict maximality of the conductor ideal. -/
theorem conductorCharacter_isPrimitive (χ : MulChar R C) :
    IsPrimitive (conductorCharacter χ) := by
  apply isPrimitive_of_ker_eq_conductorIdeal _ Ideal.Quotient.mk_surjective χ _
    (inflate_conductorCharacter χ)
  ext r
  exact Ideal.Quotient.eq_zero_iff_mem

end GaloisForLFunctions.FiniteRing
