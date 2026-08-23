import Mathlib.GroupTheory.Divisible
import Mathlib.Algebra.Category.Grp.Injective
import Mathlib.GroupTheory.Torsion
import Mathlib.FieldTheory.IsAlgClosed.Basic
import GaloisForLFunctions.HTGeometry.RetractionSplitting

/-!
# Extension of characters into a divisible group

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), Lemma 4.3 (`t3`),
first half.  The lemma extends a character `χ_μ : μ(k) → Cˣ` to `kˣ → Cˣ` with the same kernel;
its two structural inputs are recorded here.

* `Cˣ` is divisible when `C` is algebraically closed, so it is an injective `ℤ`-module and every
  character of a subgroup extends (`deningerExtend_of_rootableBy`, via `Module.Baer.of_divisible`).
* The torsion subgroup `μ(C)` of a divisible commutative group is divisible, hence a direct
  summand: `deningerTorsion_retraction` produces a retraction `Cˣ → μ(C)` of the inclusion, which
  is the splitting `Cˣ ≅ μ(C) × Cˣ/μ(C)` used in the source.
-/

namespace RHTower

/-- The unit group of an algebraically closed field is divisible. -/
noncomputable instance deningerUnitsRootableBy {C : Type*} [Field C] [IsAlgClosed C] :
    RootableBy Cˣ ℕ := by
  refine rootableByOfPowLeftSurj Cˣ ℕ (fun {n} hn u => ?_)
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (u : C) (Nat.pos_of_ne_zero hn)
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, zero_pow hn] at hz
    exact u.ne_zero hz.symm
  refine ⟨Units.mk0 z hz0, ?_⟩
  apply Units.ext
  simpa using hz

/-- A divisible commutative group is divisible for integer exponents. -/
@[implicit_reducible]
noncomputable def deningerDivisibleByInt (C : Type*) [CommGroup C] [RootableBy C ℕ] :
    DivisibleBy (Additive C) ℤ :=
  letI : RootableBy C ℤ := Group.rootableByIntOfRootableByNat C
  { div := fun a n => Additive.ofMul (RootableBy.root (Additive.toMul a) n)
    div_zero := fun a => congrArg Additive.ofMul (RootableBy.root_zero (Additive.toMul a))
    div_cancel := fun {_n} a hn =>
      congrArg Additive.ofMul (RootableBy.root_cancel (Additive.toMul a) hn) }

/-- **Extension property of divisible groups.**  A homomorphism into a divisible commutative group
extends along any injective homomorphism. -/
theorem deningerExtend_of_rootableBy {A B C : Type*} [CommGroup A] [CommGroup B] [CommGroup C]
    [RootableBy C ℕ] (f : A →* B) (hf : Function.Injective f) (g : A →* C) :
    ∃ g' : B →* C, g'.comp f = g := by
  letI := deningerDivisibleByInt C
  obtain ⟨g', hg'⟩ := (Module.Baer.of_divisible (Additive C)).extension_property_addMonoidHom
    (MonoidHom.toAdditive f) hf (MonoidHom.toAdditive g)
  refine ⟨MonoidHom.toAdditive.symm g', ?_⟩
  ext a
  have := congrArg (fun h : Additive A →+ Additive C => h (Additive.ofMul a)) hg'
  exact this

/-- The torsion subgroup of a divisible commutative group is divisible. -/
noncomputable instance deningerTorsionRootableBy {C : Type*} [CommGroup C] [RootableBy C ℕ] :
    RootableBy (CommGroup.torsion C) ℕ := by
  refine rootableByOfPowLeftSurj (CommGroup.torsion C) ℕ (fun {n} hn u => ?_)
  obtain ⟨y, hy⟩ := RootableBy.surjective_pow C ℕ hn (u : C)
  have hy' : y ^ n = (u : C) := hy
  have hytors : y ∈ CommGroup.torsion C := by
    rw [CommGroup.mem_torsion _, isOfFinOrder_iff_pow_eq_one]
    obtain ⟨m, hm, hmu⟩ :=
      isOfFinOrder_iff_pow_eq_one.mp ((CommGroup.mem_torsion _).mp u.2)
    refine ⟨n * m, Nat.mul_pos (Nat.pos_of_ne_zero hn) hm, ?_⟩
    rw [pow_mul, hy', hmu]
  refine ⟨⟨y, hytors⟩, ?_⟩
  apply Subtype.ext
  simpa using hy

/-- **The torsion subgroup of a divisible commutative group is a direct summand.**  There is a
retraction of the inclusion of the torsion subgroup. -/
theorem deningerTorsion_retraction {C : Type*} [CommGroup C] [RootableBy C ℕ] :
    ∃ r : C →* CommGroup.torsion C,
      ∀ x : CommGroup.torsion C, r (x : C) = x := by
  obtain ⟨r, hr⟩ := deningerExtend_of_rootableBy (CommGroup.torsion C).subtype
    Subtype.val_injective (MonoidHom.id (CommGroup.torsion C))
  refine ⟨r, fun x => ?_⟩
  have := congrArg (fun h : (CommGroup.torsion C) →* (CommGroup.torsion C) => h x) hr
  exact this

end RHTower

namespace RHTower

open HTGeometry

/-- **Deninger, Proposition 9.1.**  For a divisible commutative group, a retraction of the
inclusion of the torsion subgroup splits the character group into the characters of the torsion
subgroup and the characters of the kernel of the retraction. -/
def deningerCharSplitEquiv {C : Type*} [CommGroup C] {T : Type*} [CommGroup T]
    (r : C →* CommGroup.torsion C) (hr : ∀ x : CommGroup.torsion C, r (x : C) = x) :
    (C →* T) ≃ ((CommGroup.torsion C) →* T) × ((MonoidHom.ker r) →* T) :=
  homRetractionEquiv (CommGroup.torsion C).subtype r hr T

/-- **Deninger, Proposition 9.1.**  Such a splitting exists for every divisible commutative
group. -/
theorem deningerCharSplit_exists {C : Type*} [CommGroup C] [RootableBy C ℕ] (T : Type*)
    [CommGroup T] :
    ∃ (r : C →* CommGroup.torsion C) (_ : ∀ x : CommGroup.torsion C, r (x : C) = x),
      Nonempty ((C →* T) ≃ ((CommGroup.torsion C) →* T) × ((MonoidHom.ker r) →* T)) := by
  obtain ⟨r, hr⟩ := deningerTorsion_retraction (C := C)
  exact ⟨r, hr, ⟨deningerCharSplitEquiv r hr⟩⟩

/-- **Deninger, Proposition 9.1** for the units of an algebraically closed field: the characters
of `κ (x)ˣ` split into the characters of `μ (κ (x))` and the characters of a complement. -/
theorem deningerUnitsCharSplit_exists (k : Type*) [Field k] [IsAlgClosed k] (T : Type*)
    [CommGroup T] :
    ∃ (r : kˣ →* CommGroup.torsion kˣ) (_ : ∀ x : CommGroup.torsion kˣ, r (x : kˣ) = x),
      Nonempty ((kˣ →* T) ≃ ((CommGroup.torsion kˣ) →* T) × ((MonoidHom.ker r) →* T)) := by
  letI := deningerUnitsRootableBy (C := k)
  exact deningerCharSplit_exists T

end RHTower
