import GaloisForLFunctions.ScaleSignedIncidenceCriticality.TheResolutionLimitOfAReading

/-!
# Oriented readings

A class of data `D` carries an **orientation** when it comes with an involution `κ : D → D`,
the *flip*: the parity twist of a damped weight, the even flip of a divisor row, the switching of
a signed incidence form, the reflection of a scaling cycle.  A reading `r : D → O` is
**orientation-faithful** when it separates every datum from its flip
(`OrientationFaithful`); it is **blind** when it is invisible to the flip in the sense of
Scale-Signed Incidence Criticality (`Invisible r κ`: `r (κ d) = r d` for every `d`).

* **The closure law of blindness** (`Invisible.comp`, `Invisible.join`, `Invisible.pi`,
  `Invisible.of_refines`): a blind reading stays blind under post-processing, pairing, families of
  any cardinality and coarsening.  This is the structural content of the parity barrier of
  Trans-Horizon Incidence Mechanics: no amount of amplitude-derived data recovers the
  orientation.
* **Blind readings resolve only flip-invariant predicates** (`resolves_iff_invariant_of_invisible`,
  `forall_iff_of_resolves_of_invisible`): if `r` is blind and resolves `P`, then `P (κ d) ↔ P d`.
* **Resolving a flipping predicate forces faithfulness**
  (`orientationFaithful_of_resolves_of_flips`): a reading that decides a property which changes
  under the flip must separate every datum from its flip.
* **Faithfulness is the complement of invisibility on moved data**
  (`orientationFaithful_iff_forall_not_mem_shadow`, `not_orientationFaithful_of_invisible`).

Nothing here is arithmetic; the arithmetic instances (the even flip read at the prime `2`, the
switching class of a signed form) name their flip and their reading.
-/

namespace GaloisForLFunctions.ArithmeticOrientationTheory

open ScaleSignedIncidenceCriticality

set_option autoImplicit false

variable {D O O' : Type*}

/-- An orientation on a class of data: an involutive flip. -/
structure Orientation (D : Type*) where
  /-- The flip. -/
  flip : D → D
  /-- The flip is an involution. -/
  flip_flip : ∀ d, flip (flip d) = d

/-- A reading is **orientation-faithful** for the flip `κ` when it separates every datum that the
flip moves from its flip. -/
def OrientationFaithful (r : D → O) (κ : D → D) : Prop := ∀ d, κ d ≠ d → r (κ d) ≠ r d

theorem orientationFaithful_iff_forall_not_mem_shadow (r : D → O) (κ : D → D) :
    OrientationFaithful r κ ↔ ∀ d, κ d ≠ d → κ d ∉ shadow r d :=
  Iff.rfl

/-- The identity reading is faithful for every flip. -/
theorem orientationFaithful_id (κ : D → D) : OrientationFaithful (fun d => d) κ := fun _ h => h

/-- A blind reading is not faithful as soon as the flip moves something. -/
theorem not_orientationFaithful_of_invisible {r : D → O} {κ : D → D} (h : Invisible r κ) {d : D}
    (hd : κ d ≠ d) : ¬ OrientationFaithful r κ := fun hf => hf d hd (h d)

/-! ### The closure law of blindness -/

/-- Post-processing keeps a reading blind. -/
theorem Invisible.comp {r : D → O} {κ : D → D} (h : Invisible r κ) (g : O → O') :
    Invisible (g ∘ r) κ := fun d => by simp [Function.comp, h d]

/-- Pairing two blind readings keeps them blind. -/
theorem Invisible.join {r : D → O} {r' : D → O'} {κ : D → D} (h : Invisible r κ)
    (h' : Invisible r' κ) : Invisible (joinReading r r') κ := fun d => by
  simp [joinReading, h d, h' d]

/-- A family of blind readings, of any cardinality, is blind. -/
theorem Invisible.pi {ι : Type*} {O : ι → Type*} {r : ∀ i, D → O i} {κ : D → D}
    (h : ∀ i, Invisible (r i) κ) : Invisible (fun d i => r i d) κ := fun d => by
  funext i; exact h i d

/-- Coarsening keeps a reading blind: if `r` is blind and `r'` reads less than `r`, then `r'`
is blind. -/
theorem Invisible.of_refines {r : D → O} {r' : D → O'} {κ : D → D} (h : Invisible r κ)
    (hr : Refines r r') : Invisible r' κ := fun d => hr d (κ d) (h d)

/-! ### Blind readings resolve only invariant predicates -/

/-- A blind reading resolving `P` forces `P` to be flip-invariant. -/
theorem forall_iff_of_resolves_of_invisible {r : D → O} {κ : D → D} {P : D → Prop}
    (h : Invisible r κ) (hr : Resolves r P) (d : D) : P (κ d) ↔ P d :=
  hr d (κ d) (h d)

/-- For a blind reading, resolving `P` is the same as `P` being flip-invariant on every shadow
that `r` already identifies: the reading adds nothing to the orientation. -/
theorem resolves_iff_invariant_of_invisible {r : D → O} {κ : D → D} {P : D → Prop}
    (h : Invisible r κ) :
    Resolves r P → ∀ d, P (κ d) ↔ P d :=
  fun hr d => forall_iff_of_resolves_of_invisible h hr d

/-- **Resolving a flipping predicate forces faithfulness**: if `r` resolves `P` and `P` changes
under the flip wherever the flip moves, then `r` separates every moved datum from its flip. -/
theorem orientationFaithful_of_resolves_of_flips {r : D → O} {κ : D → D} {P : D → Prop}
    (hr : Resolves r P) (hflip : ∀ d, κ d ≠ d → ¬ (P (κ d) ↔ P d)) :
    OrientationFaithful r κ := by
  intro d hd heq
  exact hflip d hd (hr d (κ d) heq)

/-- A reading that is blind cannot resolve a predicate that flips somewhere. -/
theorem not_resolves_of_invisible_of_flips {r : D → O} {κ : D → D} {P : D → Prop}
    (h : Invisible r κ) {d : D} (hflip : ¬ (P (κ d) ↔ P d)) : ¬ Resolves r P :=
  fun hr => hflip (hr d (κ d) (h d))

/-! ### Orientation classes -/

/-- The orientation class of a datum: its orbit under the flip. -/
def orientationClass (κ : D → D) (d : D) : Set D := {d, κ d}

theorem mem_orientationClass_self (κ : D → D) (d : D) : d ∈ orientationClass κ d :=
  Set.mem_insert d _

theorem flip_mem_orientationClass (κ : D → D) (d : D) : κ d ∈ orientationClass κ d :=
  Set.mem_insert_of_mem d rfl

/-- A blind reading is constant on orientation classes. -/
theorem eq_of_mem_orientationClass_of_invisible {r : D → O} {κ : D → D} (h : Invisible r κ)
    {d e : D} (he : e ∈ orientationClass κ d) : r e = r d := by
  rcases he with rfl | he
  · rfl
  · rw [Set.mem_singleton_iff] at he
    rw [he]; exact h d

/-- For an involutive flip, orientation classes of flipped data coincide. -/
theorem orientationClass_flip (κ : Orientation D) (d : D) :
    orientationClass κ.flip (κ.flip d) = orientationClass κ.flip d := by
  unfold orientationClass
  rw [κ.flip_flip]
  exact Set.pair_comm _ _

end GaloisForLFunctions.ArithmeticOrientationTheory
