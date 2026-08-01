import Mathlib

/-!
# Characters of a finite abelian group span its function space

Distinct monoid homomorphisms into a field are linearly independent, and a finite abelian group has
exactly as many complex characters as elements.  So the characters, viewed as complex functions,
are a linearly independent family of the right cardinality: they span, and every complex function
on the group is a linear combination of characters.

Dually — using that a finite abelian group is its own double dual, with the isomorphism given by
evaluation — the evaluations at group elements span the function space of the character group.
That is the Fourier statement used to lift a prescribed function on a finite residue-character set.

* `deningerCharacter_linearIndependent` : distinct characters are independent.
* `deningerCharacter_card` : there are as many characters as elements.
* `deningerCharacter_span` : the characters span the complex function space.
* `deningerEvaluation_span` : evaluations span the functions on the character group.
-/

namespace RHTower

section CharacterBasis

variable {G : Type*} [CommGroup G]

/-- A character viewed as a complex function. -/
noncomputable def deningerCharacterFn (chi : G →* ℂˣ) : G → ℂ :=
  ((Units.coeHom ℂ).comp chi : G →* ℂ)

theorem deningerCharacterFn_apply (chi : G →* ℂˣ) (g : G) :
    deningerCharacterFn chi g = (chi g : ℂ) := rfl

/-- **Distinct characters are linearly independent**, by Dedekind's theorem on monoid
homomorphisms into a field. -/
theorem deningerCharacter_linearIndependent :
    LinearIndependent ℂ (deningerCharacterFn : (G →* ℂˣ) → (G → ℂ)) := by
  have hdedekind : LinearIndependent ℂ (fun f : G →* ℂ => (f : G → ℂ)) :=
    linearIndependent_monoidHom G ℂ
  have hinj : Function.Injective (fun chi : G →* ℂˣ => (Units.coeHom ℂ).comp chi) := by
    intro chi psi h
    refine MonoidHom.ext fun g => Units.ext ?_
    exact congrFun (congrArg (fun f : G →* ℂ => (f : G → ℂ)) h) g
  exact hdedekind.comp _ hinj

variable [Finite G]

/-- The character group of a finite abelian group is finite. -/
theorem deningerCharacterGroup_finite : Finite (G →* ℂˣ) :=
  Finite.of_equiv G (CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity G ℂ).some.toEquiv.symm

/-- **A finite abelian group has as many characters as elements.** -/
theorem deningerCharacter_card : Nat.card (G →* ℂˣ) = Nat.card G :=
  CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity G ℂ

/-- **Every complex function on a finite abelian group is a linear combination of characters.** -/
theorem deningerCharacter_span :
    Submodule.span ℂ (Set.range (deningerCharacterFn : (G →* ℂˣ) → (G → ℂ))) = ⊤ := by
  classical
  haveI : Finite (G →* ℂˣ) := deningerCharacterGroup_finite
  haveI : Fintype G := Fintype.ofFinite G
  haveI : Fintype (G →* ℂˣ) := Fintype.ofFinite _
  haveI : Nonempty (G →* ℂˣ) := ⟨1⟩
  refine deningerCharacter_linearIndependent.span_eq_top_of_card_eq_finrank ?_
  rw [Module.finrank_fintype_fun_eq_card]
  have h := deningerCharacter_card (G := G)
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at h
  exact h

end CharacterBasis

section EvaluationBasis

variable {G : Type*} [CommGroup G] [Finite G]

/-- Evaluation at a group element, as a function on the character group. -/
noncomputable def deningerEvaluationFn (g : G) : (G →* ℂˣ) → ℂ := fun chi => (chi g : ℂ)

/-- **Evaluations span the complex functions on the character group.**  A finite abelian group is
its own double dual through evaluation, so the characters of the character group are exactly the
evaluations, and those span by the previous theorem. -/
theorem deningerEvaluation_span :
    Submodule.span ℂ (Set.range (deningerEvaluationFn : G → ((G →* ℂˣ) → ℂ))) = ⊤ := by
  classical
  haveI : Finite (G →* ℂˣ) := deningerCharacterGroup_finite
  have hrange : Set.range (deningerCharacterFn : ((G →* ℂˣ) →* ℂˣ) → ((G →* ℂˣ) → ℂ))
      = Set.range (deningerEvaluationFn : G → ((G →* ℂˣ) → ℂ)) := by
    ext F
    constructor
    · rintro ⟨eta, rfl⟩
      refine ⟨CommGroup.monoidHomMonoidHomEquiv G ℂ eta, ?_⟩
      funext chi
      show (chi (CommGroup.monoidHomMonoidHomEquiv G ℂ eta) : ℂ) = (eta chi : ℂ)
      rw [CommGroup.apply_monoidHomMonoidHomEquiv ℂ chi eta]
    · rintro ⟨g, rfl⟩
      refine ⟨(CommGroup.monoidHomMonoidHomEquiv G ℂ).symm g, ?_⟩
      funext chi
      show (((CommGroup.monoidHomMonoidHomEquiv G ℂ).symm g) chi : ℂ) = (chi g : ℂ)
      rw [← CommGroup.apply_monoidHomMonoidHomEquiv ℂ chi
        ((CommGroup.monoidHomMonoidHomEquiv G ℂ).symm g), MulEquiv.apply_symm_apply]
  rw [← hrange]
  exact deningerCharacter_span

end EvaluationBasis

end RHTower
