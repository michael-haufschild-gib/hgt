import GaloisForLFunctions.RHTower.Artin.ArtinInducedCharacterFormula
import GaloisForLFunctions.RHTower.Artin.ArtinMonomialCharacter

/-!
# Induction of functions from a subgroup

For a subgroup `H` of a finite group `G` and a function `f` on `H`,

  `(Ind f)(g) = (1/|H|) Σ_{x ∈ G, x g x⁻¹ ∈ H} f(x g x⁻¹)`   (`inducedFunction`).

* On the character of a representation of `H` it is the character of the induced
  representation (`induced_character_eq_inducedFunction`); on a linear character it is the
  monomial character of the corpus (`monomialVirtualCharacter_val`).
* It is additive and linear (`inducedFunction_add`, `inducedFunction_smul`), and its values are
  invariant under conjugation (`inducedFunction_conj`).
* **Projection formula** (`inducedFunction_mul_restrict`): for a class function `ψ` of `G`,
  `Ind(f · ψ|_H) = Ind(f) · ψ`.
-/

open scoped Classical BigOperators

noncomputable section

universe u w

namespace GaloisForLFunctions

variable {G : Type u} [Group G] (H : Subgroup G)

/-! ### Extension by zero -/

theorem extendByZero_of_mem (f : H → ℂ) {x : G} (hx : x ∈ H) :
    extendByZero H f x = f ⟨x, hx⟩ :=
  dif_pos hx

theorem extendByZero_of_notMem (f : H → ℂ) {x : G} (hx : x ∉ H) : extendByZero H f x = 0 :=
  dif_neg hx

theorem extendByZero_add (f₁ f₂ : H → ℂ) (x : G) :
    extendByZero H (fun h => f₁ h + f₂ h) x = extendByZero H f₁ x + extendByZero H f₂ x := by
  by_cases hx : x ∈ H
  · rw [extendByZero_of_mem H _ hx, extendByZero_of_mem H _ hx, extendByZero_of_mem H _ hx]
  · rw [extendByZero_of_notMem H _ hx, extendByZero_of_notMem H _ hx,
      extendByZero_of_notMem H _ hx, add_zero]

theorem extendByZero_smul (c : ℂ) (f : H → ℂ) (x : G) :
    extendByZero H (fun h => c * f h) x = c * extendByZero H f x := by
  by_cases hx : x ∈ H
  · rw [extendByZero_of_mem H _ hx, extendByZero_of_mem H _ hx]
  · rw [extendByZero_of_notMem H _ hx, extendByZero_of_notMem H _ hx, mul_zero]

/-- The extension by zero of a product with the restriction of a function of the group. -/
theorem extendByZero_mul_restrict (f : H → ℂ) (ψ : G → ℂ) (x : G) :
    extendByZero H (fun h => f h * ψ h) x = extendByZero H f x * ψ x := by
  by_cases hx : x ∈ H
  · rw [extendByZero_of_mem H _ hx, extendByZero_of_mem H _ hx]
  · rw [extendByZero_of_notMem H _ hx, extendByZero_of_notMem H _ hx, zero_mul]

/-! ### Induction -/

variable [Fintype G]

/-- **Induction of a function on a subgroup**:
`(Ind f)(g) = (1/|H|) Σ_{x, x g x⁻¹ ∈ H} f(x g x⁻¹)`. -/
def inducedFunction (f : H → ℂ) (g : G) : ℂ :=
  (Nat.card H : ℂ)⁻¹ * ∑ x : G, extendByZero H f (x * g * x⁻¹)

/-- **The character of an induced representation is the induced function of the character.** -/
theorem induced_character_eq_inducedFunction {V : Type w} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ H V) :
    (Representation.ind H.subtype ρ).character = inducedFunction H ρ.character :=
  funext (induced_character_apply_average H ρ)

/-- A monomial character is the induced function of its linear character. -/
theorem monomialVirtualCharacter_val (χ : LinearCharacter H) :
    (monomialVirtualCharacter G H χ).val = inducedFunction H fun h => (χ h : ℂ) := by
  funext g
  rw [monomialVirtualCharacter_apply, induced_character_eq_inducedFunction]
  congr 1
  funext h
  exact linearCharacterRepresentation_character χ h

theorem inducedFunction_add (f₁ f₂ : H → ℂ) :
    inducedFunction H (fun h => f₁ h + f₂ h) =
      fun g => inducedFunction H f₁ g + inducedFunction H f₂ g := by
  funext g
  simp only [inducedFunction, extendByZero_add, Finset.sum_add_distrib, mul_add]

theorem inducedFunction_smul (c : ℂ) (f : H → ℂ) :
    inducedFunction H (fun h => c * f h) = fun g => c * inducedFunction H f g := by
  funext g
  simp only [inducedFunction, extendByZero_smul, ← Finset.mul_sum]
  ring

/-- **An induced function is a class function.** -/
theorem inducedFunction_conj (f : H → ℂ) (y g : G) :
    inducedFunction H f (y * g * y⁻¹) = inducedFunction H f g := by
  unfold inducedFunction
  congr 1
  rw [← Equiv.sum_comp (Equiv.mulRight y) fun x => extendByZero H f (x * g * x⁻¹)]
  refine Finset.sum_congr rfl fun x _ => ?_
  congr 1
  simp [mul_assoc]

/-- **The projection formula.** For a class function `ψ` of the group,
`Ind(f · ψ|_H) = Ind(f) · ψ`. -/
theorem inducedFunction_mul_restrict (f : H → ℂ) (ψ : G → ℂ)
    (hψ : ∀ x g : G, ψ (x * g * x⁻¹) = ψ g) :
    inducedFunction H (fun h => f h * ψ h) = fun g => inducedFunction H f g * ψ g := by
  funext g
  simp only [inducedFunction, extendByZero_mul_restrict, hψ, ← Finset.sum_mul]
  ring

end GaloisForLFunctions
