import GaloisForLFunctions.RepresentationLifting.Augmentation.DivisibleGroupCompletion
import Mathlib.RingTheory.Ideal.Pure
import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors

/-!
# Flatness of ordinary augmentation completion

Completion at an idempotent ideal is flat precisely when its quotient is
flat. In a domain this happens only for the zero and unit ideals; for a
nil ideal it happens only for the zero ideal. These sharp classifications
show that the ordinary augmentation completion of `𝔽_p[ℚ]`, although
equal to `𝔽_p`, is not flat over the group algebra. Its idempotent
augmentation ideal is consequently not finitely generated.

The obstruction concerns ordinary completion in the setting of
Carlsson–Joshua (arXiv:2611.15605). No conclusion about derived
completion or higher Tor groups follows from this obstruction alone.
-/

noncomputable section
namespace GaloisForLFunctions.RepresentationLifting

section PureIdeals
variable {R : Type*} [CommRing R]

/-- Quotienting by zero gives a flat module. -/
theorem botIdeal_pure : (⊥ : Ideal R).Pure :=
  Module.Flat.of_linearEquiv (AlgEquiv.quotientBot R R).toLinearEquiv

/-- A pure ideal in a domain is either zero or the whole ring. -/
theorem pure_iff_bot_or_top_of_domain [IsDomain R] (I : Ideal R) :
    I.Pure ↔ I = ⊥ ∨ I = ⊤ := by
  constructor
  · intro h
    letI : I.Pure := h
    by_cases hI : I = ⊥
    · exact Or.inl hI
    obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff I).mp hI
    obtain ⟨y, hy, hxy⟩ := Ideal.exists_eq_mul_of_pure hx
    have hy1 : y = 1 := mul_left_cancel₀ hx0 (hxy.symm.trans (mul_one x).symm)
    exact Or.inr ((Ideal.eq_top_iff_one I).mpr (hy1 ▸ hy))
  · rintro (rfl | rfl)
    · exact botIdeal_pure
    · infer_instance

/-- A nil ideal has flat quotient precisely when it is zero. -/
theorem pure_iff_bot_of_nil (I : Ideal R) (hI : ∀ x ∈ I, IsNilpotent x) :
    I.Pure ↔ I = ⊥ := by
  constructor
  · intro h
    letI : I.Pure := h
    apply le_antisymm _ bot_le
    intro x hx
    change x = 0
    obtain ⟨y, hy, hxy⟩ := Ideal.exists_eq_mul_of_pure hx
    apply (hI y hy).isUnit_one_sub.mul_left_eq_zero.mp
    rw [mul_sub, mul_one, ← hxy, sub_self]
  · rintro rfl
    exact botIdeal_pure

/-- Flatness of idempotent-ideal completion is exactly purity of the ideal. -/
theorem idempotentAdicCompletion_flat_iff (I : Ideal R) (hI : I ^ 2 = I) :
    Module.Flat R (AdicCompletion I R) ↔ I.Pure := by
  constructor
  · intro h
    letI := h
    exact Module.Flat.of_linearEquiv (idempotentAdicCompletionEquiv I hI).symm.toLinearEquiv
  · intro h
    letI := h
    exact Module.Flat.of_linearEquiv (idempotentAdicCompletionEquiv I hI).toLinearEquiv

/-- Nonflatness of an idempotent quotient forces its ideal to be infinitely generated. -/
theorem not_fg_of_idempotent_not_pure (I : Ideal R) (hI : I ^ 2 = I)
    (h : ¬ I.Pure) : ¬ I.FG := by
  intro hfg
  apply h
  exact Ideal.Pure.of_isIdempotentElem hfg (by simpa only [IsIdempotentElem, pow_two] using hI)

end PureIdeals

open HTGeometry.GroupAlgebraFirstJet
variable (p : ℕ) [Fact p.Prime]

/-- The rational group algebra has a nonzero augmentation ideal. -/
theorem rational_augmentation_ne_bot :
    augmentationIdeal (ZMod p) (Multiplicative ℚ) ≠ ⊥ := by
  obtain ⟨x, hx, hmem⟩ := rational_augmentation_not_separated p
  apply (Submodule.ne_bot_iff _).mpr
  exact ⟨x, by simpa only [Nat.zero_add, pow_one] using hmem 0, hx⟩

/-- The augmentation ideal is proper because augmentation preserves one. -/
theorem augmentation_ne_top {R G : Type*} [CommRing R] [Nontrivial R] [CommGroup G] :
    augmentationIdeal R G ≠ ⊤ := by
  intro h
  have h1 : (1 : MonoidAlgebra R G) ∈ augmentationIdeal R G := by rw [h]; trivial
  change augmentation R G 1 = 0 at h1
  exact one_ne_zero ((map_one (augmentation R G)).symm.trans h1)

/-- The scalar quotient of `𝔽_p[ℚ]` is not flat over the group algebra. -/
theorem rational_augmentation_not_pure :
    ¬ (augmentationIdeal (ZMod p) (Multiplicative ℚ)).Pure := by
  rw [pure_iff_bot_or_top_of_domain]
  exact fun h => h.elim (rational_augmentation_ne_bot p) augmentation_ne_top

/-- Ordinary augmentation completion of `𝔽_p[ℚ]` is not flat. -/
theorem rational_augmentation_completion_not_flat :
    ¬ Module.Flat (MonoidAlgebra (ZMod p) (Multiplicative ℚ))
      (AdicCompletion (augmentationIdeal (ZMod p) (Multiplicative ℚ))
        (MonoidAlgebra (ZMod p) (Multiplicative ℚ))) := by
  rw [idempotentAdicCompletion_flat_iff _ (rational_augmentation_square p)]
  exact rational_augmentation_not_pure p

/-- The nonzero idempotent rational augmentation ideal is not finitely generated. -/
theorem rational_augmentation_not_fg :
    ¬ (augmentationIdeal (ZMod p) (Multiplicative ℚ)).FG :=
  not_fg_of_idempotent_not_pure _ (rational_augmentation_square p)
    (rational_augmentation_not_pure p)

/-- Prime divisibility of rational labels forces the modular group algebra to be non-Noetherian. -/
theorem rational_groupAlgebra_not_noetherian :
    ¬ IsNoetherianRing (MonoidAlgebra (ZMod p) (Multiplicative ℚ)) := by
  intro h
  letI := h
  exact rational_augmentation_not_fg p (IsNoetherian.noetherian _)

#print axioms pure_iff_bot_or_top_of_domain
#print axioms pure_iff_bot_of_nil
#print axioms idempotentAdicCompletion_flat_iff
#print axioms rational_augmentation_completion_not_flat
#print axioms rational_augmentation_not_fg
#print axioms rational_groupAlgebra_not_noetherian

end GaloisForLFunctions.RepresentationLifting
