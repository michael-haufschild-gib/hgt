import GaloisForLFunctions.RepresentationLifting.Augmentation.FlatCompletion
import GaloisForLFunctions.RepresentationLifting.Augmentation.NilAugmentation
import Mathlib.GroupTheory.Torsion

/-!
# Ordinary completion of the primary torsion character algebra

The `p`-primary part of `ℚ/ℤ` is both `p`-divisible and primary torsion.
Its modular group algebra therefore has a nonzero idempotent nil
augmentation ideal. Ordinary completion is the coefficient field, but is
not flat; the augmentation ideal is neither finitely generated nor
nilpotent. Nilpotence of each element must thus be distinguished from
nilpotence of the ideal.
-/

noncomputable section
namespace GaloisForLFunctions.RepresentationLifting
open HTGeometry.GroupAlgebraFirstJet HTGeometry.ABHN

/-- The prime-primary subgroup of the local invariant group `ℚ/ℤ`. -/
abbrev PrimePrimaryRatModInt (p : ℕ) := AddCommGroup.primaryComponent RatModInt p

variable (p : ℕ) [Fact p.Prime]

/-- Division by `p` preserves the primary subgroup of `ℚ/ℤ`. -/
theorem primePrimaryRatModInt_smul_surjective :
    Function.Surjective fun x : PrimePrimaryRatModInt p => p • x := by
  intro x
  obtain ⟨n, hn⟩ := x.property
  obtain ⟨y, hy⟩ := ratModIntNsmulAddHom_surjective p (Fact.out : p.Prime).ne_zero x.val
  change p • y = x.val at hy
  have hymem : y ∈ AddCommGroup.primaryComponent RatModInt p := by
    refine ⟨n + 1, ?_⟩
    rw [pow_succ, mul_smul, hy, hn]
  exact ⟨⟨y, hymem⟩, Subtype.ext hy⟩

/-- The primary subgroup contains the nonzero local invariant `1/p`. -/
theorem primePrimaryRatModInt_exists_ne_zero :
    ∃ x : PrimePrimaryRatModInt p, x ≠ 0 := by
  let f := zmodRatModIntAddHom p (Fact.out : p.Prime).ne_zero
  have ht : p • f (1 : ZMod p) = 0 :=
    zmodRatModIntAddHom_mem_ratModIntNTorsion p (Fact.out : p.Prime).ne_zero 1
  have hmem : f (1 : ZMod p) ∈ AddCommGroup.primaryComponent RatModInt p :=
    ⟨1, by simpa only [pow_one] using ht⟩
  refine ⟨⟨f 1, hmem⟩, ?_⟩
  intro h
  apply (one_ne_zero : (1 : ZMod p) ≠ 0)
  apply zmodRatModIntAddHom_injective p (Fact.out : p.Prime).ne_zero
  exact (congrArg Subtype.val h).trans (map_zero f).symm

omit [Fact p.Prime] in
/-- Every multiplicative primary label is killed by some power of `p`. -/
theorem primePrimaryRatModInt_pow_torsion
    (g : Multiplicative (PrimePrimaryRatModInt p)) :
    ∃ n : ℕ, g ^ (p ^ n) = 1 := by
  obtain ⟨n, hn⟩ := g.toAdd.property
  refine ⟨n, ?_⟩
  change (p ^ n) • g.toAdd = 0
  exact Subtype.ext hn

/-- The primary augmentation ideal is idempotent. -/
theorem primary_augmentation_square :
    (augmentationIdeal (ZMod p) (Multiplicative (PrimePrimaryRatModInt p))) ^ 2 =
      augmentationIdeal (ZMod p) (Multiplicative (PrimePrimaryRatModInt p)) :=
  augmentation_square_eq_of_p_divisible p (primePrimaryRatModInt_smul_surjective p)

/-- Every primary augmentation element is nilpotent. -/
theorem primary_augmentation_isNilpotent
    (x : MonoidAlgebra (ZMod p) (Multiplicative (PrimePrimaryRatModInt p)))
    (hx : x ∈ augmentationIdeal (ZMod p) (Multiplicative (PrimePrimaryRatModInt p))) :
    IsNilpotent x :=
  mem_nilradical.mp
    (augmentationIdeal_le_nilradical p (primePrimaryRatModInt_pow_torsion p) hx)

/-- Augmentation kills precisely the nilpotent elements of the primary group algebra. -/
theorem primary_augmentation_eq_nilradical :
    augmentationIdeal (ZMod p) (Multiplicative (PrimePrimaryRatModInt p)) =
      nilradical (MonoidAlgebra (ZMod p) (Multiplicative (PrimePrimaryRatModInt p))) :=
  augmentationIdeal_eq_nilradical p (primePrimaryRatModInt_pow_torsion p)

/-- The primary augmentation ideal is nonzero despite its vanishing first-order quotient. -/
theorem primary_augmentation_ne_bot :
    augmentationIdeal (ZMod p) (Multiplicative (PrimePrimaryRatModInt p)) ≠ ⊥ := by
  obtain ⟨a, ha⟩ := primePrimaryRatModInt_exists_ne_zero p
  obtain ⟨x, hx, hmem⟩ := exists_nonzero_mem_all_augmentation_powers (R := ZMod p)
    p (primePrimaryRatModInt_smul_surjective p) a ha
  exact (Submodule.ne_bot_iff _).mpr ⟨x, by simpa only [Nat.zero_add, pow_one] using hmem 0, hx⟩

/-- Ordinary completion of the primary torsion character algebra is the coefficient field. -/
def primaryAugmentationCompletionEquiv :
    AdicCompletion (augmentationIdeal (ZMod p) (Multiplicative (PrimePrimaryRatModInt p)))
      (MonoidAlgebra (ZMod p) (Multiplicative (PrimePrimaryRatModInt p))) ≃ₐ[ZMod p] ZMod p :=
  divisibleAugmentationCompletionEquiv p (primePrimaryRatModInt_smul_surjective p)

/-- The reduced primary group algebra is exactly its coefficient field. -/
def primaryReducedGroupAlgebraEquiv :
    (MonoidAlgebra (ZMod p) (Multiplicative (PrimePrimaryRatModInt p)) ⧸
      nilradical (MonoidAlgebra (ZMod p) (Multiplicative (PrimePrimaryRatModInt p))))
        ≃ₐ[ZMod p] ZMod p := by
  rw [← primary_augmentation_eq_nilradical]
  exact Ideal.quotientKerAlgEquivOfSurjective groupAlgebra_augmentation_surjective

/-- The canonical map to ordinary completion kills exactly the nilpotent elements. -/
theorem primary_augmentation_completion_kills_iff_isNilpotent
    (x : MonoidAlgebra (ZMod p) (Multiplicative (PrimePrimaryRatModInt p))) :
    AdicCompletion.of (augmentationIdeal (ZMod p) (Multiplicative (PrimePrimaryRatModInt p))) _ x = 0 ↔
      IsNilpotent x := by
  rw [divisibleAugmentationCompletion_of_eq_zero_iff p (primePrimaryRatModInt_smul_surjective p)]
  change x ∈ augmentationIdeal (ZMod p) (Multiplicative (PrimePrimaryRatModInt p)) ↔ _
  rw [primary_augmentation_eq_nilradical, mem_nilradical]

/-- A nonzero nil augmentation ideal cannot have a flat scalar quotient. -/
theorem primary_augmentation_not_pure :
    ¬ (augmentationIdeal (ZMod p) (Multiplicative (PrimePrimaryRatModInt p))).Pure := by
  rw [pure_iff_bot_of_nil _ (primary_augmentation_isNilpotent p)]
  exact primary_augmentation_ne_bot p

/-- Ordinary primary augmentation completion is not flat over the group algebra. -/
theorem primary_augmentation_completion_not_flat :
    ¬ Module.Flat (MonoidAlgebra (ZMod p) (Multiplicative (PrimePrimaryRatModInt p)))
      (AdicCompletion (augmentationIdeal (ZMod p) (Multiplicative (PrimePrimaryRatModInt p)))
        (MonoidAlgebra (ZMod p) (Multiplicative (PrimePrimaryRatModInt p)))) := by
  rw [idempotentAdicCompletion_flat_iff _ (primary_augmentation_square p)]
  exact primary_augmentation_not_pure p

/-- The primary augmentation ideal cannot be generated by finitely many elements. -/
theorem primary_augmentation_not_fg :
    ¬ (augmentationIdeal (ZMod p) (Multiplicative (PrimePrimaryRatModInt p))).FG :=
  not_fg_of_idempotent_not_pure _ (primary_augmentation_square p)
    (primary_augmentation_not_pure p)

/-- The primary torsion group algebra is not Noetherian. -/
theorem primary_groupAlgebra_not_noetherian :
    ¬ IsNoetherianRing (MonoidAlgebra (ZMod p) (Multiplicative (PrimePrimaryRatModInt p))) := by
  intro h
  letI := h
  exact primary_augmentation_not_fg p (IsNoetherian.noetherian _)

/-- Although each augmentation element is nilpotent, no positive ideal power vanishes. -/
theorem primary_augmentation_pow_ne_bot (n : ℕ) :
    (augmentationIdeal (ZMod p) (Multiplicative (PrimePrimaryRatModInt p))) ^ (n + 1) ≠ ⊥ := by
  rw [augmentation_power_eq_of_p_divisible p (primePrimaryRatModInt_smul_surjective p)]
  exact primary_augmentation_ne_bot p

#print axioms primePrimaryRatModInt_smul_surjective
#print axioms primary_augmentation_isNilpotent
#print axioms primary_augmentation_eq_nilradical
#print axioms primaryAugmentationCompletionEquiv
#print axioms primaryReducedGroupAlgebraEquiv
#print axioms primary_augmentation_completion_kills_iff_isNilpotent
#print axioms primary_augmentation_completion_not_flat
#print axioms primary_augmentation_not_fg
#print axioms primary_groupAlgebra_not_noetherian
#print axioms primary_augmentation_pow_ne_bot

end GaloisForLFunctions.RepresentationLifting
