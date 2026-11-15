import GaloisForLFunctions.HTGeometry.GroupAlgebras.FirstJet
import GaloisForLFunctions.HTGeometry.ABHN.RatModIntTorsionExactSequence
import Mathlib.GroupTheory.Divisible

/-!
# Ordinary augmentation quotients of divisible groups

Carlsson–Joshua (arXiv:2611.15605, Sections 1–2) distinguish derived
completion from ordinary completion of representation rings. For the
abelian character groups `ℚ` and `ℚ/ℤ`, the ordinary characteristic-`p`
augmentation filtration already stabilizes at its first term.

The proof uses the first-order group-algebra equivalence:
`I/I²` is measured by `R ⊗[ℤ] A`. Division by `p` in `A` moves the
annihilating scalar onto `R`, so this tensor product vanishes. Thus
`I² = I`, and every positive augmentation quotient is exactly `R`.
These are statements about ordinary quotients, not assertions about
the homotopy groups of a derived completion.
-/

noncomputable section
open scoped TensorProduct

namespace GaloisForLFunctions.RepresentationLifting

open HTGeometry.GroupAlgebraFirstJet

variable {R A : Type*} [CommRing R] [AddCommGroup A]

/-- Characteristic-`p` coefficients kill the integral tensor product with a `p`-divisible group. -/
theorem tensor_eq_zero_of_p_divisible (p : ℕ) [CharP R p]
    (hA : Function.Surjective fun a : A => p • a) (v : R ⊗[ℤ] A) : v = 0 := by
  induction v using TensorProduct.induction_on with
  | zero => rfl
  | tmul r a =>
    obtain ⟨b, rfl⟩ := hA a
    rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    simp only [nsmul_eq_mul, CharP.cast_eq_zero R p, zero_mul, TensorProduct.zero_tmul]
  | add x y hx hy => rw [hx, hy, add_zero]

/-- For a `p`-divisible abelian group, the augmentation ideal is idempotent in characteristic `p`. -/
theorem augmentation_square_eq_of_p_divisible (p : ℕ) [CharP R p]
    (hA : Function.Surjective fun a : A => p • a) :
    (augmentationIdeal R (Multiplicative A)) ^ 2 = augmentationIdeal R (Multiplicative A) := by
  apply le_antisymm (Ideal.pow_le_self (Nat.succ_ne_zero 1))
  intro x hx
  rw [← jet_ker_eq_square]
  change jet R (Multiplicative A) x = 0
  apply TrivSqZeroExt.ext
  · exact (jet_fst R (Multiplicative A) x).trans hx
  · exact tensor_eq_zero_of_p_divisible p hA _

/-- Every positive power of the augmentation ideal is already the first power. -/
theorem augmentation_power_eq_of_p_divisible (p : ℕ) [CharP R p]
    (hA : Function.Surjective fun a : A => p • a) (n : ℕ) :
    (augmentationIdeal R (Multiplicative A)) ^ (n + 1) =
      augmentationIdeal R (Multiplicative A) := by
  induction n with
  | zero => exact pow_one _
  | succ n ih =>
    rw [pow_succ, ih, ← pow_two, augmentation_square_eq_of_p_divisible p hA]

/-- Augmentation has the scalar inclusion as a section. -/
theorem groupAlgebra_augmentation_surjective :
    Function.Surjective (augmentation R (Multiplicative A)) := by
  intro r
  exact ⟨algebraMap R _ r, (augmentation R (Multiplicative A)).commutes r⟩

/-- All positive ordinary augmentation quotients of a `p`-divisible group are the coefficient ring. -/
def divisibleAugmentationQuotientEquiv (p : ℕ) [CharP R p]
    (hA : Function.Surjective fun a : A => p • a) (n : ℕ) :
    (MonoidAlgebra R (Multiplicative A) ⧸
      (augmentationIdeal R (Multiplicative A)) ^ (n + 1)) ≃ₐ[R] R := by
  rw [augmentation_power_eq_of_p_divisible p hA]
  exact Ideal.quotientKerAlgEquivOfSurjective groupAlgebra_augmentation_surjective

/-- Every nonzero group label supplies a nonzero element in all positive augmentation powers. -/
theorem exists_nonzero_mem_all_augmentation_powers [Nontrivial R]
    (p : ℕ) [CharP R p] (hA : Function.Surjective fun a : A => p • a)
    (a : A) (ha : a ≠ 0) :
    ∃ x : MonoidAlgebra R (Multiplicative A), x ≠ 0 ∧
      ∀ n : ℕ, x ∈ (augmentationIdeal R (Multiplicative A)) ^ (n + 1) := by
  refine ⟨MonoidAlgebra.of R (Multiplicative A) (Multiplicative.ofAdd a) - 1, ?_, ?_⟩
  · intro h
    apply ha
    have he : MonoidAlgebra.of R (Multiplicative A) (Multiplicative.ofAdd a) =
        MonoidAlgebra.of R (Multiplicative A) 1 := by
      simpa only [map_one] using sub_eq_zero.mp h
    exact congrArg Multiplicative.toAdd (MonoidAlgebra.of_injective he)
  · intro n
    rw [augmentation_power_eq_of_p_divisible p hA]
    exact root_mem R (Multiplicative A) _

variable (p : ℕ) [Fact p.Prime]

/-- Rational division supplies the actual prime-division map. -/
theorem rational_prime_smul_surjective : Function.Surjective fun a : ℚ => p • a := by
  intro a
  refine ⟨a / p, ?_⟩
  change p • (a / (p : ℚ)) = a
  rw [nsmul_eq_mul, mul_div_cancel₀ a (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)]

/-- The modular group algebra of the additive rationals has an idempotent augmentation ideal. -/
theorem rational_augmentation_square :
    (augmentationIdeal (ZMod p) (Multiplicative ℚ)) ^ 2 =
      augmentationIdeal (ZMod p) (Multiplicative ℚ) :=
  augmentation_square_eq_of_p_divisible p (rational_prime_smul_surjective p)

/-- Every ordinary positive-order augmentation quotient of the rational group algebra is `𝔽_p`. -/
def rationalAugmentationQuotientEquiv (n : ℕ) :
    (MonoidAlgebra (ZMod p) (Multiplicative ℚ) ⧸
      (augmentationIdeal (ZMod p) (Multiplicative ℚ)) ^ (n + 1)) ≃ₐ[ZMod p] ZMod p :=
  divisibleAugmentationQuotientEquiv p (rational_prime_smul_surjective p) n

/-- The rational augmentation filtration is not separated: a nonzero element survives every power. -/
theorem rational_augmentation_not_separated :
    ∃ x : MonoidAlgebra (ZMod p) (Multiplicative ℚ), x ≠ 0 ∧
      ∀ n : ℕ, x ∈ (augmentationIdeal (ZMod p) (Multiplicative ℚ)) ^ (n + 1) :=
  exists_nonzero_mem_all_augmentation_powers p (rational_prime_smul_surjective p) 1 one_ne_zero

/-- The exact division sequence for `ℚ/ℤ` forces augmentation idempotence. -/
theorem ratModInt_augmentation_square :
    (augmentationIdeal (ZMod p) (Multiplicative HTGeometry.ABHN.RatModInt)) ^ 2 =
      augmentationIdeal (ZMod p) (Multiplicative HTGeometry.ABHN.RatModInt) :=
  augmentation_square_eq_of_p_divisible p
    (HTGeometry.ABHN.ratModIntNsmulAddHom_surjective p (Fact.out : p.Prime).ne_zero)

/-- Every positive ordinary augmentation quotient of `𝔽_p[ℚ/ℤ]` is exactly `𝔽_p`. -/
def ratModIntAugmentationQuotientEquiv (n : ℕ) :
    (MonoidAlgebra (ZMod p) (Multiplicative HTGeometry.ABHN.RatModInt) ⧸
      (augmentationIdeal (ZMod p) (Multiplicative HTGeometry.ABHN.RatModInt)) ^ (n + 1))
        ≃ₐ[ZMod p] ZMod p :=
  divisibleAugmentationQuotientEquiv p
    (HTGeometry.ABHN.ratModIntNsmulAddHom_surjective p (Fact.out : p.Prime).ne_zero) n

/-- The `ℚ/ℤ` augmentation filtration also has a nonzero element in every positive power. -/
theorem ratModInt_augmentation_not_separated :
    ∃ x : MonoidAlgebra (ZMod p) (Multiplicative HTGeometry.ABHN.RatModInt), x ≠ 0 ∧
      ∀ n : ℕ, x ∈
        (augmentationIdeal (ZMod p) (Multiplicative HTGeometry.ABHN.RatModInt)) ^ (n + 1) := by
  let f := HTGeometry.ABHN.zmodRatModIntAddHom 2 (Nat.succ_ne_zero 1)
  have hf : f (1 : ZMod 2) ≠ 0 := by
    intro h
    apply (one_ne_zero : (1 : ZMod 2) ≠ 0)
    apply HTGeometry.ABHN.zmodRatModIntAddHom_injective 2 (Nat.succ_ne_zero 1)
    exact h.trans (map_zero f).symm
  exact exists_nonzero_mem_all_augmentation_powers p
    (HTGeometry.ABHN.ratModIntNsmulAddHom_surjective p (Fact.out : p.Prime).ne_zero) _ hf

#print axioms rational_augmentation_square
#print axioms rationalAugmentationQuotientEquiv
#print axioms ratModInt_augmentation_square
#print axioms ratModIntAugmentationQuotientEquiv
#print axioms rational_augmentation_not_separated
#print axioms ratModInt_augmentation_not_separated

end GaloisForLFunctions.RepresentationLifting
