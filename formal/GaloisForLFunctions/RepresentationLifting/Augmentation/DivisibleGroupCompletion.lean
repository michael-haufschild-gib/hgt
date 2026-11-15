import GaloisForLFunctions.RepresentationLifting.Augmentation.DivisibleGroupQuotients
import Mathlib.RingTheory.AdicCompletion.Algebra

/-!
# Ordinary completion of divisible character-group algebras

An idempotent ideal has the same quotient at every positive stage, so its
actual adic completion is the first quotient. This requires no finite
generation assumption. For a prime-divisible abelian group in characteristic
that prime, augmentation therefore identifies the ordinary completion with
the coefficient ring and identifies the kernel of completion with the whole
augmentation ideal.

For the character groups `ℚ` and `ℚ/ℤ`, this supplies explicit ordinary
completion algebras in the setting motivating Carlsson–Joshua
(arXiv:2611.15605, Sections 1–2).
-/

noncomputable section
namespace GaloisForLFunctions.RepresentationLifting

section IdempotentIdeal
variable {S : Type*} [CommRing S] (I : Ideal S)

private theorem idempotentIdeal_pow_succ (hI : I ^ 2 = I) (n : ℕ) : I ^ (n + 1) = I := by
  induction n with
  | zero => exact pow_one I
  | succ n ih => rw [pow_succ, ih, ← pow_two, hI]

/-- For an idempotent ideal, the first residue class determines an entire adic element. -/
theorem idempotentAdicCompletion_evalOne_injective (hI : I ^ 2 = I) :
    Function.Injective (AdicCompletion.evalOneₐ I) := by
  intro x y
  refine AdicCompletion.induction_on I S
    (p := fun z => AdicCompletion.evalOneₐ I z = AdicCompletion.evalOneₐ I y → z = y) x ?_
  intro f
  refine AdicCompletion.induction_on I S
    (p := fun z => AdicCompletion.evalOneₐ I (AdicCompletion.mk I S f) =
      AdicCompletion.evalOneₐ I z → AdicCompletion.mk I S f = z) y ?_
  intro g h
  change Ideal.Quotient.mk I (f.val 1) = Ideal.Quotient.mk I (g.val 1) at h
  apply AdicCompletion.ext_evalₐ
  intro n
  simp only [AdicCompletion.evalₐ_mk]
  cases n with
  | zero =>
    rw [pow_zero, Ideal.one_eq_top]
    exact Subsingleton.elim _ _
  | succ n =>
    rw [idempotentIdeal_pow_succ I hI n]
    have hf := AdicCompletion.Ideal.mk_eq_mk I (Nat.le_add_left 1 n) f
    have hg := AdicCompletion.Ideal.mk_eq_mk I (Nat.le_add_left 1 n) g
    change Ideal.Quotient.mk (I ^ 1) (f.val (n + 1)) =
      Ideal.Quotient.mk (I ^ 1) (f.val 1) at hf
    change Ideal.Quotient.mk (I ^ 1) (g.val (n + 1)) =
      Ideal.Quotient.mk (I ^ 1) (g.val 1) at hg
    rw [pow_one] at hf hg
    exact hf.trans (h.trans hg.symm)

/-- Completion at any idempotent ideal is canonically the quotient by that ideal. -/
def idempotentAdicCompletionEquiv (hI : I ^ 2 = I) : AdicCompletion I S ≃ₐ[S] S ⧸ I :=
  AlgEquiv.ofBijective (AdicCompletion.evalOneₐ I)
    ⟨idempotentAdicCompletion_evalOne_injective I hI, AdicCompletion.evalOneₐ_surjective I⟩

/-- The completion equivalence carries the canonical map to the ordinary quotient map. -/
theorem idempotentAdicCompletionEquiv_of (hI : I ^ 2 = I) (x : S) :
    idempotentAdicCompletionEquiv I hI (AdicCompletion.of I S x) =
      Ideal.Quotient.mk I x := rfl

end IdempotentIdeal

section AlgebraQuotient
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- A surjective scalar-valued algebra map with idempotent kernel is its own completion map. -/
def idempotentKernelCompletionEquiv (f : S →ₐ[R] R) (hf : Function.Surjective f)
    (hI : (RingHom.ker f) ^ 2 = RingHom.ker f) :
    AdicCompletion (RingHom.ker f) S ≃ₐ[R] R :=
  ((idempotentAdicCompletionEquiv (RingHom.ker f) hI).restrictScalars R).trans
    (Ideal.quotientKerAlgEquivOfSurjective hf)

end AlgebraQuotient

open HTGeometry.GroupAlgebraFirstJet
variable {R A : Type*} [CommRing R] [AddCommGroup A]

/-- The ordinary augmentation completion of a prime-divisible group algebra is its scalar ring. -/
def divisibleAugmentationCompletionEquiv (p : ℕ) [CharP R p]
    (hA : Function.Surjective fun a : A => p • a) :
    AdicCompletion (augmentationIdeal R (Multiplicative A))
      (MonoidAlgebra R (Multiplicative A)) ≃ₐ[R] R :=
  idempotentKernelCompletionEquiv (augmentation R (Multiplicative A))
    (groupAlgebra_augmentation_surjective (R := R) (A := A))
    (augmentation_square_eq_of_p_divisible (R := R) p hA)

/-- Under the completion equivalence, the canonical map is exactly augmentation. -/
theorem divisibleAugmentationCompletionEquiv_of (p : ℕ) [CharP R p]
    (hA : Function.Surjective fun a : A => p • a)
    (x : MonoidAlgebra R (Multiplicative A)) :
    divisibleAugmentationCompletionEquiv p hA
      (AdicCompletion.of (augmentationIdeal R (Multiplicative A)) _ x) =
        augmentation R (Multiplicative A) x := rfl

/-- Completion kills precisely the augmentation-zero elements. -/
theorem divisibleAugmentationCompletion_of_eq_zero_iff (p : ℕ) [CharP R p]
    (hA : Function.Surjective fun a : A => p • a)
    (x : MonoidAlgebra R (Multiplicative A)) :
    AdicCompletion.of (augmentationIdeal R (Multiplicative A)) _ x = 0 ↔
      augmentation R (Multiplicative A) x = 0 := by
  constructor
  · intro h
    have he := congrArg (divisibleAugmentationCompletionEquiv p hA) h
    rw [divisibleAugmentationCompletionEquiv_of, map_zero] at he
    exact he
  · intro h
    apply (divisibleAugmentationCompletionEquiv p hA).injective
    rw [divisibleAugmentationCompletionEquiv_of, map_zero, h]

/-- The kernel of the canonical ring map to completion is the full augmentation ideal. -/
theorem divisibleAugmentationCompletion_kernel (p : ℕ) [CharP R p]
    (hA : Function.Surjective fun a : A => p • a) :
    RingHom.ker (algebraMap (MonoidAlgebra R (Multiplicative A))
      (AdicCompletion (augmentationIdeal R (Multiplicative A))
        (MonoidAlgebra R (Multiplicative A)))) = augmentationIdeal R (Multiplicative A) := by
  ext x
  change AdicCompletion.of (augmentationIdeal R (Multiplicative A)) _ x = 0 ↔
    augmentation R (Multiplicative A) x = 0
  exact divisibleAugmentationCompletion_of_eq_zero_iff p hA x

variable (p : ℕ) [Fact p.Prime]

/-- The ordinary augmentation completion of `𝔽_p[ℚ]` is exactly `𝔽_p`. -/
def rationalAugmentationCompletionEquiv :
    AdicCompletion (augmentationIdeal (ZMod p) (Multiplicative ℚ))
      (MonoidAlgebra (ZMod p) (Multiplicative ℚ)) ≃ₐ[ZMod p] ZMod p :=
  divisibleAugmentationCompletionEquiv p (rational_prime_smul_surjective p)

/-- The ordinary augmentation completion of `𝔽_p[ℚ/ℤ]` is exactly `𝔽_p`. -/
def ratModIntAugmentationCompletionEquiv :
    AdicCompletion (augmentationIdeal (ZMod p) (Multiplicative HTGeometry.ABHN.RatModInt))
      (MonoidAlgebra (ZMod p) (Multiplicative HTGeometry.ABHN.RatModInt)) ≃ₐ[ZMod p] ZMod p :=
  divisibleAugmentationCompletionEquiv p
    (HTGeometry.ABHN.ratModIntNsmulAddHom_surjective p (Fact.out : p.Prime).ne_zero)

/-- The rational character algebra contains a nonzero element killed by completion. -/
theorem rational_augmentation_completion_kills_nonzero :
    ∃ x : MonoidAlgebra (ZMod p) (Multiplicative ℚ), x ≠ 0 ∧
      AdicCompletion.of (augmentationIdeal (ZMod p) (Multiplicative ℚ)) _ x = 0 := by
  obtain ⟨x, hx, hp⟩ := rational_augmentation_not_separated p
  refine ⟨x, hx, (divisibleAugmentationCompletion_of_eq_zero_iff p
    (rational_prime_smul_surjective p) x).mpr ?_⟩
  have h := hp 0
  rw [pow_one] at h
  exact h

/-- The torsion character algebra also loses nonzero elements under ordinary completion. -/
theorem ratModInt_augmentation_completion_kills_nonzero :
    ∃ x : MonoidAlgebra (ZMod p) (Multiplicative HTGeometry.ABHN.RatModInt), x ≠ 0 ∧
      AdicCompletion.of
        (augmentationIdeal (ZMod p) (Multiplicative HTGeometry.ABHN.RatModInt)) _ x = 0 := by
  obtain ⟨x, hx, hp⟩ := ratModInt_augmentation_not_separated p
  refine ⟨x, hx, (divisibleAugmentationCompletion_of_eq_zero_iff p
    (HTGeometry.ABHN.ratModIntNsmulAddHom_surjective p (Fact.out : p.Prime).ne_zero) x).mpr ?_⟩
  have h := hp 0
  rw [pow_one] at h
  exact h

#print axioms idempotentAdicCompletionEquiv
#print axioms rationalAugmentationCompletionEquiv
#print axioms ratModIntAugmentationCompletionEquiv
#print axioms divisibleAugmentationCompletion_kernel
#print axioms rational_augmentation_completion_kills_nonzero
#print axioms ratModInt_augmentation_completion_kills_nonzero

end GaloisForLFunctions.RepresentationLifting
