import GaloisForLFunctions.HTGeometry.TailScalingAction
import Mathlib.FieldTheory.Fixed
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# The fixed field of the deck transformations

The deck transformations form a finite group of automorphisms of the polynomial ring in the
parameters, hence of its field of rational functions.  Artin's theorem computes the degree of that
field over the fixed subfield: it is the order of the group.

Since distinct roots of unity give distinct deck transformations, that order is the number of
`n`-th roots of unity in the constants, which is `n` when the constants are algebraically closed.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

variable {K : Type*} [Field K] {n : ℕ}

/-- The deck transformations as a group of automorphisms of the parameter ring. -/
noncomputable def deckGroup (K : Type*) [Field K] (n : ℕ) :
    Subgroup (RingAut (MvPolynomial (Fin n) K)) :=
  (rootsOfUnityScale K n).range

theorem deckGroup_smul (g : deckGroup K n) (p : MvPolynomial (Fin n) K) :
    g • p = (g : RingAut (MvPolynomial (Fin n) K)) p := rfl

instance deckGroupFaithful : FaithfulSMul (deckGroup K n) (MvPolynomial (Fin n) K) where
  eq_of_smul_eq_smul := by
    intro g h hgh
    refine Subtype.ext (RingEquiv.ext fun p => ?_)
    have := hgh p
    rwa [deckGroup_smul, deckGroup_smul] at this

noncomputable instance deckGroupFracAction :
    MulSemiringAction (deckGroup K n) (FractionRing (MvPolynomial (Fin n) K)) :=
  IsFractionRing.mulSemiringAction (deckGroup K n) (MvPolynomial (Fin n) K)
    (FractionRing (MvPolynomial (Fin n) K))

noncomputable instance deckGroupFracFaithful :
    FaithfulSMul (deckGroup K n) (FractionRing (MvPolynomial (Fin n) K)) :=
  IsFractionRing.faithfulSMul (deckGroup K n) (MvPolynomial (Fin n) K)
    (FractionRing (MvPolynomial (Fin n) K))

/-- **The deck group is the group of `n`-th roots of unity.** -/
noncomputable def deckGroupEquiv (K : Type*) [Field K] (n : ℕ) [NeZero n] :
    rootsOfUnity n K ≃* deckGroup K n :=
  MulEquiv.ofBijective ((rootsOfUnityScale K n).rangeRestrict)
    ⟨fun _ _ h => rootsOfUnityScale_injective (K := K) (n := n)
      (congrArg Subtype.val h), (rootsOfUnityScale K n).rangeRestrict_surjective⟩

/-- **Artin's theorem for the deck transformations.**  The rational function field in the parameters
has degree the order of the deck group over the fixed field. -/
theorem finrank_fixedField_deckGroup [Fintype (deckGroup K n)] :
    Module.finrank
        (FixedPoints.subfield (deckGroup K n) (FractionRing (MvPolynomial (Fin n) K)))
        (FractionRing (MvPolynomial (Fin n) K)) =
      Fintype.card (deckGroup K n) :=
  FixedPoints.finrank_eq_card (deckGroup K n) (FractionRing (MvPolynomial (Fin n) K))

/-- **The tail coefficients lie in the fixed field.** -/
theorem algebraMap_tailCoeff_mem_fixedField (j : Fin n) :
    algebraMap (MvPolynomial (Fin n) K) (FractionRing (MvPolynomial (Fin n) K))
        (tailCoeff K n j) ∈
      FixedPoints.subfield (deckGroup K n) (FractionRing (MvPolynomial (Fin n) K)) := by
  intro g
  obtain ⟨u, hu⟩ := g.2
  have hcompat : g • (algebraMap (MvPolynomial (Fin n) K)
        (FractionRing (MvPolynomial (Fin n) K)) (tailCoeff K n j)) =
      algebraMap (MvPolynomial (Fin n) K) (FractionRing (MvPolynomial (Fin n) K))
        (g • tailCoeff K n j) := by
    have h := smul_distrib_smul g (tailCoeff K n j)
      (1 : FractionRing (MvPolynomial (Fin n) K))
    rwa [smul_one, Algebra.smul_def, Algebra.smul_def, mul_one, mul_one] at h
  rw [hcompat]
  congr 1
  rw [deckGroup_smul, ← hu]
  exact rootsOfUnityScale_tailCoeff u j

/-- **The deck group has order `n`.**  Distinct roots of unity give distinct deck transformations,
and a primitive root supplies exactly `n` of them. -/
theorem card_deckGroup [NeZero n] {ζ : K} (hζ : IsPrimitiveRoot ζ n) :
    Nat.card (deckGroup K n) = n := by
  rw [← Nat.card_congr (deckGroupEquiv K n).toEquiv]
  exact hζ.card_rootsOfUnity

end GaloisForLFunctions.HTGeometry
