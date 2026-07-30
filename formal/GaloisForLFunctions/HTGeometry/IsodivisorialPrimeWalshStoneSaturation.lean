import GaloisForLFunctions.HTGeometry.ExponentZeroPrimeWalshSaturation
import GaloisForLFunctions.HTGeometry.PrimeWalshShiftEntropy
import Mathlib.Topology.Category.LightProfinite.Basic
import Mathlib.Topology.Category.Profinite.Nobeling.Induction

/-!
# Isodivisorial Prime-Walsh Stone saturation

This capstone identifies every pointed compact metrizable Stone space with a closed anchored
Boolean constraint, realizes it on an exponent-zero sparse prime reservoir, and packages the
ordinary differential-independence and quantitative Prime-Walsh rank/entropy consequences.
-/

open CategoryTheory Topology TopologicalSpace

namespace GaloisForLFunctions.HTGeometry

open Filter Set Topology

noncomputable section

instance secondCountableTopology_lightToProfinite (S : LightProfinite) :
    SecondCountableTopology (lightToProfinite.obj S) := by
  change SecondCountableTopology S
  infer_instance

instance countableClopens_lightToProfinite (S : LightProfinite) :
    Countable (Clopens (lightToProfinite.obj S)) := by
  rw [TopologicalSpace.Clopens.countable_iff_secondCountable]
  infer_instance

/-- Pointed Nöbeling coordinates, with one extra frozen anchor coordinate. -/
def pointedStoneOrientation (S : LightProfinite) (base : S) :
    S → (Unit ⊕ Clopens (lightToProfinite.obj S) → Bool) :=
  fun x j => match j with
    | Sum.inl _ => false
    | Sum.inr C =>
        let C' : {U : Set (lightToProfinite.obj S) // IsClopen U} :=
          ⟨C, C.isClopen⟩
        Bool.xor (Profinite.Nobeling.ι (lightToProfinite.obj S) x C')
          (Profinite.Nobeling.ι (lightToProfinite.obj S) base C')

theorem continuous_pointedStoneOrientation (S : LightProfinite) (base : S) :
    Continuous (pointedStoneOrientation S base) := by
  apply continuous_pi
  intro j
  cases j with
  | inl u => exact continuous_const
  | inr C =>
      let C' : {U : Set (lightToProfinite.obj S) // IsClopen U} :=
        ⟨C, C.isClopen⟩
      have hcoord : Continuous
          (fun x => Profinite.Nobeling.ι (lightToProfinite.obj S) x C') :=
        (continuous_apply C').comp
          (Profinite.Nobeling.isClosedEmbedding (lightToProfinite.obj S)).continuous
      have hxor : Continuous (fun b : Bool => Bool.xor b
          (Profinite.Nobeling.ι (lightToProfinite.obj S) base C')) :=
        continuous_of_discreteTopology
      exact hxor.comp hcoord

theorem injective_pointedStoneOrientation (S : LightProfinite) (base : S) :
    Function.Injective (pointedStoneOrientation S base) := by
  intro x y hxy
  apply (Profinite.Nobeling.isClosedEmbedding (lightToProfinite.obj S)).injective
  funext C
  let C' : Clopens (lightToProfinite.obj S) := ⟨C.1, C.2⟩
  have hC := congrFun hxy (Sum.inr C')
  simp only [pointedStoneOrientation] at hC
  change Bool.xor (Profinite.Nobeling.ι (lightToProfinite.obj S) x C)
      (Profinite.Nobeling.ι (lightToProfinite.obj S) base C) =
    Bool.xor (Profinite.Nobeling.ι (lightToProfinite.obj S) y C)
      (Profinite.Nobeling.ι (lightToProfinite.obj S) base C) at hC
  revert hC
  cases Profinite.Nobeling.ι (lightToProfinite.obj S) x C <;>
    cases Profinite.Nobeling.ι (lightToProfinite.obj S) y C <;>
    cases Profinite.Nobeling.ι (lightToProfinite.obj S) base C <;> simp

theorem isClosedEmbedding_pointedStoneOrientation (S : LightProfinite) (base : S) :
    IsClosedEmbedding (pointedStoneOrientation S base) :=
  Continuous.isClosedEmbedding (continuous_pointedStoneOrientation S base)
    (injective_pointedStoneOrientation S base)

/-- The closed Boolean constraint associated to a pointed compact metrizable Stone space. -/
def pointedStoneConstraint (S : LightProfinite) (base : S) :
    Set (Unit ⊕ Clopens (lightToProfinite.obj S) → Bool) :=
  Set.range (pointedStoneOrientation S base)

theorem isClosed_pointedStoneConstraint (S : LightProfinite) (base : S) :
    IsClosed (pointedStoneConstraint S base) :=
  (isClosedEmbedding_pointedStoneOrientation S base).isClosed_range

instance pointedStoneConstraint_nonempty (S : LightProfinite) (base : S) :
    Nonempty (pointedStoneConstraint S base) :=
  ⟨⟨pointedStoneOrientation S base base, base, rfl⟩⟩

theorem pointedStoneOrientation_base (S : LightProfinite) (base : S) :
    pointedStoneOrientation S base base = allPositiveOrientationPattern := by
  funext j
  cases j <;> simp [pointedStoneOrientation, allPositiveOrientationPattern]

theorem allPositiveOrientationPattern_mem_pointedStoneConstraint
    (S : LightProfinite) (base : S) :
    allPositiveOrientationPattern ∈ pointedStoneConstraint S base := by
  refine ⟨base, ?_⟩
  exact pointedStoneOrientation_base S base

theorem pointedStoneConstraint_anchor
    (S : LightProfinite) (base : S)
    (x : Unit ⊕ Clopens (lightToProfinite.obj S) → Bool)
    (hx : x ∈ pointedStoneConstraint S base) :
    x (Sum.inl ()) = false := by
  obtain ⟨y, rfl⟩ := hx
  rfl

/-- The original pointed Stone space is homeomorphic to the closed Boolean constraint, and the
distinguished point maps to the all-positive pattern. -/
def pointedStoneConstraintHomeomorph (S : LightProfinite) (base : S) :
    S ≃ₜ pointedStoneConstraint S base :=
  (isClosedEmbedding_pointedStoneOrientation S base).isEmbedding.toHomeomorph

@[simp]
theorem pointedStoneConstraintHomeomorph_base (S : LightProfinite) (base : S) :
    pointedStoneConstraintHomeomorph S base base =
      ⟨allPositiveOrientationPattern,
        allPositiveOrientationPattern_mem_pointedStoneConstraint S base⟩ := by
  apply Subtype.ext
  simpa [pointedStoneConstraintHomeomorph] using! pointedStoneOrientation_base S base

/-- Linear independence of the coordinate sign functions on the prescribed finite projection
forces tail independence of the corresponding sparse prime orientations. -/
theorem sparseClosedConstraint_tailIndependent_of_coordinateSigns
    {J : Type*} [Countable J] (pi : ℕ ≃ Nat.Primes)
    (K : Set (J → Bool)) [Nonempty K] (hK : IsClosed K)
    (hall : allPositiveOrientationPattern ∈ K) (I : Finset J)
    (hlinear : ∀ c : I → ℂ,
      (∀ x ∈ orientationRestriction I '' K,
        ∑ i, c i * primeDirichletSign (x i) = 0) → c = 0) :
    PrimeOrientationTailIndependent
      (fun i : I => sparseClosedConstraintPrimeOrientation K i.1) := by
  rw [primeOrientationTailIndependent_iff_recurringPatternsSpan]
  intro c hrec
  apply hlinear c
  intro x hx
  have hr : x ∈ primeRecurringPatternChamber pi
      (fun i : I => sparseClosedConstraintPrimeOrientation K i.1) := by
    rw [primeRecurringPatternChamber_sparseClosedConstraint_projection pi K hK hall I]
    exact hx
  have hinf := primeRecurringPatternChamber_fiber_infinite pi
    (fun i : I => sparseClosedConstraintPrimeOrientation K i.1) ⟨x, hr⟩
  exact hrec x (by simpa [primeOrientationPattern] using! hinf)

/-- Every finite shift rectangle of a coordinate-independent closed constraint is differentially
independent over the finite-prime rational differential field. -/
theorem sparseClosedConstraint_signedPrimeShiftPalette_differentialIndependent
    {J A : Type*} [Countable J]
    [Fintype A] [DecidableEq A] [Nonempty A]
    (pi : ℕ ≃ Nat.Primes) (K : Set (J → Bool)) [Nonempty K]
    (hK : IsClosed K) (hall : allPositiveOrientationPattern ∈ K)
    (I : Finset J) (hI : I.Nonempty)
    (alpha : A → ℂ) (hdistinct : Function.Injective (fun a => (alpha a).re))
    (hlinear : ∀ c : I → ℂ,
      (∀ x ∈ orientationRestriction I '' K,
        ∑ i, c i * primeDirichletSign (x i) = 0) → c = 0) :
    GaloisForLFunctions.DifferentialIndependent finitePrimeRationalCoefficientField
      (fun ia : I × A => signedPrimeShiftCarrier
        (sparseClosedConstraintPrimeOrientation K ia.1.1) (alpha ia.2)) := by
  classical
  letI : Nonempty I := hI.to_subtype
  exact (signedPrimeShiftPalette_differentialIndependent_iff
    (fun i : I => sparseClosedConstraintPrimeOrientation K i.1)
      alpha hdistinct).2
    (sparseClosedConstraint_tailIndependent_of_coordinateSigns
      pi K hK hall I hlinear)

/-- Prefix complexity of the sparse realization is exactly the cardinality of the corresponding
finite projection of the prescribed closed constraint. -/
theorem sparseClosedConstraint_primePrefixPatternComplexity_eq
    (pi : ℕ ≃ Nat.Primes) (K : Set (ℕ → Bool)) [Nonempty K]
    (hK : IsClosed K) (hall : allPositiveOrientationPattern ∈ K) (n : ℕ) :
    primePrefixPatternComplexity pi (sparseClosedConstraintPrimeOrientation K) n =
      Nat.card (primePrefixRestriction n '' K) := by
  have hfull := primeRecurringPatternChamber_sparseClosedConstraint pi K hK hall
  unfold primeRecurringPatternChamber at hfull
  rw [primePrefixPatternComplexity, primeRecurringPrefixChamber_eq_image, hfull]

/-- Exact finite-rank formula in the prefix chamber. -/
theorem sparseClosedConstraint_primeWalshPrefixDifferentialRank_eq
    (pi : ℕ ≃ Nat.Primes) (K : Set (ℕ → Bool)) [Nonempty K]
    (hK : IsClosed K) (hall : allPositiveOrientationPattern ∈ K)
    (A : Type*) (n : ℕ) :
    primeWalshPrefixDifferentialRank pi
        (sparseClosedConstraintPrimeOrientation K) A n =
      Nat.card A * Nat.card (primePrefixRestriction n '' K) := by
  rw [primeWalshPrefixDifferentialRank,
    sparseClosedConstraint_primePrefixPatternComplexity_eq pi K hK hall n]

/-- Shift invariance of a closed Boolean constraint. -/
def ClosedBooleanConstraintShiftInvariant (K : Set (ℕ → Bool)) : Prop :=
  ∀ x ∈ K, ∀ m, (fun j => x (m + j)) ∈ K

theorem sparseClosedConstraint_primeTailShiftInvariant
    (pi : ℕ ≃ Nat.Primes) (K : Set (ℕ → Bool)) [Nonempty K]
    (hK : IsClosed K) (hall : allPositiveOrientationPattern ∈ K)
    (hshift : ClosedBooleanConstraintShiftInvariant K) :
    PrimeTailShiftInvariant pi (sparseClosedConstraintPrimeOrientation K) := by
  have hfull := primeRecurringPatternChamber_sparseClosedConstraint pi K hK hall
  unfold primeRecurringPatternChamber at hfull
  intro x hx m
  rw [hfull] at hx ⊢
  exact hshift x hx m

/-- For a shift-invariant closed constraint, prefix-projection complexity and its exact
Prime-Walsh differential rank converge to the same entropy rate. -/
theorem sparseClosedConstraint_primeWalshRankEntropy_tendsto
    (pi : ℕ ≃ Nat.Primes) (K : Set (ℕ → Bool)) [Nonempty K]
    (hK : IsClosed K) (hall : allPositiveOrientationPattern ∈ K)
    (A : Type*) [Finite A] [Nonempty A]
    (hshift : ClosedBooleanConstraintShiftInvariant K) :
    ∃ h : ℝ,
      Tendsto
          (fun n => realNormalizedLogCard
            (Nat.card (primePrefixRestriction n '' K)) n)
          atTop (𝓝 h) ∧
      Tendsto
          (fun n => realNormalizedLogCard
            (Nat.card A * Nat.card (primePrefixRestriction n '' K)) n)
          atTop (𝓝 h) := by
  have h := primeWalshRankEntropy_tendsto_of_shiftInvariant pi
    (sparseClosedConstraintPrimeOrientation K) A
    (sparseClosedConstraint_primeTailShiftInvariant pi K hK hall hshift)
  simpa only [
    sparseClosedConstraint_primePrefixPatternComplexity_eq pi K hK hall,
    primeWalshPrefixDifferentialRank,
    sparseClosedConstraint_primePrefixPatternComplexity_eq pi K hK hall] using h

/-- Every pointed light profinite space is realized exactly as a sparse recurring prime-pattern
constraint, with its distinguished point sent to the all-positive orientation. -/
theorem pointedStoneConstraint_sparsePrime_realization
    (S : LightProfinite) (base : S) (pi : ℕ ≃ Nat.Primes) :
    primeRecurringPatternChamber pi
        (sparseClosedConstraintPrimeOrientation (pointedStoneConstraint S base)) =
      pointedStoneConstraint S base :=
  primeRecurringPatternChamber_sparseClosedConstraint pi
    (pointedStoneConstraint S base)
    (isClosed_pointedStoneConstraint S base)
    (allPositiveOrientationPattern_mem_pointedStoneConstraint S base)

end

end GaloisForLFunctions.HTGeometry
