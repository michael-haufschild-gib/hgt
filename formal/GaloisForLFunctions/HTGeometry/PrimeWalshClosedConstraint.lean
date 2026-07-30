import GaloisForLFunctions.HTGeometry.PrimeWalshStoneReconstruction
import GaloisForLFunctions.HTGeometry.PrimeWalshDifferentialRank

/-!
# Closed Boolean constraints as exact Prime-Walsh tail geometries

Every nonempty closed constraint in a countable Boolean cube has a canonical dense sequence.
Repeating that sequence infinitely often realizes the constraint exactly as a prime-orientation
tail cluster.  The construction preserves frozen anchor coordinates, reconstructs the full
locally constant Stone algebra, and gives the exact differential rank of every finite Walsh
projection.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Set Topology

noncomputable section

/-- A chosen dense sequence in a nonempty closed Boolean constraint. -/
def denseBooleanConstraintProfile {J : Type*} [Countable J]
    (K : Set (J → Bool)) [Nonempty K] : ℕ → (J → Bool) :=
  fun n => (TopologicalSpace.denseSeq K n).1

/-- Canonically repeat a dense sequence in a Boolean constraint so that every attained finite
pattern recurs infinitely often. -/
def closedConstraintOrientation {J : Type*} [Countable J]
    (K : Set (J → Bool)) [Nonempty K] : ℕ → (J → Bool) :=
  infinitelyRepeatedOrientation (denseBooleanConstraintProfile K)

theorem denseBooleanConstraintProfile_mem {J : Type*} [Countable J]
    (K : Set (J → Bool)) [Nonempty K] (n : ℕ) :
    denseBooleanConstraintProfile K n ∈ K :=
  (TopologicalSpace.denseSeq K n).2

theorem denseBooleanConstraintProfile_finitePattern
    {J : Type*} [Countable J]
    (K : Set (J → Bool)) [Nonempty K]
    (x : J → Bool) (hx : x ∈ K) (I : Finset J) :
    ∃ n, orientationRestriction I (denseBooleanConstraintProfile K n) =
      orientationRestriction I x := by
  let U : Set K := Subtype.val ⁻¹'
    orientationCylinder I (orientationRestriction I x)
  have hUopen : IsOpen U :=
    (isClopen_orientationCylinder I (orientationRestriction I x)).2.preimage
      continuous_subtype_val
  have hxU : (⟨x, hx⟩ : K) ∈ U := by
    exact (mem_orientationCylinder_iff I _ x).2 (fun _ => rfl)
  obtain ⟨n, hn⟩ := (TopologicalSpace.denseRange_denseSeq K).exists_mem_open
    hUopen ⟨⟨x, hx⟩, hxU⟩
  refine ⟨n, ?_⟩
  exact hn

/-- Membership in a closed Boolean constraint is equivalent to matching its dense sequence on
every finite coordinate chamber. -/
theorem mem_closedBooleanConstraint_iff_finitePatterns
    {J : Type*} [Countable J]
    (K : Set (J → Bool)) [Nonempty K] (hK : IsClosed K) (x : J → Bool) :
    x ∈ K ↔ ∀ I : Finset J, ∃ n,
      orientationRestriction I (denseBooleanConstraintProfile K n) =
        orientationRestriction I x := by
  constructor
  · intro hx I
    exact denseBooleanConstraintProfile_finitePattern K x hx I
  · intro hpattern
    by_contra hx
    have hxcompl : x ∈ Kᶜ := hx
    have hnhds : Kᶜ ∈ nhds x := hK.isOpen_compl.mem_nhds hxcompl
    obtain ⟨t, hts, htopen, hxt⟩ := mem_nhds_iff.mp hnhds
    obtain ⟨I, u, hu, hpi⟩ := isOpen_pi_iff.mp htopen x hxt
    obtain ⟨n, hn⟩ := hpattern I
    have hdense_mem_t : denseBooleanConstraintProfile K n ∈ t := by
      apply hpi
      intro j hj
      have hj' : denseBooleanConstraintProfile K n j = x j :=
        congrFun hn ⟨j, hj⟩
      rw [hj']
      exact (hu j hj).2
    have hdense_compl : denseBooleanConstraintProfile K n ∈ Kᶜ := hts hdense_mem_t
    exact hdense_compl (denseBooleanConstraintProfile_mem K n)

/-- The complete tail cluster of the canonical repeated dense sequence is exactly the prescribed
closed Boolean constraint. -/
theorem tailCluster_infinitelyRepeatedDenseBooleanConstraint
    {J : Type*} [Countable J]
    (K : Set (J → Bool)) [Nonempty K] (hK : IsClosed K) :
    primeOrientationTailClusterSet
        (closedConstraintOrientation K) = K := by
  apply tailCluster_infinitelyRepeatedOrientation_eq
  intro x
  exact mem_closedBooleanConstraint_iff_finitePatterns K hK x

/-- The canonical realization preserves any coordinate frozen throughout the constraint. -/
theorem closedConstraintOrientation_eq_of_coordinate_eq
    {J : Type*} [Countable J]
    (K : Set (J → Bool)) [Nonempty K] (j : J) (b : Bool)
    (hj : ∀ x ∈ K, x j = b) (n : ℕ) :
    closedConstraintOrientation K n j = b := by
  exact hj _ (denseBooleanConstraintProfile_mem K (Nat.unpair n).1)

/-- Stone reconstruction for a prescribed closed Boolean constraint, with the tail-cluster
subtype transported to the constraint subtype itself. -/
def closedConstraintPrimeTailLocallyConstantQuotientEquiv
    {J : Type*} [Countable J] [DecidableEq J]
    (K : Set (J → Bool)) [Nonempty K] (hK : IsClosed K) :
    (LocallyConstant (J → Bool) ℂ ⧸
        primeTailVanishingIdeal (closedConstraintOrientation K)) ≃ₐ[ℂ]
      LocallyConstant K ℂ :=
  (primeTailLocallyConstantQuotientEquiv (closedConstraintOrientation K)).trans
    (LocallyConstant.congrLeftₐ ℂ
      (Homeomorph.setCongr
        (tailCluster_infinitelyRepeatedDenseBooleanConstraint K hK)))

/-- Transport the canonical constraint sequence to the prime coordinates through an enumeration. -/
def enumeratedClosedConstraintPrimeOrientation
    {J : Type*} [Countable J] (e : ℕ ≃ Nat.Primes)
    (K : Set (J → Bool)) [Nonempty K] (j : J) (p : Nat.Primes) : Bool :=
  closedConstraintOrientation K (e.symm p) j

/-- Every finite prime chamber of the enumerated realization is exactly the corresponding
projection of the prescribed closed Boolean constraint. -/
theorem primeRecurringPatternChamber_enumeratedClosedConstraint
    {J : Type*} [Countable J] (e : ℕ ≃ Nat.Primes)
    (K : Set (J → Bool)) [Nonempty K] (hK : IsClosed K) (I : Finset J) :
    primeRecurringPatternChamber e
        (fun i : I => enumeratedClosedConstraintPrimeOrientation e K i.1) =
      orientationRestriction I '' K := by
  have hseq : (fun n i =>
      enumeratedClosedConstraintPrimeOrientation e K i.1 (e n)) =
      fun n => orientationRestriction I (closedConstraintOrientation K n) := by
    funext n i
    simp [enumeratedClosedConstraintPrimeOrientation, orientationRestriction]
  unfold primeRecurringPatternChamber
  rw [hseq, ← image_tailCluster_orientationRestriction]
  rw [tailCluster_infinitelyRepeatedDenseBooleanConstraint K hK]

/-- The full Walsh palette over every finite coordinate chamber has differential rank equal to
the number of patterns in that projection of the closed constraint. -/
theorem enumeratedClosedConstraintPrimeWalsh_differentialBasis_and_rank
    {J A : Type*} [Countable J]
    [Fintype A] [DecidableEq A] [Nonempty A]
    (e : ℕ ≃ Nat.Primes) (K : Set (J → Bool)) [Nonempty K]
    (hK : IsClosed K) (I : Finset J)
    (alpha : A → ℂ) (hdistinct : Function.Injective (fun a => (alpha a).re)) :
    let epsilon : I → Nat.Primes → Bool :=
      fun i => enumeratedClosedConstraintPrimeOrientation e K i.1
    GaloisForLFunctions.DifferentialIndependent finitePrimeRationalCoefficientField
        (primeTailPatternDeltaShiftPalette e epsilon alpha) ∧
      GaloisForLFunctions.differentialAdjoin finitePrimeRationalCoefficientField
          (Set.range (primeTailPatternDeltaShiftPalette e epsilon alpha)) =
        GaloisForLFunctions.differentialAdjoin finitePrimeRationalCoefficientField
          (Set.range (primeWalshShiftPalette epsilon alpha)) ∧
      Nat.card (primeRecurringPatternChamber e epsilon × A) =
        Nat.card A * Nat.card (orientationRestriction I '' K) := by
  dsimp only
  have hbasis := primeWalshShiftPalette_differentialBasis e
    (fun i : I => enumeratedClosedConstraintPrimeOrientation e K i.1) alpha hdistinct
  refine ⟨hbasis.1, hbasis.2, ?_⟩
  rw [primeWalshDifferentialBasis_card,
    primeRecurringPatternChamber_enumeratedClosedConstraint e K hK I]

end

end GaloisForLFunctions.HTGeometry
