import GaloisForLFunctions.HTGeometry.SquarefreeVeroneseIdeal

/-!
# Normal-crossing criticalization and derived-capacity phase

This file assembles the already formalized squarefree-Veronese, intrinsic-critical-ideal, and
coface-syzygy results into the theorem surfaces used by the Barnes/multiple-sine/multiple-elliptic
Gamma cards.  The special-function annihilator calculations, cotangent Fitting calculation, and
standard grade-sensitivity theorem are explicit inputs.  They are not introduced as axioms.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions.VeroneseIdeal
open MvPolynomial

noncomputable section

/-- Exact special-function and cotangent inputs for the cross-family criticalization theorem.
`Packet` indexes arbitrary finite structural operator packets, so the rank fields express equality
of the complete structural differential matroids rather than only equality of annihilator ideals. -/
structure NormalCrossingFamilyCriticalizationInput
    (F : Type*) [Field F] (r : ℕ) (Packet : Type*) where
  barnesAnnihilator : Ideal (MvPolynomial (Fin (r + 1)) F)
  sineAnnihilator : Ideal (MvPolynomial (Fin (r + 1)) F)
  ellipticGammaAnnihilator : Ideal (MvPolynomial (Fin (r + 1)) F)
  cotangentFittingPullback : Ideal (MvPolynomial (Fin (r + 1)) F)
  sineRank : Packet → ℕ
  ellipticGammaRank : Packet → ℕ
  quotientRank : Packet → ℕ
  barnes_exact : barnesAnnihilator =
    Ideal.span {normalCrossingPolynomial (F := F) r}
  sine_exact : sineAnnihilator = veroneseIdeal F (Fin (r + 1)) r
  ellipticGamma_exact :
    ellipticGammaAnnihilator = veroneseIdeal F (Fin (r + 1)) r
  cotangentFitting_exact :
    cotangentFittingPullback = veroneseIdeal F (Fin (r + 1)) r
  sine_rank_exact : sineRank = quotientRank
  ellipticGamma_rank_exact : ellipticGammaRank = quotientRank

/-- Barnes reflection and multiple-elliptic completion realize the same intrinsic critical ideal,
the same cotangent Fitting degeneracy scheme, and the same rank on every finite structural packet. -/
theorem normalCrossing_crossFamily_criticalization
    {F : Type*} [Field F] {r : ℕ} {Packet : Type*}
    (input : NormalCrossingFamilyCriticalizationInput F r Packet) :
    input.sineAnnihilator = input.ellipticGammaAnnihilator ∧
      input.sineAnnihilator =
        derivationalCriticalIdeal (R := F)
          (normalCrossingPolynomial (F := F) r) ∧
      input.cotangentFittingPullback = input.sineAnnihilator ∧
      input.sineRank = input.ellipticGammaRank := by
  refine ⟨input.sine_exact.trans input.ellipticGamma_exact.symm, ?_, ?_, ?_⟩
  · exact input.sine_exact.trans
      (normalCrossingDerivationalCriticalIdeal_eq_veroneseIdeal
        (F := F) r).symm
  · exact input.cotangentFitting_exact.trans input.sine_exact.symm
  · exact input.sine_rank_exact.trans input.ellipticGamma_rank_exact.symm

/-- The criticalization conclusion is invariant under replacing the normal-crossing source
equation by a unit multiple. -/
theorem normalCrossing_criticalization_unitPresentationInvariant
    {F : Type*} [Field F] (r : ℕ)
    (u : (MvPolynomial (Fin (r + 1)) F)ˣ) :
    derivationalCriticalIdeal (R := F)
        ((u : MvPolynomial (Fin (r + 1)) F) *
          normalCrossingPolynomial (F := F) r) =
      veroneseIdeal F (Fin (r + 1)) r := by
  rw [derivationalCriticalIdeal_unit_mul]
  exact normalCrossingDerivationalCriticalIdeal_eq_veroneseIdeal r

/-- A predicate family has exact homological amplitude `a` when degree `a` is nonzero and every
higher degree vanishes. -/
def HasExactHomologicalAmplitude (homologyNonzero : ℕ → Prop) (a : ℕ) : Prop :=
  homologyNonzero a ∧ ∀ i, a < i → ¬ homologyNonzero i

/-- Explicit standard commutative-algebra input for the normal-crossing Koszul complex.  It keeps
the grade computation and grade-sensitivity theorem visible at their exact boundary. -/
structure NormalCrossingKoszulGradeInput (r : ℕ) where
  homologyNonzero : ℕ → Prop
  grade : ℕ
  grade_eq_two : grade = 2
  gradeSensitivity :
    HasExactHomologicalAmplitude homologyNonzero ((r + 1) - grade)

/-- For `N=r+1 ≥ 2` normal-crossing coordinates, grade two gives exact derived amplitude
`N-2=r-1`. -/
theorem normalCrossing_exactDerivedAmplitude
    {r : ℕ} (hr : 1 ≤ r) (input : NormalCrossingKoszulGradeInput r) :
    HasExactHomologicalAmplitude input.homologyNonzero (r - 1) := by
  have hdegree : (r + 1) - input.grade = r - 1 := by
    rw [input.grade_eq_two]
    omega
  simpa [hdegree] using input.gradeSensitivity

/-- At two source coordinates (`r=1`) every positive Koszul homology degree vanishes. -/
theorem normalCrossing_twoCoordinates_noPositiveDerivedExcess
    (input : NormalCrossingKoszulGradeInput 1) :
    ∀ i, 0 < i → ¬ input.homologyNonzero i := by
  have h := normalCrossing_exactDerivedAmplitude (r := 1) (by omega) input
  simpa only [Nat.reduceSubDiff] using h.2

/-- From three source coordinates onward the top excess degree `N-2=r-1` is nonzero. -/
theorem normalCrossing_threeOrMore_topDerivedExcess_ne_zero
    {r : ℕ} (hr : 2 ≤ r) (input : NormalCrossingKoszulGradeInput r) :
    input.homologyNonzero (r - 1) :=
  (normalCrossing_exactDerivedAmplitude (hr.trans' (by omega)) input).1

/-- The normal-crossing derived amplitude is unbounded along the hierarchy. -/
theorem normalCrossing_derivedAmplitude_unbounded :
    ∀ bound : ℕ, ∃ r : ℕ, 1 ≤ r ∧ bound < r - 1 := by
  intro bound
  exact ⟨bound + 2, by omega, by omega⟩

/-- The canonical all-degree exterior classes, expressed in a single graded receiver.  The label
is a nonempty proper subset of the `r=N-1` star comparisons; linear independence is exactly the
truncated exterior injection supplied by the paper's boundary-coordinate argument. -/
structure NormalCrossingExteriorCoherenceWitness
    (F M : Type*) [Field F] [AddCommGroup M] [Module F M] (r : ℕ) where
  exteriorClass :
    {J : Finset (Fin r) // J.Nonempty ∧ J.card < r} → M
  independent : LinearIndependent F exteriorClass

/-- The all-degree exterior injection and the exact exponential capacity count.  The latter is
proved internally from the binomial identity already established in `SquarefreeVeroneseIdeal`. -/
theorem normalCrossing_exteriorCoherence_exactCapacity
    {F M : Type*} [Field F] [AddCommGroup M] [Module F M]
    {r : ℕ} (hr : 1 ≤ r)
    (witness : NormalCrossingExteriorCoherenceWitness F M r) :
    LinearIndependent F witness.exteriorClass ∧
      (∑ p ∈ Finset.Icc 1 (r - 1), r.choose p) = 2 ^ r - 2 :=
  ⟨witness.independent, truncatedExteriorCapacity_count r hr⟩

/-- Any linear readout that erases all source-labelled exterior classes is nonconservative as soon
as the first positive exterior layer exists.  This is the abelian-quotient no-go in a receiver-
independent form. -/
theorem normalCrossing_exteriorClasses_erased_not_injective
    {F M Q : Type*} [Field F] [AddCommGroup M] [Module F M]
    [AddCommGroup Q] [Module F Q]
    {r : ℕ} (hr : 2 ≤ r)
    (witness : NormalCrossingExteriorCoherenceWitness F M r)
    (readout : M →ₗ[F] Q)
    (herases : ∀ J, readout (witness.exteriorClass J) = 0) :
    ¬ Function.Injective readout := by
  let i : Fin r := ⟨0, by omega⟩
  let J : {J : Finset (Fin r) // J.Nonempty ∧ J.card < r} :=
    ⟨{i}, by simp [i]; omega⟩
  have hclass : witness.exteriorClass J ≠ 0 :=
    witness.independent.ne_zero J
  intro hinjective
  apply hclass
  apply hinjective
  simpa using herases J

end

end GaloisForLFunctions.HTGeometry
