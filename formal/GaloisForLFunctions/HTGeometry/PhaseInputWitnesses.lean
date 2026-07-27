import GaloisForLFunctions.HTGeometry.CountableMultivariateAffineJetPattern
import GaloisForLFunctions.HTGeometry.MomentFiberPickSchurPhase
import GaloisForLFunctions.HTGeometry.GeometricTorsionLanguageCompletion
import GaloisForLFunctions.HTGeometry.ProjectiveConstraintTopologicalCapacityPhase
import GaloisForLFunctions.HTGeometry.InfiniteGeometricLayerTowerWitness

/-!
# Inhabitants of the remaining phase inputs

Six more bundles consumed as hypotheses and constructed nowhere.

* affine jet patterns: the empty pattern exists over every alphabet, and a one-frame one-monomial
  pattern over a nonempty one, both injectivity conditions being automatic on `Fin 0` and `Fin 1`;
* the Pick defect phase: **both** phases are realized, by defect `0` and defect `1`, so the
  singular/free dichotomy is not a statement about an empty class on either side;
* the geometric periodic level input: the zero level polynomial along the identity subsequence —
  and by `geometricPeriodic_everyLevelPolynomial_eq_zero` this is the only possible level
  polynomial, so the witness is canonical;
* the locked-face input: for the explicit hypertranscendental entire function the two
  differential-algebraicity implications are discharged vacuously;
* the two projective survival witnesses: the genus family `g i = i` on `ℕ` with the exact Hurwitz
  storage `42(2g − 2)` and the modular storage `6(2g + s − 2)` at one cusp, whose degrees are
  unbounded above.
-/

namespace GaloisForLFunctions.HTGeometry

/-! ### Affine jet patterns -/

/-- The empty affine jet pattern: no frames and no monomials. -/
def emptyMultivariateAffineJetPattern (Λ : Type*) (d : ℕ) :
    FiniteMultivariateAffineJetPattern Λ d where
  frameCount := 0
  frameCode := Fin.elim0
  orders := Fin.elim0
  monomialCount := 0
  coordinateExponent := Fin.elim0
  jetExponent := Fin.elim0
  frameCode_injective := by intro a; exact a.elim0
  decoratedExponent_injective := by intro a; exact a.elim0

/-- A one-frame, one-monomial affine jet pattern over a nonempty alphabet. -/
noncomputable def singletonMultivariateAffineJetPattern (Λ : Type*) [Nonempty Λ] (d : ℕ) :
    FiniteMultivariateAffineJetPattern Λ d where
  frameCount := 1
  frameCode := fun _ => Classical.arbitrary Λ
  orders := fun _ => 0
  monomialCount := 1
  coordinateExponent := fun _ => 0
  jetExponent := fun _ => 0
  frameCode_injective := fun a b _ => Subsingleton.elim a b
  decoratedExponent_injective := fun a b _ => Subsingleton.elim a b

/-! ### The Pick defect phases -/

/-- The singular phase, at defect zero. -/
def finitePickDefectPhaseInput_singular : FinitePickDefectPhaseInput where
  defect := 0
  singular := True
  freePhase := False
  defect_nonnegative := le_rfl
  singular_iff := by simp
  freePhase_iff := by simp

/-- The free phase, at defect one. -/
def finitePickDefectPhaseInput_free : FinitePickDefectPhaseInput where
  defect := 1
  singular := False
  freePhase := True
  defect_nonnegative := zero_le_one
  singular_iff := by simp
  freePhase_iff := by simp

/-- **Both Pick phases occur.**  The singular/free dichotomy is non-vacuous on either side. -/
theorem finitePickDefect_both_phases_occur :
    finitePickDefectPhaseInput_singular.singular ∧ finitePickDefectPhaseInput_free.freePhase :=
  ⟨trivial, trivial⟩

/-! ### The geometric periodic level input -/

/-- The zero level polynomial along the identity subsequence.  By
`geometricPeriodic_everyLevelPolynomial_eq_zero` no other level polynomial is possible, so this is
the canonical input. -/
noncomputable def geometricPeriodicLevelInput_zero (κ : Type*) :
    GeometricPeriodicLevelInput κ where
  levelPolynomial := fun _ => 0
  levelSubsequence := fun _ n => n
  levelSubsequence_strictMono := fun _ => strictMono_id
  levelPolynomial_tendsto_zero := fun _ => by simp

/-! ### The locked-face input -/

/-- A locked-face input for the explicit hypertranscendental entire function: both
differential-algebraicity implications are vacuous. -/
def geometricTLULockedFaceInput_dyadic (ι : Type*) [Fintype ι] [DecidableEq ι] :
    GeometricTLULockedFaceInput dyadicLayerEntireFunction ι where
  torsionOrder := 1
  jetDegree := 0
  degree_lt_torsionOrder := zero_lt_one
  face := ∅
  weight := fun _ => 0
  multiplicity_le := fun e he => absurd he (Finset.notMem_empty e)
  nonzeroWeight_of_differentiallyAlgebraic := fun hDA =>
    absurd hDA hypertranscendental_dyadicLayerEntireFunction
  torsionFaceVanishes_of_differentiallyAlgebraic := fun hDA =>
    absurd hDA hypertranscendental_dyadicLayerEntireFunction

/-! ### The projective survival witnesses -/

/-- The Hurwitz survival family with genus `i` and exact storage `42(2i − 2)`. -/
def hurwitzProjectiveSurvivalWitness_nat : HurwitzProjectiveSurvivalWitness ℕ where
  degree := fun i => 42 * (2 * (i : ℤ) - 2)
  genus := fun i => (i : ℤ)
  commonPullback := fun _ => True
  irreducible := fun _ => True
  exactStorage := fun _ => rfl
  survives := fun _ => ⟨trivial, trivial⟩
  degree_unbounded := by
    intro bound
    refine ⟨bound.toNat + 2, ?_⟩
    have hb : bound ≤ (bound.toNat : ℤ) := Int.self_le_toNat bound
    have h0 : (0 : ℤ) ≤ (bound.toNat : ℤ) := Int.natCast_nonneg _
    push_cast
    omega

/-- The modular survival family with genus `i`, one cusp, and exact storage `6(2i + 1 − 2)`. -/
def modularProjectiveSurvivalWitness_nat : ModularProjectiveSurvivalWitness ℕ where
  degree := fun i => 6 * (2 * (i : ℤ) + 1 - 2)
  genus := fun i => (i : ℤ)
  cuspCard := fun _ => 1
  commonPullback := fun _ => True
  irreducible := fun _ => True
  exactStorage := fun _ => rfl
  survives := fun _ => ⟨trivial, trivial⟩
  degree_unbounded := by
    intro bound
    refine ⟨bound.toNat + 2, ?_⟩
    have hb : bound ≤ (bound.toNat : ℤ) := Int.self_le_toNat bound
    have h0 : (0 : ℤ) ≤ (bound.toNat : ℤ) := Int.natCast_nonneg _
    push_cast
    omega

end GaloisForLFunctions.HTGeometry
