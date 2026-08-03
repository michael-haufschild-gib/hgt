import GaloisForLFunctions.HTGeometry.MassShiftGlobalAvoidance
import GaloisForLFunctions.HTGeometry.PerturbedOuterFamilyJets

/-!
# Reading the avoidance statement in the coordinates of a relation

The transversality argument runs in the sigma-indexed jet coordinates; a differential relation is
written in the folded coordinates of the evaluation matrix.  The fold is the same map in both
places, so avoiding the transported rank defect is exactly full column rank of the relation's
evaluation matrix at the family's jets.
-/

open Filter Topology MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem sigmaJetCLE_apply (row : Type) [Fintype row] (r d D : ℕ) (h : r * (d + 1) = D)
    (y : (Σ _ : row × Fin r, Fin (d + 1)) → ℂ) (p : row × Fin D) :
    sigmaJetCLE row r d D h y p = y ((sigmaJetIndexEquiv r d D h).symm p) := rfl

/-- **The fold of the observation is the family observation plus the folded carrier.** -/
theorem fold_massShiftObservation {row : Type} [Fintype row] (z : row → ℂ) {r : ℕ} (d D : ℕ)
    (h : r * (d + 1) = D) (x ε : ℕ → ℝ)
    (carrier : (Fin r → ℝ) → ((Σ _ : row × Fin r, Fin (d + 1)) → ℂ))
    (u : MassParameter) (t : Fin r → ℝ) :
    sigmaJetCLE row r d D h (massShiftObservation z d x ε carrier (u, t))
      = familyOuterObservation r d D h z t x ε u
        + fun p => carrier t ((sigmaJetIndexEquiv r d D h).symm p) := by
  funext p
  rfl

/-- **Avoiding the transported rank defect is full column rank of the relation matrix.** -/
theorem mulVec_injective_of_notMem_outerShiftBad {row : Type} [Fintype row] {κ : Type}
    [Fintype κ] [DecidableEq κ] (z : row → ℂ) {r : ℕ} (d D q : ℕ) (h : r * (d + 1) = D)
    (exponent : κ → (Fin D →₀ ℕ)) (x ε : ℕ → ℝ)
    (carrier : (Fin r → ℝ) → ((Σ _ : row × Fin r, Fin (d + 1)) → ℂ))
    (u : MassParameter) (t : Fin r → ℝ)
    (havoid : massShiftObservation z d x ε carrier (u, t)
      ∉ outerShiftBad row r d D q h z exponent) :
    Function.Injective (expandedDifferentialEvaluationMatrix q D z exponent
      (familyOuterObservation r d D h z t x ε u
        + fun p => carrier t ((sigmaJetIndexEquiv r d D h).symm p))).mulVec := by
  rw [← fold_massShiftObservation z d D h x ε carrier u t]
  by_contra hcontra
  exact havoid ((mem_expandedDifferentialEvaluationRankDefect_iff q D z exponent _).mpr hcontra)

/-- **A relation dies against any rigid observation of its jets, on any row packet.**  The row type
is arbitrary, so more evaluation points than columns are allowed -- which is what the codimension
count in a parametric transversality argument requires. -/
theorem eq_zero_of_relation_of_rigid_jets_row {m' n : ℕ} {g : Fin (m' + 1) → ℂ → ℂ} {U : Set ℂ}
    {row : Type} [Fintype row] [DecidableEq row]
    (P : MvPolynomial (FamilyJetIndex (m' + 1) n) ℂ)
    (hrel : ∀ z ∈ U, MvPolynomial.eval (familyJetVec (n := n) g z) P = 0)
    (znodes : row → ℂ) (hznodes : ∀ b, znodes b ∈ U)
    (jets : row × Fin ((relationShapeOf P).depthPred + 1) → ℂ)
    (hjets : ∀ p, jets p = iteratedDeriv
      ((((familyJetVariablesEquiv m' n).symm p.2).2 : Fin (n + 1)) : ℕ)
      (g (((familyJetVariablesEquiv m' n).symm p.2).1)) (znodes p.1))
    (hrigid : ∀ c, (expandedDifferentialEvaluationMatrix (relationShapeOf P).spectralDegree
      ((relationShapeOf P).depthPred + 1) znodes (relationShapeOf P).exponent jets).mulVec c = 0 →
      c = 0) :
    P = 0 := by
  refine eq_zero_of_rigid_of_relation znodes hznodes P hrel fun c hc => ?_
  refine hrigid c ?_
  rw [funext hjets]
  exact hc

end

end GaloisForLFunctions.HTGeometry
