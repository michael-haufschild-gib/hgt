/-
# Endpoint completeness meets genericity over any parameter space

Endpoint visibility of the canonical eigenvectors is an open condition wherever the eigenvalue
branches are analytic, so on any parameter space it meets every dense set.  Combined with the
eigenbranch engine at a unitarily diagonalisable simple point, this is the induction step of
Lemma A1 in the coordinates of an arbitrary architecture, not only of the one-qubit extension
chart.

Main results:
* `endpointEigenvector` — the canonical eigenvector of a branch.
* `exists_mem_dense_endpointComplete_of_analyticBranches` — **the intersection**.
-/
import GaloisForLFunctions.HTGeometry.GeneralParametricEigenbranch
import GaloisForLFunctions.HTGeometry.EndpointCompleteGenericIntersection

open Filter Topology Matrix
open scoped Matrix.Norms.Elementwise

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {P A : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P] [Fintype A] [DecidableEq A]

/-- The canonical eigenvector attached to an eigenvalue branch. -/
def endpointEigenvector (H : P → Matrix (A × Bool) (A × Bool) ℂ)
    (branch : (A × Bool) → P → ℂ) (x : A × Bool) (p : P) : A × Bool → ℂ :=
  fun y => (Matrix.scalar (A × Bool) (branch x p) - H p).adjugate y x

/-- **The induction step over an arbitrary parameter space.**  If the eigenvalue branches are
analytic at a base point where every ordered pair is endpoint visible, then every dense set of
parameters contains one at which every ordered pair is still endpoint visible. -/
theorem exists_mem_dense_endpointComplete_of_analyticBranches
    {H : P → Matrix (A × Bool) (A × Bool) ℂ} {p₀ : P}
    (hH : AnalyticAt ℂ H p₀)
    {branch : (A × Bool) → P → ℂ} (hbranch : ∀ x, AnalyticAt ℂ (branch x) p₀)
    (hcomplete : ∀ q : (A × Bool) × (A × Bool), q.1 ≠ q.2 →
      layerReducedTransition (endpointEigenvector H branch q.1 p₀)
        (endpointEigenvector H branch q.2 p₀) ≠ 0)
    {Good : Set P} (hdense : Dense Good) :
    ∃ p ∈ Good, ∀ q : (A × Bool) × (A × Bool), q.1 ≠ q.2 →
      layerReducedTransition (endpointEigenvector H branch q.1 p)
        (endpointEigenvector H branch q.2 p) ≠ 0 := by
  refine exists_mem_dense_forall_layerReducedTransition_ne_zero
    (fun i p => endpointEigenvector H branch i p) ?_ hcomplete hdense
  intro i y
  exact (analyticAt_generalAdjugateColumn hH (hbranch i) i y).continuousAt

end

end GaloisForLFunctions.HTGeometry
