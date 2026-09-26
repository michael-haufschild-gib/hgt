import GaloisForLFunctions.HTGeometry.ChebyshevMomentTrace
import GaloisForLFunctions.RHTower.GomesStieltjesAtomicFrameGeometry

open Polynomial
open scoped BigOperators

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- Chebyshev trace coordinates of the squared-weight atomic moment source. -/
def gomesChebyshevMomentTrace (S : Finset ℝ) (w : ℝ → ℝ) (n : ℕ) : ℝ :=
  _root_.HTGeometry.chebyshevMomentTrace (gomesAtomicMoment S w) n

theorem gomesChebyshevMomentTrace_eq_nodes
    (S : Finset ℝ) (w : ℝ → ℝ) (n : ℕ) :
    gomesChebyshevMomentTrace S w n =
      ∑ x ∈ S, w x ^ (2 : ℕ) * x *
        (Chebyshev.T ℝ (n : ℤ)).eval (1 - 2 * x) := by
  classical
  unfold gomesChebyshevMomentTrace gomesAtomicMoment
  exact _root_.HTGeometry.chebyshevMomentTrace_finset_atoms
    S (fun x => w x ^ (2 : ℕ)) (fun x => x) n

end

end GaloisForLFunctions.RHTower
