import GaloisForLFunctions.HTGeometry.PoincareHopf.DegreeDomainChange

/-!
# The index is the degree on any isolating neighbourhood

If a bounded open set `U` contains the point `q` and the field has no other zero in the closure of
`U`, then the degree of the field on `U` at `0` is the index at `q`: excision replaces `U` by a
small ball around `q`.
-/

open Matrix Finset Set MeasureTheory

namespace GaloisForLFunctions.HTGeometry.PoincareHopf

variable {n : ℕ} {v : (Fin n → ℝ) → (Fin n → ℝ)} {U : Set (Fin n → ℝ)} {q : Fin n → ℝ}

theorem index_eq_degree_of_isolating (hv : ContDiff ℝ 2 v) (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) (hq : q ∈ U)
    (hzero : ∀ x ∈ closure U, x ≠ q → v x ≠ 0) :
    index v q = degree v U 0 := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU q hq
  have hεpos : 0 < r / 2 := by linarith
  have hclos : Metric.closedBall q (r / 2) ⊆ U := by
    intro x hx
    refine hball ?_
    rw [Metric.mem_closedBall] at hx
    rw [Metric.mem_ball]
    linarith
  have hiso : IsolatingRadius v q (r / 2) :=
    ⟨hεpos, fun x hx hxq => hzero x (subset_closure (hclos hx)) hxq⟩
  rw [index_eq_degree hv hiso]
  refine (degree_eq_of_subset hv hU hUb Metric.isOpen_ball
    (subset_trans Metric.ball_subset_closedBall hclos) ?_).symm
  intro x hx
  have hxq : x ≠ q := fun h => hx.2 (by rw [h]; exact Metric.mem_ball_self hεpos)
  exact hzero x hx.1 hxq

end GaloisForLFunctions.HTGeometry.PoincareHopf
