import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Tactic

/-! # Completion of bounded orthogonal prefixes

If each later vector has the same real inner product with an earlier vector as
the earlier vector has with itself, squared distances are differences of squared
norms. Bounded squared norms therefore give convergence in a complete Hilbert space.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter
open scoped Topology

theorem cauchySeq_of_prefix_re_inner
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (f : ℕ → E)
    (hinner : ∀ n m, n ≤ m → (inner ℂ (f n) (f m)).re = ‖f n‖ ^ 2)
    (hbound : BddAbove (Set.range fun n => ‖f n‖ ^ 2)) : CauchySeq f := by
  have hdist : ∀ n m, n ≤ m → dist (f n) (f m) ^ 2 = ‖f m‖ ^ 2 - ‖f n‖ ^ 2 := by
    intro n m hnm
    rw [dist_eq_norm, norm_sub_sq (𝕜 := ℂ)]
    change ‖f n‖ ^ 2 - 2 * (inner ℂ (f n) (f m)).re + ‖f m‖ ^ 2 = _
    rw [hinner n m hnm]
    ring
  have hmono : Monotone (fun n => ‖f n‖ ^ 2) := by
    intro n m hnm
    have := sq_nonneg (dist (f n) (f m))
    rw [hdist n m hnm] at this
    linarith
  have hc : CauchySeq (fun n => ‖f n‖ ^ 2) :=
    (tendsto_atTop_ciSup hmono hbound).cauchySeq
  apply Metric.cauchySeq_iff.2
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hc (ε ^ 2) (sq_pos_of_pos hε)
  refine ⟨N, fun n hn m hm => ?_⟩
  have hreal := hN n hn m hm
  rw [Real.dist_eq] at hreal
  rcases le_total n m with hnm | hmn
  · have hs := hdist n m hnm
    have hl := (abs_lt.mp hreal).1
    nlinarith [dist_nonneg (x := f n) (y := f m)]
  · have hs := hdist m n hmn
    have hl := (abs_lt.mp hreal).2
    rw [dist_comm (f m) (f n)] at hs
    nlinarith [dist_nonneg (x := f n) (y := f m)]

theorem exists_limit_of_prefix_re_inner
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (f : ℕ → E)
    (hinner : ∀ n m, n ≤ m → (inner ℂ (f n) (f m)).re = ‖f n‖ ^ 2)
    (hbound : BddAbove (Set.range fun n => ‖f n‖ ^ 2)) :
    ∃ g : E, Tendsto f atTop (𝓝 g) :=
  cauchySeq_tendsto_of_complete (cauchySeq_of_prefix_re_inner f hinner hbound)

end GaloisForLFunctions.HTGeometry
