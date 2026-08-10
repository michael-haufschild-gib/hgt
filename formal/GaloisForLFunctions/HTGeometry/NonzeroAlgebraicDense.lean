import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.MetricSpace.Basic

/-!
# The nonzero algebraic reals are dense

Every open interval contains a nonzero algebraic real — a nonzero rational will do.  Consequently
a set of reals containing no nonzero algebraic number has empty interior, and its complement is
dense.

This is the elementary half of a "low-complexity times are exceptional" argument: once a bound is
known at every nonzero algebraic time, the times violating it can never fill an interval.  The
stronger statement that they form a *finite* set needs o-minimality and is not proved here.
-/

namespace GaloisForLFunctions.HTGeometry

open Set

/-- Every nonempty open interval contains a nonzero algebraic real. -/
theorem exists_nonzero_algebraic_mem_Ioo {a b : ℝ} (hab : a < b) :
    ∃ t : ℝ, t ∈ Ioo a b ∧ t ≠ 0 ∧ IsAlgebraic ℚ t := by
  obtain ⟨q, haq, hqb⟩ := exists_rat_btwn hab
  by_cases hq : (q : ℝ) = 0
  · have hb : (0 : ℝ) < b := by rw [← hq]; exact hqb
    obtain ⟨r, hr0, hrb⟩ := exists_rat_btwn hb
    refine ⟨(r : ℝ), ⟨?_, hrb⟩, ne_of_gt hr0, isAlgebraic_rat ℚ r⟩
    calc a < (q : ℝ) := haq
      _ = 0 := hq
      _ < (r : ℝ) := hr0
  · exact ⟨(q : ℝ), ⟨haq, hqb⟩, hq, isAlgebraic_rat ℚ q⟩

/-- **The nonzero algebraic reals are dense.** -/
theorem dense_nonzero_algebraic : Dense {t : ℝ | t ≠ 0 ∧ IsAlgebraic ℚ t} := by
  rw [Metric.dense_iff]
  intro x r hr
  obtain ⟨t, ht, htne, htalg⟩ := exists_nonzero_algebraic_mem_Ioo
    (show x - r < x + r by linarith)
  refine ⟨t, ?_, htne, htalg⟩
  rw [Metric.mem_ball, Real.dist_eq, abs_lt]
  constructor <;> [linarith [ht.1]; linarith [ht.2]]

/-- **A set avoiding every nonzero algebraic real has empty interior.** -/
theorem interior_eq_empty_of_forall_not_algebraic {S : Set ℝ}
    (h : ∀ t ∈ S, t = 0 ∨ ¬ IsAlgebraic ℚ t) : interior S = ∅ := by
  by_contra hne
  obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hne
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior x hx
  obtain ⟨t, ht, htne, htalg⟩ := exists_nonzero_algebraic_mem_Ioo
    (show x - r < x + r by linarith)
  have htball : t ∈ Metric.ball x r := by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> [linarith [ht.1]; linarith [ht.2]]
  have htS : t ∈ S := interior_subset (hball htball)
  rcases h t htS with h0 | halg
  · exact htne h0
  · exact halg htalg

/-- **The complement is dense.**  If a bound holds at every nonzero algebraic time, the times
violating it are nowhere dense in the weak sense that their complement is dense. -/
theorem dense_compl_of_forall_not_algebraic {S : Set ℝ}
    (h : ∀ t ∈ S, t = 0 ∨ ¬ IsAlgebraic ℚ t) : Dense Sᶜ := by
  exact interior_eq_empty_iff_dense_compl.mp (interior_eq_empty_of_forall_not_algebraic h)

end GaloisForLFunctions.HTGeometry
