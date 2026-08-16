import GaloisForLFunctions.HTGeometry.FiniteModificationZeroOne

/-!
# Convergence of a coordinatewise series is a zero–one event

A series whose `n`-th term depends only on the `n`-th coordinate of a countable product converges on
a set that is unchanged by modifying finitely many coordinates: altering the first `n₁` coordinates
shifts every partial sum past `n₁` by one and the same constant, and a constant shift does not
affect convergence.  By the finite-modification zero–one law the convergence set therefore has
measure zero or one under any product measure.

This is Kolmogorov's zero–one law in the form used for random Dirichlet series: the abscissa of
convergence of `∑ a_n X_n n^{-s}` with independent coordinates is almost surely deterministic,
because for each fixed `s` the convergence event is a tail event.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology

namespace GaloisForLFunctions.HTGeometry

variable {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
variable {E : Type*} [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]

/-- Partial sums of a series whose `n`-th term reads only the `n`-th coordinate. -/
def coordPartialSum (g : ∀ n, X n → E) (N : ℕ) (x : ∀ m, X m) : E :=
  ∑ n ∈ Finset.range N, g n (x n)

/-- The set on which such a series converges. -/
def coordSeriesConverges (g : ∀ n, X n → E) : Set (∀ m, X m) :=
  {x | ∃ L : E, Tendsto (fun N => coordPartialSum g N x) atTop (𝓝 L)}

omit [∀ n, MeasurableSpace (X n)] in
/-- Modifying finitely many coordinates shifts all late partial sums by one constant. -/
theorem coordPartialSum_sub_eq (g : ∀ n, X n → E) {x y : ∀ m, X m} {n₁ : ℕ}
    (hn₁ : ∀ m, n₁ ≤ m → x m = y m) {N : ℕ} (hN : n₁ ≤ N) :
    coordPartialSum g N x - coordPartialSum g N y
      = ∑ n ∈ Finset.range n₁, (g n (x n) - g n (y n)) := by
  have h1 : coordPartialSum g N x - coordPartialSum g N y
      = ∑ n ∈ Finset.range N, (g n (x n) - g n (y n)) := by
    rw [coordPartialSum, coordPartialSum, ← Finset.sum_sub_distrib]
  rw [h1]
  refine (Finset.sum_subset (Finset.range_subset_range.2 hN) ?_).symm
  intro n _ hn
  rw [hn₁ n (by simpa [Finset.mem_range, Nat.not_lt] using hn), sub_self]

omit [∀ n, MeasurableSpace (X n)] in
private theorem coordSeriesConverges_of_finite_diff (g : ∀ n, X n → E) {x y : ∀ m, X m}
    (h : {m | x m ≠ y m}.Finite) (hx : x ∈ coordSeriesConverges g) :
    y ∈ coordSeriesConverges g := by
  obtain ⟨L, hL⟩ := hx
  obtain ⟨n₀, hb⟩ := h.bddAbove
  have hn₁ : ∀ m, n₀ + 1 ≤ m → x m = y m := by
    intro m hm
    by_contra hne
    exact absurd (hb (Set.mem_setOf.2 hne)) (by omega)
  set D : E := ∑ n ∈ Finset.range (n₀ + 1), (g n (x n) - g n (y n)) with hD
  refine ⟨L - D, ?_⟩
  refine (hL.sub_const D).congr' ?_
  filter_upwards [eventually_ge_atTop (n₀ + 1)] with N hN
  have hkey := coordPartialSum_sub_eq g hn₁ hN
  rw [← hD] at hkey
  rw [← hkey]
  abel

omit [∀ n, MeasurableSpace (X n)] in
/-- **Convergence of a coordinatewise series is invariant under finite modification.** -/
theorem coordSeriesConverges_invariant (g : ∀ n, X n → E) {x y : ∀ m, X m}
    (h : {m | x m ≠ y m}.Finite) :
    x ∈ coordSeriesConverges g ↔ y ∈ coordSeriesConverges g := by
  have hsymm : {m | y m ≠ x m}.Finite := by
    refine h.subset fun m hm => ?_
    exact fun hxy => hm (hxy.symm)
  exact ⟨coordSeriesConverges_of_finite_diff g h,
    coordSeriesConverges_of_finite_diff g hsymm⟩

variable [MeasurableSpace E] [OpensMeasurableSpace E] [MeasurableAdd₂ E]
  [TopologicalSpace.IsCompletelyPseudoMetrizableSpace E] [SecondCountableTopology E]

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [OpensMeasurableSpace E]
  [TopologicalSpace.IsCompletelyPseudoMetrizableSpace E] [SecondCountableTopology E] in
theorem measurable_coordPartialSum (g : ∀ n, X n → E) (hg : ∀ n, Measurable (g n)) (N : ℕ) :
    Measurable (fun x : ∀ m, X m => coordPartialSum g N x) := by
  refine Finset.measurable_sum _ fun n _ => ?_
  exact (hg n).comp (measurable_pi_apply n)

theorem measurableSet_coordSeriesConverges (g : ∀ n, X n → E) (hg : ∀ n, Measurable (g n)) :
    MeasurableSet (coordSeriesConverges g) :=
  measurableSet_exists_tendsto (fun N => measurable_coordPartialSum g hg N)

/-- **Kolmogorov's zero–one law for a coordinatewise series.**  Under a countable product of
probability measures the series converges either almost nowhere or almost everywhere. -/
theorem measure_coordSeriesConverges_eq_zero_or_one
    (μ : ∀ n, Measure (X n)) [∀ n, IsProbabilityMeasure (μ n)] (a : ∀ m, X m)
    (g : ∀ n, X n → E) (hg : ∀ n, Measurable (g n)) :
    Measure.infinitePi μ (coordSeriesConverges g) = 0 ∨
      Measure.infinitePi μ (coordSeriesConverges g) = 1 :=
  measure_infinitePi_eq_zero_or_one_of_invariant μ a
    (measurableSet_coordSeriesConverges g hg)
    fun _ _ h => coordSeriesConverges_invariant g h

end GaloisForLFunctions.HTGeometry

end
