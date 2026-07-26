import GaloisForLFunctions.HTGeometry.RankThreePeriods
import GaloisForLFunctions.HTGeometry.BoundaryWedgePeriodRankObstruction

/-!
# Rank-two period rigidity in the real-dependent case

Two `ℚ`-linearly independent complex periods that are **real**-linearly dependent generate a
rank-two integer subgroup of a real line inside `ℂ`.  Such a subgroup cannot be discrete: a discrete
integer span has equal integer and real ranks, while the real rank here is at most one.  So the
subgroup contains nonzero elements converging to zero, and meromorphic normal-form rigidity forces
the function to be constant.

This is the non-elliptic half of the classical period-rank law for hypertranscendental meromorphic
functions: of the two cases `β/α ∈ ℝ` and `β/α ∉ ℝ`, the first is settled here unconditionally, and
only the second (the genuine elliptic case, where the periods form a lattice and the function is an
elliptic function of that lattice) needs Weierstrass theory.

* `not_discrete_intSpan_fin_two_of_not_linearIndependent_real`;
* `exists_small_rankTwo_realDependent_periods`;
* `meromorphicNF_constant_of_rankTwo_realDependent_periods`;
* `no_scalarFacetRealization_of_two_omitted_realDependent` — the corresponding sharpening of the
  facet obstruction: a facet omitting only *two* vertices already kills a one-variable realization
  as soon as the two omitted translation steps are real-dependent.

The construction mirrors `RankThreePeriods`, with the real-rank bound coming from the dependence
hypothesis instead of from `dim_ℝ ℂ = 2`.
-/

namespace GaloisForLFunctions

open Filter
open scoped Topology

/-- The integer span of two `ℚ`-independent but `ℝ`-dependent complex numbers is not discrete. -/
theorem not_discrete_intSpan_fin_two_of_not_linearIndependent_real (v : Fin 2 → ℂ)
    (hv : LinearIndependent ℚ v) (hdep : ¬ LinearIndependent ℝ v) :
    ¬ DiscreteTopology (Submodule.span ℤ (Set.range v)) := by
  intro hd
  have hvz : LinearIndependent ℤ v := hv.restrict_scalars' ℤ
  have hz : Set.finrank ℤ (Set.range v) = 2 := by
    change Module.finrank ℤ (Submodule.span ℤ (Set.range v)) = 2
    rw [finrank_span_eq_card hvz]
    simp
  have heq := Real.finrank_eq_int_finrank_of_discrete (s := Set.range v) hd
  have hle : Set.finrank ℝ (Set.range v) ≤ 2 := by
    simpa using finrank_range_le_card (R := ℝ) v
  have hne : Set.finrank ℝ (Set.range v) ≠ 2 := by
    intro h
    exact hdep (linearIndependent_iff_card_eq_finrank_span.mpr (by simpa using h.symm))
  omega

/-- A real-dependent rank-two period group supplies arbitrarily small nonzero periods. -/
theorem exists_small_rankTwo_realDependent_periods (v : Fin 2 → ℂ)
    (hv : LinearIndependent ℚ v) (hdep : ¬ LinearIndependent ℝ v) :
    ∃ p : ℕ → ℂ, (∀ n, p n ∈ Submodule.span ℤ (Set.range v)) ∧
      (∀ n, p n ≠ 0) ∧ Tendsto p atTop (𝓝 0) :=
  exists_small_nonzero_of_not_discrete_intSubmodule _
    (not_discrete_intSpan_fin_two_of_not_linearIndependent_real v hv hdep)

/-- **Real-dependent rank-two period rigidity.**  A meromorphic normal-form function invariant under
the integer span of two `ℚ`-independent, `ℝ`-dependent periods is constant.  This is the
non-elliptic case of the period-rank law. -/
theorem meromorphicNF_constant_of_rankTwo_realDependent_periods
    (f : ℂ → ℂ) (hf : MeromorphicNFOn f Set.univ)
    (v : Fin 2 → ℂ) (hv : LinearIndependent ℚ v) (hdep : ¬ LinearIndependent ℝ v)
    (hperiod : ∀ p ∈ Submodule.span ℤ (Set.range v), Function.Periodic f p) :
    ∀ x y, f x = f y := by
  obtain ⟨p, hp_mem, hp_ne, hp_zero⟩ := exists_small_rankTwo_realDependent_periods v hv hdep
  exact meromorphicNF_constant_of_small_periods f hf p hp_zero hp_ne
    (fun n => hperiod (p n) (hp_mem n))

/-- A hypertranscendental meromorphic normal-form function has no two `ℚ`-independent,
`ℝ`-dependent periods. -/
theorem not_hypertranscendental_of_rankTwo_realDependent_periods
    {f : ℂ → ℂ} (hf : MeromorphicNFOn f Set.univ)
    (v : Fin 2 → ℂ) (hv : LinearIndependent ℚ v) (hdep : ¬ LinearIndependent ℝ v)
    (hperiod : ∀ p ∈ Submodule.span ℤ (Set.range v), Function.Periodic f p) :
    ¬ Hypertranscendental f :=
  not_hypertranscendental_of_const
    (meromorphicNF_constant_of_rankTwo_realDependent_periods f hf v hv hdep hperiod)

/-! ### Sharpening the facet obstruction -/

/-- The two-element tuple of distinct vertices is injective. -/
theorem injective_cons_two {α : Type*} {a b : α} (hab : a ≠ b) :
    Function.Injective ![a, b] := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all

/-- **Two omitted vertices already suffice when their steps are real-dependent.**  A facet that omits
two vertices whose translation steps are `ℝ`-dependent gives its carrier two `ℚ`-independent,
`ℝ`-dependent periods, hence a non-discrete period group, hence a constant carrier — contradicting
hypertranscendence. -/
theorem no_scalarFacetRealization_of_two_omitted_realDependent
    {α : Type*} [DecidableEq α] {V : Finset α} {facets : Set (Finset α)}
    (R : ScalarFacetRealization V facets) {F : Finset α} (hF : F ∈ facets)
    {a b : α} (ha : a ∈ V \ F) (hb : b ∈ V \ F) (hab : a ≠ b)
    (hdep : ¬ LinearIndependent ℝ (R.ω ∘ ![a, b])) : False := by
  have hindep : LinearIndependent ℚ (R.ω ∘ ![a, b]) :=
    R.indep.comp _ (injective_cons_two hab)
  have hmem : ∀ i : Fin 2, ![a, b] i ∈ V \ F := by
    intro i
    fin_cases i
    · simpa using ha
    · simpa using hb
  have hper : ∀ i, Function.Periodic (R.carrier F) ((R.ω ∘ ![a, b]) i) :=
    fun i => R.carrier_periodic F hF (![a, b] i) (hmem i)
  have hspan := periodic_of_mem_span_range (f := R.carrier F) (R.ω ∘ ![a, b]) hper
  exact not_hypertranscendental_of_rankTwo_realDependent_periods
    (R.carrier_meromorphic F hF) (R.ω ∘ ![a, b]) hindep hdep hspan
    (R.carrier_hypertranscendental F hF)

end GaloisForLFunctions
