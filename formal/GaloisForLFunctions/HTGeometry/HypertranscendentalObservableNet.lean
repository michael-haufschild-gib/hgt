import GaloisForLFunctions.HTGeometry.HypertranscendentalClockBoundary

/-!
# The hypertranscendental observable net remembers clock resolution

For a hypertranscendental element, its finite jet-observable fields form a strict inclusion net.
More precisely, the clock-resolution order is recovered exactly from field inclusion:

`jetObservableField F x M ≤ jetObservableField F x N ↔ M ≤ N`.

Thus the clock index is encoded by which rational observables are available.  Hypertranscendence
is used as an observability structure, not as a rule propagating a state in time.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped Differential

/-- **Exact jet visibility.**  For a hypertranscendental clock, the `n`-th jet is visible at
resolution `N` exactly when `n < N`. -/
theorem differentialJet_mem_jetObservableField_iff_lt
    {F E : Type*} [Field F] [Field E] [Algebra F E] [Differential E]
    {x : E} (hx : HypertranscendentalOver F x) (n N : ℕ) :
    differentialJet n x ∈ jetObservableField F x N ↔ n < N := by
  constructor
  · intro hmem
    by_contra hnot
    have hNn : N ≤ n := Nat.le_of_not_gt hnot
    have hmemn : differentialJet n x ∈ jetObservableField F x n :=
      jetObservableField_mono x hNn hmem
    have ht := hypertranscendental_jet_transcendental_observableField hx n
    apply ht
    have halg := isAlgebraic_algebraMap
      (R := jetObservableField F x n) (A := E)
      (⟨differentialJet n x, hmemn⟩ : jetObservableField F x n)
    simpa using halg
  · intro hn
    apply IntermediateField.subset_adjoin F
    exact ⟨n, hn, rfl⟩

/-- Every increase in hypertranscendental clock resolution strictly enlarges the rational
observable field. -/
theorem hypertranscendental_jetObservableField_strictMono
    {F E : Type*} [Field F] [Field E] [Algebra F E] [Differential E]
    {x : E} (hx : HypertranscendentalOver F x) :
    StrictMono (jetObservableField F x) := by
  intro M N hMN
  refine lt_of_le_of_ne (jetObservableField_mono x (Nat.le_of_lt hMN)) ?_
  intro heq
  have hfresh : differentialJet M x ∈ jetObservableField F x N :=
    (differentialJet_mem_jetObservableField_iff_lt hx M N).mpr hMN
  have hold : differentialJet M x ∉ jetObservableField F x M :=
    fun h => (Nat.lt_irrefl M)
      ((differentialJet_mem_jetObservableField_iff_lt hx M M).mp h)
  exact hold (by rw [heq]; exact hfresh)

/-- **Observable-net reconstruction of the clock order.**  Inclusion between finite rational
observable fields is equivalent to the order of their resolution indices. -/
theorem hypertranscendental_jetObservableField_le_iff
    {F E : Type*} [Field F] [Field E] [Algebra F E] [Differential E]
    {x : E} (hx : HypertranscendentalOver F x) (M N : ℕ) :
    jetObservableField F x M ≤ jetObservableField F x N ↔ M ≤ N := by
  constructor
  · intro hfield
    by_contra hnot
    have hNM : N < M := Nat.lt_of_not_ge hnot
    have hstrict := hypertranscendental_jetObservableField_strictMono hx hNM
    exact (not_lt_of_ge hfield) hstrict
  · exact jetObservableField_mono x

/-- Two finite hypertranscendental clock resolutions expose the same rational observable field
exactly when their resolution indices agree. -/
theorem hypertranscendental_jetObservableField_eq_iff
    {F E : Type*} [Field F] [Field E] [Algebra F E] [Differential E]
    {x : E} (hx : HypertranscendentalOver F x) (M N : ℕ) :
    jetObservableField F x M = jetObservableField F x N ↔ M = N := by
  constructor
  · intro heq
    apply Nat.le_antisymm
    · exact (hypertranscendental_jetObservableField_le_iff hx M N).mp (le_of_eq heq)
    · exact (hypertranscendental_jetObservableField_le_iff hx N M).mp (le_of_eq heq.symm)
  · intro heq
    rw [heq]

end

end GaloisForLFunctions.HTGeometry
