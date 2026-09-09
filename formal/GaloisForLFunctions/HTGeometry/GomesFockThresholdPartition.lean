import GaloisForLFunctions.HTGeometry.GomesFockSpectralPOVM

/-! Canonical finite spectral experiments from arbitrary thresholds. Every Boolean
record labels the Borel cell where exactly those lower-threshold tests succeed.
The cells form a disjoint cover without ordering assumptions on the input data.
This supplies a concrete finite observation menu for the reconstruction viewpoint
of Gomes, arXiv:2607.24901v1; no measurements or ordering proofs are assumed. -/

open scoped Classical
noncomputable section
namespace GaloisForLFunctions.HTGeometry
open MeasureTheory

/-- The exact Boolean record produced by finitely many lower spectral tests. -/
def gomesFockThresholdOutcome {n : ℕ} (cuts : Fin n → ℝ) (t : ℝ) : Fin n → Bool :=
  fun i => if t ≤ cuts i then true else false

/-- A spectral cell for one complete threshold record. -/
def gomesFockThresholdCell {n : ℕ} (cuts : Fin n → ℝ) (bits : Fin n → Bool) : Set ℝ :=
  ⋂ i, if bits i then Set.Iic (cuts i) else Set.Ioi (cuts i)

/-- Every threshold cell is Borel, for arbitrary real threshold data. -/
theorem gomesFockThresholdCell_measurable {n : ℕ} (cuts : Fin n → ℝ) (bits : Fin n → Bool) :
    MeasurableSet (gomesFockThresholdCell cuts bits) := by
  apply MeasurableSet.iInter
  intro i
  cases bits i <;> simp

/-- Cell membership means exact equality with the observed Boolean record. -/
theorem gomesFockThresholdCell_mem_iff {n : ℕ} (cuts : Fin n → ℝ)
    (bits : Fin n → Bool) (t : ℝ) :
    t ∈ gomesFockThresholdCell cuts bits ↔ bits = gomesFockThresholdOutcome cuts t := by
  rw [funext_iff]
  simp only [gomesFockThresholdCell,Set.mem_iInter]
  apply forall_congr'
  intro i
  cases bits i <;> by_cases ht : t ≤ cuts i <;>
    simp_all [gomesFockThresholdOutcome]

/-- Every energy belongs to its own observed cell. -/
theorem gomesFockThresholdOutcome_mem {n : ℕ} (cuts : Fin n → ℝ) (t : ℝ) :
    t ∈ gomesFockThresholdCell cuts (gomesFockThresholdOutcome cuts t) := by
  rw [gomesFockThresholdCell_mem_iff]

/-- Distinct complete threshold records have disjoint spectral cells. -/
theorem gomesFockThresholdCell_pairwise {n : ℕ} (cuts : Fin n → ℝ) :
    Pairwise (fun a b => Disjoint (gomesFockThresholdCell cuts a) (gomesFockThresholdCell cuts b)) := by
  intro a b hab
  apply Set.disjoint_left.mpr
  intro t ha hb
  apply hab
  exact ((gomesFockThresholdCell_mem_iff cuts a t).mp ha).trans
    ((gomesFockThresholdCell_mem_iff cuts b t).mp hb).symm

/-- The finite record menu covers the entire energy axis. -/
theorem gomesFockThresholdCell_iUnion {n : ℕ} (cuts : Fin n → ℝ) :
    (⋃ bits : Fin n → Bool, gomesFockThresholdCell cuts bits) = Set.univ := by
  ext t
  simp only [Set.mem_iUnion,Set.mem_univ,iff_true]
  exact ⟨gomesFockThresholdOutcome cuts t, gomesFockThresholdOutcome_mem cuts t⟩

/-- The labelled menu has exactly two-to-the-number-of-tests records; some cells may be empty. -/
theorem gomesFockThresholdOutcome_card (n : ℕ) : Fintype.card (Fin n → Bool) = 2^n := by
  simp

/-- Exact lower and upper inequalities encoded by a threshold record. -/
theorem gomesFockThresholdCell_mem_bounds {n : ℕ} (cuts : Fin n → ℝ)
    (bits : Fin n → Bool) (t : ℝ) :
    t ∈ gomesFockThresholdCell cuts bits ↔
      (∀ i, bits i = true → t ≤ cuts i) ∧ (∀ i, bits i = false → cuts i < t) := by
  simp only [gomesFockThresholdCell,Set.mem_iInter]
  constructor
  · intro h
    constructor
    · intro i hi
      simpa [hi] using h i
    · intro i hi
      simpa [hi] using h i
  · rintro ⟨hT,hF⟩ i
    cases hi : bits i
    · simpa [hi] using hF i hi
    · simpa [hi] using hT i hi

/-- A record is realizable exactly when every failed cut lies strictly below every successful cut. -/
theorem gomesFockThresholdCell_nonempty_iff {n : ℕ} (cuts : Fin n → ℝ)
    (bits : Fin n → Bool) :
    (gomesFockThresholdCell cuts bits).Nonempty ↔
      ∀ i j, bits i = true → bits j = false → cuts j < cuts i := by
  constructor
  · rintro ⟨t,ht⟩ i j hi hj
    obtain ⟨hT,hF⟩ := (gomesFockThresholdCell_mem_bounds cuts bits t).mp ht
    exact lt_of_lt_of_le (hF j hj) (hT i hi)
  · intro h
    by_cases hT : ∃ i, bits i = true
    · let T : Finset (Fin n) := Finset.univ.filter (fun i => bits i = true)
      have hne : T.Nonempty := by
        obtain ⟨i,hi⟩ := hT
        exact ⟨i,by simp [T,hi]⟩
      obtain ⟨i,hi,hmin⟩ := Finset.exists_min_image T cuts hne
      have hiT : bits i = true := (Finset.mem_filter.mp hi).2
      refine ⟨cuts i,(gomesFockThresholdCell_mem_bounds cuts bits (cuts i)).mpr ?_⟩
      constructor
      · intro j hj
        exact hmin j (by simp [T,hj])
      · intro j hj
        exact h i j hiT hj
    · by_cases hn : (Finset.univ : Finset (Fin n)).Nonempty
      · obtain ⟨i,_,hmax⟩ := Finset.exists_max_image Finset.univ cuts hn
        refine ⟨cuts i+1,(gomesFockThresholdCell_mem_bounds cuts bits (cuts i+1)).mpr ?_⟩
        constructor
        · intro j hj
          exact False.elim (hT ⟨j,hj⟩)
        · intro j _
          have hj := hmax j (Finset.mem_univ j)
          linarith
      · refine ⟨0,(gomesFockThresholdCell_mem_bounds cuts bits 0).mpr ?_⟩
        constructor
        · intro j _
          exact False.elim (hn ⟨j,Finset.mem_univ j⟩)
        · intro j _
          exact False.elim (hn ⟨j,Finset.mem_univ j⟩)

end GaloisForLFunctions.HTGeometry
