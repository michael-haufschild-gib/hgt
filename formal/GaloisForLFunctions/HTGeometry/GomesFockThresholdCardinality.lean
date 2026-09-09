import GaloisForLFunctions.HTGeometry.GomesFockThresholdPartition

/-! Sharp finite threshold reconstruction. The complete Boolean menu contains
2^n labels, but its realizable records are classified by one optional boundary:
no failed cut, or the largest failed cut value. This is a concrete refinement
of the observation-menu reconstruction viewpoint of Gomes, arXiv:2607.24901v1,
inside the corpus's spectral experiments. Arbitrary repeated and unordered
threshold data are allowed; no numerical enumeration is used. -/

open scoped Classical
noncomputable section
namespace GaloisForLFunctions.HTGeometry

/-- Distinct numerical cut values in the experiment. -/
def gomesFockThresholdCutSet {n : ℕ} (cuts : Fin n → ℝ) : Finset ℝ :=
  Finset.univ.image cuts

/-- Membership retains an actual source threshold index. -/
theorem gomesFockThresholdCutSet_mem {n : ℕ} (cuts : Fin n → ℝ) (r : ℝ) :
    r ∈ gomesFockThresholdCutSet cuts ↔ ∃ i, cuts i = r := by
  simp [gomesFockThresholdCutSet]

/-- Canonical record determined by the largest failed threshold, or by no failed threshold. -/
def gomesFockThresholdBoundaryRecord {n : ℕ} (cuts : Fin n → ℝ)
    (r : Option ↑(gomesFockThresholdCutSet cuts)) : Fin n → Bool :=
  match r with
  | none => fun _ => true
  | some r => fun i => if r.1 < cuts i then true else false

/-- Every optional boundary produces a realizable threshold record. -/
theorem gomesFockThresholdBoundaryRecord_realizable {n : ℕ} (cuts : Fin n → ℝ)
    (r : Option ↑(gomesFockThresholdCutSet cuts)) :
    (gomesFockThresholdCell cuts (gomesFockThresholdBoundaryRecord cuts r)).Nonempty := by
  apply (gomesFockThresholdCell_nonempty_iff cuts _).mpr
  intro i j hi hj
  cases r with
  | none => simp [gomesFockThresholdBoundaryRecord] at hj
  | some r =>
    have hi' : r.1 < cuts i := by simpa [gomesFockThresholdBoundaryRecord] using hi
    have hj' : cuts j ≤ r.1 := by simpa [gomesFockThresholdBoundaryRecord] using hj
    exact lt_of_le_of_lt hj' hi'

/-- Distinct optional boundaries produce distinct complete observation records. -/
theorem gomesFockThresholdBoundaryRecord_injective {n : ℕ} (cuts : Fin n → ℝ) :
    Function.Injective (gomesFockThresholdBoundaryRecord cuts) := by
  intro r s h
  cases r with
  | none =>
    cases s with
    | none => rfl
    | some s =>
      obtain ⟨i,hi⟩ := (gomesFockThresholdCutSet_mem cuts s.1).mp s.2
      have hh := congrFun h i
      simp [gomesFockThresholdBoundaryRecord,hi] at hh
  | some r =>
    cases s with
    | none =>
      obtain ⟨i,hi⟩ := (gomesFockThresholdCutSet_mem cuts r.1).mp r.2
      have hh := congrFun h i
      simp [gomesFockThresholdBoundaryRecord,hi] at hh
    | some s =>
      have hrs : r.1 ≤ s.1 := by
        by_contra hn
        have hsr : s.1 < r.1 := lt_of_not_ge hn
        obtain ⟨i,hi⟩ := (gomesFockThresholdCutSet_mem cuts r.1).mp r.2
        have hh := congrFun h i
        simp [gomesFockThresholdBoundaryRecord,hi,hsr] at hh
      have hsr : s.1 ≤ r.1 := by
        by_contra hn
        have hrs' : r.1 < s.1 := lt_of_not_ge hn
        obtain ⟨i,hi⟩ := (gomesFockThresholdCutSet_mem cuts s.1).mp s.2
        have hh := congrFun h i
        simp [gomesFockThresholdBoundaryRecord,hi,hrs'] at hh
      exact congrArg some (Subtype.ext (le_antisymm hrs hsr))

/-- A record is realizable exactly when it comes from one optional maximal failed cut. -/
theorem gomesFockThresholdCell_boundary_classification {n : ℕ} (cuts : Fin n → ℝ)
    (bits : Fin n → Bool) :
    (gomesFockThresholdCell cuts bits).Nonempty ↔
      ∃ r, gomesFockThresholdBoundaryRecord cuts r = bits := by
  constructor
  · intro hcell
    have hcompat := (gomesFockThresholdCell_nonempty_iff cuts bits).mp hcell
    by_cases hF : ∃ i, bits i = false
    · let F : Finset (Fin n) := Finset.univ.filter (fun i => bits i = false)
      have hne : F.Nonempty := by
        obtain ⟨i,hi⟩ := hF
        exact ⟨i,by simp [F,hi]⟩
      obtain ⟨j,hj,hmax⟩ := Finset.exists_max_image F cuts hne
      have hjF : bits j = false := (Finset.mem_filter.mp hj).2
      let r : ↑(gomesFockThresholdCutSet cuts) :=
        ⟨cuts j,(gomesFockThresholdCutSet_mem cuts (cuts j)).mpr ⟨j,rfl⟩⟩
      refine ⟨some r,?_⟩
      funext i
      cases hi : bits i with
      | false =>
        have hle : cuts i ≤ cuts j := hmax i (by simp [F,hi])
        simp [gomesFockThresholdBoundaryRecord,r,not_lt_of_ge hle]
      | true =>
        have hlt : cuts j < cuts i := hcompat i j hi hjF
        simp [gomesFockThresholdBoundaryRecord,r,hlt]
    · refine ⟨none,?_⟩
      funext i
      cases hi : bits i with
      | false => exact False.elim (hF ⟨i,hi⟩)
      | true => rfl
  · rintro ⟨r,hr⟩
    rw [← hr]
    exact gomesFockThresholdBoundaryRecord_realizable cuts r

/-- Canonical equivalence between optional distinct cut values and realizable records. -/
def gomesFockThresholdRealizableEquiv {n : ℕ} (cuts : Fin n → ℝ) :
    Option ↑(gomesFockThresholdCutSet cuts) ≃
      {bits : Fin n → Bool // (gomesFockThresholdCell cuts bits).Nonempty} :=
  Equiv.ofBijective
    (fun r => ⟨gomesFockThresholdBoundaryRecord cuts r, gomesFockThresholdBoundaryRecord_realizable cuts r⟩)
    ⟨fun _ _ h => gomesFockThresholdBoundaryRecord_injective cuts (congrArg Subtype.val h), by
      intro bits
      obtain ⟨r,hr⟩ := (gomesFockThresholdCell_boundary_classification cuts bits.1).mp bits.2
      exact ⟨r,Subtype.ext hr⟩⟩

/-- Sharp number of realizable records: one more than the number of distinct threshold values. -/
theorem gomesFockThreshold_realizable_card {n : ℕ} (cuts : Fin n → ℝ) :
    Fintype.card {bits : Fin n → Bool // (gomesFockThresholdCell cuts bits).Nonempty} =
      (gomesFockThresholdCutSet cuts).card + 1 := by
  rw [← Fintype.card_congr (gomesFockThresholdRealizableEquiv cuts)]
  simp

/-- The same exact count in the explicit finite filtering interface. -/
theorem gomesFockThreshold_realizable_filter_card {n : ℕ} (cuts : Fin n → ℝ) :
    (Finset.univ.filter (fun bits : Fin n → Bool => (gomesFockThresholdCell cuts bits).Nonempty)).card =
      (gomesFockThresholdCutSet cuts).card + 1 := by
  rw [← Fintype.card_subtype]
  exact gomesFockThreshold_realizable_card cuts

/-- An experiment with n threshold tests has at most n+1 realizable records. -/
theorem gomesFockThreshold_realizable_card_le {n : ℕ} (cuts : Fin n → ℝ) :
    Fintype.card {bits : Fin n → Bool // (gomesFockThresholdCell cuts bits).Nonempty} ≤ n+1 := by
  rw [gomesFockThreshold_realizable_card]
  have h : (gomesFockThresholdCutSet cuts).card ≤ n := by
    simpa [gomesFockThresholdCutSet] using
      (Finset.card_image_le (s := Finset.univ) (f := cuts))
  exact Nat.add_le_add_right h 1

/-- The n+1 bound is attained exactly when all input threshold values are distinct. -/
theorem gomesFockThreshold_realizable_card_max_iff {n : ℕ} (cuts : Fin n → ℝ) :
    Fintype.card {bits : Fin n → Bool // (gomesFockThresholdCell cuts bits).Nonempty} = n+1 ↔
      Function.Injective cuts := by
  rw [gomesFockThreshold_realizable_card,Nat.add_right_cancel_iff]
  simpa [gomesFockThresholdCutSet] using
    (Finset.card_image_iff (s := Finset.univ) (f := cuts))

end GaloisForLFunctions.HTGeometry
