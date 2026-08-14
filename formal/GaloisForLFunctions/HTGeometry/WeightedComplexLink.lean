import GaloisForLFunctions.HTGeometry.WeightedGraphSpectralGap

/-!
# Weighted simplicial complexes and the links of their faces

Garland's vanishing method reads a simplicial complex through the links of its faces, each of which
enters only as a weighted graph.  This file supplies that reading: a finite complex presented by its
top-dimensional faces with a weight on each, the induced weight of an arbitrary face, and the link
of a face as a weighted graph.

The link of `σ` joins two vertices *outside* `σ` with the weight of the face they span together with
`σ`; vertices of `σ` itself are isolated in it, which is what makes the weighted degree of a vertex
of the link a multiple of the weight of `σ ∪ {u}` on a pure complex.

* `WeightedComplex` : the complex, presented by weighted top faces.
* `m` : **the weight of a face** — the total weight of the top faces containing it.
* `linkGraph` : **the link of a face, as a weighted graph.**
-/

namespace GaloisForLFunctions.HTGeometry

/-- **A finite weighted simplicial complex**, presented by its top-dimensional faces with a
nonnegative weight on each. -/
structure WeightedComplex (V : Type*) [DecidableEq V] where
  /-- the top-dimensional faces -/
  top : Finset (Finset V)
  /-- the weight of a top face -/
  wt : Finset V → ℝ
  /-- weights are nonnegative -/
  wt_nonneg : ∀ s, 0 ≤ wt s

namespace WeightedComplex

variable {V : Type*} [DecidableEq V] (X : WeightedComplex V)

/-- A finset is a face when it is contained in a top face. -/
def IsFace (τ : Finset V) : Prop := ∃ s ∈ X.top, τ ⊆ s

/-- **The weight of a face**: the total weight of the top faces containing it. -/
noncomputable def m (τ : Finset V) : ℝ := ∑ s ∈ X.top.filter (fun s => τ ⊆ s), X.wt s

theorem m_nonneg (τ : Finset V) : 0 ≤ X.m τ :=
  Finset.sum_nonneg fun s _ => X.wt_nonneg s

theorem m_mono {τ τ' : Finset V} (h : τ ⊆ τ') : X.m τ' ≤ X.m τ := by
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun s _ _ => X.wt_nonneg s)
  intro s hs
  rw [Finset.mem_filter] at hs ⊢
  exact ⟨hs.1, h.trans hs.2⟩

/-- The vertices excluded from the link of `σ`: `σ` itself, and the diagonal. -/
private def linkExcluded (σ : Finset V) (u u' : V) : Prop := u = u' ∨ u ∈ σ ∨ u' ∈ σ

instance (σ : Finset V) (u u' : V) : Decidable (linkExcluded σ u u') := by
  unfold linkExcluded; infer_instance

omit [DecidableEq V] in
private theorem linkExcluded_symm {σ : Finset V} {u u' : V} (h : linkExcluded σ u u') :
    linkExcluded σ u' u := by
  rcases h with h | h | h
  exacts [Or.inl h.symm, Or.inr (Or.inr h), Or.inr (Or.inl h)]

/-- **The link of a face, as a weighted graph**: two vertices outside `σ` are joined with the weight
of the face they span together with `σ`. -/
noncomputable def linkGraph (σ : Finset V) : WeightedGraph V where
  w u u' := if linkExcluded σ u u' then 0 else X.m (insert u (insert u' σ))
  w_symm u u' := by
    by_cases h : linkExcluded σ u u'
    · rw [if_pos h, if_pos (linkExcluded_symm h)]
    · rw [if_neg h, if_neg (fun hc => h (linkExcluded_symm hc)), Finset.insert_comm]
  w_nonneg u u' := by
    by_cases h : linkExcluded σ u u'
    · rw [if_pos h]
    · rw [if_neg h]
      exact X.m_nonneg _
  w_diag _ := if_pos (Or.inl rfl)

theorem linkGraph_w_eq_zero (σ : Finset V) {u u' : V} (h : linkExcluded σ u u') :
    (X.linkGraph σ).w u u' = 0 := if_pos h

theorem linkGraph_w_of_not (σ : Finset V) {u u' : V} (h : ¬ linkExcluded σ u u') :
    (X.linkGraph σ).w u u' = X.m (insert u (insert u' σ)) := if_neg h

theorem linkGraph_w_eq (σ : Finset V) (u u' : V) :
    (X.linkGraph σ).w u u'
      = if u = u' ∨ u ∈ σ ∨ u' ∈ σ then 0 else X.m (insert u (insert u' σ)) := rfl

section Pure

theorem insert_insert_subset_iff {σ : Finset V} {u u' : V} {s : Finset V} :
    insert u (insert u' σ) ⊆ s ↔ u ∈ s ∧ u' ∈ s ∧ σ ⊆ s := by
  rw [Finset.insert_subset_iff, Finset.insert_subset_iff]

theorem m_eq_sum_ite (τ : Finset V) :
    X.m τ = ∑ s ∈ X.top, (if τ ⊆ s then X.wt s else 0) := by
  rw [m, Finset.sum_filter]

variable [Fintype V]

/-- **The weighted degree of a vertex of the link of `σ` on a pure complex.**  Every top face
containing `σ ∪ {u}` has exactly `n - |σ|` further vertices, and each of them contributes one edge
of the link at `u`. -/
theorem linkGraph_mass {n : ℕ} (hpure : ∀ s ∈ X.top, s.card = n + 1)
    {σ : Finset V} {u : V} (hu : u ∉ σ) :
    (X.linkGraph σ).mass u = ((n - σ.card : ℕ) : ℝ) * X.m (insert u σ) := by
  classical
  have hw : ∀ u' : V, (X.linkGraph σ).w u u'
      = ∑ s ∈ X.top, (if ((u' ≠ u ∧ u' ∉ σ) ∧ insert u (insert u' σ) ⊆ s) then X.wt s else 0) := by
    intro u'
    by_cases h : linkExcluded σ u u'
    · rw [X.linkGraph_w_eq_zero σ h]
      symm
      refine Finset.sum_eq_zero fun s _ => if_neg ?_
      rintro ⟨⟨h1, h2⟩, -⟩
      rcases h with h | h | h
      exacts [h1 h.symm, hu h, h2 h]
    · rw [X.linkGraph_w_of_not σ h, X.m_eq_sum_ite]
      refine Finset.sum_congr rfl fun s _ => ?_
      have hcond : u' ≠ u ∧ u' ∉ σ :=
        ⟨fun hc => h (Or.inl hc.symm), fun hc => h (Or.inr (Or.inr hc))⟩
      by_cases hs : insert u (insert u' σ) ⊆ s
      · rw [if_pos hs, if_pos ⟨hcond, hs⟩]
      · rw [if_neg hs, if_neg (fun hc => hs hc.2)]
  rw [WeightedGraph.mass, Finset.sum_congr rfl (fun u' _ => hw u'), Finset.sum_comm,
    X.m_eq_sum_ite (insert u σ), Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [← Finset.sum_filter]
  by_cases hus : insert u σ ⊆ s
  · have hus' := Finset.insert_subset_iff.1 hus
    have hfilter : (Finset.univ.filter
        (fun u' : V => (u' ≠ u ∧ u' ∉ σ) ∧ insert u (insert u' σ) ⊆ s)) = s \ insert u σ := by
      ext u'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff,
        Finset.mem_insert, insert_insert_subset_iff]
      constructor
      · rintro ⟨⟨h1, h2⟩, -, h4, -⟩
        exact ⟨h4, fun hc => hc.elim h1 h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨⟨fun hc => h2 (Or.inl hc), fun hc => h2 (Or.inr hc)⟩, hus'.1, h1, hus'.2⟩
    rw [hfilter, Finset.sum_const, if_pos hus, Finset.card_sdiff_of_subset hus,
      Finset.card_insert_of_notMem hu, hpure s hs,
      show n + 1 - (σ.card + 1) = n - σ.card from by omega, nsmul_eq_mul]
  · have hfilter : (Finset.univ.filter
        (fun u' : V => (u' ≠ u ∧ u' ∉ σ) ∧ insert u (insert u' σ) ⊆ s)) = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro u' hu'
      rw [Finset.mem_filter, insert_insert_subset_iff] at hu'
      exact hus (Finset.insert_subset_iff.2 ⟨hu'.2.2.1, hu'.2.2.2.2⟩)
    rw [hfilter, Finset.sum_empty, if_neg hus, mul_zero]

end Pure

end WeightedComplex

/-! ## The counting weight -/

variable {V : Type*} [DecidableEq V]

/-- **A complex with every top face of weight one.**  This is the weighting a building carries: the
weight of a face is then the number of chambers containing it. -/
def unitComplex (top : Finset (Finset V)) : WeightedComplex V where
  top := top
  wt := fun _ => 1
  wt_nonneg := fun _ => zero_le_one

@[simp]
theorem unitComplex_top (top : Finset (Finset V)) : (unitComplex top).top = top := rfl

/-- **The weight of a face in the counting weighting is the number of top faces containing it.** -/
theorem unitComplex_m (top : Finset (Finset V)) (τ : Finset V) :
    (unitComplex top).m τ = ((top.filter (fun s => τ ⊆ s)).card : ℝ) := by
  simp [WeightedComplex.m, unitComplex]

/-- **A face of a complex with the counting weighting has positive weight exactly when some top
face contains it.** -/
theorem unitComplex_m_pos_iff (top : Finset (Finset V)) (τ : Finset V) :
    0 < (unitComplex top).m τ ↔ ∃ s ∈ top, τ ⊆ s := by
  rw [unitComplex_m]
  constructor
  · intro h
    have hcard : 0 < (top.filter (fun s => τ ⊆ s)).card := by exact_mod_cast h
    obtain ⟨s, hs⟩ := Finset.card_pos.1 hcard
    rw [Finset.mem_filter] at hs
    exact ⟨s, hs.1, hs.2⟩
  · rintro ⟨s, hs, hts⟩
    have hmem : s ∈ top.filter (fun s => τ ⊆ s) := Finset.mem_filter.2 ⟨hs, hts⟩
    have hcard : 0 < (top.filter (fun s => τ ⊆ s)).card :=
      Finset.card_pos.2 ⟨s, hmem⟩
    exact_mod_cast hcard


end GaloisForLFunctions.HTGeometry
