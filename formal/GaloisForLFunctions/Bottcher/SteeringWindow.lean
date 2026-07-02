/-
# Steering windows past a totally disconnected set (B1a)

The elementary core of the disconnected-lane steering theorem (docs/open-problems/02-answer.md,
Statement A).  A totally disconnected subset of `ℝ` has empty interior; hence for finitely many
injective continuous arcs the bad parameter sets `η_ν⁻¹(K)` against a closed totally disconnected
target `K ⊆ ℂ` are closed with empty interior, and a common closed subwindow avoiding `K` on
every arc can be extracted by induction.  Pure topology; no dynamics.  Axiom-clean.
-/
import Mathlib.Analysis.Complex.Basic

open Set Metric Topology

namespace Bottcher

/-- **A totally disconnected subset of `ℝ` has empty interior**: an interior point would carry a
whole open interval, a preconnected set with two distinct points, inside the set. -/
theorem interior_eq_empty_of_isTotallyDisconnected {E : Set ℝ}
    (hE : IsTotallyDisconnected E) : interior E = ∅ := by
  by_contra h
  obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr h
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hx)
  have hIoo : Ioo (x - δ) (x + δ) ⊆ E := by
    rw [← Real.ball_eq_Ioo]; exact hball
  have hsub := hE (Ioo (x - δ) (x + δ)) hIoo isPreconnected_Ioo
  have h1 : x - δ / 2 ∈ Ioo (x - δ) (x + δ) := by constructor <;> [linarith; linarith]
  have h2 : x + δ / 2 ∈ Ioo (x - δ) (x + δ) := by constructor <;> [linarith; linarith]
  have := hsub h1 h2
  linarith [this]

/-- **A closed set with empty interior misses a closed subinterval of any nondegenerate open
interval**: the window-extraction step. -/
theorem exists_Icc_subset_Ioo_disjoint_of_isClosed_interior_empty {E : Set ℝ}
    (hcl : IsClosed E) (hint : interior E = ∅) {a b : ℝ} (hab : a < b) :
    ∃ c d : ℝ, c < d ∧ Icc c d ⊆ Ioo a b ∧ ∀ t ∈ Icc c d, t ∉ E := by
  have hnot : ¬ Ioo a b ⊆ E := by
    intro hsub
    have h1 : Ioo a b ⊆ interior E := interior_maximal hsub isOpen_Ioo
    have h2 : (a + b) / 2 ∈ Ioo a b := by constructor <;> linarith
    have := h1 h2
    rw [hint] at this
    exact this
  obtain ⟨x, hxab, hxE⟩ := Set.not_subset.mp hnot
  have hopen : IsOpen (Ioo a b ∩ Eᶜ) := isOpen_Ioo.inter hcl.isOpen_compl
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hopen x ⟨hxab, hxE⟩
  refine ⟨x - δ / 2, x + δ / 2, by linarith, ?_, ?_⟩
  · intro t ht
    have : t ∈ ball x δ := by
      rw [Real.ball_eq_Ioo]
      exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    exact (hball this).1
  · intro t ht
    have : t ∈ ball x δ := by
      rw [Real.ball_eq_Ioo]
      exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    exact (hball this).2

/-- **The bad parameter set of an injective arc against a totally disconnected target is totally
disconnected**: a preconnected parameter piece maps to a preconnected subset of `K`, hence a
point, and injectivity pulls the collapse back. -/
theorem isTotallyDisconnected_arc_preimage {K : Set ℂ} (hK : IsTotallyDisconnected K)
    {η : ℝ → ℂ} {A : Set ℝ} (hc : ContinuousOn η A) (hinj : InjOn η A) :
    IsTotallyDisconnected (A ∩ η ⁻¹' K) := by
  intro t hts hp
  have himg : (η '' t).Subsingleton :=
    hK (η '' t) (by rintro _ ⟨u, hu, rfl⟩; exact (hts hu).2)
      (hp.image η (hc.mono fun u hu => (hts hu).1))
  intro u hu v hv
  exact hinj (hts hu).1 (hts hv).1 (himg ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩)

/-- The bad parameter set of a continuous arc on a closed parameter set is closed. -/
theorem isClosed_arc_preimage {K : Set ℂ} (hKcl : IsClosed K)
    {η : ℝ → ℂ} {A : Set ℝ} (hAcl : IsClosed A) (hc : ContinuousOn η A) :
    IsClosed (A ∩ η ⁻¹' K) :=
  hc.preimage_isClosed_of_isClosed hAcl hKcl

/-- **The steering window (02-A, elementary core).**  Given finitely many arcs, each continuous
and injective on the parameter window `[a, b]`, and a closed totally disconnected target
`K ⊆ ℂ`, some nondegenerate closed subwindow `[c, d] ⊆ (a, b)` steers every arc past `K`:
each bad set `Icc a b ∩ η_i⁻¹(K)` is closed with empty interior, and window extraction folds
over the finite index set. -/
theorem exists_steering_window {ι : Type*} [DecidableEq ι] (s : Finset ι) {K : Set ℂ}
    (hKcl : IsClosed K) (hKtd : IsTotallyDisconnected K)
    {a b : ℝ} (hab : a < b) (η : ι → ℝ → ℂ)
    (hc : ∀ i ∈ s, ContinuousOn (η i) (Icc a b))
    (hinj : ∀ i ∈ s, InjOn (η i) (Icc a b)) :
    ∃ c d : ℝ, c < d ∧ Icc c d ⊆ Ioo a b ∧ ∀ i ∈ s, ∀ t ∈ Icc c d, η i t ∉ K := by
  classical
  revert hc hinj
  refine Finset.induction_on s ?_ ?_
  · intro _ _
    refine ⟨a + (b - a) / 3, b - (b - a) / 3, by linarith, ?_, by simp⟩
    intro t ht
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  · rintro j s hj ih hc hinj
    obtain ⟨c, d, hcd, hsub, havoid⟩ :=
      ih (fun i hi => hc i (Finset.mem_insert_of_mem hi))
        (fun i hi => hinj i (Finset.mem_insert_of_mem hi))
    have hIccsub : Icc c d ⊆ Icc a b := hsub.trans Ioo_subset_Icc_self
    have hcj : ContinuousOn (η j) (Icc c d) :=
      (hc j (Finset.mem_insert_self j s)).mono hIccsub
    have hinjj : InjOn (η j) (Icc c d) :=
      (hinj j (Finset.mem_insert_self j s)).mono hIccsub
    have hEcl : IsClosed (Icc c d ∩ η j ⁻¹' K) :=
      isClosed_arc_preimage hKcl isClosed_Icc hcj
    have hEint : interior (Icc c d ∩ η j ⁻¹' K) = ∅ :=
      interior_eq_empty_of_isTotallyDisconnected
        (isTotallyDisconnected_arc_preimage hKtd hcj hinjj)
    obtain ⟨c', d', hcd', hsub', havoid'⟩ :=
      exists_Icc_subset_Ioo_disjoint_of_isClosed_interior_empty hEcl hEint hcd
    have hsub'' : Icc c' d' ⊆ Icc c d := hsub'.trans Ioo_subset_Icc_self
    refine ⟨c', d', hcd', hsub''.trans hsub, ?_⟩
    intro i hi t ht
    rcases Finset.mem_insert.mp hi with rfl | hi'
    · intro hK'
      exact havoid' t ht ⟨hsub'' ht, hK'⟩
    · exact havoid i hi' t (hsub'' ht)

end Bottcher
