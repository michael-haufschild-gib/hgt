import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.PhaseBoundary.FiniteCertificates.BudgetComparisons.AnalyticCoefficients

/-! # Eventual comparisons of algebraic functions on one side of a physical date -/

open Set Filter Topology
namespace GaloisForLFunctions.HTGeometry.PhaseBoundary.FiniteCertificates.ContactStability.RationalOrder
open BudgetComparisons
noncomputable section

/-- A compact interval has finitely many zero boundaries. On a sufficiently
short left interval the function is identically zero or has a fixed strict sign. -/
theorem left_sign {f : ℝ → ℝ} (hf : Continuous f) (h : IsAlgebraic coefficients f) (v : ℝ) :
    (∀ᶠ t in 𝓝[<] v, f t=0) ∨ (∀ᶠ t in 𝓝[<] v, 0<f t) ∨ (∀ᶠ t in 𝓝[<] v, f t<0) := by
  let S := {t | f t=0}
  let F := Icc (v-1) v ∩ frontier S
  have hfin : F.Finite := finite_zero_frontier hf h _ _
  have hF : (F \ {v})ᶜ∈𝓝 v := (hfin.diff (t:={v})).isClosed.isOpen_compl.mem_nhds (fun ht => ht.2 rfl)
  have hfree : ∀ᶠ t in 𝓝[<] v, t∉frontier S := by
    filter_upwards [nhdsWithin_le_nhds hF,nhdsWithin_le_nhds (lt_mem_nhds (sub_one_lt v)),
      self_mem_nhdsWithin] with t ht hlo hhi
    exact fun hb => ht ⟨⟨⟨hlo.le,hhi.le⟩,hb⟩,hhi.ne⟩
  obtain ⟨a,ha,hI⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp hfree
  have hwin : Ioo a v∈𝓝[<] v := mem_nhdsLT_iff_exists_Ioo_subset.mpr ⟨a,ha,Subset.rfl⟩
  have hS : IsClosed S := isClosed_eq hf continuous_const
  have cover : Ioo a v⊆interior S∪Sᶜ := by
    intro t ht
    by_cases hz : t∈S
    · exact Or.inl (by_contra fun hni => hI ht ⟨subset_closure hz,hni⟩)
    · exact Or.inr hz
  rcases IsPreconnected.subset_or_subset isOpen_interior hS.isOpen_compl
    (disjoint_left.mpr fun _ ht hn => hn (interior_subset ht)) cover isPreconnected_Ioo with hz|hne
  · exact Or.inl (hwin.mono fun _ ht => interior_subset (hz ht))
  right
  have hsgn : Ioo a v ⊆ {t | 0<f t} ∪ {t | f t<0} := fun t ht =>
    (lt_or_gt_of_ne (Ne.symm (hne ht : f t≠0)))
  rcases IsPreconnected.subset_or_subset (isOpen_lt continuous_const hf) (isOpen_lt hf continuous_const)
    (disjoint_left.mpr fun _ hp hn => hp.not_ge hn.le) hsgn isPreconnected_Ioo with hp|hn
  · exact Or.inl (hwin.mono fun _ ht => hp ht)
  · exact Or.inr (hwin.mono fun _ ht => hn ht)

/-- Every bounded ratio that eventually decides each real cut has a limit.
A frequently attained compact positive range suffices in place of global bounds. -/
theorem limit_of_settled_cuts {ι : Type*} {l : Filter ι} [l.NeBot] (g : ι → ℝ)
    (hcut : ∀ c : ℝ, (∀ᶠ t in l, c<g t) ∨ (∀ᶠ t in l, g t≤c))
    {a b : ℝ} (hrange : ∃ᶠ t in l, g t∈Icc a b) :
    ∃ z∈Icc a b, Tendsto g l (𝓝 z) := by
  let S := {c | ∀ᶠ t in l, c<g t}
  have lower (c : ℝ) (hc : c<a) : c∈S := by
    rcases hcut c with h|h
    · exact h
    · obtain ⟨t,ht,hg⟩ := (hrange.and_eventually h).exists
      exact False.elim (hc.not_ge (ht.1.trans hg))
  have hne : S.Nonempty := ⟨_,lower _ (sub_one_lt a)⟩
  have upper (c : ℝ) (hc : c∈S) : c≤b := by
    obtain ⟨t,ht,hg⟩ := (hrange.and_eventually hc).exists
    exact hg.le.trans ht.2
  have hb : BddAbove S := ⟨b,upper⟩
  have ha : a≤sSup S := by
    by_contra! h
    obtain ⟨c,hc,hca⟩ := exists_between h
    exact hc.not_ge (le_csSup hb (lower c hca))
  refine ⟨_,⟨ha,csSup_le hne upper⟩,tendsto_order.mpr ⟨?_,?_⟩⟩
  · intro c hc
    obtain ⟨d,hd,hcd⟩ := exists_lt_of_lt_csSup hne hc
    exact hd.mono fun _ hg => hcd.trans hg
  · intro c hc
    obtain ⟨d,hd,hdc⟩ := exists_between hc
    exact ((hcut d).resolve_left fun hs => hd.not_ge (le_csSup hb hs)).mono fun _ hg => hg.trans_lt hdc

/-- If an algebraic numerator divided by a positive algebraic denominator
frequently stays in a compact interval, its one-sided limit exists there. -/
theorem algebraic_ratio_limit {f d : ℝ → ℝ} (hf : Continuous f) (h : IsAlgebraic coefficients f)
    (hc : Continuous d) (halg : IsAlgebraic coefficients d) (v : ℝ)
    (hd : ∀ᶠ t in 𝓝[<] v, 0<d t) {a b : ℝ} (hr : ∃ᶠ t in 𝓝[<] v, f t/d t∈Icc a b) :
    ∃ z∈Icc a b, Tendsto (fun t => f t/d t) (𝓝[<] v) (𝓝 z) := by
  apply limit_of_settled_cuts _ _ hr
  intro c
  let C : coefficients := ⟨fun _ => c,analyticOnNhd_const⟩
  have hh : IsAlgebraic coefficients (fun t => c*d t) :=
    (show IsAlgebraic coefficients (fun _ : ℝ => c) from isAlgebraic_algebraMap C).mul halg
  rcases left_sign (hf.sub (continuous_const.mul hc)) (h.sub hh) v with hz|hp|hn
  · exact Or.inr ((hz.and hd).mono fun t ht => (div_le_iff₀ ht.2).mpr (sub_eq_zero.mp ht.1).le)
  · exact Or.inl ((hp.and hd).mono fun t ht => (lt_div_iff₀ ht.2).mpr (sub_pos.mp ht.1))
  · exact Or.inr ((hn.and hd).mono fun t ht => (div_le_iff₀ ht.2).mpr (sub_neg.mp ht.1).le)

#print axioms algebraic_ratio_limit
end
end GaloisForLFunctions.HTGeometry.PhaseBoundary.FiniteCertificates.ContactStability.RationalOrder
