import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! # Length of a small-value strip with finitely many derivative crossings -/

open Set MeasureTheory
open scoped ENNReal
namespace GaloisForLFunctions.HTGeometry.SpectralJets
noncomputable section

/-- Index a point by the number of cuts to its left. -/
private def lineCell (C : Finset ℝ) (x : ℝ) : Fin (C.card+1) :=
  ⟨(C.filter (· ≤ x)).card, Nat.lt_succ_of_le (Finset.card_le_card (Finset.filter_subset _ _))⟩

private theorem no_cut_between {C : Finset ℝ} {x y : ℝ} (hx : x ∉ C) (hxy : x ≤ y)
    (he : lineCell C x = lineCell C y) {t : ℝ} (ht : t ∈ Icc x y) : t ∉ C := by
  intro hC
  have hxt : x < t := lt_of_le_of_ne ht.1 (fun e => hx (e.symm ▸ hC))
  have hsub : C.filter (· ≤ x) ⊆ C.filter (· ≤ y) := by
    intro z hz
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hz).1,(Finset.mem_filter.mp hz).2.trans hxy⟩
  have hss := Finset.ssubset_iff_of_subset hsub |>.mpr
    ⟨t,Finset.mem_filter.mpr ⟨hC,ht.2⟩,fun h => hxt.not_ge (Finset.mem_filter.mp h).2⟩
  exact (Finset.card_lt_card hss).ne (congrArg Fin.val he)

/-- A finite number of cuts divides the line into at most card(C)+1 cells.
If the cut-free portions of a set have pairwise distance at most d, the
set is covered, up to finitely many points, by as many intervals of length 2d. -/
theorem volume_le_of_cut_free_diameter (E : Set ℝ) (C : Finset ℝ) (d : ℝ) (hd : 0 ≤ d)
    (h : ∀ x ∈ E, ∀ y ∈ E, x < y → (∀ t ∈ Icc x y, t ∉ C) → y-x ≤ d) :
    volume E ≤ ((C.card+1 : ℕ) : ℝ≥0∞)*ENNReal.ofReal (2*d) := by
  classical
  let B (i : Fin (C.card+1)) : Set ℝ := {x | x ∈ E ∧ x ∉ C ∧ lineCell C x = i}
  have hcell (i : Fin (C.card+1)) : volume (B i) ≤ ENNReal.ofReal (2*d) := by
    rcases (B i).eq_empty_or_nonempty with he | ⟨x,hx⟩
    · simp [he]
    have hsub : B i ⊆ Icc (x-d) (x+d) := by
      intro y hy
      have he : lineCell C x = lineCell C y := hx.2.2.trans hy.2.2.symm
      rcases lt_trichotomy x y with hxy | hxy | hyx
      · have hh := h x hx.1 y hy.1 hxy (fun _ ht => no_cut_between hx.2.1 hxy.le he ht)
        exact ⟨by linarith,by linarith⟩
      · subst y
        exact ⟨by linarith,by linarith⟩
      · have hh := h y hy.1 x hx.1 hyx (fun _ ht => no_cut_between hy.2.1 hyx.le he.symm ht)
        exact ⟨by linarith,by linarith⟩
    exact (measure_mono hsub).trans_eq (by rw [Real.volume_Icc]; congr 1; ring)
  have hsub : E ⊆ (C : Set ℝ) ∪ ⋃ i, B i := by
    intro x hx
    by_cases hC : x ∈ C
    · exact Or.inl hC
    · exact Or.inr (Set.mem_iUnion.mpr ⟨lineCell C x,hx,hC,rfl⟩)
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
  rw [C.measure_zero volume,zero_add]
  apply (measure_iUnion_le B).trans
  rw [tsum_fintype]
  exact (Finset.sum_le_sum fun i _ => hcell i).trans_eq (by simp [nsmul_eq_mul])

/-- The portion of |f| < b on which |f'| ≥ 2a has length at most
4b/a times the number of cut-free intervals. Cuts may include singularities;
they must contain every regular level crossing |f'|=a. -/
theorem regular_strip_volume_le (f : ℝ → ℝ) (C : Finset ℝ) {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b)
    (hreg : ∀ x ∉ C, DifferentiableAt ℝ f x ∧ ContinuousAt (deriv f) x)
    (hcut : ∀ x ∉ C, |deriv f x| ≠ a) :
    volume {x | |f x| < b ∧ 2*a ≤ |deriv f x|} ≤
      ((C.card+1 : ℕ) : ℝ≥0∞)*ENNReal.ofReal (4*b/a) := by
  have hc := volume_le_of_cut_free_diameter {x | |f x| < b ∧ 2*a ≤ |deriv f x|} C (2*b/a)
    (by positivity) (by
      intro x hx y hy hxy hfree
      have hfc : ContinuousOn f (Icc x y) :=
        fun t ht => (hreg t (hfree t ht)).1.continuousAt.continuousWithinAt
      have hfd : DifferentiableOn ℝ f (Ioo x y) := fun t ht =>
        (hreg t (hfree t ⟨ht.1.le,ht.2.le⟩)).1.differentiableWithinAt
      obtain ⟨z,hz,hslope⟩ := exists_deriv_eq_slope f hxy hfc hfd
      have hder : a ≤ |deriv f z| := by
        by_contra! hsmall
        have hcont : ContinuousOn (fun t => |deriv f t|) (Icc x z) := fun t ht =>
          (hreg t (hfree t ⟨ht.1,ht.2.trans hz.2.le⟩)).2.abs.continuousWithinAt
        obtain ⟨t,ht,het⟩ := intermediate_value_Icc' hz.1.le hcont
          (show a ∈ Icc |deriv f z| |deriv f x| from ⟨hsmall.le,(by linarith only [ha,hx.2])⟩)
        exact hcut t (hfree t ⟨ht.1,ht.2.trans hz.2.le⟩) het
      rw [hslope,abs_div,abs_of_pos (sub_pos.mpr hxy)] at hder
      have hm := (le_div_iff₀ (sub_pos.mpr hxy)).mp hder
      apply (le_div_iff₀ ha).mpr
      linarith only [hm,abs_sub (f y) (f x),hx.1,hy.1])
  have he : 2*(2*b/a) = 4*b/a := by ring
  rwa [he] at hc

#print axioms regular_strip_volume_le
end
end GaloisForLFunctions.HTGeometry.SpectralJets
