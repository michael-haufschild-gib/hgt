import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.ReturnSpacing

/-! # Counting marked returns by disjoint intervals of unit length -/
open Set MeasureTheory Filter Topology
namespace GaloisForLFunctions.HTGeometry.HarmonicRuns
noncomputable section
open SharpOccupation

/-- Number of marked dates among the first n returns after the origin. -/
def markedReturns (t : ℕ → ℝ) (B : Set ℝ) (n : ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter fun i : Fin n => t (i.val+1) ∈ B).card

/-- Each marked return contributes a disjoint unit interval immediately
preceding it. The record at the initial origin is excluded. -/
theorem markedReturns_le_volume {N s : ℕ} {H : selfAdjoint (Register N)} {ε a : ℝ}
    {t : ℕ → ℝ} (ht : records H s ε a t) (B S : Set ℝ) (n : ℕ)
    (sweep : ∀ r ∈ visitSet H s ε, r ∈ B → Ioc (r-1) r ⊆ S) :
    (markedReturns t B n : ℝ) ≤ volume.real (S ∩ Icc a (t n)) := by
  classical
  let F := Finset.univ.filter fun i : Fin n => t (i.val+1) ∈ B
  let C (i : F) := Ioc (t (i.val.val+1)-1) (t (i.val.val+1))
  have step (i : ℕ) := (ht.2 i).1.1
  have mono : Monotone t := monotone_nat_of_le_succ fun i => (le_add_of_nonneg_right zero_le_one).trans (step i)
  have sep (i j : F) (h : i.val.val < j.val.val) : Disjoint (C i) (C j) := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    have h₁ := mono (show i.val.val+1 ≤ j.val.val from h)
    have h₂ := step j.val.val
    have h₃ : t (j.val.val+1)-1 < x := hy.1
    linarith only [h₁,h₂,h₃,hx.2]
  have pair : Pairwise (fun i j => Disjoint (C i) (C j)) := by
    intro i j hij
    have h : i.val.val ≠ j.val.val := fun e => hij (Subtype.ext (Fin.ext e))
    exact (lt_or_gt_of_ne h).elim (sep i j) (fun e => (sep j i e).symm)
  have sub : (⋃ i, C i) ⊆ S ∩ Icc a (t n) := by
    intro x hx
    obtain ⟨i,hi⟩ := mem_iUnion.mp hx
    have hmark := (Finset.mem_filter.mp i.property).2
    have hfirst := (ht.2 i.val.val).1
    have h₀ : a ≤ t i.val.val := ht.1 ▸ mono (Nat.zero_le _)
    have hl : t (i.val.val+1)-1 < x := hi.1
    exact ⟨sweep _ hfirst.2 hmark hi,by linarith only [hl,hfirst.1,h₀],hi.2.trans (mono i.val.isLt)⟩
  calc
    _ = ∑ i, volume.real (C i) := by
      simp [C,markedReturns,F,Real.volume_real_Ioc_of_le (sub_le_self _ zero_le_one)]
    _ = volume.real (⋃ i, C i) := (measureReal_iUnion_fintype pair (fun _ => measurableSet_Ioc)
      (fun _ => measure_Ioc_lt_top.ne)).symm
    _ ≤ _ := measureReal_mono sub (measure_ne_top_of_subset inter_subset_right measure_Icc_lt_top.ne)

#print axioms markedReturns_le_volume
end
end GaloisForLFunctions.HTGeometry.HarmonicRuns
