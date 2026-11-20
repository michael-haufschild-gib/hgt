import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Real

/-! # Occupation and first hits separated by a positive time resolution -/
open Set MeasureTheory
namespace GaloisForLFunctions.HTGeometry
noncomputable section

/-- The first n waiting intervals cover all affordable time before the nth
recorded return. The n intervals immediately preceding those returns give
disjoint starts of windows containing a hit. -/
theorem resolved_visit_occupation_bounds (A : Set ℝ) (t : ℕ → ℝ) (a h W : ℝ)
    (hh : 0 < h) (hW : h ≤ W) (hzero : t 0 = a)
    (hfirst : ∀ i, IsLeast {v | t i+h ≤ v ∧ v ∈ A} (t (i+1))) (n : ℕ) :
    volume.real (A ∩ Icc a (t n)) ≤ n*h ∧
      n*h ≤ volume.real ({u | ∃ v ∈ Icc u (u+W), v ∈ A} ∩ Icc a (t n)) := by
  classical
  have hstep (i : ℕ) : t i+h ≤ t (i+1) := (hfirst i).1.1
  have hmono : Monotone t := monotone_nat_of_le_succ fun i => (le_add_of_nonneg_right hh.le).trans (hstep i)
  have hpos (i : ℕ) : a ≤ t i := hzero ▸ hmono (Nat.zero_le i)
  have cover (j : ℕ) : ∀ x ∈ A, a ≤ x → x < t j → ∃ i < j, x ∈ Icc (t i) (t i+h) := by
    induction j with
    | zero => intro x _ hx hn; rw [hzero] at hn; exact False.elim ((not_lt_of_ge hx) hn)
    | succ j ih =>
      intro x hx hx0 hxj
      by_cases hp : x < t j
      · obtain ⟨i,hi,hb⟩ := ih x hx hx0 hp
        exact ⟨i,Nat.lt_succ_of_lt hi,hb⟩
      · refine ⟨j,Nat.lt_succ_self _,le_of_not_gt hp,?_⟩
        by_contra! h
        exact (not_le_of_gt hxj) ((hfirst j).2 ⟨h.le,hx⟩)
  constructor
  · let B (i : Fin n) := Icc (t i.val) (t i.val+h)
    let P := (⋃ i : Fin n, B i) ∪ {t n}
    have hsub : A ∩ Icc a (t n) ⊆ P := by
      rintro x ⟨hx,h0,hn⟩
      rcases lt_or_eq_of_le hn with h | rfl
      · obtain ⟨i,hi,hb⟩ := cover n x hx h0 h
        exact Or.inl (mem_iUnion.mpr ⟨⟨i,hi⟩,hb⟩)
      · exact Or.inr rfl
    have hfinite : P ⊆ Icc a (t n+h) := by
      intro x hx
      rcases hx with hx | hx
      · obtain ⟨i,hi⟩ := mem_iUnion.mp hx
        exact ⟨(hpos _).trans hi.1,hi.2.trans (add_le_add (hmono i.isLt.le) le_rfl)⟩
      · have he : x = t n := hx
        rw [he]; exact ⟨hpos _,le_add_of_nonneg_right hh.le⟩
    calc
      _ ≤ volume.real P := measureReal_mono hsub (measure_ne_top_of_subset hfinite measure_Icc_lt_top.ne)
      _ ≤ volume.real (⋃ i, B i)+volume.real {t n} := measureReal_union_le _ _
      _ ≤ (∑ i, volume.real (B i))+0 := add_le_add (measureReal_iUnion_fintype_le B) (by simp [Measure.real])
      _ = _ := by simp [B,Real.volume_real_Icc_of_le (le_add_of_nonneg_right hh.le)]
  · let B (i : Fin n) := Ioc (t (i.val+1)-h) (t (i.val+1))
    have hsep (i j : Fin n) (hij : i < j) : Disjoint (B i) (B j) := by
      apply Set.disjoint_left.mpr
      intro x hx hy
      have he := hmono (show i.val+1 ≤ j.val from hij)
      have hh' := hstep j.val
      have hl : t (j.val+1)-h < x := hy.1
      linarith only [he,hh',hl,hx.2]
    have hpair : Pairwise (fun i j => Disjoint (B i) (B j)) := fun i j hij =>
      (lt_or_gt_of_ne hij).elim (hsep i j) (fun h => (hsep j i h).symm)
    have hsub : (⋃ i, B i) ⊆ {u | ∃ v ∈ Icc u (u+W), v ∈ A} ∩ Icc a (t n) := by
      intro x hx
      obtain ⟨i,hi⟩ := mem_iUnion.mp hx
      have hl : t (i.val+1)-h < x := hi.1
      have hb := hstep i.val
      refine ⟨⟨t (i.val+1),⟨hi.2,by linarith only [hl,hW]⟩,(hfirst i.val).1.2⟩,
        ⟨by linarith only [hl,hb,hpos i.val],hi.2.trans (hmono i.isLt)⟩⟩
    calc
      _ = ∑ i, volume.real (B i) := by simp [B,Real.volume_real_Ioc_of_le (sub_le_self _ hh.le)]
      _ = volume.real (⋃ i, B i) := (measureReal_iUnion_fintype hpair (fun _ => measurableSet_Ioc)
        (fun _ => measure_Ioc_lt_top.ne)).symm
      _ ≤ _ := measureReal_mono hsub (measure_ne_top_of_subset inter_subset_right measure_Icc_lt_top.ne)

#print axioms resolved_visit_occupation_bounds
end
end GaloisForLFunctions.HTGeometry
