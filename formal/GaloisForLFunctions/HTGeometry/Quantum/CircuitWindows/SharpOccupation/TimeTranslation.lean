import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.BudgetOccupation

/-! # Finite-interval occupation from relatively dense approximate periods -/
open Filter Set MeasureTheory Topology
namespace GaloisForLFunctions.HTGeometry.SharpOccupation
noncomputable section

/-- Copies of the original time set in consecutive disjoint blocks transfer
a density of the enlarged set to every finite observation interval. -/
theorem occupation_from_periods (E F : Set ℝ) (hE : MeasurableSet E) {G p : ℝ}
    (hG : 0 < G) (hperiod : ∀ u : ℝ, ∃ τ ∈ Icc u (u+G), ∀ t ∈ E, t+τ ∈ F)
    (hocc : ∀ᶠ R : ℝ in atTop, volume.real (F ∩ Icc 0 R) ≤ p*R) (a T : ℝ) (hT : 0 ≤ T) :
    volume.real (E ∩ Icc a (a+T)) ≤ p*(T+G) := by
  classical
  let L := T+G
  have hL : 0 < L := add_pos_of_nonneg_of_pos hT hG
  obtain ⟨b,hb⟩ := eventually_atTop.mp hocc
  obtain ⟨m,hm⟩ := exists_nat_gt (max 0 (b/L))
  have hmpos : 0 < (m:ℝ) := (le_max_left ..).trans_lt hm
  have hbound := hb ((m:ℝ)*L) ((div_lt_iff₀ hL).mp ((le_max_right ..).trans_lt hm)).le
  let K := E ∩ Ioc a (a+T)
  choose τ hτ hrep using hperiod
  let d (i : Fin m) := τ ((i.val:ℝ)*L-a)
  let B (i : Fin m) := (fun u : ℝ => u+(-d i)) ⁻¹' K
  have hK : MeasurableSet K := hE.inter measurableSet_Ioc
  have hmeas (i : Fin m) : MeasurableSet (B i) := hK.preimage (measurable_id.add_const _)
  have hval (i : Fin m) : volume (B i) = volume K :=
    (measurePreserving_add_right volume (-d i)).measure_preimage hK.nullMeasurableSet
  have hblock (i : Fin m) {u} (hu : u ∈ B i) : u ∈ Ioc ((i.val:ℝ)*L) (((i.val:ℝ)+1)*L) := by
    have h := hτ ((i.val:ℝ)*L-a)
    have hk : u+(-d i) ∈ Ioc a (a+T) := hu.2
    change (i.val:ℝ)*L-a ≤ d i ∧ d i ≤ (i.val:ℝ)*L-a+G at h
    constructor
    · linarith only [h.1,hk.1]
    · rw [add_mul,one_mul]
      change _ ≤ _+(T+G)
      linarith only [h.2,hk.2]
  have hdis (i j : Fin m) (h : i < j) : Disjoint (B i) (B j) := by
    apply Set.disjoint_left.mpr
    intro u hi hj
    have hij : (i.val:ℝ)+1 ≤ j.val := by exact_mod_cast (show i.val+1 ≤ j.val from h)
    exact (not_lt_of_ge ((hblock i hi).2.trans (mul_le_mul_of_nonneg_right hij hL.le))) (hblock j hj).1
  have hp : Pairwise (fun i j => Disjoint (B i) (B j)) := fun i j hij =>
    (lt_or_gt_of_ne hij).elim (hdis i j) (fun h => (hdis j i h).symm)
  have hsub : (⋃ i : Fin m, B i) ⊆ F ∩ Icc 0 ((m:ℝ)*L) := by
    intro u hu
    obtain ⟨i,hi⟩ := mem_iUnion.mp hu
    have he := hrep ((i.val:ℝ)*L-a) (u+(-d i)) hi.1
    change u+(-d i)+d i ∈ F at he
    have hij : (i.val:ℝ)+1 ≤ m := by exact_mod_cast i.isLt
    exact ⟨by simpa only [add_assoc,neg_add_cancel,add_zero] using he,
      (mul_nonneg (Nat.cast_nonneg _) hL.le).trans (hblock i hi).1.le,
      (hblock i hi).2.trans (mul_le_mul_of_nonneg_right hij hL.le)⟩
  have hKfin : volume K ≠ ⊤ := measure_ne_top_of_subset inter_subset_right measure_Ioc_lt_top.ne
  have hall : (m:ℝ)*volume.real K ≤ p*((m:ℝ)*L) := calc
    _ = ∑ i : Fin m, volume.real (B i) := by simp [Measure.real,hval]
    _ = volume.real (⋃ i : Fin m, B i) := (measureReal_iUnion_fintype hp hmeas
      (fun i => (hval i).symm ▸ hKfin)).symm
    _ ≤ volume.real (F ∩ Icc 0 ((m:ℝ)*L)) := measureReal_mono hsub
      (measure_ne_top_of_subset inter_subset_right measure_Icc_lt_top.ne)
    _ ≤ _ := hbound
  rw [mul_left_comm p] at hall
  have heq : volume.real K = volume.real (E ∩ Icc a (a+T)) :=
    measureReal_congr (ae_eq_set_inter (Filter.EventuallyEq.rfl) Ioc_ae_eq_Icc)
  exact heq ▸ (le_of_mul_le_mul_left hall hmpos)

#print axioms occupation_from_periods
end
end GaloisForLFunctions.HTGeometry.SharpOccupation
