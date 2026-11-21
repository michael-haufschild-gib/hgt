import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.ShortArcHaar
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SpectralEnclosingArc

/-!
# The full range of finite enclosing arcs

Testing a finite phase packet against a covering arc works up to a full turn.
The complementary forward arcs bound the worst covering length by one turn
minus the reciprocal of the number of phases.
-/

open MeasureTheory Set
open scoped ENNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

private def unitPhaseTurn (x : UnitAddCircle) : ℝ :=
  (AddCircle.equivIco (1 : ℝ) 0 x : ℝ)

private theorem unitPhaseTurn_mem (x : UnitAddCircle) : unitPhaseTurn x ∈ Ico (0 : ℝ) 1 := by
  simpa only [unitPhaseTurn, zero_add] using (AddCircle.equivIco (1 : ℝ) 0 x).property

private theorem coe_unitPhaseTurn (x : UnitAddCircle) : (unitPhaseTurn x : UnitAddCircle) = x :=
  AddCircle.coe_equivIco

private theorem unitPhaseTurn_coe_of_mem {a : ℝ} (ha : a ∈ Ico (0 : ℝ) 1) :
    unitPhaseTurn (a : UnitAddCircle) = a :=
  AddCircle.equivIco_coe_of_mem (by simpa only [zero_add] using ha)

private theorem unitPhaseTurn_coe (a : ℝ) : unitPhaseTurn (a : UnitAddCircle) = Int.fract a := by
  have hz : (((⌊a⌋ : ℤ) : ℝ) : UnitAddCircle) = 0 :=
    (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr ⟨⌊a⌋, by simp [zsmul_eq_mul]⟩
  have h : ((Int.fract a : ℝ) : UnitAddCircle) = (a : UnitAddCircle) := by
    rw [Int.fract, AddCircle.coe_sub, hz, sub_zero]
  rw [← h]
  exact unitPhaseTurn_coe_of_mem ⟨Int.fract_nonneg a, Int.fract_lt_one a⟩

private theorem mem_forwardUnitArc_iff_turn (x : UnitAddCircle) (r : Icc (0 : ℝ) 1) :
    x ∈ forwardUnitArc r ↔ unitPhaseTurn x ≤ (r : ℝ) := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    by_cases h : a < 1
    · simpa only [unitPhaseTurn_coe_of_mem ⟨ha.1, h⟩] using ha.2
    · exact (unitPhaseTurn_mem _).2.le.trans ((not_lt.mp h).trans ha.2)
  · intro h
    exact ⟨unitPhaseTurn x, ⟨(unitPhaseTurn_mem x).1, h⟩, coe_unitPhaseTurn x⟩

/-- Haar length of a forward arc through the full unit-turn range. -/
theorem volume_forwardUnitArc_full (r : Icc (0 : ℝ) 1) :
    volume (forwardUnitArc r) = ENNReal.ofReal (r : ℝ) := by
  by_cases hr : (r : ℝ) = 1
  · have hset : forwardUnitArc (r : ℝ) = univ := eq_univ_of_forall fun x =>
      (mem_forwardUnitArc_iff_turn x r).mpr (by rw [hr]; exact (unitPhaseTurn_mem x).2.le)
    rw [hset, UnitAddCircle.measure_univ, hr, ENNReal.ofReal_one]
  · let a := ((r : ℝ) - 1) / 2
    have hlt : (r : ℝ) < 1 := lt_of_le_of_ne r.2.2 hr
    have hsub : Icc 0 (r : ℝ) ⊆ Ioc a (a + 1) := by
      intro x hx
      dsimp only [a]
      exact ⟨by linarith only [hlt, hx.1], by linarith only [hlt, hx.2]⟩
    rw [AddCircle.add_projection_respects_measure 1 a (isClosed_forwardUnitArc r).measurableSet]
    have he : (((↑) : ℝ → UnitAddCircle) ⁻¹' forwardUnitArc (r : ℝ)) ∩ Ioc a (a + 1) = Icc 0 (r : ℝ) := by
      ext x
      constructor
      · rintro ⟨⟨y, hy, he⟩, hx⟩
        exact (AddCircle.coe_eq_coe_iff_of_mem_Ioc (hsub hy) hx).mp he ▸ hy
      · intro hx
        exact ⟨⟨x, hx, rfl⟩, hsub hx⟩
    rw [he, Real.volume_Icc, sub_zero]

/-- The largest possible minimal covering length for `D` phases, in turns. -/
def finitePhaseArcCeiling (D : ℕ) : ℝ := 1 - (D : ℝ)⁻¹

section Finite

variable {ι : Type*} [Fintype ι] [Nonempty ι]

private theorem forwardPhaseGap_eq_turn (a b : ℝ) :
    forwardPhaseGap a b =
      unitPhaseTurn (((b / (2 * Real.pi) : ℝ) : UnitAddCircle) -
        ((a / (2 * Real.pi) : ℝ) : UnitAddCircle)) * (2 * Real.pi) := by
  rw [← AddCircle.coe_sub, ← sub_div, unitPhaseTurn_coe, forwardPhaseGap]

/-- The normalized angular and torus definitions of enclosure agree
through the full turn. -/
theorem mem_enclosingUnitArc_iff_spectralEnclosingArcLength_full (θ : ι → ℝ) (r : Icc (0 : ℝ) 1) :
    (fun j => ((θ j / (2 * Real.pi) : ℝ) : UnitAddCircle)) ∈ enclosingUnitArc r ↔
      spectralEnclosingArcLength θ ≤ 2 * Real.pi * (r : ℝ) := by
  let y := fun j => ((θ j / (2 * Real.pi) : ℝ) : UnitAddCircle)
  have hgap (i j : ι) : y j - y i ∈ forwardUnitArc r ↔
      forwardPhaseGap (θ i) (θ j) ≤ 2 * Real.pi * (r : ℝ) := by
    rw [mem_forwardUnitArc_iff_turn _ r, forwardPhaseGap_eq_turn, mul_comm (2 * Real.pi)]
    exact (mul_le_mul_iff_of_pos_right two_pi_pos).symm
  change y ∈ enclosingUnitArc r ↔ _
  rw [enclosingUnitArc, mem_iUnion, spectralEnclosingArcLength_le_iff]
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨i, fun j => ?_⟩
    by_cases h : j = i
    · subst j
      rw [forwardPhaseGap, sub_self, zero_div, Int.fract_zero, zero_mul]
      exact mul_nonneg two_pi_pos.le r.2.1
    · exact (hgap i j).mp (hi j h)
  · rintro ⟨i, hi⟩
    exact ⟨i, fun j _ => (hgap i j).mpr (hi j)⟩

private theorem mem_enclosingUnitArc_of_complement_lt (x : ι → UnitAddCircle) (r : Icc (0 : ℝ) 1)
    (hr : (Fintype.card ι : ℝ) * (1 - (r : ℝ)) < 1) : x ∈ enclosingUnitArc r := by
  let s : Icc (0 : ℝ) 1 := ⟨1 - (r : ℝ), sub_nonneg.mpr r.2.2, sub_le_self 1 r.2.1⟩
  let C (j : ι) := {c : UnitAddCircle | c - x j ∈ forwardUnitArc s}
  have hvol (j : ι) : volume.real (C j) = 1 - (r : ℝ) := by
    have hC : C j = (fun c : UnitAddCircle => c + (-x j)) ⁻¹' forwardUnitArc (s : ℝ) := by
      ext c
      simp only [C, mem_setOf_eq, mem_preimage, sub_eq_add_neg]
    rw [hC, Measure.real, measure_preimage_add_right, volume_forwardUnitArc_full s,
      ENNReal.toReal_ofReal s.2.1]
  have hbound : volume.real (⋃ j, C j) ≤ (Fintype.card ι : ℝ) * (1 - (r : ℝ)) := by
    refine (measureReal_iUnion_fintype_le C).trans_eq ?_
    simp only [hvol, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  obtain ⟨c, hc⟩ : ∃ c, c ∉ ⋃ j, C j := by
    by_contra! hc
    rw [eq_univ_of_forall hc, Measure.real, UnitAddCircle.measure_univ, ENNReal.toReal_one] at hbound
    exact (not_lt_of_ge hbound) hr
  let a (j : ι) := unitPhaseTurn (x j - c)
  have ha (j : ι) : a j ≤ (r : ℝ) := by
    by_contra! h
    have hmem : 1 - a j ∈ Icc 0 (s : ℝ) :=
      ⟨sub_nonneg.mpr (unitPhaseTurn_mem _).2.le, sub_le_sub_left h.le 1⟩
    have hcoe : ((1 - a j : ℝ) : UnitAddCircle) = c - x j := by
      change ((1 - unitPhaseTurn (x j - c) : ℝ) : UnitAddCircle) = _
      rw [AddCircle.coe_sub, AddCircle.coe_period, coe_unitPhaseTurn, zero_sub, neg_sub]
    exact hc (mem_iUnion.mpr ⟨j, ⟨1 - a j, hmem, hcoe⟩⟩)
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty a
  have hmin (j : ι) : a i ≤ a j := hi ▸ Finset.inf'_le a (Finset.mem_univ j)
  refine mem_iUnion.mpr ⟨i, fun j _ => ⟨a j - a i, ?_, ?_⟩⟩
  · exact ⟨sub_nonneg.mpr (hmin j), (sub_le_self _ (unitPhaseTurn_mem _).1).trans (ha j)⟩
  · change ((unitPhaseTurn (x j - c) - unitPhaseTurn (x i - c) : ℝ) : UnitAddCircle) = x j - x i
    rw [AddCircle.coe_sub, coe_unitPhaseTurn, coe_unitPhaseTurn, sub_sub_sub_cancel_right]

/-- The shortest enclosing arc of `D` phases is at most `1 - 1/D` turns. -/
theorem spectralEnclosingArcLength_le_finitePhaseArcCeiling (θ : ι → ℝ) :
    spectralEnclosingArcLength θ ≤ 2 * Real.pi * finitePhaseArcCeiling (Fintype.card ι) := by
  let D : ℝ := Fintype.card ι
  let b := finitePhaseArcCeiling (Fintype.card ι)
  let L := spectralEnclosingArcLength θ
  let P := 2 * Real.pi
  have hP : 0 < P := two_pi_pos
  have hn : 1 ≤ Fintype.card ι := Fintype.card_pos
  have hD1 : 1 ≤ D := by dsimp only [D]; exact_mod_cast hn
  have hD : 0 < D := zero_lt_one.trans_le hD1
  have hb : 0 ≤ b := by
    exact sub_nonneg.mpr (by simpa only [one_div] using (div_le_one hD).mpr hD1)
  have hLt : L / P < 1 := (div_lt_one hP).mpr (spectralEnclosingArcLength_lt_two_pi θ)
  change L ≤ P * b
  by_contra! h
  have hbr : b < L / P := (lt_div_iff₀ hP).mpr (by simpa only [mul_comm] using h)
  let r := (b + L / P) / 2
  have hr0 : 0 ≤ r := by dsimp only [r]; linarith only [hb, hbr]
  have hr1 : r ≤ 1 := by dsimp only [r]; linarith only [hbr, hLt]
  have hm : D * (1 - r) < 1 := by
    have hh : D * (1 - b) = 1 := by
      change D * (1 - (1 - D⁻¹)) = 1
      rw [sub_sub_cancel, mul_inv_cancel₀ hD.ne']
    calc
      D * (1 - r) < D * (1 - b) :=
        mul_lt_mul_of_pos_left (by dsimp only [r]; linarith only [hbr]) hD
      _ = 1 := hh
  let s : Icc (0 : ℝ) 1 := ⟨r, hr0, hr1⟩
  have hs : L ≤ P * r := (mem_enclosingUnitArc_iff_spectralEnclosingArcLength_full θ s).mp
    (mem_enclosingUnitArc_of_complement_lt _ s hm)
  have hs' : L / P ≤ r := (div_le_iff₀ hP).mpr (by simpa only [mul_comm] using hs)
  dsimp only [r] at hs'
  linarith only [hs', hbr]

/-- At the dimension-dependent threshold every configuration is enclosed. -/
theorem enclosingUnitArc_eq_univ_of_ceiling (r : Icc (0 : ℝ) 1)
    (hr : finitePhaseArcCeiling (Fintype.card ι) ≤ (r : ℝ)) :
    enclosingUnitArc (ι := ι) r = univ := by
  refine eq_univ_of_forall fun x => ?_
  let θ (i : ι) := 2 * Real.pi * unitPhaseTurn (x i)
  have hx : (fun i => ((θ i / (2 * Real.pi) : ℝ) : UnitAddCircle)) = x := by
    funext i
    dsimp only [θ]
    rw [mul_comm (2 * Real.pi), mul_div_cancel_right₀ _ two_pi_pos.ne', coe_unitPhaseTurn]
  rw [← hx]
  exact (mem_enclosingUnitArc_iff_spectralEnclosingArcLength_full θ r).mpr
    ((spectralEnclosingArcLength_le_finitePhaseArcCeiling θ).trans (mul_le_mul_of_nonneg_left hr two_pi_pos.le))

end Finite

/-- Equally spaced points along an arc realize any covering length up to
the dimension-dependent threshold, including the extremal regular polygon. -/
theorem spectralEnclosingArcLength_equispaced (m : ℕ) {r : ℝ} (hr0 : 0 ≤ r)
    (hr : r ≤ finitePhaseArcCeiling (m + 2)) :
    spectralEnclosingArcLength (fun i : Fin (m + 2) =>
      (2 * Real.pi) * ((i.val : ℝ) * (r / ((m : ℝ) + 1)))) = 2 * Real.pi * r := by
  let P := 2 * Real.pi
  let δ := r / ((m : ℝ) + 1)
  let a (i : Fin (m + 2)) := (i.val : ℝ) * δ
  let θ (i : Fin (m + 2)) := P * a i
  have hm : 0 < (m : ℝ) + 1 := by positivity
  have hm' : 0 < (m : ℝ) + 2 := by positivity
  have hlt : r < 1 := hr.trans_lt (sub_lt_self _ (inv_pos.mpr (by positivity)))
  have hr' : r ≤ ((m : ℝ) + 1) / ((m : ℝ) + 2) := by
    refine hr.trans_eq ?_
    unfold finitePhaseArcCeiling
    push_cast
    field_simp [hm'.ne']
    ring
  have hδ0 : 0 ≤ δ := div_nonneg hr0 hm.le
  have hδr : δ ≤ 1 - r := by
    refine (div_le_iff₀ hm).mpr ?_
    have h := (le_div_iff₀ hm').mp hr'
    nlinarith only [h]
  have hmul : ((m : ℝ) + 1) * δ = r := by
    rw [mul_comm]; exact div_mul_cancel₀ _ hm.ne'
  have har (i : Fin (m + 2)) : a i ≤ r := by
    have hi : i.val ≤ m + 1 := by omega
    rw [← hmul]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hi) hδ0
  have hap (i : Fin (m + 2)) : 0 ≤ a i := mul_nonneg (Nat.cast_nonneg _) hδ0
  have hnorm (i : Fin (m + 2)) : θ i / (2 * Real.pi) = a i := by
    change P * a i / P = a i
    rw [mul_comm, mul_div_cancel_right₀ _ two_pi_pos.ne']
  have hgap (i j : Fin (m + 2)) : forwardPhaseGap (θ i) (θ j) =
      unitPhaseTurn ((a j - a i : ℝ) : UnitAddCircle) * P := by
    rw [forwardPhaseGap_eq_turn, hnorm i, hnorm j, AddCircle.coe_sub]
  have hzero : a 0 = 0 := by simp [a]
  change spectralEnclosingArcLength θ = P * r
  apply le_antisymm
  · refine (spectralEnclosingArcLength_le_iff θ (P * r)).mpr ⟨0, fun j => ?_⟩
    rw [hgap, hzero, sub_zero, unitPhaseTurn_coe_of_mem ⟨hap j, (har j).trans_lt hlt⟩, mul_comm P r]
    exact mul_le_mul_of_nonneg_right (har j) two_pi_pos.le
  · by_cases hrz : r = 0
    · rw [hrz, mul_zero]
      exact spectralEnclosingArcLength_nonneg θ
    have hδ : 0 < δ := div_pos (lt_of_le_of_ne hr0 (Ne.symm hrz)) hm
    obtain ⟨i, hi⟩ := (spectralEnclosingArcLength_le_iff θ _).mp le_rfl
    by_cases hval : i.val = 0
    · let j := Fin.last (m + 1)
      have hj : a j = r := by simpa only [a, j, Fin.val_last, Nat.cast_add, Nat.cast_one] using hmul
      have hai : a i = 0 := by simp only [a, hval, Nat.cast_zero, zero_mul]
      have he := hi j
      rw [hgap, hj, hai, sub_zero, unitPhaseTurn_coe_of_mem ⟨hr0, hlt⟩, mul_comm r P] at he
      exact he
    · let j : Fin (m + 2) := ⟨i.val - 1, (Nat.sub_le _ _).trans_lt i.isLt⟩
      have hj : a j - a i = -δ := by
        change ((i.val - 1 : ℕ) : ℝ) * δ - (i.val : ℝ) * δ = -δ
        rw [Nat.cast_sub (by omega : 1 ≤ i.val), Nat.cast_one]
        ring
      have hshift : ((-δ : ℝ) : UnitAddCircle) = ((1 - δ : ℝ) : UnitAddCircle) := by
        rw [AddCircle.coe_sub, AddCircle.coe_period, zero_sub, AddCircle.coe_neg]
      have hrδ : r ≤ 1 - δ := by linarith only [hδr]
      have hmem : 1 - δ ∈ Ico (0 : ℝ) 1 := ⟨hr0.trans hrδ, sub_lt_self _ hδ⟩
      have he := hi j
      rw [hgap, hj, hshift, unitPhaseTurn_coe_of_mem hmem] at he
      rw [mul_comm P r]
      exact (mul_le_mul_of_nonneg_right hrδ two_pi_pos.le).trans he

#print axioms volume_forwardUnitArc_full
#print axioms mem_enclosingUnitArc_iff_spectralEnclosingArcLength_full
#print axioms spectralEnclosingArcLength_le_finitePhaseArcCeiling
#print axioms enclosingUnitArc_eq_univ_of_ceiling
#print axioms spectralEnclosingArcLength_equispaced

end

end GaloisForLFunctions.HTGeometry
