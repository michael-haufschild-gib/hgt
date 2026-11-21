import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.AnchorGapCompression
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.AnchorSetOccupation

/-!
# Exact overlap masses for covering anchors

The marked anchor phases lift to a box with mandatory pairwise gaps.
After removing those gaps each marked coordinate contributes the same
allowed length as each unmarked coordinate.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal Matrix.Norms.L2Operator

namespace GaloisForLFunctions.HTGeometry

noncomputable section

local instance exactAnchorCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  ⟨UnitAddCircle.measure_univ⟩

private theorem volume_unitCircleCoordinates_chart {J : Type*} [Fintype J]
    (A : Set (J → UnitAddCircle)) (hA : MeasurableSet A) :
    volume A = volume ((fun x : J → ℝ => fun j => (x j : UnitAddCircle)) ⁻¹' A ∩
      (univ : Set J).pi (fun _ => Ioc (0 : ℝ) 1)) := by
  have hsingle : MeasurePreserving (((↑) : ℝ → UnitAddCircle)) (volume.restrict (Ioc (0 : ℝ) 1)) volume := by
    simpa only [zero_add] using AddCircle.measurePreserving_mk (1 : ℝ) 0
  have h := measurePreserving_pi (fun _ : J => volume.restrict (Ioc (0 : ℝ) 1))
    (fun _ : J => (volume : Measure UnitAddCircle)) (fun _ => hsingle)
  have he := h.measure_preimage hA.nullMeasurableSet
  rw [← Measure.restrict_pi_pi, Measure.restrict_apply (h.measurable hA)] at he
  exact he.symm

private theorem coe_mem_unitArcAnchorSeparation_iff {a : ℝ} (r : Ico (1 / 2 : ℝ) 1)
    (ha : a ∈ Icc (0 : ℝ) 1) :
    (a : UnitAddCircle) ∈ unitArcAnchorSeparation r ↔ a ∈ Icc (1 - (r : ℝ)) (r : ℝ) := by
  constructor
  · intro h
    have ha1 : a ≠ 1 := fun he => h.2.2 (by rw [he, AddCircle.coe_period])
    rw [unitArcAnchorSeparation_eq_image r] at h
    obtain ⟨b, hb, hba⟩ := h
    have ha' : a ∈ Ico (0 : ℝ) (0 + 1) := ⟨ha.1, by simpa only [zero_add] using lt_of_le_of_ne ha.2 ha1⟩
    have hb' : b ∈ Ico (0 : ℝ) (0 + 1) := ⟨(sub_nonneg.mpr r.2.2.le).trans hb.1,
      by simpa only [zero_add] using hb.2.trans_lt r.2.2⟩
    exact ((AddCircle.coe_eq_coe_iff_of_mem_Ico (p := (1 : ℝ)) hb' ha').mp hba) ▸ hb
  · intro h
    rw [unitArcAnchorSeparation_eq_image r]
    exact ⟨a, h, rfl⟩

private theorem neg_mem_unitArcAnchorSeparation_iff {r : ℝ} {z : UnitAddCircle} :
    -z ∈ unitArcAnchorSeparation r ↔ z ∈ unitArcAnchorSeparation r := by
  simp only [unitArcAnchorSeparation, mem_setOf_eq, neg_neg, neg_ne_zero, and_left_comm]

private theorem sub_mem_unitArcAnchorSeparation_iff {a b : ℝ} (r : Ico (1 / 2 : ℝ) 1)
    (ha : a ∈ Icc (1 - (r : ℝ)) (r : ℝ)) (hb : b ∈ Icc (1 - (r : ℝ)) (r : ℝ)) :
    (b : UnitAddCircle) - (a : UnitAddCircle) ∈ unitArcAnchorSeparation r ↔ 1 - (r : ℝ) ≤ |b - a| := by
  have hordered {x y : ℝ} (hx : x ∈ Icc (1 - (r : ℝ)) (r : ℝ))
      (hy : y ∈ Icc (1 - (r : ℝ)) (r : ℝ)) (hxy : x ≤ y) :
      (y : UnitAddCircle) - (x : UnitAddCircle) ∈ unitArcAnchorSeparation r ↔ 1 - (r : ℝ) ≤ y - x := by
    have hhi : y - x ≤ (r : ℝ) := (sub_le_self _ ((sub_nonneg.mpr r.2.2.le).trans hx.1)).trans hy.2
    have hchart : y - x ∈ Icc (0 : ℝ) 1 := ⟨sub_nonneg.mpr hxy, hhi.trans r.2.2.le⟩
    rw [← AddCircle.coe_sub, coe_mem_unitArcAnchorSeparation_iff r hchart]
    exact ⟨fun h => h.1, fun h => ⟨h, hhi⟩⟩
  rcases le_total a b with hab | hba
  · rw [abs_of_nonneg (sub_nonneg.mpr hab)]
    exact hordered ha hb hab
  · rw [← neg_sub (a : UnitAddCircle) (b : UnitAddCircle), neg_mem_unitArcAnchorSeparation_iff,
      abs_of_nonpos (sub_nonpos.mpr hba), neg_sub]
    exact hordered hb ha hba

section Marked

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
private theorem chart_admissibleMarkedAnchorPhases (s : Finset ι) {b : ι} (hb : b ∈ s)
    (r : Ico (1 / 2 : ℝ) 1) :
    (fun x : markedAnchorIndex s b → ℝ => fun j => (x j : UnitAddCircle)) ⁻¹'
        admissibleMarkedAnchorPhases s b r ∩ (univ : Set (markedAnchorIndex s b)).pi (fun _ => Ioc (0 : ℝ) 1) =
      separatedCoordinateBox (markedAnchorIndex s b) (1 - (r : ℝ)) r := by
  ext x
  let J := markedAnchorIndex s b
  let z := markedAnchorPhasePacket s b (fun j : J => (x j : UnitAddCircle))
  have hd : 0 < 1 - (r : ℝ) := sub_pos.mpr r.2.2
  have hz0 : z b = 0 := by
    have h : ¬ (b ≠ b ∧ b ∈ s) := fun h => h.1 rfl
    simp only [z, markedAnchorPhasePacket, dif_neg h]
  have hz (j : J) : z j.val.val = (x j : UnitAddCircle) := by
    have h : j.val.val ≠ b ∧ j.val.val ∈ s := ⟨j.val.property, j.property⟩
    simp only [z, markedAnchorPhasePacket, dif_pos h]
    exact congrArg (fun j : J => (x j : UnitAddCircle)) (Subtype.ext (Subtype.ext rfl))
  change ((s : Set ι).Pairwise (fun i j => z j - z i ∈ unitArcAnchorSeparation r) ∧
      x ∈ (univ : Set J).pi (fun _ => Ioc (0 : ℝ) 1)) ↔ _
  constructor
  · rintro ⟨hsep, hchart⟩
    have hbox (j : J) : x j ∈ Icc (1 - (r : ℝ)) (r : ℝ) := by
      have hx : x j ∈ Ioc (0 : ℝ) 1 := Set.mem_pi.mp hchart j (mem_univ j)
      have h : z j.val.val - z b ∈ unitArcAnchorSeparation r := hsep hb j.property j.val.property.symm
      rw [hz j, hz0, sub_zero] at h
      exact (coe_mem_unitArcAnchorSeparation_iff r ⟨hx.1.le, hx.2⟩).mp h
    refine ⟨hbox, ?_⟩
    intro i j hij
    have hne : i.val.val ≠ j.val.val := fun h => hij (Subtype.ext (Subtype.ext h))
    have h : z j.val.val - z i.val.val ∈ unitArcAnchorSeparation r := hsep i.property j.property hne
    rw [hz i, hz j] at h
    exact (sub_mem_unitArcAnchorSeparation_iff r (hbox i) (hbox j)).mp h
  · rintro ⟨hbox, hsep⟩
    have hchart (j : J) : x j ∈ Ioc (0 : ℝ) 1 := ⟨hd.trans_le (hbox j).1, (hbox j).2.trans r.2.2.le⟩
    have hfromBase (j : J) : z j.val.val ∈ unitArcAnchorSeparation r := by
      rw [hz j]
      exact (coe_mem_unitArcAnchorSeparation_iff r ⟨(hchart j).1.le, (hchart j).2⟩).mpr (hbox j)
    refine ⟨?_, Set.mem_pi.mpr fun j _ => hchart j⟩
    intro i hi j hj hij
    by_cases hib : i = b
    · subst i
      let l : J := ⟨⟨j, hij.symm⟩, hj⟩
      rw [hz0, sub_zero]
      exact hfromBase l
    · by_cases hjb : j = b
      · subst j
        let l : J := ⟨⟨i, hib⟩, hi⟩
        rw [hz0, zero_sub, neg_mem_unitArcAnchorSeparation_iff]
        exact hfromBase l
      · let a : J := ⟨⟨i, hib⟩, hi⟩
        let c : J := ⟨⟨j, hjb⟩, hj⟩
        have hne : a ≠ c := fun e => hij (congrArg (fun j : J => j.val.val) e)
        change z c.val.val - z a.val.val ∈ unitArcAnchorSeparation r
        rw [hz a, hz c]
        exact (sub_mem_unitArcAnchorSeparation_iff r (hbox a) (hbox c)).mpr (hsep hne)

private theorem card_markedAnchorIndex (s : Finset ι) {b : ι} (hb : b ∈ s) :
    Fintype.card (markedAnchorIndex s b) = s.card - 1 := by
  let e : markedAnchorIndex s b ≃ ↥(s.erase b) :=
    { toFun := fun j => ⟨j.val.val, Finset.mem_erase.mpr ⟨j.val.property, j.property⟩⟩
      invFun := fun j => ⟨⟨j.val, (Finset.mem_erase.mp j.property).1⟩, (Finset.mem_erase.mp j.property).2⟩
      left_inv := fun _ => Subtype.ext (Subtype.ext rfl)
      right_inv := fun _ => Subtype.ext rfl }
  rw [Fintype.card_congr e, Fintype.card_coe, Finset.card_erase_of_mem hb]

/-- The separated marked phases have the volume of the gap-compressed box. -/
theorem volume_admissibleMarkedAnchorPhases (s : Finset ι) {b : ι} (hb : b ∈ s)
    (r : Ico (1 / 2 : ℝ) 1) :
    volume (admissibleMarkedAnchorPhases s b r) =
      ENNReal.ofReal (1 - (s.card : ℝ) * (1 - (r : ℝ))) ^ (s.card - 1) := by
  have hc : 1 ≤ s.card := Finset.card_pos.mpr ⟨b, hb⟩
  have hw : (r : ℝ) - ((s.card - 1 : ℕ) : ℝ) * (1 - (r : ℝ)) = 1 - (s.card : ℝ) * (1 - (r : ℝ)) := by
    rw [Nat.cast_sub hc, Nat.cast_one]
    ring
  rw [volume_unitCircleCoordinates_chart _ (isClosed_admissibleMarkedAnchorPhases s b r).measurableSet,
    chart_admissibleMarkedAnchorPhases s hb r, volume_separatedCoordinateBox (sub_pos.mpr r.2.2),
    card_markedAnchorIndex s hb, hw]

private theorem volume_biInter_relativeAnchoredUnitArc_upperRange (ref : ι) (s : Finset ι) (hs : s.Nonempty)
    (r : Ico (1 / 2 : ℝ) 1) : volume (⋂ i ∈ s, relativeAnchoredUnitArc ref i r) =
      ENNReal.ofReal (1 - (s.card : ℝ) * (1 - (r : ℝ))) ^ (Fintype.card ι - 1) := by
  obtain ⟨b, hb⟩ := hs
  rw [volume_biInter_relativeAnchoredUnitArc_factor_of_reference ref s hb r,
    volume_admissibleMarkedAnchorPhases s hb r, ← pow_add]
  have hD := Finset.card_le_univ s
  have hc := Finset.card_pos.mpr (show s.Nonempty from ⟨b, hb⟩)
  congr 1
  omega

/-- Each nonempty marked subset of size `k` has joint probability given by
the positive allowed length to the power `D - 1`, throughout the unit turn. -/
theorem volume_biInter_relativeAnchoredUnitArc_exact (ref : ι) (s : Finset ι) (hs : s.Nonempty)
    (r : Icc (0 : ℝ) 1) : volume (⋂ i ∈ s, relativeAnchoredUnitArc ref i r) =
      ENNReal.ofReal (1 - (s.card : ℝ) * (1 - (r : ℝ))) ^ (Fintype.card ι - 1) := by
  classical
  by_cases htop : (r : ℝ) = 1
  · have hArc : forwardUnitArc (1 : ℝ) = univ := by
      refine eq_univ_of_forall fun z => ?_
      let a : ℝ := (AddCircle.equivIco (1 : ℝ) 0 z : ℝ)
      have ha : a ∈ Ico (0 : ℝ) (0 + 1) := (AddCircle.equivIco (1 : ℝ) 0 z).2
      have he : (a : UnitAddCircle) = z := AddCircle.coe_equivIco
      exact ⟨a, ⟨ha.1, by simpa only [zero_add] using ha.2.le⟩, he⟩
    have hset : (⋂ i ∈ s, relativeAnchoredUnitArc ref i r) = univ := by
      ext x
      simp [relativeAnchoredUnitArc, anchoredUnitArc, htop, hArc]
    rw [hset, measure_univ, htop, sub_self, mul_zero, sub_zero, ENNReal.ofReal_one, one_pow]
  by_cases hhalf : (1 / 2 : ℝ) ≤ (r : ℝ)
  · exact volume_biInter_relativeAnchoredUnitArc_upperRange ref s hs ⟨r, hhalf, lt_of_le_of_ne r.2.2 htop⟩
  by_cases hsingle : s.card = 1
  · obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hsingle
    have hset : (⋂ j ∈ s, relativeAnchoredUnitArc ref j r) = relativeAnchoredUnitArc ref i r := by
      rw [hi]
      ext x
      simp only [mem_iInter, Finset.mem_singleton, forall_eq]
    rw [hset, volume_relativeAnchoredUnitArc_full ref i r, hsingle, Nat.cast_one, one_mul, sub_sub_cancel]
  · have hs2 : 2 ≤ s.card := by have h := Finset.card_pos.mpr hs; omega
    have hD : s.card ≤ Fintype.card ι := Finset.card_le_univ s
    have hpred : Fintype.card ι - 1 ≠ 0 := by omega
    have hzero {a : ℝ} (ha : a ≤ 1 / 2) :
        ENNReal.ofReal (1 - (s.card : ℝ) * (1 - a)) ^ (Fintype.card ι - 1) = 0 := by
      have hs' : (2 : ℝ) ≤ (s.card : ℝ) := by exact_mod_cast hs2
      have h : 1 ≤ (s.card : ℝ) * (1 - a) := calc
        1 = (2 : ℝ) * (1 / 2) := by norm_num
        _ ≤ (s.card : ℝ) * (1 / 2) := mul_le_mul_of_nonneg_right hs' (by norm_num)
        _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith only [ha]) (Nat.cast_nonneg _)
      rw [ENNReal.ofReal_eq_zero.mpr (sub_nonpos.mpr h), zero_pow hpred]
    rw [hzero (lt_of_not_ge hhalf).le]
    have hhalf0 : volume (⋂ i ∈ s, relativeAnchoredUnitArc ref i (1 / 2 : ℝ)) = 0 :=
      (volume_biInter_relativeAnchoredUnitArc_upperRange ref s hs ⟨1 / 2, le_rfl, by norm_num⟩).trans (hzero le_rfl)
    refine measure_mono_null ?_ hhalf0
    intro x hx
    refine mem_iInter.mpr fun i => mem_iInter.mpr fun hi => ?_
    have h : relativeUnitPhasePacket ref x ∈ anchoredUnitArc i r := mem_iInter.mp (mem_iInter.mp hx i) hi
    intro j hj
    exact image_mono (Icc_subset_Icc_right (lt_of_not_ge hhalf).le) (h j hj)

/-- Inclusion–exclusion for all enclosing radii, with one term per anchor count. -/
def zeroGateArcOccupationPolynomial (D : ℕ) (r : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 D, (D.choose k : ℝ) * ((-1 : ℝ) ^ (k + 1) * max 0 (1 - (k : ℝ) * (1 - r)) ^ (D - 1))

/-- The full Haar occupation profile is the circular-spacing polynomial. -/
theorem relativeUnitArcMass_eq_exactPolynomial (ref : ι) (r : Icc (0 : ℝ) 1) :
    relativeUnitArcMass ref r = zeroGateArcOccupationPolynomial (Fintype.card ι) r := by
  classical
  let A (i : ι) := relativeAnchoredUnitArc ref i (r : ℝ)
  let D := Fintype.card ι
  let m (k : ℕ) := max 0 (1 - (k : ℝ) * (1 - (r : ℝ))) ^ (D - 1)
  have hm (s : Finset ι) (_ : s ⊆ Finset.univ) (hs : s.Nonempty) : volume.real (⋂ i ∈ s, A i) = m s.card := by
    have h : ∀ x : ℝ, (ENNReal.ofReal x).toReal = max 0 x := fun x => by
      by_cases hx : 0 ≤ x
      · rw [ENNReal.toReal_ofReal hx, max_eq_right hx]
      · rw [ENNReal.ofReal_eq_zero.mpr (lt_of_not_ge hx).le, ENNReal.toReal_zero, max_eq_left (lt_of_not_ge hx).le]
    simp only [Measure.real, A, volume_biInter_relativeAnchoredUnitArc_exact ref s hs r, ENNReal.toReal_pow, h, m, D]
  have h := measureReal_biUnion_eq_sum_choose_card (μ := volume) (Finset.univ : Finset ι) A
    (fun i _ => (isClosed_relativeAnchoredUnitArc ref i r).measurableSet) m hm
  have he : (⋃ i ∈ (Finset.univ : Finset ι), A i) = relativeEnclosingUnitArc ref r := by
    simp [A, relativeEnclosingUnitArc, enclosingUnitArc, preimage_iUnion]
  rw [he, Finset.card_univ] at h
  change volume.real (relativeEnclosingUnitArc ref r) = _
  rw [h, zeroGateArcOccupationPolynomial]
  let f (k : ℕ) := (D.choose k : ℝ) * ((-1 : ℝ) ^ (k + 1) * m k)
  have hf : (Finset.range (D + 1)).filter (fun k => k ≠ 0) = Finset.Icc 1 D := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
    omega
  change (∑ k ∈ Finset.range (D + 1), (D.choose k : ℝ) * (if k = 0 then 0 else (-1 : ℝ) ^ (k + 1) * m k)) =
    ∑ k ∈ Finset.Icc 1 D, f k
  rw [← hf, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : k = 0 <;> simp [f, hk]

end Marked

/-- The exact full-scale occupation law on `n` qubits. -/
theorem zeroGateFullArcMass_eq_exactPolynomial (n : ℕ) (r : Icc (0 : ℝ) 1) :
    zeroGateFullArcMass n r = zeroGateArcOccupationPolynomial (2 ^ n) r := by
  simpa only [zeroGateFullArcMass, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] using
    relativeUnitArcMass_eq_exactPolynomial (fun _ : Fin n => false) r

private abbrev Reg (n : ℕ) := Matrix (Fin n → Bool) (Fin n → Bool) ℂ

/-- The circular-spacing polynomial is the actual long-time return fraction
at every tolerance on every open prefix of one typical Gaussian draw. -/
theorem gaussian_path_zeroGate_exactArcOccupation :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ, ∀ r : Icc (0 : ℝ) 1, ∀ a : ℝ,
      let u := pathPauliDisorderShell ω (k + 1)
      let H : selfAdjoint (Reg (k + 3)) := ⟨pathHamiltonian u, isSelfAdjoint_pathHamiltonian u⟩
      Tendsto (fun T => volume.real (zeroGateReturnSet H r ∩ Icc a T) / (T - a)) atTop
        (𝓝 (zeroGateArcOccupationPolynomial (2 ^ (k + 3)) r)) := by
  filter_upwards [gaussian_path_zeroGateFullOccupation_from_start] with ω hω
  intro k r a
  have h := hω k r a
  rwa [zeroGateFullArcMass_eq_exactPolynomial] at h

#print axioms volume_admissibleMarkedAnchorPhases
#print axioms volume_biInter_relativeAnchoredUnitArc_exact
#print axioms relativeUnitArcMass_eq_exactPolynomial
#print axioms gaussian_path_zeroGate_exactArcOccupation

end

end GaloisForLFunctions.HTGeometry
