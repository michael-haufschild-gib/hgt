import GaloisForLFunctions.HTGeometry.PaleyZygmund
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.ZeroGateFullOccupation

/-!
# Empty arcs in Haar phase packets

An empty open arc gives a closed covering arc of complementary length.
Disjoint trial arcs have negatively correlated emptiness events, so the
second moment of their count bounds the probability of finding a gap.
-/

open MeasureTheory Set
open scoped ENNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Equal-mass events with nonpositive pairwise covariance have union
probability at least `q / (1 + q)`, where `q` is the mean number of hits. -/
theorem measureReal_iUnion_ge_mean_div_one_add_mean {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (A : I → Set Ω) (hA : ∀ i, MeasurableSet (A i))
    (p : ℝ) (hvol : ∀ i, μ.real (A i) = p)
    (hpair : ∀ i j, i ≠ j → μ.real (A i ∩ A j) ≤ p ^ 2)
    (hmean : 0 < (Fintype.card I : ℝ) * p) :
    ((Fintype.card I : ℝ) * p) / (1 + (Fintype.card I : ℝ) * p) ≤ μ.real (⋃ i, A i) := by
  classical
  let f (i : I) := (A i).indicator (fun _ : Ω => (1 : ℝ))
  let W (i j : I) := (A i ∩ A j).indicator (fun _ : Ω => (1 : ℝ))
  let Z (x : Ω) := ∑ i, f i x
  let q := (Fintype.card I : ℝ) * p
  have hf (i : I) : Integrable (f i) μ := (integrable_const _).indicator (hA i)
  have hf0 (i : I) (x : Ω) : 0 ≤ f i x := by
    by_cases hx : x ∈ A i <;> simp [f, hx]
  have hW (i j : I) : Integrable (W i j) μ := (integrable_const _).indicator ((hA i).inter (hA j))
  have hZ : Measurable Z := Finset.measurable_sum _ fun i _ => measurable_const.indicator (hA i)
  have hZi : Integrable Z μ := integrable_finsetSum _ fun i _ => hf i
  have hZsq : (fun x => Z x ^ 2) = fun x => ∑ i, ∑ j, W i j x := by
    funext x
    simp only [Z, pow_two, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    by_cases hi : x ∈ A i <;> by_cases hj : x ∈ A j <;> simp [f, W, hi, hj]
  have hZi2 : Integrable (fun x => Z x ^ 2) μ := by
    rw [hZsq]
    exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hW i j
  have hfirst : (∫ x, Z x ∂μ) = q := by
    have hi (i : I) : (∫ x, f i x ∂μ) = p := (integral_indicator_one (hA i)).trans (hvol i)
    change (∫ x, ∑ i, f i x ∂μ) = _
    rw [integral_finsetSum _ (fun i _ => hf i)]
    simp only [hi, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, q]
  have hinner (i : I) : (∫ x, ∑ j, W i j x ∂μ) = ∑ j, μ.real (A i ∩ A j) := by
    rw [integral_finsetSum _ (fun j _ => hW i j)]
    exact Finset.sum_congr rfl fun j _ => integral_indicator_one ((hA i).inter (hA j))
  have hsecond : (∫ x, Z x ^ 2 ∂μ) ≤ q + q ^ 2 := by
    rw [hZsq, integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => hW i j)]
    simp only [hinner]
    calc
      _ ≤ ∑ i : I, ∑ j : I, (p ^ 2 + if i = j then p else 0) := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
        by_cases h : i = j
        · subst j
          rw [inter_self, hvol, if_pos rfl]
          exact le_add_of_nonneg_left (sq_nonneg p)
        · rw [if_neg h, add_zero]
          exact hpair i j h
      _ = q + q ^ 2 := by
        simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          Finset.sum_ite_eq, Finset.mem_univ, if_true, q]
        ring
  have hset : {x : Ω | 0 < Z x} = ⋃ i, A i := by
    ext x
    constructor
    · intro hx
      by_contra hnot
      have hn (i : I) : x ∉ A i := fun hi => hnot (mem_iUnion.mpr ⟨i, hi⟩)
      have hz : Z x = 0 := by simp [Z, f, hn]
      exact (ne_of_gt hx) hz
    · intro hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      have hfi : 0 < f i x := by simp [f, hi]
      exact hfi.trans_le (Finset.single_le_sum (fun j _ => hf0 j x) (Finset.mem_univ i))
  have hpz := paley_zygmund hZ (fun x => Finset.sum_nonneg fun i _ => hf0 i x) hZi hZi2
    (θ := 0) le_rfl zero_lt_one
  simp only [sub_zero, one_pow, one_mul, zero_mul, hfirst, hset, ← measureReal_def] at hpz
  have h := hpz.trans (mul_le_mul_of_nonneg_right hsecond (measureReal_nonneg (μ := μ)))
  have hq : 0 < q := hmean
  change q / (1 + q) ≤ μ.real (⋃ i, A i)
  apply (div_le_iff₀ (by linarith only [hq])).mpr
  apply (mul_le_mul_iff_of_pos_right hq).mp
  nlinarith only [h]

local instance emptyArcCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  ⟨UnitAddCircle.measure_univ⟩

private def openUnitArc (a b : ℝ) : Set UnitAddCircle := (((↑) : ℝ → UnitAddCircle) '' Ioo a b)

private theorem isOpen_openUnitArc (a b : ℝ) : IsOpen (openUnitArc a b) :=
  QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo

private theorem volume_openUnitArc {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) :
    volume (openUnitArc a b) = ENNReal.ofReal (b - a) := by
  have hab : Ioo a b ⊆ Ioc (0 : ℝ) (0 + 1) := fun x hx =>
    ⟨ha.trans_lt hx.1, by simpa only [zero_add] using hx.2.le.trans hb⟩
  rw [AddCircle.add_projection_respects_measure 1 0 (isOpen_openUnitArc a b).measurableSet]
  have he : (((↑) : ℝ → UnitAddCircle) ⁻¹' openUnitArc a b) ∩ Ioc (0 : ℝ) (0 + 1) = Ioo a b := by
    ext x
    constructor
    · rintro ⟨⟨y, hy, he⟩, hx⟩
      exact (AddCircle.coe_eq_coe_iff_of_mem_Ioc (hab hy) hx).mp he ▸ hy
    · intro hx
      exact ⟨⟨x, hx, rfl⟩, hab hx⟩
  rw [he, Real.volume_Ioo]

/-- A packet that avoids an open arc is covered by a complementary arc. -/
private theorem mem_enclosingUnitArc_of_openUnitArc_empty {ι : Type*} [Fintype ι] [Nonempty ι]
    (x : ι → UnitAddCircle) (a s : ℝ) (h : ∀ j, x j ∉ openUnitArc a (a + s)) :
    x ∈ enclosingUnitArc (1 - s) := by
  let y (j : ι) : ℝ := (AddCircle.equivIco (1 : ℝ) (a + s) (x j) : ℝ)
  have hcoe (j : ι) : (y j : UnitAddCircle) = x j := AddCircle.coe_equivIco
  have hy (j : ι) : y j ∈ Ico (a + s) (a + s + 1) := (AddCircle.equivIco (1 : ℝ) (a + s) (x j)).2
  have hupper (j : ι) : y j ≤ a + 1 := by
    by_contra! hj
    have hm : y j - 1 ∈ Ioo a (a + s) :=
      ⟨by linarith only [hj], by linarith only [(hy j).2]⟩
    have he : ((y j - 1 : ℝ) : UnitAddCircle) = x j := by
      rw [AddCircle.coe_sub, AddCircle.coe_period, sub_zero, hcoe]
    exact h j ⟨y j - 1, hm, he⟩
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty y
  have hmin (j : ι) : y i ≤ y j := hi ▸ Finset.inf'_le y (Finset.mem_univ j)
  refine mem_iUnion.mpr ⟨i, fun j _ => ⟨y j - y i, ⟨sub_nonneg.mpr (hmin j), ?_⟩, ?_⟩⟩
  · linarith only [hupper j, (hy i).1]
  · rw [AddCircle.coe_sub, hcoe, hcoe]

private theorem measureReal_pi_const {J : Type*} [Fintype J] (B : Set UnitAddCircle) :
    volume.real ((univ : Set J).pi (fun _ => B)) = (volume.real B) ^ Fintype.card J := by
  rw [Measure.real, volume_pi_pi]
  simp only [Finset.prod_const, Finset.card_univ, ENNReal.toReal_pow, Measure.real]

/-- If `m` open arcs of length `s` fit on the circle, their expected empty
count is `m * (1-s)^(D-1)`. The relative enclosure mass at `1-s` is at
least this count divided by one plus the count. -/
theorem relativeUnitArcMass_complement_ge_emptyArcs {ι : Type*} [Fintype ι] [DecidableEq ι] (ref : ι)
    {m : ℕ} (hm : 0 < m) (s : Ico (0 : ℝ) 1) (hpack : (m : ℝ) * (s : ℝ) ≤ 1) :
    let q := (m : ℝ) * (1 - (s : ℝ)) ^ (Fintype.card ι - 1)
    q / (1 + q) ≤ relativeUnitArcMass ref (1 - (s : ℝ)) := by
  classical
  let β := {j : ι // j ≠ ref}
  let a (i : Fin m) := (i.val : ℝ) * (s : ℝ)
  let B (i : Fin m) := openUnitArc (a i) (a i + (s : ℝ))
  let A (i : Fin m) : Set (β → UnitAddCircle) := univ.pi (fun _ => (B i)ᶜ)
  have ha0 (i : Fin m) : 0 ≤ a i := mul_nonneg (Nat.cast_nonneg _) s.2.1
  have hadd (i : Fin m) : a i + (s : ℝ) = ((i.val : ℝ) + 1) * (s : ℝ) := by
    dsimp only [a]
    ring
  have hb1 (i : Fin m) : a i + (s : ℝ) ≤ 1 := by
    rw [hadd i]
    have hi : (i.val : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast Nat.succ_le_of_lt i.isLt
    exact (mul_le_mul_of_nonneg_right hi s.2.1).trans hpack
  have hcoord (i : Fin m) : Ioo (a i) (a i + (s : ℝ)) ⊆ Ioo (0 : ℝ) 1 :=
    fun _ hx => ⟨(ha0 i).trans_lt hx.1, hx.2.trans_le (hb1 i)⟩
  have hzero (i : Fin m) : (0 : UnitAddCircle) ∉ B i := by
    rintro ⟨t, ht, hz⟩
    obtain ⟨ht0, ht1⟩ := hcoord i ht
    have he := (AddCircle.coe_eq_zero_iff_of_mem_Ico (p := (1 : ℝ)) ⟨ht0.le, ht1⟩).mp hz
    exact ht0.ne' he
  have hsep {i j : Fin m} (h : i.val < j.val) : a i + (s : ℝ) ≤ a j := by
    rw [hadd i]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.succ_le_of_lt h) s.2.1
  have hdisj (i j : Fin m) (hij : i ≠ j) : Disjoint (B i) (B j) := by
    refine Set.disjoint_left.mpr ?_
    rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, he⟩
    have hmem (i : Fin m) {t : ℝ} (ht : t ∈ Ioo (a i) (a i + (s : ℝ))) :
        t ∈ Ioc (0 : ℝ) (0 + 1) := ⟨(hcoord i ht).1, by simpa only [zero_add] using (hcoord i ht).2.le⟩
    have hxy := (AddCircle.coe_eq_coe_iff_of_mem_Ioc (hmem j hy) (hmem i hx)).mp he
    subst y
    rcases lt_or_gt_of_ne (fun h : i.val = j.val => hij (Fin.ext h)) with hij' | hji'
    · exact (not_lt_of_ge ((hsep hij').trans hy.1.le)) hx.2
    · exact (not_lt_of_ge ((hsep hji').trans hx.1.le)) hy.2
  have hB (i : Fin m) : MeasurableSet (B i) := (isOpen_openUnitArc _ _).measurableSet
  have hA (i : Fin m) : MeasurableSet (A i) := MeasurableSet.univ_pi fun _ => (hB i).compl
  have hvol (i : Fin m) : volume.real (B i) = (s : ℝ) := by
    change (volume (openUnitArc (a i) (a i + (s : ℝ)))).toReal = (s : ℝ)
    rw [volume_openUnitArc (ha0 i) (hb1 i), add_sub_cancel_left, ENNReal.toReal_ofReal s.2.1]
  have hcard : Fintype.card β = Fintype.card ι - 1 := by
    dsimp only [β]
    rw [Fintype.card_subtype_compl (fun j => j = ref), Fintype.card_subtype_eq]
  have hsingle (i : Fin m) : volume.real (A i) = (1 - (s : ℝ)) ^ (Fintype.card ι - 1) := by
    change volume.real ((univ : Set β).pi (fun _ => (B i)ᶜ)) = _
    rw [measureReal_pi_const, probReal_compl_eq_one_sub (hB i), hvol, hcard]
  have hpair (i j : Fin m) (hij : i ≠ j) :
      volume.real (A i ∩ A j) ≤ ((1 - (s : ℝ)) ^ (Fintype.card ι - 1)) ^ 2 := by
    have hset : A i ∩ A j = (univ : Set β).pi (fun _ => (B i ∪ B j)ᶜ) := by
      ext x
      simp only [A, mem_inter_iff, Set.mem_pi, mem_univ, true_implies, mem_compl_iff, mem_union,
        not_or, forall_and]
    have hcompl : volume.real ((B i ∪ B j)ᶜ) = 1 - ((s : ℝ) + (s : ℝ)) := by
      rw [probReal_compl_eq_one_sub ((hB i).union (hB j)), measureReal_union (hdisj i j hij) (hB j), hvol, hvol]
    have hnon : 0 ≤ 1 - ((s : ℝ) + (s : ℝ)) := by rw [← hcompl]; exact measureReal_nonneg
    rw [hset, measureReal_pi_const, hcompl, hcard, ← pow_mul, mul_comm (Fintype.card ι - 1), pow_mul]
    exact pow_le_pow_left₀ hnon (by nlinarith only [sq_nonneg (s : ℝ)]) _
  have hmean : 0 < (Fintype.card (Fin m) : ℝ) * (1 - (s : ℝ)) ^ (Fintype.card ι - 1) := by
    rw [Fintype.card_fin]
    exact mul_pos (Nat.cast_pos.mpr hm) (pow_pos (sub_pos.mpr s.2.2) _)
  have hsubset : (⋃ i, A i) ⊆ relativeEnclosingUnitArc ref (1 - (s : ℝ)) := by
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    haveI : Nonempty ι := ⟨ref⟩
    change relativeUnitPhasePacket ref x ∈ enclosingUnitArc (1 - (s : ℝ))
    apply mem_enclosingUnitArc_of_openUnitArc_empty _ (a i) (s : ℝ)
    intro j
    by_cases hj : j ≠ ref
    · have hjmem := Set.mem_pi.mp hi (⟨j, hj⟩ : β) (mem_univ _)
      simpa only [relativeUnitPhasePacket, dif_pos hj, mem_compl_iff] using hjmem
    · simpa only [relativeUnitPhasePacket, dif_neg hj] using hzero i
  have h := measureReal_iUnion_ge_mean_div_one_add_mean A hA _ hsingle hpair hmean
  rw [Fintype.card_fin] at h
  exact h.trans (measureReal_mono hsubset (measure_ne_top _ _))

/-- Packed empty trial arcs give a finite-register lower occupation bound. -/
theorem zeroGateFullArcMass_complement_ge_emptyArcs (n : ℕ) {m : ℕ} (hm : 0 < m)
    (s : Ico (0 : ℝ) 1) (hpack : (m : ℝ) * (s : ℝ) ≤ 1) :
    let q := (m : ℝ) * (1 - (s : ℝ)) ^ (2 ^ n - 1)
    q / (1 + q) ≤ zeroGateFullArcMass n (1 - (s : ℝ)) := by
  simpa only [zeroGateFullArcMass, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] using
    relativeUnitArcMass_complement_ge_emptyArcs (fun _ : Fin n => false) hm s hpack

#print axioms measureReal_iUnion_ge_mean_div_one_add_mean
#print axioms relativeUnitArcMass_complement_ge_emptyArcs
#print axioms zeroGateFullArcMass_complement_ge_emptyArcs

end

end GaloisForLFunctions.HTGeometry
