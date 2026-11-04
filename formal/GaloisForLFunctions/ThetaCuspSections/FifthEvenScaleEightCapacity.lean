import GaloisForLFunctions.ThetaCuspSections.FifthEvenScaleEightSourceBounds

/-!
# Exact scaling capacity of the fixed theta cross-load

At scale eight the negative compensation turns the positive cross-load into
an ordered affine pencil. Its positive interval ends at a singular
semidefinite matrix, strictly between the half load and the full load.
-/

noncomputable section
open Matrix Set Filter Topology RHTower
namespace GaloisForLFunctions.ThetaCuspSections.EightCrossCapacity
open EightCrossSource EightCrossData FifthNativeRay FifthRemainder FifthLeadingPair

private theorem gram_entry_continuous (i j : Fin 5) :
    Continuous (fun t => scaledGram t i j) := by
  simp only [scaledGram_eq,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]
  fun_prop

private theorem energy_continuous (v : Fin 5 → ℝ) :
    Continuous (fun t => v ⬝ᵥ (scaledGram t *ᵥ v)) := by
  simp only [scaledGram_eq,Matrix.add_mulVec,Matrix.smul_mulVec,dotProduct_add,
    dotProduct_smul,smul_eq_mul]
  fun_prop

private theorem energy_antitone {s t : ℝ} (hst : s ≤ t) (v : Fin 5 → ℝ) :
    v ⬝ᵥ (scaledGram t *ᵥ v) ≤ v ⬝ᵥ (scaledGram s *ᵥ v) := by
  have hK := sourceUnit_pos (x := center) (by rw [center_scale]; norm_num)
  have hc : thetaCuspCenterCompensationSource center/sourceUnit center ≤ 0 :=
    (div_neg_of_neg_of_pos compensation_negative hK).le
  have hV := (loadGram_posSemidef 8).dotProduct_mulVec_nonneg v
  simp only [star_trivial] at hV
  have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonpos_right hst hc) hV
  simp only [scaledGram_eq,Matrix.add_mulVec,Matrix.smul_mulVec,dotProduct_add,
    dotProduct_smul,smul_eq_mul]
  linarith only [h]

private theorem posDef_downward {s t : ℝ} (hst : s ≤ t) (ht : (scaledGram t).PosDef) :
    (scaledGram s).PosDef := by
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨scaledGram_hermitian s,?_⟩
  intro v hv
  have h := ht.dotProduct_mulVec_pos hv
  simp only [star_trivial] at h ⊢
  exact h.trans_le (energy_antitone hst v)

private theorem posDef_right {t : ℝ} (ht : (scaledGram t).PosDef) :
    ∃ u, t < u ∧ (scaledGram u).PosDef := by
  have he := GaloisForLFunctions.HTGeometry.posDef_eventually_of_tendsto ht
    (Filter.Eventually.of_forall scaledGram_hermitian)
    (fun i j => (gram_entry_continuous i j).continuousAt.tendsto)
  obtain ⟨δ,hδ,hh⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨t+δ/2,by linarith only [hδ],hh ?_⟩
  rw [Real.dist_eq,show t+δ/2-t=δ/2 by ring,abs_of_pos (half_pos hδ)]
  linarith only [hδ]

/-- Supremal scalar multiple preserving strict positivity at scale eight. -/
def capacity : ℝ := sSup {t : ℝ | (scaledGram t).PosDef}

private theorem positive_nonempty : {t : ℝ | (scaledGram t).PosDef}.Nonempty :=
  ⟨1/2,half_load_posDef⟩

private theorem positive_lt_one {t : ℝ} (ht : (scaledGram t).PosDef) : t < 1 := by
  by_contra h
  exact full_load_not_posSemidef (posDef_downward (le_of_not_gt h) ht).posSemidef

private theorem positive_bdd : BddAbove {t : ℝ | (scaledGram t).PosDef} :=
  ⟨1,fun _ ht => (positive_lt_one ht).le⟩

private theorem below_capacity {t : ℝ} (ht : t < capacity) : (scaledGram t).PosDef := by
  obtain ⟨u,hu,htu⟩ := (lt_csSup_iff positive_bdd positive_nonempty).mp ht
  exact posDef_downward htu.le hu

private theorem capacity_not_posDef : ¬ (scaledGram capacity).PosDef := by
  intro h
  obtain ⟨u,hu,hpu⟩ := posDef_right h
  exact (not_lt_of_ge (le_csSup positive_bdd hpu)) hu

/-- Strict positivity holds precisely below the scaling capacity. -/
theorem posDef_iff {t : ℝ} : (scaledGram t).PosDef ↔ t < capacity := by
  constructor
  · intro ht
    obtain ⟨u,htu,hu⟩ := posDef_right ht
    exact htu.trans_le (le_csSup positive_bdd hu)
  · exact below_capacity

private theorem capacity_posSemidef : (scaledGram capacity).PosSemidef := by
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨scaledGram_hermitian _,?_⟩
  intro v
  simp only [star_trivial]
  by_contra h
  have hn : v ⬝ᵥ (scaledGram capacity *ᵥ v) < 0 := lt_of_not_ge h
  have he : ∀ᶠ t in 𝓝 capacity, v ⬝ᵥ (scaledGram t *ᵥ v) < 0 :=
    (energy_continuous v).continuousAt (isOpen_Iio.mem_nhds hn)
  obtain ⟨δ,hδ,hh⟩ := Metric.eventually_nhds_iff.mp he
  have ht : capacity-δ/2 < capacity := by linarith only [hδ]
  have hp := (below_capacity ht).posSemidef.dotProduct_mulVec_nonneg v
  simp only [star_trivial] at hp
  apply (not_lt_of_ge hp) (hh ?_)
  rw [Real.dist_eq,show capacity-δ/2-capacity=-(δ/2) by ring,abs_neg,
    abs_of_pos (half_pos hδ)]
  linarith only [hδ]

/-- The exact positive capacity lies strictly between one half and one. -/
theorem capacity_bounds : (1/2 : ℝ) < capacity ∧ capacity < 1 := by
  refine ⟨posDef_iff.mp half_load_posDef,?_⟩
  have hle : capacity ≤ 1 := csSup_le positive_nonempty (fun _ ht => (positive_lt_one ht).le)
  refine lt_of_le_of_ne hle ?_
  intro h
  have hp := capacity_posSemidef
  rw [h] at hp
  exact full_load_not_posSemidef hp


private theorem zero_posDef : (scaledGram 0).PosDef :=
  posDef_downward (by norm_num : (0 : ℝ) ≤ 1/2) half_load_posDef

private theorem interior_posDef_of_posSemidef {t : ℝ}
    (ht : capacity < t) (hp : (scaledGram t).PosSemidef) :
    (scaledGram capacity).PosDef := by
  have hc : 0 < capacity := by linarith only [capacity_bounds.1]
  have ht0 : 0 < t := hc.trans ht
  have hλ : 0 < capacity/t := div_pos hc ht0
  have hλ1 : capacity/t < 1 := (div_lt_one ht0).mpr ht
  have he : scaledGram capacity=(1-capacity/t) • scaledGram 0+(capacity/t) • scaledGram t := by
    ext i j
    simp only [scaledGram_eq,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,zero_mul]
    field_simp [ht0.ne']
    ring
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨scaledGram_hermitian _,?_⟩
  intro v hv
  have h0 := zero_posDef.dotProduct_mulVec_pos hv
  have h1 := hp.dotProduct_mulVec_nonneg v
  simp only [star_trivial] at h0 h1 ⊢
  rw [he]
  simp only [Matrix.add_mulVec,Matrix.smul_mulVec,dotProduct_add,dotProduct_smul,smul_eq_mul]
  exact add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr hλ1) h0) (mul_nonneg hλ.le h1)

/-- Nonnegativity includes the capacity endpoint and no larger load. -/
theorem posSemidef_iff {t : ℝ} : (scaledGram t).PosSemidef ↔ t ≤ capacity := by
  constructor
  · intro ht
    by_contra h
    exact capacity_not_posDef (interior_posDef_of_posSemidef (lt_of_not_ge h) ht)
  · intro ht
    refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨scaledGram_hermitian _,?_⟩
    intro v
    have h := capacity_posSemidef.dotProduct_mulVec_nonneg v
    simp only [star_trivial] at h ⊢
    exact h.trans (energy_antitone ht v)

/-- At capacity the complete matrix is positive semidefinite and singular. -/
theorem boundary : (scaledGram capacity).PosSemidef ∧ (scaledGram capacity).det=0 := by
  refine ⟨capacity_posSemidef,?_⟩
  by_contra h
  exact capacity_not_posDef (capacity_posSemidef.posDef_iff_det_ne_zero.mpr h)


/-- Exact capacity law in the original moment coordinates. -/
theorem source_posDef_iff {t : ℝ} : (scaledSource t).PosDef ↔ t < capacity := by
  rw [← scaledGram_posDef_iff]
  exact posDef_iff

/-- The admissible nonnegative loads form a closed half-line. -/
theorem source_posSemidef_iff {t : ℝ} : (scaledSource t).PosSemidef ↔ t ≤ capacity := by
  rw [← scaledGram_posSemidef_iff]
  exact posSemidef_iff

/-- The capacity endpoint is a singular positive semidefinite complete source. -/
theorem source_boundary : (scaledSource capacity).PosSemidef ∧ (scaledSource capacity).det=0 := by
  have hp := (scaledGram_posSemidef_iff _).mp boundary.1
  refine ⟨hp,?_⟩
  by_contra hn
  have hd := hp.posDef_iff_det_ne_zero.mpr hn
  exact capacity_not_posDef ((scaledGram_posDef_iff _).mpr hd)

/-- A strict half-load/full-load bracket determines the sharp admissibility boundary. -/
theorem exact_scaling_capacity : ∃ τ : ℝ, 1/2 < τ ∧ τ < 1 ∧
    (∀ t : ℝ, (scaledSource t).PosDef ↔ t < τ) ∧
    (∀ t : ℝ, (scaledSource t).PosSemidef ↔ t ≤ τ) ∧
    (scaledSource τ).det=0 :=
  ⟨capacity,capacity_bounds.1,capacity_bounds.2,
    fun _ => source_posDef_iff,fun _ => source_posSemidef_iff,source_boundary.2⟩

end GaloisForLFunctions.ThetaCuspSections.EightCrossCapacity
