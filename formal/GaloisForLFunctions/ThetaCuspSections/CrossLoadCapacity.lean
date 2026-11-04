import GaloisForLFunctions.HTGeometry.PositiveDefiniteMatrixLimit

/-!
# Capacity of an ordered finite cross-load

A positive definite source minus a positive semidefinite load has an initial
open interval of strict positivity. If the unit load fails semidefiniteness,
this interval ends strictly between zero and one at a singular semidefinite
matrix. Continuity and convexity give both endpoint classifications.
-/

noncomputable section
open Matrix Set Filter Topology
namespace GaloisForLFunctions.ThetaCuspSections.CrossLoadCapacity

variable {n : ℕ}

/-- The affine source with scalar load. -/
def pencil (A B : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) : Matrix (Fin n) (Fin n) ℝ := A-t • B

/-- Supremal strictly positive load. -/
def capacity (A B : Matrix (Fin n) (Fin n) ℝ) : ℝ := sSup {t : ℝ | (pencil A B t).PosDef}

variable {A B : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) (hB : B.PosSemidef)
  (h1 : ¬ (pencil A B 1).PosSemidef)

include hA hB

private theorem hermitian (t : ℝ) : (pencil A B t).IsHermitian :=
  hA.isHermitian.sub (hB.isHermitian.smul (by rfl))

omit hA hB in
private theorem entry_continuous (i j : Fin n) : Continuous (fun t => pencil A B t i j) := by
  simp only [pencil,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul]
  fun_prop

omit hA hB in
private theorem energy_continuous (v : Fin n → ℝ) :
    Continuous (fun t => v ⬝ᵥ (pencil A B t *ᵥ v)) := by
  simp only [pencil,Matrix.sub_mulVec,Matrix.smul_mulVec,dotProduct_sub,
    dotProduct_smul,smul_eq_mul]
  fun_prop

omit hA in
private theorem energy_antitone {s t : ℝ} (hst : s ≤ t) (v : Fin n → ℝ) :
    v ⬝ᵥ (pencil A B t *ᵥ v) ≤ v ⬝ᵥ (pencil A B s *ᵥ v) := by
  have hb := hB.dotProduct_mulVec_nonneg v
  simp only [star_trivial] at hb
  have h := mul_le_mul_of_nonneg_right hst hb
  simp only [pencil,Matrix.sub_mulVec,Matrix.smul_mulVec,dotProduct_sub,
    dotProduct_smul,smul_eq_mul]
  linarith only [h]

private theorem posDef_downward {s t : ℝ} (hst : s ≤ t)
    (ht : (pencil A B t).PosDef) : (pencil A B s).PosDef := by
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨hermitian hA hB s,?_⟩
  intro v hv
  have h := ht.dotProduct_mulVec_pos hv
  simp only [star_trivial] at h ⊢
  exact h.trans_le (energy_antitone hB hst v)

private theorem posDef_right {t : ℝ} (ht : (pencil A B t).PosDef) :
    ∃ u, t < u ∧ (pencil A B u).PosDef := by
  have he := GaloisForLFunctions.HTGeometry.posDef_eventually_of_tendsto ht
    (Filter.Eventually.of_forall (hermitian hA hB))
    (fun i j => (entry_continuous i j).continuousAt.tendsto)
  obtain ⟨δ,hδ,hh⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨t+δ/2,by linarith only [hδ],hh ?_⟩
  rw [Real.dist_eq,show t+δ/2-t=δ/2 by ring,abs_of_pos (half_pos hδ)]
  linarith only [hδ]

omit hB in
private theorem zero_posDef : (pencil A B 0).PosDef := by
  simpa only [pencil,zero_smul,sub_zero] using hA

omit hB in
private theorem positive_nonempty : {t : ℝ | (pencil A B t).PosDef}.Nonempty :=
  ⟨0,zero_posDef hA⟩

include h1

private theorem positive_lt_one {t : ℝ} (ht : (pencil A B t).PosDef) : t < 1 := by
  by_contra h
  exact h1 (posDef_downward hA hB (le_of_not_gt h) ht).posSemidef

private theorem positive_bdd : BddAbove {t : ℝ | (pencil A B t).PosDef} :=
  ⟨1,fun _ ht => (positive_lt_one hA hB h1 ht).le⟩

private theorem below_capacity {t : ℝ} (ht : t < capacity A B) :
    (pencil A B t).PosDef := by
  obtain ⟨u,hu,htu⟩ := (lt_csSup_iff (positive_bdd hA hB h1) (positive_nonempty hA)).mp ht
  exact posDef_downward hA hB htu.le hu

private theorem capacity_not_posDef : ¬ (pencil A B (capacity A B)).PosDef := by
  intro h
  obtain ⟨u,hu,hpu⟩ := posDef_right hA hB h
  exact (not_lt_of_ge (le_csSup (positive_bdd hA hB h1) hpu)) hu

/-- Strict positivity holds exactly below capacity. -/
theorem posDef_iff {t : ℝ} : (pencil A B t).PosDef ↔ t < capacity A B := by
  constructor
  · intro ht
    obtain ⟨u,htu,hu⟩ := posDef_right hA hB ht
    exact htu.trans_le (le_csSup (positive_bdd hA hB h1) hu)
  · exact below_capacity hA hB h1

private theorem capacity_posSemidef : (pencil A B (capacity A B)).PosSemidef := by
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨hermitian hA hB _,?_⟩
  intro v
  simp only [star_trivial]
  by_contra h
  have hn : v ⬝ᵥ (pencil A B (capacity A B) *ᵥ v) < 0 := lt_of_not_ge h
  have he : ∀ᶠ t in 𝓝 (capacity A B), v ⬝ᵥ (pencil A B t *ᵥ v) < 0 :=
    (energy_continuous v).continuousAt (isOpen_Iio.mem_nhds hn)
  obtain ⟨δ,hδ,hh⟩ := Metric.eventually_nhds_iff.mp he
  have ht : capacity A B-δ/2 < capacity A B := by linarith only [hδ]
  have hp := (below_capacity hA hB h1 ht).posSemidef.dotProduct_mulVec_nonneg v
  simp only [star_trivial] at hp
  apply (not_lt_of_ge hp) (hh ?_)
  rw [Real.dist_eq,show capacity A B-δ/2-capacity A B=-(δ/2) by ring,abs_neg,
    abs_of_pos (half_pos hδ)]
  linarith only [hδ]

/-- Unit-load failure brackets capacity strictly between zero and one. -/
theorem capacity_bounds : 0 < capacity A B ∧ capacity A B < 1 := by
  refine ⟨(posDef_iff hA hB h1).mp (zero_posDef hA),?_⟩
  have hle : capacity A B ≤ 1 :=
    csSup_le (positive_nonempty hA) (fun _ ht => (positive_lt_one hA hB h1 ht).le)
  refine lt_of_le_of_ne hle ?_
  intro h
  have hp := capacity_posSemidef hA hB h1
  rw [h] at hp
  exact h1 hp

private theorem interior_posDef_of_posSemidef {t : ℝ}
    (ht : capacity A B < t) (hp : (pencil A B t).PosSemidef) :
    (pencil A B (capacity A B)).PosDef := by
  have hc := (capacity_bounds hA hB h1).1
  have ht0 : 0 < t := hc.trans ht
  have hweight : 0 < capacity A B/t := div_pos hc ht0
  have hweight_lt : capacity A B/t < 1 := (div_lt_one ht0).mpr ht
  have he : pencil A B (capacity A B)=
      (1-capacity A B/t) • pencil A B 0+(capacity A B/t) • pencil A B t := by
    ext i j
    simp only [pencil,Matrix.sub_apply,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,zero_mul]
    field_simp [ht0.ne']
    ring
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨hermitian hA hB _,?_⟩
  intro v hv
  have h0 := (zero_posDef (B := B) hA).dotProduct_mulVec_pos hv
  have h2 := hp.dotProduct_mulVec_nonneg v
  simp only [star_trivial] at h0 h2 ⊢
  rw [he]
  simp only [Matrix.add_mulVec,Matrix.smul_mulVec,dotProduct_add,dotProduct_smul,smul_eq_mul]
  exact add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr hweight_lt) h0)
    (mul_nonneg hweight.le h2)

/-- Semidefiniteness holds precisely on the closed capacity half-line. -/
theorem posSemidef_iff {t : ℝ} : (pencil A B t).PosSemidef ↔ t ≤ capacity A B := by
  constructor
  · intro ht
    by_contra h
    exact capacity_not_posDef hA hB h1
      (interior_posDef_of_posSemidef hA hB h1 (lt_of_not_ge h) ht)
  · intro ht
    refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨hermitian hA hB _,?_⟩
    intro v
    have h := (capacity_posSemidef hA hB h1).dotProduct_mulVec_nonneg v
    simp only [star_trivial] at h ⊢
    exact h.trans (energy_antitone hB ht v)

/-- The endpoint is positive semidefinite and singular. -/
theorem boundary : (pencil A B (capacity A B)).PosSemidef ∧
    (pencil A B (capacity A B)).det=0 := by
  refine ⟨capacity_posSemidef hA hB h1,?_⟩
  by_contra h
  exact capacity_not_posDef hA hB h1
    ((capacity_posSemidef hA hB h1).posDef_iff_det_ne_zero.mpr h)

end GaloisForLFunctions.ThetaCuspSections.CrossLoadCapacity
