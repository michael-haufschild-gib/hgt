import GaloisForLFunctions.HTGeometry.TopologyHelpers

/-!
# The two star-shaped pieces of a punctured product

Removing the origin from `W × ℝ` leaves the union of two pieces: the complement of the closed lower
ray `{0} × (-∞, 0]` and the complement of the closed upper ray `{0} × [0, ∞)`.  Each is open and
star-shaped about `(0, 1)` resp. `(0, -1)`, and their intersection is `{p | p.1 ≠ 0}`, which is the
punctured `W` times the line.
-/

namespace GaloisForLFunctions.HTGeometry

universe v

/-- The punctured space. -/
def punct (V : Type v) [Zero V] : Set V := {x | x ≠ 0}

variable (W : Type v) [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- The complement of the closed lower ray. -/
def upperPiece : Set (W × ℝ) := {p | ¬(p.1 = 0 ∧ p.2 ≤ 0)}

/-- The complement of the closed upper ray. -/
def lowerPiece : Set (W × ℝ) := {p | ¬(p.1 = 0 ∧ 0 ≤ p.2)}

omit [NormedSpace ℝ W] in
theorem upperPiece_eq : upperPiece W = {p : W × ℝ | p.1 ≠ 0} ∪ {p : W × ℝ | 0 < p.2} := by
  ext p
  simp only [upperPiece, Set.mem_setOf_eq, Set.mem_union, not_and, not_le]
  constructor
  · intro h
    by_cases h1 : p.1 = 0
    · exact Or.inr (h h1)
    · exact Or.inl h1
  · rintro (h1 | h2) hp1
    · exact absurd hp1 h1
    · exact h2

omit [NormedSpace ℝ W] in
theorem lowerPiece_eq : lowerPiece W = {p : W × ℝ | p.1 ≠ 0} ∪ {p : W × ℝ | p.2 < 0} := by
  ext p
  simp only [lowerPiece, Set.mem_setOf_eq, Set.mem_union, not_and, not_le]
  constructor
  · intro h
    by_cases h1 : p.1 = 0
    · exact Or.inr (h h1)
    · exact Or.inl h1
  · rintro (h1 | h2) hp1
    · exact absurd hp1 h1
    · exact h2

omit [NormedSpace ℝ W] in
theorem isOpen_upperPiece : IsOpen (upperPiece W) := by
  rw [upperPiece_eq]
  exact (isOpen_compl_singleton.preimage continuous_fst).union
    (isOpen_lt continuous_const continuous_snd)

omit [NormedSpace ℝ W] in
theorem isOpen_lowerPiece : IsOpen (lowerPiece W) := by
  rw [lowerPiece_eq]
  exact (isOpen_compl_singleton.preimage continuous_fst).union
    (isOpen_lt continuous_snd continuous_const)

theorem starConvex_upperPiece : StarConvex ℝ ((0 : W), (1 : ℝ)) (upperPiece W) := by
  rintro q hq a b ha hb hab hmem
  obtain ⟨h1, h2⟩ := hmem
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_zero, zero_add,
    smul_eq_mul, mul_one] at h1 h2
  rcases eq_or_lt_of_le hb with hb0 | hb0
  · rw [← hb0] at h1 h2 hab
    simp only [zero_mul, add_zero] at h2 hab
    rw [hab] at h2
    linarith
  · have hq1 : q.1 = 0 := by
      rcases smul_eq_zero.mp h1 with h | h
      · exact absurd h (ne_of_gt hb0)
      · exact h
    have hq2 : 0 < q.2 := by
      by_contra hle
      exact hq ⟨hq1, not_lt.mp hle⟩
    nlinarith

theorem starConvex_lowerPiece : StarConvex ℝ ((0 : W), (-1 : ℝ)) (lowerPiece W) := by
  rintro q hq a b ha hb hab hmem
  obtain ⟨h1, h2⟩ := hmem
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_zero, zero_add,
    smul_eq_mul, mul_neg, mul_one] at h1 h2
  rcases eq_or_lt_of_le hb with hb0 | hb0
  · rw [← hb0] at h1 h2 hab
    simp only [zero_mul, add_zero] at h2 hab
    rw [hab] at h2
    linarith
  · have hq1 : q.1 = 0 := by
      rcases smul_eq_zero.mp h1 with h | h
      · exact absurd h (ne_of_gt hb0)
      · exact h
    have hq2 : q.2 < 0 := by
      by_contra hle
      exact hq ⟨hq1, not_lt.mp hle⟩
    nlinarith

omit [NormedSpace ℝ W] in
theorem mem_upperPiece_center : ((0 : W), (1 : ℝ)) ∈ upperPiece W := by
  rintro ⟨-, h⟩
  linarith

omit [NormedSpace ℝ W] in
theorem mem_lowerPiece_center : ((0 : W), (-1 : ℝ)) ∈ lowerPiece W := by
  rintro ⟨-, h⟩
  linarith

omit [NormedSpace ℝ W] in
theorem union_pieces : upperPiece W ∪ lowerPiece W = punct (W × ℝ) := by
  ext p
  constructor
  · rintro (h | h) hp
    · exact h ⟨congrArg Prod.fst hp, le_of_eq (congrArg Prod.snd hp)⟩
    · exact h ⟨congrArg Prod.fst hp, ge_of_eq (congrArg Prod.snd hp)⟩
  · intro hp
    by_cases h1 : p.1 = 0
    · have h2 : p.2 ≠ 0 := by
        intro h2
        exact hp (Prod.ext h1 h2)
      rcases lt_or_gt_of_ne h2 with h | h
      · exact Or.inr (fun hc => absurd hc.2 (not_le.mpr h))
      · exact Or.inl (fun hc => absurd hc.2 (not_le.mpr h))
    · exact Or.inl (fun hc => h1 hc.1)

omit [NormedSpace ℝ W] in
theorem inter_pieces : upperPiece W ∩ lowerPiece W = {p : W × ℝ | p.1 ≠ 0} := by
  ext p
  constructor
  · rintro ⟨hu, hl⟩ h1
    rcases le_total p.2 0 with h | h
    · exact hu ⟨h1, h⟩
    · exact hl ⟨h1, h⟩
  · intro h
    exact ⟨fun hc => h hc.1, fun hc => h hc.1⟩

omit [NormedSpace ℝ W] in
/-- The intersection of the two pieces is the punctured factor times the line. -/
noncomputable def punctProdHomeomorph :
    ↥({p : W × ℝ | p.1 ≠ 0}) ≃ₜ ↥(punct W) × ℝ where
  toFun p := (⟨(p : W × ℝ).1, p.2⟩, (p : W × ℝ).2)
  invFun q := ⟨((q.1 : W), q.2), q.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun :=
    Continuous.prodMk (Continuous.subtype_mk (continuous_fst.comp continuous_subtype_val) _)
      (continuous_snd.comp continuous_subtype_val)
  continuous_invFun :=
    Continuous.subtype_mk
      (Continuous.prodMk (continuous_subtype_val.comp continuous_fst) continuous_snd) _

end GaloisForLFunctions.HTGeometry
