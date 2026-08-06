import GaloisForLFunctions.HTGeometry.StokesContactRealization

/-!
# Threshold equivalence classes of a contact matrix

The direct reconstruction of the branching skeleton from the contact matrix reads the matrix at a
threshold: two labels are related at level `a` when their complementary contact does not exceed
`a`, with the diagonal always related to itself.  The acute inequality makes this an equivalence
relation, its classes grow with the threshold, and the whole family across thresholds is laminar.

Every nonsingleton class is a contact ball, so the nonsingleton threshold classes are exactly the
clusters of the reconstructed skeleton, and conversely every cluster occurs as a threshold class.
-/

namespace GaloisForLFunctions
namespace IrregularStokes

namespace ContactMatrix

variable {n : ℕ} (κ : ContactMatrix n)

/-- Two labels are related at threshold `a` when their complementary contact does not exceed `a`;
the diagonal is related to itself at every threshold. -/
def ThresholdRel (a : ℝ) (i j : Fin n) : Prop := i = j ∨ κ.val i j ≤ a

theorem thresholdRel_refl (a : ℝ) (i : Fin n) : κ.ThresholdRel a i i := Or.inl rfl

theorem thresholdRel_symm {a : ℝ} {i j : Fin n} (h : κ.ThresholdRel a i j) :
    κ.ThresholdRel a j i := by
  rcases h with h | h
  · exact Or.inl h.symm
  · exact Or.inr (by rw [κ.val_symm]; exact h)

/-- **The acute inequality makes the threshold relation transitive.** -/
theorem thresholdRel_trans {a : ℝ} {i j k : Fin n} (hij : κ.ThresholdRel a i j)
    (hjk : κ.ThresholdRel a j k) : κ.ThresholdRel a i k := by
  rcases hij with rfl | hij
  · exact hjk
  rcases hjk with rfl | hjk
  · exact Or.inr hij
  refine Or.inr (le_trans (κ.val_acute i k j) ?_)
  refine max_le hij ?_
  rw [κ.val_symm k j]
  exact hjk

/-- The threshold equivalence of a contact matrix. -/
def thresholdSetoid (a : ℝ) : Setoid (Fin n) where
  r := κ.ThresholdRel a
  iseqv :=
    { refl := κ.thresholdRel_refl a
      symm := κ.thresholdRel_symm
      trans := κ.thresholdRel_trans }

/-- The threshold class of a label: its contact ball together with the label itself. -/
noncomputable def thresholdClass (a : ℝ) (i : Fin n) : Finset (Fin n) :=
  insert i (κ.ball i a)

@[simp] theorem mem_thresholdClass {a : ℝ} {i j : Fin n} :
    j ∈ κ.thresholdClass a i ↔ κ.ThresholdRel a i j := by
  simp only [thresholdClass, Finset.mem_insert, mem_ball, ThresholdRel]
  constructor
  · rintro (rfl | h)
    · exact Or.inl rfl
    · exact Or.inr h
  · rintro (rfl | h)
    · exact Or.inl rfl
    · exact Or.inr h

theorem self_mem_thresholdClass (a : ℝ) (i : Fin n) : i ∈ κ.thresholdClass a i :=
  Finset.mem_insert_self _ _

/-- **Threshold classes grow with the threshold.** -/
theorem thresholdClass_mono {a b : ℝ} (hab : a ≤ b) (i : Fin n) :
    κ.thresholdClass a i ⊆ κ.thresholdClass b i := by
  intro p hp
  rw [mem_thresholdClass] at hp ⊢
  rcases hp with rfl | hp
  · exact Or.inl rfl
  · exact Or.inr (le_trans hp hab)

/-- Members of a threshold class carry the same class. -/
theorem thresholdClass_eq_of_mem {a : ℝ} {i j : Fin n} (h : j ∈ κ.thresholdClass a i) :
    κ.thresholdClass a j = κ.thresholdClass a i := by
  rw [mem_thresholdClass] at h
  ext p
  rw [mem_thresholdClass, mem_thresholdClass]
  constructor
  · exact fun hp => κ.thresholdRel_trans h hp
  · exact fun hp => κ.thresholdRel_trans (κ.thresholdRel_symm h) hp

/-- Two classes at one threshold are equal or disjoint. -/
theorem thresholdClass_eq_or_disjoint (a : ℝ) (i j : Fin n) :
    κ.thresholdClass a i = κ.thresholdClass a j ∨
      Disjoint (κ.thresholdClass a i) (κ.thresholdClass a j) := by
  by_cases h : (κ.thresholdClass a i ∩ κ.thresholdClass a j).Nonempty
  · obtain ⟨p, hp⟩ := h
    rw [Finset.mem_inter] at hp
    refine Or.inl ?_
    rw [← κ.thresholdClass_eq_of_mem hp.1, ← κ.thresholdClass_eq_of_mem hp.2]
  · exact Or.inr (Finset.disjoint_iff_inter_eq_empty.mpr (Finset.not_nonempty_iff_eq_empty.mp h))

/-- **The threshold family is laminar.**  Across thresholds, two classes are nested or disjoint. -/
theorem thresholdClass_laminar {a b : ℝ} (hab : a ≤ b) (i j : Fin n) :
    κ.thresholdClass a i ⊆ κ.thresholdClass b j ∨
      Disjoint (κ.thresholdClass a i) (κ.thresholdClass b j) := by
  by_cases h : (κ.thresholdClass a i ∩ κ.thresholdClass b j).Nonempty
  · obtain ⟨p, hp⟩ := h
    rw [Finset.mem_inter] at hp
    refine Or.inl ?_
    calc κ.thresholdClass a i = κ.thresholdClass a p := (κ.thresholdClass_eq_of_mem hp.1).symm
      _ ⊆ κ.thresholdClass b p := κ.thresholdClass_mono hab p
      _ = κ.thresholdClass b j := κ.thresholdClass_eq_of_mem hp.2
  · exact Or.inr (Finset.disjoint_iff_inter_eq_empty.mpr (Finset.not_nonempty_iff_eq_empty.mp h))

/-- Below the diagonal value a label is alone in its class. -/
theorem thresholdClass_eq_singleton {a : ℝ} {i : Fin n} (h : a < κ.val i i) :
    κ.thresholdClass a i = {i} := by
  ext p
  rw [mem_thresholdClass, Finset.mem_singleton]
  constructor
  · rintro (rfl | hp)
    · rfl
    · exact absurd (lt_of_le_of_lt (le_trans (κ.val_self_le i p) hp) h) (lt_irrefl _)
  · rintro rfl
    exact Or.inl rfl

/-- **Every nonsingleton threshold class is a contact ball**, hence a vertex of the reconstructed
skeleton: the ball of the farthest member of the class. -/
theorem isCluster_thresholdClass {a : ℝ} {i : Fin n} (h : 1 < (κ.thresholdClass a i).card) :
    κ.IsCluster (κ.thresholdClass a i) := by
  classical
  have hne : ((κ.thresholdClass a i).erase i).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem (κ.self_mem_thresholdClass a i)]
    omega
  obtain ⟨j, hjmem, hjmax⟩ :=
    Finset.exists_max_image ((κ.thresholdClass a i).erase i) (fun p => κ.val i p) hne
  have hj : j ∈ κ.thresholdClass a i := Finset.mem_of_mem_erase hjmem
  have hjne : j ≠ i := Finset.ne_of_mem_erase hjmem
  have hja : κ.val i j ≤ a := by
    rw [mem_thresholdClass] at hj
    rcases hj with rfl | hj
    · exact absurd rfl hjne
    · exact hj
  refine ⟨i, j, ?_⟩
  ext p
  rw [mem_thresholdClass, mem_ball]
  constructor
  · rintro (rfl | hp)
    · exact κ.val_self_le i j
    · by_cases hpi : p = i
      · subst hpi
        exact κ.val_self_le p j
      · exact hjmax p (Finset.mem_erase.mpr ⟨hpi, by rw [mem_thresholdClass]; exact Or.inr hp⟩)
  · intro hp
    exact Or.inr (le_trans hp hja)

/-- **Every contact ball occurs as a threshold class.**  Reading the matrix at the off-diagonal
value `K_ij` returns exactly the cluster of that value. -/
theorem thresholdClass_val_eq_ball (i j : Fin n) :
    κ.thresholdClass (κ.val i j) i = κ.ball i (κ.val i j) := by
  ext p
  rw [mem_thresholdClass, mem_ball]
  constructor
  · rintro (rfl | hp)
    · exact κ.val_self_le i j
    · exact hp
  · exact fun hp => Or.inr hp

end ContactMatrix

end IrregularStokes
end GaloisForLFunctions
