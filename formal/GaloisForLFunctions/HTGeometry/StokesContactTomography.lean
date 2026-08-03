import GaloisForLFunctions.HTGeometry.StokesContactProfile

/-!
# Strict contact tomography on finite rooted fission trees

Complementary contact is an antitone height of least common ancestors in a rooted tree.  This file
proves strict diagonal separation, acute-isosceles contact, canonical laminar threshold recovery,
uniqueness of the recovered labelled hierarchy, and the four-point law for polarized energy.
-/

namespace GaloisForLFunctions
namespace IrregularStokes

/-- In a predecessor-archimedean tree, a strictly lower meet of two branches is also the meet of
the two opposite branches. -/
lemma inf_eq_of_inf_lt_inf {T : Type*} [SemilatticeInf T] [PredOrder T]
    [IsPredArchimedean T] {x y z : T} (h : x ⊓ y < x ⊓ z) :
    y ⊓ z = x ⊓ y := by
  let a := x ⊓ y
  let b := x ⊓ z
  let c := y ⊓ z
  have hay : a ≤ y := by exact inf_le_right
  have hab : a ≤ b := h.le
  have hbz : b ≤ z := by exact inf_le_right
  have hac : a ≤ c := le_inf hay (hab.trans hbz)
  have hcy : c ≤ y := by exact inf_le_left
  have hcz : c ≤ z := by exact inf_le_right
  by_cases hacEq : a = c
  · exact hacEq.symm
  have haclt : a < c := lt_of_le_of_ne hac hacEq
  rcases lt_or_le_of_directed hbz hcz with hbc | hcb
  · have hbx : b ≤ x := by exact inf_le_left
    have hba : b ≤ a := le_inf hbx (hbc.le.trans hcy)
    exact False.elim ((not_le_of_gt h) hba)
  · have hcx : c ≤ x := hcb.trans inf_le_left
    have hca : c ≤ a := le_inf hcx hcy
    exact False.elim ((not_le_of_gt haclt) hca)

/-- Three values have their maximum at least twice. -/
def MaxTwice (a b c : ℝ) : Prop :=
  (a = b ∧ c ≤ a) ∨ (a = c ∧ b ≤ a) ∨ (b = c ∧ a ≤ b)

/-- Pairwise acute-isosceles inequalities are equivalent to a repeated maximum. -/
theorem maxTwice_iff_acute (a b c : ℝ) : MaxTwice a b c ↔
    a ≤ max b c ∧ b ≤ max a c ∧ c ≤ max a b := by
  constructor
  · rintro (⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩) <;> simp_all
  · rintro ⟨ha, hb, hc⟩
    rcases le_total a b with hab | hba
    · rcases le_total b c with hbc | hcb
      · have hca : c ≤ b := by simpa [max_eq_right hab] using hc
        exact Or.inr (Or.inr ⟨le_antisymm hbc hca, hab⟩)
      · rcases le_total a c with hac | hca
        · have hbc' : b ≤ c := by simpa [max_eq_right hac] using hb
          exact Or.inr (Or.inr ⟨le_antisymm hbc' hcb, hab⟩)
        · have hba' : b ≤ a := by simpa [max_eq_left hca] using hb
          exact Or.inl ⟨le_antisymm hab hba', hcb.trans hba'⟩
    · rcases le_total a c with hac | hca
      · have hcb : c ≤ a := by simpa [max_eq_left hba] using hc
        exact Or.inr (Or.inl ⟨le_antisymm hac hcb, hba⟩)
      · rcases le_total b c with hbc | hcb
        · have hac' : a ≤ c := by simpa [max_eq_right hbc] using ha
          exact Or.inr (Or.inl ⟨le_antisymm hac' hca, hba⟩)
        · have hab' : a ≤ b := by simpa [max_eq_left hcb] using ha
          exact Or.inl ⟨le_antisymm hab' hba, hca⟩

/-- Four compatible three-point repeated-maximum laws imply the four-point repeated-maximum law
for pair sums. -/
theorem four_sum_maxTwice {a b c d e f : ℝ}
    (habd : MaxTwice a b d) (hace : MaxTwice a c e)
    (hbcf : MaxTwice b c f) (hdef : MaxTwice d e f) :
    MaxTwice (a + f) (b + e) (c + d) := by
  simp only [MaxTwice] at *
  rcases habd with habd | habd | habd <;>
  rcases hace with hace | hace | hace <;>
  rcases hbcf with hbcf | hbcf | hbcf <;>
  rcases hdef with hdef | hdef | hdef <;>
  rcases habd with ⟨rfl, habd⟩ <;>
  rcases hace with ⟨hace, hace'⟩ <;>
  rcases hbcf with ⟨hbcf, hbcf'⟩ <;>
  rcases hdef with ⟨hdef, hdef'⟩ <;>
  subst_vars
  all_goals
    apply (maxTwice_iff_acute _ _ _).2
    constructor
    · rw [max_def]
      split <;> linarith
    · constructor
      · rw [max_def]
        split <;> linarith
      · rw [max_def]
        split <;> linarith

/-- A positive affine change of coordinate preserves repeated maxima. -/
theorem MaxTwice.positiveAffine {a b c p q : ℝ} (h : MaxTwice a b c) (hp : 0 < p) :
    MaxTwice (p * a + q) (p * b + q) (p * c + q) := by
  simp only [MaxTwice] at h ⊢
  rcases h with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩
  · exact Or.inl ⟨rfl, by nlinarith⟩
  · exact Or.inr (Or.inl ⟨rfl, by nlinarith⟩)
  · exact Or.inr (Or.inr ⟨rfl, by nlinarith⟩)

/-- Antitone height of a meet satisfies the acute-isosceles inequality. -/
lemma antitone_inf_le_max {T : Type*} [SemilatticeInf T] [PredOrder T]
    [IsPredArchimedean T] (kappa : T → ℝ) (hkappa : Antitone kappa)
    (x y z : T) :
    kappa (x ⊓ y) ≤ max (kappa (x ⊓ z)) (kappa (y ⊓ z)) := by
  rcases le_total_of_directed (inf_le_left : x ⊓ y ≤ x) (inf_le_left : x ⊓ z ≤ x) with h | h
  · exact (hkappa h).trans (le_max_left _ _)
  · by_cases heq : x ⊓ y = x ⊓ z
    · rw [heq]
      exact le_max_left _ _
    · have hlt : x ⊓ y < x ⊓ z := lt_of_le_of_ne h heq
      rw [inf_eq_of_inf_lt_inf hlt]
      exact le_max_right _ _

/-- Finite labelled leaf data in a rooted tree with strictly antitone complementary-contact
height.  Incomparability says distinct labels are genuine leaves of the represented skeleton. -/
structure RootedContactTree (n : ℕ) where
  tree : RootedTree
  leaf : Fin n → tree
  leaf_antichain : ∀ i j, i ≠ j → ¬ leaf i ≤ leaf j
  kappa : tree → ℝ
  kappa_strictAnti : StrictAnti kappa

namespace RootedContactTree

/-- Complementary contact is height at the least common ancestor. -/
def contact {n : ℕ} (t : RootedContactTree n) (i j : Fin n) : ℝ :=
  t.kappa (t.leaf i ⊓ t.leaf j)

theorem contact_symm {n : ℕ} (t : RootedContactTree n) (i j : Fin n) :
    t.contact i j = t.contact j i := by simp [contact, inf_comm]

/-- Strict leaf-to-meet separation. -/
theorem contact_diagonal_lt {n : ℕ} (t : RootedContactTree n) {i j : Fin n}
    (hij : i ≠ j) : t.contact i i < t.contact i j := by
  have hle : t.leaf i ⊓ t.leaf j ≤ t.leaf i := inf_le_left
  have hne : t.leaf i ⊓ t.leaf j ≠ t.leaf i := by
    intro h
    apply t.leaf_antichain i j hij
    rw [← h]
    exact inf_le_right
  have hlt : t.leaf i ⊓ t.leaf j < t.leaf i := lt_of_le_of_ne hle hne
  simpa [contact] using t.kappa_strictAnti hlt

/-- Complementary contacts satisfy the acute-isosceles inequality. -/
theorem contact_acute {n : ℕ} (t : RootedContactTree n) (i j k : Fin n) :
    t.contact i j ≤ max (t.contact i k) (t.contact j k) := by
  exact antitone_inf_le_max t.kappa t.kappa_strictAnti.antitone
    (t.leaf i) (t.leaf j) (t.leaf k)

/-- Every rooted contact triangle has its maximum at least twice. -/
theorem contact_maxTwice {n : ℕ} (t : RootedContactTree n) (i j k : Fin n) :
    MaxTwice (t.contact i j) (t.contact i k) (t.contact j k) := by
  apply (maxTwice_iff_acute _ _ _).2
  exact ⟨t.contact_acute i j k, by simpa [t.contact_symm] using t.contact_acute i k j,
    by simpa [t.contact_symm] using t.contact_acute j k i⟩

/-- Reflexive contact-threshold relation. -/
def thresholdRel {n : ℕ} (t : RootedContactTree n) (a : ℝ) (i j : Fin n) : Prop :=
  i = j ∨ t.contact i j ≤ a

/-- Canonical contact-threshold partition. -/
def thresholdSetoid {n : ℕ} (t : RootedContactTree n) (a : ℝ) : Setoid (Fin n) where
  r := t.thresholdRel a
  iseqv := {
    refl := fun i => Or.inl rfl
    symm := by
      intro i j h
      rcases h with rfl | h
      · exact Or.inl rfl
      · exact Or.inr (by simpa [t.contact_symm] using h)
    trans := by
      intro i j k hij hjk
      rcases hij with rfl | hij
      · exact hjk
      rcases hjk with rfl | hjk
      · exact Or.inr hij
      right
      exact (t.contact_acute i k j).trans (max_le hij (by simpa [t.contact_symm] using hjk)) }

/-- Threshold partitions coarsen monotonically. -/
theorem thresholdRel_mono {n : ℕ} (t : RootedContactTree n) {a b : ℝ} (hab : a ≤ b)
    {i j : Fin n} : t.thresholdRel a i j → t.thresholdRel b i j := by
  rintro (h | h)
  · exact Or.inl h
  · exact Or.inr (h.trans hab)

/-- Equivalence class of a leaf at contact threshold `a`. -/
def cluster {n : ℕ} (t : RootedContactTree n) (a : ℝ) (i : Fin n) : Set (Fin n) :=
  {j | t.thresholdRel a i j}

/-- Canonical labelled branching hierarchy reconstructed from all contact thresholds. -/
def hierarchy {n : ℕ} (t : RootedContactTree n) : Set (Set (Fin n)) :=
  {A | ∃ a i, A = t.cluster a i}

/-- The diagonal threshold recovers each labelled singleton leaf. -/
theorem cluster_at_diagonal {n : ℕ} (t : RootedContactTree n) (i : Fin n) :
    t.cluster (t.contact i i) i = {i} := by
  ext j
  simp only [cluster, Set.mem_setOf_eq, thresholdRel, Set.mem_singleton_iff]
  constructor
  · rintro (rfl | h)
    · rfl
    · by_contra hne
      exact (not_le_of_gt (t.contact_diagonal_lt (Ne.symm hne))) h
  · intro h
    exact Or.inl h.symm

/-- Intersecting classes at an earlier threshold refine classes at a later threshold. -/
theorem cluster_subset_of_le_of_common {n : ℕ} (t : RootedContactTree n)
    {a b : ℝ} (hab : a ≤ b) {i j x : Fin n}
    (hxi : x ∈ t.cluster a i) (hxj : x ∈ t.cluster b j) :
    t.cluster a i ⊆ t.cluster b j := by
  intro y hyi
  let sa := t.thresholdSetoid a
  let sb := t.thresholdSetoid b
  have hyxA : sa.r y x := sa.iseqv.trans (sa.iseqv.symm hyi) hxi
  have hyxB : sb.r y x := t.thresholdRel_mono hab hyxA
  have hxjB : sb.r x j := sb.iseqv.symm hxj
  exact sb.iseqv.symm (@Equivalence.trans _ sb.r sb.iseqv y x j hyxB hxjB)

/-- Any two contact-threshold clusters are nested or disjoint. -/
theorem clusters_laminar {n : ℕ} (t : RootedContactTree n)
    (a b : ℝ) (i j : Fin n) :
    t.cluster a i ⊆ t.cluster b j ∨ t.cluster b j ⊆ t.cluster a i ∨
      Disjoint (t.cluster a i) (t.cluster b j) := by
  rcases le_total a b with hab | hba
  · by_cases hd : Disjoint (t.cluster a i) (t.cluster b j)
    · exact Or.inr (Or.inr hd)
    · obtain ⟨x, hxi, hxj⟩ := Set.not_disjoint_iff.mp hd
      exact Or.inl (t.cluster_subset_of_le_of_common hab hxi hxj)
  · by_cases hd : Disjoint (t.cluster a i) (t.cluster b j)
    · exact Or.inr (Or.inr hd)
    · obtain ⟨x, hxi, hxj⟩ := Set.not_disjoint_iff.mp hd
      exact Or.inr (Or.inl (t.cluster_subset_of_le_of_common hba hxj hxi))

/-- The reconstructed threshold hierarchy is laminar. -/
theorem hierarchy_laminar {n : ℕ} (t : RootedContactTree n) {A B : Set (Fin n)}
    (hA : A ∈ t.hierarchy) (hB : B ∈ t.hierarchy) :
    A ⊆ B ∨ B ⊆ A ∨ Disjoint A B := by
  obtain ⟨a, i, rfl⟩ := hA
  obtain ⟨b, j, rfl⟩ := hB
  exact t.clusters_laminar a b i j

/-- Contact matrix uniquely determines the labelled threshold hierarchy. -/
theorem hierarchy_eq_of_contact_eq {n : ℕ} (s t : RootedContactTree n)
    (hcontact : ∀ i j, s.contact i j = t.contact i j) : s.hierarchy = t.hierarchy := by
  have hrel : ∀ a i j, s.thresholdRel a i j ↔ t.thresholdRel a i j := by
    intro a i j
    simp only [thresholdRel, hcontact]
  have hcluster : ∀ a i, s.cluster a i = t.cluster a i := by
    intro a i
    ext j
    exact hrel a i j
  ext A
  simp only [hierarchy, Set.mem_setOf_eq]
  constructor
  · rintro ⟨a, i, rfl⟩
    exact ⟨a, i, hcluster a i⟩
  · rintro ⟨a, i, rfl⟩
    exact ⟨a, i, (hcluster a i).symm⟩

/-- Polarized complementary-contact energy. -/
def energy {n : ℕ} (t : RootedContactTree n) (i j : Fin n) : ℝ :=
  2 * t.contact i j - t.contact i i - t.contact j j

/-- Four-point tree law: among the three energy pair sums, the maximum occurs at least twice. -/
theorem energy_fourPoint {n : ℕ} (t : RootedContactTree n) (i j k l : Fin n) :
    MaxTwice (t.energy i j + t.energy k l)
      (t.energy i k + t.energy j l) (t.energy i l + t.energy j k) := by
  have hcontact := four_sum_maxTwice (t.contact_maxTwice i j k)
    (t.contact_maxTwice i j l) (t.contact_maxTwice i k l)
    (t.contact_maxTwice j k l)
  have h := hcontact.positiveAffine (p := 2)
    (q := -(t.contact i i + t.contact j j + t.contact k k + t.contact l l)) (by norm_num)
  convert h using 1 <;> simp only [energy] <;> ring

end RootedContactTree

end IrregularStokes
end GaloisForLFunctions
