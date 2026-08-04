import GaloisForLFunctions.HTGeometry.StokesFinitePuiseuxDendrogram

namespace GaloisForLFunctions.IrregularStokes.NatContactDendrogram

noncomputable section

variable {m K N : ℕ}

/-- Branch set of one class in one canonical threshold partition. -/
def thresholdBlock (d : NatContactDendrogram m K N) (t : Fin (K + 1))
    (c : Quotient (d.thresholdSetoid t)) : Set (Fin m) :=
  {i | d.thresholdClass t i = c}

@[simp]
theorem mem_thresholdBlock_iff (d : NatContactDendrogram m K N)
    (t : Fin (K + 1)) (c : Quotient (d.thresholdSetoid t)) (i : Fin m) :
    i ∈ d.thresholdBlock t c ↔ d.thresholdClass t i = c := Iff.rfl

/-- A threshold block can only grow as threshold increases. -/
theorem thresholdBlock_mono (d : NatContactDendrogram m K N)
    {t u : Fin (K + 1)} (htu : t.val ≤ u.val) (i : Fin m) :
    d.thresholdBlock t (d.thresholdClass t i) ⊆
      d.thresholdBlock u (d.thresholdClass u i) := by
  intro j hj
  have htcontact : d.contactNumerator j i < t.val + 1 :=
    (d.thresholdClass_eq_iff t j i).mp hj
  apply (d.thresholdClass_eq_iff u j i).mpr
  omega

/-- Blocks from any two threshold levels are nested or disjoint.  This is the laminarity axiom
that makes the finite hierarchy a dendrogram. -/
theorem thresholdBlock_pair_laminar (d : NatContactDendrogram m K N)
    (t u : Fin (K + 1)) (c : Quotient (d.thresholdSetoid t))
    (e : Quotient (d.thresholdSetoid u)) :
    d.thresholdBlock t c ⊆ d.thresholdBlock u e ∨
      d.thresholdBlock u e ⊆ d.thresholdBlock t c ∨
      Disjoint (d.thresholdBlock t c) (d.thresholdBlock u e) := by
  by_cases htu : t.val ≤ u.val
  · by_cases hinter : (d.thresholdBlock t c ∩ d.thresholdBlock u e).Nonempty
    · left
      obtain ⟨i, hit, hiu⟩ := hinter
      intro j hj
      have hji_t : d.thresholdClass t j = d.thresholdClass t i := hj.trans hit.symm
      have hji_u : d.thresholdClass u j = d.thresholdClass u i :=
        d.thresholdBlock_mono htu i hji_t
      exact hji_u.trans hiu
    · right
      right
      apply Set.disjoint_left.2
      intro i hit hiu
      exact hinter ⟨i, hit, hiu⟩
  · have hut : u.val ≤ t.val := by omega
    by_cases hinter : (d.thresholdBlock t c ∩ d.thresholdBlock u e).Nonempty
    · right
      left
      obtain ⟨i, hit, hiu⟩ := hinter
      intro j hj
      have hji_u : d.thresholdClass u j = d.thresholdClass u i := hj.trans hiu.symm
      have hji_t : d.thresholdClass t j = d.thresholdClass t i :=
        d.thresholdBlock_mono hut i hji_u
      exact hji_t.trans hit
    · right
      right
      apply Set.disjoint_left.2
      intro i hit hiu
      exact hinter ⟨i, hit, hiu⟩

/-- Top threshold is the unique root block containing every branch. -/
theorem top_thresholdBlock_eq_univ (d : NatContactDendrogram m K N) (i : Fin m) :
    d.thresholdBlock ⟨K, by omega⟩
      (d.thresholdClass ⟨K, by omega⟩ i) = Set.univ := by
  ext j
  simp only [mem_thresholdBlock_iff, Set.mem_univ, iff_true]
  apply (d.thresholdClass_eq_iff ⟨K, by omega⟩ j i).mpr
  have := d.contact_le j i
  change d.contactNumerator j i < K + 1
  omega

/-- Threshold zero blocks are exactly the singleton leaves. -/
theorem zero_thresholdBlock_eq_singleton (d : NatContactDendrogram m K N) (i : Fin m) :
    d.thresholdBlock 0 (d.thresholdClass 0 i) = {i} := by
  ext j
  simp only [mem_thresholdBlock_iff, Set.mem_singleton_iff]
  constructor
  · intro hclass
    have hlt := (d.thresholdClass_eq_iff 0 j i).mp hclass
    have hlt' : d.contactNumerator j i < 1 := by simpa using hlt
    by_contra hne
    have hpos := d.contact_pos_of_ne hne
    omega
  · rintro rfl
    rfl

/-- First threshold at which two branches share a block. -/
def birthThreshold (d : NatContactDendrogram m K N) (i j : Fin m) : Fin (K + 1) :=
  ⟨d.contactNumerator i j, Nat.lt_succ_of_le (d.contact_le i j)⟩

/-- Two labels are together at their birth threshold. -/
theorem thresholdClass_birth_eq (d : NatContactDendrogram m K N) (i j : Fin m) :
    d.thresholdClass (d.birthThreshold i j) i =
      d.thresholdClass (d.birthThreshold i j) j := by
  apply (d.thresholdClass_eq_iff (d.birthThreshold i j) i j).mpr
  simp [birthThreshold]

/-- No earlier threshold contains both labels: equality of threshold classes forces the birth
level to be no larger than the given level. -/
theorem birthThreshold_le_of_thresholdClass_eq (d : NatContactDendrogram m K N)
    (t : Fin (K + 1)) (i j : Fin m)
    (hclass : d.thresholdClass t i = d.thresholdClass t j) :
    (d.birthThreshold i j).val ≤ t.val := by
  have hlt := (d.thresholdClass_eq_iff t i j).mp hclass
  simp only [birthThreshold]
  omega

/-- Dependency-closed canonical dendrogram theorem: finite threshold blocks form a laminar rooted
hierarchy with singleton leaves, and pairwise birth is exactly highest-difference contact. -/
theorem canonicalDendrogramHierarchy (d : NatContactDendrogram m K N) :
    (∀ t u c e,
      d.thresholdBlock t c ⊆ d.thresholdBlock u e ∨
        d.thresholdBlock u e ⊆ d.thresholdBlock t c ∨
        Disjoint (d.thresholdBlock t c) (d.thresholdBlock u e)) ∧
    (∀ i, d.thresholdBlock ⟨K, by omega⟩
      (d.thresholdClass ⟨K, by omega⟩ i) = Set.univ) ∧
    (∀ i, d.thresholdBlock 0 (d.thresholdClass 0 i) = {i}) ∧
    (∀ i j,
      d.thresholdClass (d.birthThreshold i j) i =
        d.thresholdClass (d.birthThreshold i j) j ∧
      ∀ t, d.thresholdClass t i = d.thresholdClass t j →
        (d.birthThreshold i j).val ≤ t.val) := by
  exact ⟨d.thresholdBlock_pair_laminar, d.top_thresholdBlock_eq_univ,
    d.zero_thresholdBlock_eq_singleton,
    fun i j ↦ ⟨d.thresholdClass_birth_eq i j,
      fun t h ↦ d.birthThreshold_le_of_thresholdClass_eq t i j h⟩⟩

end

end GaloisForLFunctions.IrregularStokes.NatContactDendrogram
