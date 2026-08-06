import GaloisForLFunctions.HTGeometry.StokesDecoratedCore

/-!
# Rooted realization of acute contact matrices

A finite symmetric matrix that is acute-isosceles and strictly separates its diagonal is exactly
the complementary-contact matrix of a rooted skeleton.  The skeleton is reconstructed from the
matrix itself: vertices are the contact balls, the order is reverse inclusion, the meet of two
vertices is the smallest ball containing both, the parent is the smallest strictly larger ball,
and the height of a vertex is its contact diameter.

Consequently the strict tomography, four-point and negative-type laws for decorated Stokes cores
are not vacuous: a decorated core admits a rooted realization exactly when its rescaled contact
matrix is acute and its integral diagonal obstruction is strict.
-/

namespace GaloisForLFunctions
namespace IrregularStokes

/-- A finite symmetric contact matrix which is acute-isosceles and strictly separates its
diagonal. -/
structure ContactMatrix (n : ℕ) where
  /-- Complementary contact of a pair of labels. -/
  val : Fin n → Fin n → ℝ
  val_symm : ∀ i j, val i j = val j i
  val_acute : ∀ i j k, val i j ≤ max (val i k) (val j k)
  val_diagonal_lt : ∀ {i j}, i ≠ j → val i i < val i j

namespace ContactMatrix

variable {n : ℕ} (κ : ContactMatrix n)

/-- The contact ball of radius `a` around `i`. -/
noncomputable def ball (i : Fin n) (a : ℝ) : Finset (Fin n) :=
  Finset.univ.filter fun p => κ.val i p ≤ a

@[simp] theorem mem_ball {i p : Fin n} {a : ℝ} : p ∈ κ.ball i a ↔ κ.val i p ≤ a := by
  simp [ball]

/-- The diagonal is the smallest contact from any label. -/
theorem val_self_le (i j : Fin n) : κ.val i i ≤ κ.val i j := by
  by_cases h : i = j
  · subst h; exact le_rfl
  · exact (κ.val_diagonal_lt h).le

theorem self_mem_ball (i j : Fin n) : i ∈ κ.ball i (κ.val i j) := by
  simp [κ.val_self_le i j]

/-- Every point of a contact ball is a centre of it. -/
theorem ball_eq_ball_of_le {i p : Fin n} {a : ℝ} (h : κ.val i p ≤ a) :
    κ.ball i a = κ.ball p a := by
  ext q
  simp only [mem_ball]
  constructor
  · intro hq
    refine (κ.val_acute p q i).trans (max_le ?_ ?_)
    · rw [κ.val_symm p i]; exact h
    · rw [κ.val_symm q i]; exact hq
  · intro hq
    refine (κ.val_acute i q p).trans (max_le h ?_)
    · rw [κ.val_symm q p]; exact hq

/-- Strict diagonal separation makes each singleton a contact ball. -/
theorem singleton_eq_ball (i : Fin n) : ({i} : Finset (Fin n)) = κ.ball i (κ.val i i) := by
  ext p
  simp only [Finset.mem_singleton, mem_ball]
  constructor
  · rintro rfl; exact le_rfl
  · intro hp
    by_contra hpi
    exact absurd hp (not_le_of_gt (κ.val_diagonal_lt (Ne.symm hpi)))

/-- Common-truncation clusters: the contact balls whose radius is an actual contact value. -/
def IsCluster (S : Finset (Fin n)) : Prop := ∃ i j, S = κ.ball i (κ.val i j)

/-- A vertex of the common-truncation skeleton. -/
@[ext] structure Vtx (c : ContactMatrix n) where
  /-- The set of labels descending from the vertex. -/
  set : Finset (Fin n)
  isCluster : c.IsCluster set

noncomputable instance : DecidableEq κ.Vtx := Classical.decEq _

noncomputable instance : Fintype κ.Vtx :=
  Fintype.ofInjective (fun S : κ.Vtx => S.set) (fun _ _ h => Vtx.ext h)

/-- Every cluster contains its centre. -/
theorem Vtx.nonempty (S : κ.Vtx) : S.set.Nonempty := by
  obtain ⟨i, j, hij⟩ := S.isCluster
  exact ⟨i, by rw [hij]; exact κ.self_mem_ball i j⟩

/-- Radius of a cluster measured from one of its points. -/
noncomputable def rad (S : κ.Vtx) (i : Fin n) : ℝ :=
  S.set.sup' (S.nonempty) fun p => κ.val i p

theorem le_rad {S : κ.Vtx} {i p : Fin n} (hp : p ∈ S.set) : κ.val i p ≤ κ.rad S i :=
  Finset.le_sup' _ hp

theorem rad_le {S : κ.Vtx} {i : Fin n} {a : ℝ} (h : ∀ p ∈ S.set, κ.val i p ≤ a) :
    κ.rad S i ≤ a :=
  Finset.sup'_le _ _ h

/-- A cluster is the contact ball of its own radius around any of its points. -/
theorem set_eq_ball_rad (S : κ.Vtx) {i : Fin n} (hi : i ∈ S.set) :
    S.set = κ.ball i (κ.rad S i) := by
  obtain ⟨c, d, hcd⟩ := S.isCluster
  have hci : κ.val c i ≤ κ.val c d := by
    have : i ∈ κ.ball c (κ.val c d) := by rw [← hcd]; exact hi
    simpa using this
  have hset : S.set = κ.ball i (κ.val c d) := by
    rw [hcd, κ.ball_eq_ball_of_le hci]
  have hradle : κ.rad S i ≤ κ.val c d := by
    refine κ.rad_le ?_
    intro p hp
    rw [hset] at hp
    simpa using hp
  apply Finset.Subset.antisymm
  · intro p hp
    simpa using κ.le_rad hp
  · intro p hp
    rw [hset]
    simp only [mem_ball] at hp ⊢
    exact hp.trans hradle

/-- Contact diameter of a cluster. -/
noncomputable def kappaV (S : κ.Vtx) : ℝ :=
  S.set.sup' (S.nonempty) fun p => S.set.sup' (S.nonempty) fun q => κ.val p q

/-- The contact diameter is the radius measured from any point of the cluster. -/
theorem kappaV_eq_rad {S : κ.Vtx} {i : Fin n} (hi : i ∈ S.set) :
    κ.kappaV S = κ.rad S i := by
  apply le_antisymm
  · refine Finset.sup'_le _ _ ?_
    intro p hp
    refine Finset.sup'_le _ _ ?_
    intro q hq
    refine (κ.val_acute p q i).trans (max_le ?_ ?_)
    · rw [κ.val_symm p i]; exact κ.le_rad hp
    · rw [κ.val_symm q i]; exact κ.le_rad hq
  · refine κ.rad_le ?_
    intro q hq
    refine le_trans ?_ (Finset.le_sup' (s := S.set)
      (fun p => S.set.sup' (S.nonempty) fun q => κ.val p q) hi)
    exact Finset.le_sup' (s := S.set) (fun q => κ.val i q) hq

/-- Skeleton order: a vertex is below another exactly when it carries more labels. -/
instance : PartialOrder κ.Vtx where
  le S T := T.set ⊆ S.set
  le_refl _ := Finset.Subset.refl _
  le_trans _ _ _ hab hbc := hbc.trans hab
  le_antisymm _ _ hab hba := Vtx.ext (Finset.Subset.antisymm hba hab)

theorem le_iff_subset {S T : κ.Vtx} : S ≤ T ↔ T.set ⊆ S.set := Iff.rfl

theorem lt_iff {S T : κ.Vtx} : S < T ↔ T.set ⊆ S.set ∧ ¬ S.set ⊆ T.set := Iff.rfl

instance : DecidableRel (fun S T : κ.Vtx => S ≤ T) :=
  fun S T => inferInstanceAs (Decidable (T.set ⊆ S.set))

instance : DecidableRel (fun S T : κ.Vtx => S < T) :=
  fun S T => inferInstanceAs (Decidable (T.set ⊆ S.set ∧ ¬ S.set ⊆ T.set))

/-- Two clusters meeting in a common label are nested. -/
theorem set_subset_or_subset (S T : κ.Vtx) {p : Fin n} (hS : p ∈ S.set) (hT : p ∈ T.set) :
    S.set ⊆ T.set ∨ T.set ⊆ S.set := by
  have hSb := κ.set_eq_ball_rad S hS
  have hTb := κ.set_eq_ball_rad T hT
  rcases le_total (κ.rad S p) (κ.rad T p) with h | h
  · left
    intro q hq
    rw [hTb]
    rw [hSb] at hq
    simp only [mem_ball] at hq ⊢
    exact hq.trans h
  · right
    intro q hq
    rw [hSb]
    rw [hTb] at hq
    simp only [mem_ball] at hq ⊢
    exact hq.trans h

/-- A distinguished point of a cluster. -/
noncomputable def centre (S : κ.Vtx) : Fin n := (S.nonempty).choose

theorem centre_mem (S : κ.Vtx) : κ.centre S ∈ S.set := (S.nonempty).choose_spec

theorem union_nonempty (S T : κ.Vtx) : (S.set ∪ T.set).Nonempty :=
  Finset.union_nonempty.mpr (Or.inl (S.nonempty))

/-- Radius of the smallest cluster containing two vertices. -/
noncomputable def meetRadius (S T : κ.Vtx) : ℝ :=
  (S.set ∪ T.set).sup' (κ.union_nonempty S T) fun p => κ.val (κ.centre S) p

/-- The smallest cluster containing two vertices. -/
noncomputable def meet (S T : κ.Vtx) : κ.Vtx where
  set := κ.ball (κ.centre S) (κ.meetRadius S T)
  isCluster := by
    obtain ⟨p, _, hp⟩ := Finset.exists_mem_eq_sup' (κ.union_nonempty S T)
      fun p => κ.val (κ.centre S) p
    exact ⟨κ.centre S, p, by rw [meetRadius, hp]⟩

theorem meet_le_left (S T : κ.Vtx) : κ.meet S T ≤ S := by
  intro p hp
  simp only [meet, mem_ball]
  exact Finset.le_sup' _ (Finset.mem_union_left _ hp)

theorem meet_le_right (S T : κ.Vtx) : κ.meet S T ≤ T := by
  intro p hp
  simp only [meet, mem_ball]
  exact Finset.le_sup' _ (Finset.mem_union_right _ hp)

theorem le_meet {U S T : κ.Vtx} (hS : U ≤ S) (hT : U ≤ T) : U ≤ κ.meet S T := by
  have hcentre : κ.centre S ∈ U.set := hS (κ.centre_mem S)
  have hU := κ.set_eq_ball_rad U hcentre
  intro p hp
  simp only [meet, mem_ball] at hp
  have hrad : κ.meetRadius S T ≤ κ.rad U (κ.centre S) := by
    refine Finset.sup'_le _ _ ?_
    intro q hq
    rcases Finset.mem_union.mp hq with hq | hq
    · exact κ.le_rad (hS hq)
    · exact κ.le_rad (hT hq)
  rw [hU]
  simp only [mem_ball]
  exact hp.trans hrad

noncomputable instance : SemilatticeInf κ.Vtx :=
  { (inferInstance : PartialOrder κ.Vtx) with
    inf := κ.meet
    inf_le_left := fun S T => κ.meet_le_left S T
    inf_le_right := fun S T => κ.meet_le_right S T
    le_inf := fun _ _ _ hS hT => κ.le_meet hS hT }

theorem inf_def (S T : κ.Vtx) : S ⊓ T = κ.meet S T := rfl

/-- The full label set is a cluster; it is the root of the skeleton. -/
theorem isCluster_univ [NeZero n] : κ.IsCluster (Finset.univ : Finset (Fin n)) := by
  obtain ⟨p, _, hp⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := Fin n))
    fun p => κ.val default p
  refine ⟨default, p, ?_⟩
  apply Finset.Subset.antisymm
  · intro q _
    simp only [mem_ball, ← hp]
    exact Finset.le_sup' _ (Finset.mem_univ q)
  · exact Finset.subset_univ _

noncomputable instance [NeZero n] : OrderBot κ.Vtx where
  bot := ⟨Finset.univ, κ.isCluster_univ⟩
  bot_le _ := Finset.subset_univ _

theorem bot_set [NeZero n] : (⊥ : κ.Vtx).set = Finset.univ := rfl

/-- Clusters strictly closer to the root. -/
noncomputable def strictParents (S : κ.Vtx) : Finset κ.Vtx :=
  Finset.univ.filter fun C => C < S

@[simp] theorem mem_strictParents {S C : κ.Vtx} : C ∈ κ.strictParents S ↔ C < S := by
  simp [strictParents]

/-- The parent of a vertex: the smallest cluster strictly containing it. -/
noncomputable def parent (S : κ.Vtx) : κ.Vtx :=
  if h : (κ.strictParents S).Nonempty then
    (Finset.exists_min_image (κ.strictParents S) (fun C => C.set.card) h).choose
  else S

theorem parent_mem {S : κ.Vtx} (h : (κ.strictParents S).Nonempty) :
    κ.parent S ∈ κ.strictParents S := by
  rw [parent, dif_pos h]
  exact (Finset.exists_min_image (κ.strictParents S) (fun C => C.set.card) h).choose_spec.1

theorem parent_card_le {S : κ.Vtx} (h : (κ.strictParents S).Nonempty)
    {C : κ.Vtx} (hC : C < S) : (κ.parent S).set.card ≤ C.set.card := by
  rw [parent, dif_pos h]
  exact (Finset.exists_min_image (κ.strictParents S) (fun C => C.set.card) h).choose_spec.2 C
    (κ.mem_strictParents.mpr hC)

theorem parent_lt {S : κ.Vtx} (h : (κ.strictParents S).Nonempty) : κ.parent S < S :=
  κ.mem_strictParents.mp (κ.parent_mem h)

theorem parent_le (S : κ.Vtx) : κ.parent S ≤ S := by
  by_cases h : (κ.strictParents S).Nonempty
  · exact (κ.parent_lt h).le
  · rw [parent, dif_neg h]

theorem isMin_of_strictParents_empty {S : κ.Vtx} (h : ¬ (κ.strictParents S).Nonempty) :
    IsMin S := by
  intro C hC
  by_contra hSC
  exact h ⟨C, κ.mem_strictParents.mpr (lt_of_le_of_ne hC (by rintro rfl; exact hSC le_rfl))⟩

theorem le_parent_of_lt {a b : κ.Vtx} (h : a < b) : a ≤ κ.parent b := by
  have hne : (κ.strictParents b).Nonempty := ⟨a, κ.mem_strictParents.mpr h⟩
  have hpar := κ.parent_lt hne
  obtain ⟨p, hp⟩ := b.nonempty
  have hpa : p ∈ a.set := h.le hp
  have hpp : p ∈ (κ.parent b).set := hpar.le hp
  rcases κ.set_subset_or_subset a (κ.parent b) hpa hpp with hsub | hsub
  · have hcard : (κ.parent b).set.card ≤ a.set.card := κ.parent_card_le hne h
    have : a.set = (κ.parent b).set := Finset.eq_of_subset_of_card_le hsub hcard
    exact le_of_eq (Vtx.ext this)
  · exact hsub

noncomputable instance : PredOrder κ.Vtx where
  pred := κ.parent
  pred_le := κ.parent_le
  min_of_le_pred := by
    intro a h
    by_cases hne : (κ.strictParents a).Nonempty
    · exact absurd (lt_of_le_of_lt h (κ.parent_lt hne)) (lt_irrefl a)
    · exact κ.isMin_of_strictParents_empty hne
  le_pred_of_lt := fun h => κ.le_parent_of_lt h

theorem pred_eq_parent (S : κ.Vtx) : Order.pred S = κ.parent S := rfl

theorem exists_parent_iterate :
    ∀ (d : ℕ) (a b : κ.Vtx), a ≤ b → a.set.card - b.set.card ≤ d →
      ∃ k, (κ.parent)^[k] b = a := by
  intro d
  induction d with
  | zero =>
      intro a b hab hcard
      have hsub : b.set ⊆ a.set := hab
      have hle : b.set.card ≤ a.set.card := Finset.card_le_card hsub
      have : a.set.card ≤ b.set.card := by omega
      exact ⟨0, Vtx.ext (Finset.eq_of_subset_of_card_le hsub this)⟩
  | succ d ih =>
      intro a b hab hcard
      by_cases hEq : a = b
      · exact ⟨0, hEq.symm⟩
      · have hlt : a < b := lt_of_le_of_ne hab hEq
        have hne : (κ.strictParents b).Nonempty := ⟨a, κ.mem_strictParents.mpr hlt⟩
        have hpar : κ.parent b < b := κ.parent_lt hne
        have hap : a ≤ κ.parent b := κ.le_parent_of_lt hlt
        have hcardb : b.set.card < (κ.parent b).set.card :=
          Finset.card_lt_card ⟨hpar.le, fun hc => hpar.not_ge hc⟩
        have hcardpa : (κ.parent b).set.card ≤ a.set.card := Finset.card_le_card hap
        obtain ⟨k, hk⟩ := ih a (κ.parent b) hap (by omega)
        exact ⟨k + 1, by rw [Function.iterate_succ_apply]; exact hk⟩

instance : IsPredArchimedean κ.Vtx where
  exists_pred_iterate_of_le := by
    intro a b h
    exact κ.exists_parent_iterate _ a b h le_rfl

/-- Contact height strictly decreases away from the root. -/
theorem kappaV_strictAnti : StrictAnti κ.kappaV := by
  intro a b hab
  obtain ⟨hsub, hnsub⟩ := hab
  obtain ⟨i, hi⟩ := b.nonempty
  have hia : i ∈ a.set := hsub hi
  obtain ⟨j, hja, hjb⟩ : ∃ j, j ∈ a.set ∧ j ∉ b.set := by
    by_contra hcon
    push Not at hcon
    exact hnsub fun q hq => hcon q hq
  have hb : b.set = κ.ball i (κ.rad b i) := κ.set_eq_ball_rad b hi
  have hjgt : κ.rad b i < κ.val i j := by
    by_contra hle
    push Not at hle
    exact hjb (by rw [hb]; simpa using hle)
  calc κ.kappaV b = κ.rad b i := κ.kappaV_eq_rad hi
    _ < κ.val i j := hjgt
    _ ≤ κ.rad a i := κ.le_rad hja
    _ = κ.kappaV a := (κ.kappaV_eq_rad hia).symm

/-- Leaf vertex of a label. -/
noncomputable def leafVtx (i : Fin n) : κ.Vtx where
  set := {i}
  isCluster := ⟨i, i, κ.singleton_eq_ball i⟩

@[simp] theorem leafVtx_set (i : Fin n) : (κ.leafVtx i).set = {i} := rfl

/-- The rooted skeleton reconstructed from a contact matrix. -/
noncomputable def realization (hn : 1 < n) : RootedContactTree n :=
  haveI : NeZero n := ⟨by omega⟩
  { tree := { α := κ.Vtx }
    decidableEqTree := (inferInstance : DecidableEq κ.Vtx)
    decidableLETree := (inferInstance : DecidableRel (fun S T : κ.Vtx => S ≤ T))
    fintypeTree := (inferInstance : Fintype κ.Vtx)
    leaf := fun i => (κ.leafVtx i : κ.Vtx)
    leaf_ne_root := by
      intro i hcon
      have hset : ({i} : Finset (Fin n)) = Finset.univ :=
        congrArg (fun S : κ.Vtx => S.set) hcon
      have hcard : (1 : ℕ) = n := by
        simpa [Finset.card_univ] using congrArg Finset.card hset
      omega
    leaf_antichain := by
      intro i j hij hcon
      have : ({j} : Finset (Fin n)) ⊆ {i} := hcon
      exact hij (Finset.mem_singleton.mp (this (Finset.mem_singleton_self j))).symm
    kappa := κ.kappaV
    kappa_strictAnti := κ.kappaV_strictAnti }

/-- The reconstructed skeleton has exactly the given contact matrix. -/
theorem realization_contact (hn : 1 < n) (i j : Fin n) :
    (κ.realization hn).contact i j = κ.val i j := by
  haveI : NeZero n := ⟨by omega⟩
  show κ.kappaV (κ.leafVtx i ⊓ κ.leafVtx j) = κ.val i j
  set M := κ.leafVtx i ⊓ κ.leafVtx j with hM
  have hiM : i ∈ M.set := by
    have : (κ.leafVtx i).set ⊆ M.set := inf_le_left (a := κ.leafVtx i) (b := κ.leafVtx j)
    exact this (Finset.mem_singleton_self i)
  have hjM : j ∈ M.set := by
    have : (κ.leafVtx j).set ⊆ M.set := inf_le_right (a := κ.leafVtx i) (b := κ.leafVtx j)
    exact this (Finset.mem_singleton_self j)
  have hUpper : M.set ⊆ κ.ball i (κ.val i j) := by
    have hU : κ.IsCluster (κ.ball i (κ.val i j)) := ⟨i, j, rfl⟩
    have hUS : (⟨κ.ball i (κ.val i j), hU⟩ : κ.Vtx) ≤ κ.leafVtx i := by
      intro p hp
      have hpi : p = i := Finset.mem_singleton.mp hp
      subst hpi
      exact κ.self_mem_ball p j
    have hUT : (⟨κ.ball i (κ.val i j), hU⟩ : κ.Vtx) ≤ κ.leafVtx j := by
      intro p hp
      have hpj : p = j := Finset.mem_singleton.mp hp
      subst hpj
      simp
    exact le_inf hUS hUT
  rw [κ.kappaV_eq_rad hiM]
  apply le_antisymm
  · refine κ.rad_le ?_
    intro p hp
    simpa using hUpper hp
  · exact κ.le_rad hjM

/-- The energy metric of the reconstructed skeleton, read off the contact matrix. -/
theorem realization_energy (hn : 1 < n) (i j : Fin n) :
    (κ.realization hn).energy i j = 2 * κ.val i j - κ.val i i - κ.val j j := by
  rw [RootedContactTree.energy, κ.realization_contact hn, κ.realization_contact hn,
    κ.realization_contact hn]

/-- **Contact realization.**  Every acute contact matrix with strictly separated diagonal is the
complementary-contact matrix of a rooted skeleton. -/
theorem exists_realization (hn : 1 < n) :
    ∃ t : RootedContactTree n, ∀ i j, t.contact i j = κ.val i j :=
  ⟨κ.realization hn, κ.realization_contact hn⟩

end ContactMatrix

namespace DecoratedStokesCore

variable {n : ℕ} (g : DecoratedStokesCore n)

/-- The rescaled contact matrix of a decorated core, packaged once its two structural inequalities
are known. -/
noncomputable def toContactMatrix
    (hacute : ∀ i j k, g.realContactMatrix i j ≤
      max (g.realContactMatrix i k) (g.realContactMatrix j k))
    (hstrict : ∀ i j, i ≠ j →
      (g.ramification j : ℤ) * (g.B i i - 1) < (g.ramification i : ℤ) * g.B i j) :
    IrregularStokes.ContactMatrix n where
  val := g.realContactMatrix
  val_symm := g.realContactMatrix_symm
  val_acute := hacute
  val_diagonal_lt := by
    intro i j hij
    have hq : g.diagonalContact i < g.pairContact i j := (g.strictDiagonal_iff i j).mpr
      (hstrict i j hij)
    have : ((g.diagonalContact i : ℚ) : ℝ) < ((g.pairContact i j : ℚ) : ℝ) := by
      exact_mod_cast hq
    simpa [realContactMatrix, contactMatrix_self, g.contactMatrix_of_ne hij] using this

/-- **Realizability criterion for decorated Stokes cores.**  A decorated core is the rescaled
contact matrix of a rooted fission skeleton exactly when it is acute and its integral diagonal
obstruction is strict. -/
theorem nonempty_rootedRealization_iff (hn : 1 < n) :
    Nonempty g.RootedRealization ↔
      ((∀ i j k, g.realContactMatrix i j ≤
          max (g.realContactMatrix i k) (g.realContactMatrix j k)) ∧
        ∀ i j, i ≠ j →
          (g.ramification j : ℤ) * (g.B i i - 1) < (g.ramification i : ℤ) * g.B i j) := by
  constructor
  · rintro ⟨realization⟩
    refine ⟨?_, fun i j hij => realization.strictCoreObstruction hij⟩
    intro i j k
    have := realization.tree.contact_acute i j k
    rw [realization.contact_eq, realization.contact_eq, realization.contact_eq] at this
    exact this
  · rintro ⟨hacute, hstrict⟩
    refine ⟨⟨(g.toContactMatrix hacute hstrict).realization hn, ?_⟩⟩
    intro i j
    exact (g.toContactMatrix hacute hstrict).realization_contact hn i j

end DecoratedStokesCore

/-! ### The two encodings are the same object -/

namespace RootedContactTree

/-- **Every rooted skeleton is a contact matrix.**  Symmetry, the acute inequality and strict
diagonal separation are precisely the axioms of a contact matrix, so the complementary contact of a
rooted skeleton is one. -/
def toContactMatrix {n : ℕ} (t : RootedContactTree n) : ContactMatrix n where
  val := t.contact
  val_symm := t.contact_symm
  val_acute := t.contact_acute
  val_diagonal_lt := fun hij => t.contact_diagonal_lt hij

@[simp] theorem toContactMatrix_val {n : ℕ} (t : RootedContactTree n) (i j : Fin n) :
    t.toContactMatrix.val i j = t.contact i j := rfl

/-- **The reconstruction round trip.**  The skeleton reconstructed from a rooted skeleton's own
contact matrix has exactly that skeleton's contact matrix. -/
theorem realization_contact_eq {n : ℕ} (t : RootedContactTree n) (hn : 1 < n) (i j : Fin n) :
    (t.toContactMatrix.realization hn).contact i j = t.contact i j :=
  t.toContactMatrix.realization_contact hn i j

/-- **Theorem 8.3 as a round trip.**  A rooted skeleton and the skeleton reconstructed from its own
contact matrix have the same labelled hierarchy: the matrix loses nothing that `S(Theta)` retains. -/
theorem hierarchy_realization_eq {n : ℕ} (t : RootedContactTree n) (hn : 1 < n) :
    (t.toContactMatrix.realization hn).hierarchy = t.hierarchy :=
  hierarchy_eq_of_contact_eq _ _ (t.realization_contact_eq hn)

end RootedContactTree

end IrregularStokes
end GaloisForLFunctions
