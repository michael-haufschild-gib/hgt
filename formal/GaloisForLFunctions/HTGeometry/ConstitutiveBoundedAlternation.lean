import GaloisForLFunctions.HTGeometry.ConstitutiveClosedAdmissionHull

namespace HTGeometry

noncomputable section

open Set Topology

/-!
# Bounded alternation and first-shell depth divergence

Finite composites of closed relations on a compact Hausdorff space are closed.  Consequently every
bounded `E/F` path layer is closed.  The full algebraic join is the union of these finite layers,
and a point in its closure but outside the join is approached, in every sufficiently small
neighborhood, only through paths whose minimal length exceeds any prescribed finite bound.
-/

/-- Relational composite, with the path running first through `R` and then through `S`. -/
def admissionRelationComp {X : Type*}
    (R S : X → X → Prop) (x z : X) : Prop :=
  ∃ y, R x y ∧ S y z

/-- Composition preserves closedness on a compact middle space. -/
theorem isClosed_admissionRelationComp
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {R S : X → X → Prop}
    (hR : IsClosed (admissionRelationGraph R))
    (hS : IsClosed (admissionRelationGraph S)) :
    IsClosed (admissionRelationGraph (admissionRelationComp R S)) := by
  let T : Set ((X × X) × X) :=
    {p | R p.1.1 p.2 ∧ S p.2 p.1.2}
  have hcR : Continuous (fun p : (X × X) × X => (p.1.1, p.2)) :=
    (continuous_fst.comp continuous_fst).prodMk continuous_snd
  have hcS : Continuous (fun p : (X × X) × X => (p.2, p.1.2)) :=
    continuous_snd.prodMk (continuous_snd.comp continuous_fst)
  have hT : IsClosed T := hR.preimage hcR |>.inter (hS.preimage hcS)
  have hgraph :
      admissionRelationGraph (admissionRelationComp R S) = Prod.fst '' T := by
    ext p
    constructor
    · rintro ⟨y, hpyR, hypS⟩
      exact ⟨(p, y), ⟨hpyR, hypS⟩, rfl⟩
    · rintro ⟨q, ⟨hqR, hqS⟩, hqp⟩
      subst p
      exact ⟨q.2, hqR, hqS⟩
  rw [hgraph]
  exact isClosedMap_fst_of_compactSpace T hT

/-- Paths of exactly `n` edges in a relation. -/
def admissionRelationPower {X : Type*} (R : X → X → Prop) :
    ℕ → X → X → Prop
  | 0 => (· = ·)
  | n + 1 => admissionRelationComp (admissionRelationPower R n) R

@[simp] theorem admissionRelationPower_zero
    {X : Type*} (R : X → X → Prop) (x y : X) :
    admissionRelationPower R 0 x y ↔ x = y :=
  Iff.rfl

@[simp] theorem admissionRelationPower_succ
    {X : Type*} (R : X → X → Prop) (n : ℕ) (x z : X) :
    admissionRelationPower R (n + 1) x z ↔
      ∃ y, admissionRelationPower R n x y ∧ R y z :=
  Iff.rfl

theorem admissionRelationPower_one
    {X : Type*} (R : X → X → Prop) (x y : X) :
    admissionRelationPower R 1 x y ↔ R x y := by
  simp [admissionRelationPower_succ]

/-- Every exact finite path layer of a closed relation is closed. -/
theorem isClosed_admissionRelationPower
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    {R : X → X → Prop}
    (hR : IsClosed (admissionRelationGraph R)) :
    ∀ n, IsClosed (admissionRelationGraph (admissionRelationPower R n)) := by
  intro n
  induction n with
  | zero =>
      change IsClosed {p : X × X | p.1 = p.2}
      exact isClosed_eq continuous_fst continuous_snd
  | succ n ih =>
      exact isClosed_admissionRelationComp ih hR

/-- Concatenation adds exact path lengths. -/
theorem admissionRelationPower_add
    {X : Type*} {R : X → X → Prop}
    {m n : ℕ} {x y z : X}
    (hxy : admissionRelationPower R m x y)
    (hyz : admissionRelationPower R n y z) :
    admissionRelationPower R (m + n) x z := by
  induction n generalizing z with
  | zero =>
      have : y = z := hyz
      subst z
      simpa using hxy
  | succ n ih =>
      rcases hyz with ⟨w, hyw, hwz⟩
      rw [Nat.add_succ, admissionRelationPower_succ]
      exact ⟨w, ih hyw, hwz⟩

/-- Exact path layers inherit symmetry from the edge relation. -/
theorem admissionRelationPower_symm
    {X : Type*} {R : X → X → Prop}
    (hR : ∀ x y, R x y → R y x) :
    ∀ {n x y}, admissionRelationPower R n x y →
      admissionRelationPower R n y x := by
  intro n
  induction n with
  | zero =>
      intro x y hxy
      exact hxy.symm
  | succ n ih =>
      intro x y hxy
      rcases hxy with ⟨z, hxz, hzy⟩
      have hyz : admissionRelationPower R 1 y z :=
        (admissionRelationPower_one R y z).2 (hR z y hzy)
      have hzx : admissionRelationPower R n z x := ih hxz
      simpa [Nat.add_comm] using admissionRelationPower_add hyz hzx

/-- Paths of at most `d` edges in the union of two equivalence relations. -/
def boundedAlternationJoin {X : Type*}
    (E F : Setoid X) (d : ℕ) (x y : X) : Prop :=
  ∃ n ∈ Finset.range (d + 1),
    admissionRelationPower (fun a b => E a b ∨ F a b) n x y

/-- Every bounded alternation layer is closed. -/
theorem isClosed_boundedAlternationJoin
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (E F : Setoid X)
    (hE : IsClosedAdmissionSetoid E)
    (hF : IsClosedAdmissionSetoid F)
    (d : ℕ) :
    IsClosed (admissionRelationGraph (boundedAlternationJoin E F d)) := by
  have hUnion :
      IsClosed (admissionRelationGraph (fun x y => E x y ∨ F x y)) := by
    rw [show admissionRelationGraph (fun x y => E x y ∨ F x y) =
      admissionRelationGraph E ∪ admissionRelationGraph F by
        ext p
        rfl]
    exact hE.union hF
  have hclosed :
      IsClosed (⋃ n ∈ Finset.range (d + 1),
        admissionRelationGraph
          (admissionRelationPower (fun x y => E x y ∨ F x y) n)) :=
    isClosed_biUnion_finset fun n _ =>
      isClosed_admissionRelationPower hUnion n
  convert hclosed using 1
  ext p
  simp [boundedAlternationJoin, admissionRelationGraph]

theorem admissionRelationPower_union_le_eqvGen
    {X : Type*} (E F : Setoid X) :
    ∀ {n x y},
      admissionRelationPower (fun a b => E a b ∨ F a b) n x y →
        Relation.EqvGen (fun a b => E a b ∨ F a b) x y := by
  intro n
  induction n with
  | zero =>
      intro x y hxy
      subst y
      exact Relation.EqvGen.refl x
  | succ n ih =>
      intro x y hxy
      rcases hxy with ⟨z, hxz, hzy⟩
      exact Relation.EqvGen.trans x z y (ih hxz)
        (Relation.EqvGen.rel z y hzy)

/-- The algebraic join is exactly the union of all finite path layers. -/
theorem eqvGen_union_iff_exists_admissionRelationPower
    {X : Type*} (E F : Setoid X) (x y : X) :
    Relation.EqvGen (fun a b => E a b ∨ F a b) x y ↔
      ∃ n, admissionRelationPower (fun a b => E a b ∨ F a b) n x y := by
  constructor
  · intro hxy
    induction hxy with
    | rel x y hxy =>
        exact ⟨1, (admissionRelationPower_one _ _ _).2 hxy⟩
    | refl x =>
        exact ⟨0, rfl⟩
    | symm x y _ ih =>
        obtain ⟨n, hn⟩ := ih
        exact ⟨n, admissionRelationPower_symm
          (fun a b h => h.elim (fun hE => Or.inl (E.symm hE))
            (fun hF => Or.inr (F.symm hF))) hn⟩
    | trans x y z _ _ ihxy ihyz =>
        obtain ⟨m, hm⟩ := ihxy
        obtain ⟨n, hn⟩ := ihyz
        exact ⟨m + n, admissionRelationPower_add hm hn⟩
  · rintro ⟨n, hn⟩
    exact admissionRelationPower_union_le_eqvGen E F hn

theorem eqvGen_union_iff_exists_boundedAlternationJoin
    {X : Type*} (E F : Setoid X) (x y : X) :
    Relation.EqvGen (fun a b => E a b ∨ F a b) x y ↔
      ∃ d, boundedAlternationJoin E F d x y := by
  rw [eqvGen_union_iff_exists_admissionRelationPower]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, n, Finset.mem_range.mpr (Nat.lt_succ_self n), hn⟩
  · rintro ⟨d, n, -, hn⟩
    exact ⟨n, hn⟩

theorem boundedAlternationJoin_le_eqvGen
    {X : Type*} (E F : Setoid X) {d : ℕ} {x y : X}
    (hxy : boundedAlternationJoin E F d x y) :
    Relation.EqvGen (fun a b => E a b ∨ F a b) x y := by
  rcases hxy with ⟨n, -, hn⟩
  exact admissionRelationPower_union_le_eqvGen E F hn

theorem not_boundedAlternationJoin_iff_all_short_paths_absent
    {X : Type*} (E F : Setoid X) (d : ℕ) (x y : X) :
    ¬ boundedAlternationJoin E F d x y ↔
      ∀ n < d + 1,
        ¬ admissionRelationPower (fun a b => E a b ∨ F a b) n x y := by
  simp [boundedAlternationJoin]

/-- **Bounded-alternation depth divergence.** At a closure point outside the algebraic join, for
every finite bound there is a neighborhood such that every smaller neighborhood contains a joined
pair with no path of length at most that bound. -/
theorem boundedAlternation_depth_diverges_at_firstShell
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (E F : Setoid X)
    (hE : IsClosedAdmissionSetoid E)
    (hF : IsClosedAdmissionSetoid F)
    (p : X × X)
    (hclosure : p ∈ closure
      (admissionRelationGraph
        (Relation.EqvGen (fun a b => E a b ∨ F a b))))
    (houtside : ¬ Relation.EqvGen (fun a b => E a b ∨ F a b) p.1 p.2) :
    ∀ d, ∃ W ∈ 𝓝 p, ∀ V ∈ 𝓝 p, V ⊆ W →
      ∃ q ∈ V,
        Relation.EqvGen (fun a b => E a b ∨ F a b) q.1 q.2 ∧
        ¬ boundedAlternationJoin E F d q.1 q.2 := by
  intro d
  have hclosed := isClosed_boundedAlternationJoin E F hE hF d
  have hpnot : p ∉ admissionRelationGraph (boundedAlternationJoin E F d) := by
    intro hp
    exact houtside (boundedAlternationJoin_le_eqvGen E F hp)
  let W := (admissionRelationGraph (boundedAlternationJoin E F d))ᶜ
  have hW : W ∈ 𝓝 p := hclosed.compl_mem_nhds hpnot
  refine ⟨W, hW, ?_⟩
  intro V hV hVW
  obtain ⟨q, hqV, hqJoin⟩ := (mem_closure_iff_nhds.mp hclosure) V hV
  refine ⟨q, hqV, hqJoin, ?_⟩
  intro hqBound
  exact hVW hqV hqBound

/-- Bundled unconditional bounded-alternation capstone. -/
theorem boundedAlternation_capstone
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (E F : Setoid X)
    (hE : IsClosedAdmissionSetoid E)
    (hF : IsClosedAdmissionSetoid F) :
    (∀ d, IsClosed (admissionRelationGraph (boundedAlternationJoin E F d))) ∧
    (∀ x y, Relation.EqvGen (fun a b => E a b ∨ F a b) x y ↔
      ∃ d, boundedAlternationJoin E F d x y) := by
  exact ⟨isClosed_boundedAlternationJoin E F hE hF,
    eqvGen_union_iff_exists_boundedAlternationJoin E F⟩

end

end HTGeometry
