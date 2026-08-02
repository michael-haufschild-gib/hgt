import GaloisForLFunctions.HTGeometry.FamilyStepDegreeOne

/-!
# Solomon--Tits vanishing for a graded modular lattice

The induction on rank.  For a family of intervals of a bounded modular lattice, all of rank at least
`i + 3`, the disjoint union of their buildings has no homology in degree `i`.

The step replaces the family by the family of intervals below the coatoms, whose rank is one less,
and drops the degree by one.  At the bottom of the descent the degree is one, and there vanishing is
replaced by the injectivity that componentwise connectedness supplies.  If nothing in a component
spans, that component's cover is its base alone, which is locally conical — that case is handled
separately and needs no rank at all.

The rank function is only asked to be strictly monotone, to vanish at the bottom, and to increase by
one across a covering; `Module.finrank` on the subspaces of a finite-dimensional vector space is such
a function.
-/

namespace GaloisForLFunctions.HTGeometry

open CategoryTheory Limits Simplicial Opposite

universe v u

variable {L : Type u} [Lattice L] [BoundedOrder L] [IsModularLattice L]

/-- **A spanning coatom is covered by the top of its interval.** -/
theorem covBy_famCoverTop {ι : Type u} {W p : ι → L} (hp : ∀ a, IsAtom (p a))
    (c : famCoverIndex W p) : famCoverTop c ⋖ W (Subtype.val c).1 := by
  refine ⟨c.2.1, fun z hz1 hz2 => ?_⟩
  exact absurd (eq_of_lt_of_spanningBelow (hp _) c.2 hz1 (le_of_lt hz2)) (ne_of_lt hz2)

omit [IsModularLattice L] in
/-- An atom has rank one. -/
theorem rank_atom_eq_one (rk : L → ℕ) (hrk0 : rk ⊥ = 0)
    (hrkcov : ∀ {U V : L}, U ⋖ V → rk V = rk U + 1) {q : L} (hq : IsAtom q) : rk q = 1 := by
  rw [hrkcov hq.bot_covBy, hrk0]

omit [IsModularLattice L] in
/-- Below an element of rank at least two there is a proper nonzero element. -/
theorem exists_properBelow (rk : L → ℕ) (hrk0 : rk ⊥ = 0)
    (hrkcov : ∀ {U V : L}, U ⋖ V → rk V = rk U + 1)
    (hatomic : ∀ V : L, ⊥ < V → ∃ q, IsAtom q ∧ q ≤ V)
    {V : L} (hV : ⊥ < V) (hVtop : V < ⊤) (hrank : 2 ≤ rk V) :
    ∃ x : properPart L, x ∈ properBelow V := by
  obtain ⟨q, hq, hqV⟩ := hatomic V hV
  have hqlt : q < V := by
    refine lt_of_le_of_ne hqV (fun heq => ?_)
    rw [← heq, rank_atom_eq_one rk hrk0 hrkcov hq] at hrank
    omega
  exact ⟨⟨q, hq.1.bot_lt, lt_trans hqlt hVtop⟩, hqlt⟩

/-- **The disjoint union over a single component is the proper part itself.** -/
def famBuildingPUnitOrderIso :
    famBuilding (fun _ : PUnit.{u + 1} => (⊤ : L)) ≃o properPart L where
  toFun q := (Subtype.val q).2
  invFun x := ⟨(PUnit.unit, x), x.2.2⟩
  left_inv q := Subtype.ext (Prod.ext rfl rfl)
  right_inv _ := rfl
  map_rel_iff' := by
    intro q q'
    constructor
    · intro h
      exact ⟨rfl, h⟩
    · intro h
      exact (famPoset_le_iff.1 h).2

section

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{u} C]

/-- **Solomon--Tits vanishing, for a family of intervals at once.**  Every component of rank at least
`i + 3` contributes nothing to the homology of the disjoint union in degree `i`. -/
theorem isZero_homology_famBuilding_of_rank (rk : L → ℕ) (hrk0 : rk ⊥ = 0)
    (hrkcov : ∀ {U V : L}, U ⋖ V → rk V = rk U + 1)
    (hatomic : ∀ V : L, ⊥ < V → ∃ q, IsAtom q ∧ q ≤ V) (R : C) :
    ∀ (i : ℕ), 1 ≤ i → ∀ (ι : Type u) (W : ι → L), (∀ a, ⊥ < W a) → (∀ a, i + 3 ≤ rk (W a)) →
      Limits.IsZero ((nerve (famBuilding W)).homology R i) := by
  classical
  intro i
  induction i with
  | zero => intro h; exact absurd h (by omega)
  | succ n ih =>
      intro _ ι W hbot hrank
      choose p hp hpW using fun a => hatomic (W a) (hbot a)
      have hbot' : ∀ c : famCoverIndex W p, ⊥ < famCoverTop c :=
        fun c => (Subtype.val c).2.2.1
      have htop' : ∀ c : famCoverIndex W p, famCoverTop c < ⊤ :=
        fun c => (Subtype.val c).2.2.2
      have hrank' : ∀ c : famCoverIndex W p, rk (famCoverTop c) + 1 = rk (W (Subtype.val c).1) :=
        fun c => (hrkcov (covBy_famCoverTop hp c)).symm
      rcases isEmpty_or_nonempty (famCoverIndex W p) with hem | hne
      · exact isZero_homology_famBuilding_of_isEmpty hp hpW R (n + 1) (by omega)
      · rcases Nat.eq_zero_or_pos n with rfl | hn
        · -- degree one: the injectivity form, with connectedness one level down
          choose p' hp' hp'W using fun c : famCoverIndex W p => hatomic (famCoverTop c) (hbot' c)
          choose v hv using fun c : famCoverIndex W p =>
            exists_properBelow rk hrk0 hrkcov hatomic (hbot' c) (htop' c)
              (by have := hrank (Subtype.val c).1; have := hrank' c; omega)
          have hsmall : SSet.homologyMap (famAtomMap hp' hp'W) R 0 = 𝟙 _ := by
            rcases isEmpty_or_nonempty
                (famCoverIndex (fun c : famCoverIndex W p => famCoverTop c) p') with hem' | hne'
            · exact homologyMap_famAtomMap_eq_id_of_isEmpty hp' hp'W R 0
            · choose v' hv' using fun d : famCoverIndex
                  (fun c : famCoverIndex W p => famCoverTop c) p' =>
                exists_properBelow rk hrk0 hrkcov hatomic
                  ((Subtype.val d).2.2.1) ((Subtype.val d).2.2.2)
                  (by
                    have h1 := hrank (Subtype.val (Subtype.val d).1).1
                    have h2 := hrank' (Subtype.val d).1
                    have h3 : rk (((Subtype.val d).2 : properPart L) : L) + 1
                        = rk (famCoverTop (Subtype.val d).1) :=
                      (hrkcov (covBy_famCoverTop hp' d)).symm
                    omega)
              exact homologyMap_famAtomMap_eq_id hp' hp'W v' hv' R
          exact isZero_homology_famBuilding_one hp hpW v hv p' hp' hp'W R hsmall
        · -- degree at least two: the vanishing form, from the induction hypothesis
          refine isZero_homology_famBuilding_of_isZero hp hpW R (n + 1) n rfl (by omega) ?_
          refine ih (by omega) _ (fun c : famCoverIndex W p => famCoverTop c) hbot' ?_
          intro c
          have h1 := hrank' c
          have h2 := hrank (Subtype.val c).1
          omega

/-- **Solomon--Tits vanishing.**  The order complex of the proper part of a bounded modular lattice
of rank at least `i + 3`, with atoms below every nonzero element and a graded rank, has no homology
in degree `i` for `1 ≤ i`. -/
theorem isZero_homology_properPart_of_rank (rk : L → ℕ) (hrk0 : rk ⊥ = 0)
    (hrkcov : ∀ {U V : L}, U ⋖ V → rk V = rk U + 1)
    (hatomic : ∀ V : L, ⊥ < V → ∃ q, IsAtom q ∧ q ≤ V) (R : C) (i : ℕ) (hi : 1 ≤ i)
    (hbot : (⊥ : L) < ⊤) (hrank : i + 3 ≤ rk (⊤ : L)) :
    Limits.IsZero ((nerve (properPart L)).homology R i) := by
  have h := isZero_homology_famBuilding_of_rank rk hrk0 hrkcov hatomic R i hi PUnit.{u + 1}
    (fun _ => (⊤ : L)) (fun _ => hbot) (fun _ => hrank)
  exact Limits.IsZero.of_iso h
    ((SSet.homologyFunctor R i).mapIso (orderIsoNerveIso (famBuildingPUnitOrderIso (L := L))).symm)

end

end GaloisForLFunctions.HTGeometry
