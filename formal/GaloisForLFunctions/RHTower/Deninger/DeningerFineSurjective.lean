import GaloisForLFunctions.RHTower.Deninger.DeningerFineLifting

/-!
# Sections of a short exact sequence with fine kernel

On a paracompact space, if the kernel of a short exact sequence of sheaves of abelian groups carries
a multiplication by continuous functions, then global sections of the quotient lift to global
sections of the middle term.

The lift is the classical cocycle correction.  A global section of the quotient lifts locally, say
to `s_i` over `V_i`; the differences `c_{ij} = s_i − s_j` are sections of the kernel; a partition of
unity `ρ_i` subordinate to the cover turns them into the correction `∑_j ρ_j c_{ij}`, which is a
section over `V_i` because each summand extends by zero and the family is locally finite.  On an
overlap the corrections differ by `∑_k ρ_k (c_{ik} − c_{jk}) = ∑_k ρ_k c_{ij} = c_{ij}`, exactly
cancelling the discrepancy of the local lifts, so the corrected sections glue.

* `RHTower.deningerFine_sections_surjective` : **the lifting theorem.**
-/

namespace RHTower

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite TopCat

universe u

variable {X : TopCat.{u}}

/-- Restriction commutes with a morphism of sheaves. -/
theorem deningerRes_app {F G : TopCat.Sheaf AddCommGrpCat.{u} X} (φ : F ⟶ G) {U W : Opens X}
    (h : W ≤ U) (s : ToType (F.1.obj (op U))) :
    deningerRes G h (ConcreteCategory.hom (φ.1.app (op U)) s)
      = ConcreteCategory.hom (φ.1.app (op W)) (deningerRes F h s) :=
  (CategoryTheory.NatTrans.naturality_apply φ.1 (homOfLE h).op s).symm

/-- A family of multipliers admits partitions of unity when every pointwise-indexed open cover of
the space has a subordinate, locally finite family in it summing to one. -/
def DeningerHasPartitions (R : AddSubgroup C(X, ℝ)) : Prop :=
  ∀ V : ∀ _ : (X : Type u), Opens X, (∀ x, x ∈ V x) →
    ∃ ρ : ∀ _ : (X : Type u), ↥R,
      (∀ i, tsupport (fun y => (ρ i : C(X, ℝ)) y) ⊆ (V i : Set (X : Type u))) ∧
      LocallyFinite (fun i => tsupport (fun y => (ρ i : C(X, ℝ)) y)) ∧
      ∀ x : (X : Type u), ∑ᶠ i, (ρ i : C(X, ℝ)) x = 1

/-- **Continuous functions admit partitions of unity** on a normal paracompact space. -/
theorem deningerHasPartitions_top [NormalSpace (X : Type u)] [ParacompactSpace (X : Type u)] :
    DeningerHasPartitions (⊤ : AddSubgroup C(X, ℝ)) := by
  intro V hV
  obtain ⟨ρ, hρsub⟩ := PartitionOfUnity.exists_isSubordinate (ι := (X : Type u))
    isClosed_univ (fun i => (V i : Set (X : Type u))) (fun i => (V i).2)
    (fun x _ => Set.mem_iUnion.2 ⟨x, hV x⟩)
  exact ⟨fun i => ⟨ρ i, AddSubgroup.mem_top _⟩, hρsub, ρ.locallyFinite.closure,
    fun x => ρ.sum_eq_one (Set.mem_univ x)⟩

/-- **Global sections lift through a short exact sequence with fine kernel.** -/
theorem deningerFine_sections_surjective {R : AddSubgroup C(X, ℝ)}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact) (A : DeningerFineAction S.X₁ R) (hpu : DeningerHasPartitions R)
    (g : ToType (S.X₃.1.obj (op (⊤ : Opens X)))) :
    ∃ b : ToType (S.X₂.1.obj (op (⊤ : Opens X))),
      ConcreteCategory.hom (S.g.1.app (op (⊤ : Opens X))) b = g := by
  classical
  haveI := hS.mono_f
  haveI := hS.epi_g
  -- local lifts of `g`
  have hloc : TopCat.Presheaf.IsLocallySurjective S.g.1 :=
    (TopCat.Sheaf.isLocallySurjective_iff_epi S.g).2 hS.epi_g
  have hlift : ∀ x : (X : Type u), ∃ V : Opens X, x ∈ V ∧
      ∃ s : ToType (S.X₂.1.obj (op V)),
        ConcreteCategory.hom (S.g.1.app (op V)) s = deningerRes S.X₃ (le_top : V ≤ ⊤) g := by
    intro x
    obtain ⟨V, hVU, ⟨s, hs⟩, hxV⟩ :=
      (TopCat.Presheaf.isLocallySurjective_iff S.g.1).1 hloc ⊤ g x trivial
    exact ⟨V, hxV, s, hs⟩
  choose Vs hxV s hs using hlift
  -- a partition of unity subordinate to the cover
  obtain ⟨ρ, hρsub, hlf, hone⟩ := hpu Vs hxV
  -- the differences of the local lifts, as sections of the kernel
  have hcex : ∀ i j : (X : Type u), ∃ c : ToType (S.X₁.1.obj (op (Vs i ⊓ Vs j))),
      ConcreteCategory.hom (S.f.1.app (op (Vs i ⊓ Vs j))) c
        = deningerRes S.X₂ (inf_le_left : Vs i ⊓ Vs j ≤ Vs i) (s i)
          - deningerRes S.X₂ (inf_le_right : Vs i ⊓ Vs j ≤ Vs j) (s j) := by
    intro i j
    refine deningerSections_exact hS _ _ ?_
    rw [map_sub, deningerRes_app S.g (inf_le_left : Vs i ⊓ Vs j ≤ Vs i) (s i) |>.symm,
      deningerRes_app S.g (inf_le_right : Vs i ⊓ Vs j ≤ Vs j) (s j) |>.symm, hs i, hs j,
      deningerRes_res, deningerRes_res, sub_self]
  choose c hc using hcex
  -- the cocycle identity
  have hcocycle : ∀ (i j k : (X : Type u)) (Z : Opens X) (hi : Z ≤ Vs i) (hj : Z ≤ Vs j)
      (hk : Z ≤ Vs k),
      deningerRes S.X₁ (le_inf hi hk) (c i k) - deningerRes S.X₁ (le_inf hj hk) (c j k)
        = deningerRes S.X₁ (le_inf hi hj) (c i j) := by
    intro i j k Z hi hj hk
    refine deningerSections_injective S.f Z ?_
    rw [map_sub, ← deningerRes_app S.f (le_inf hi hk) (c i k),
      ← deningerRes_app S.f (le_inf hj hk) (c j k), ← deningerRes_app S.f (le_inf hi hj) (c i j),
      hc, hc, hc, deningerRes_sub, deningerRes_sub, deningerRes_sub, deningerRes_res,
      deningerRes_res, deningerRes_res, deningerRes_res, deningerRes_res, deningerRes_res]
    abel
  -- the extensions by zero of the corrected differences
  have hext : ∀ i j : (X : Type u), ∃ E : ToType (S.X₁.1.obj (op (Vs i))),
      deningerRes S.X₁ (inf_le_left : Vs i ⊓ Vs j ≤ Vs i) E
          = A.smul (ρ j) (Vs i ⊓ Vs j) (c i j) ∧
      ∀ (Z : Opens X) (hZ : Z ≤ Vs i), Z ≤ deningerOffSupport (ρ j : C(X, ℝ)) →
        deningerRes S.X₁ hZ E = 0 :=
    fun i j => deningerFineAction_extendByZero A (ρ j) (hρsub j) (c i j)
  choose e he1 he2 using hext
  -- a neighbourhood on which only finitely many bumps are alive, and the partition sums to one
  have hnbhd : ∀ (Z : Opens X) (y : (X : Type u)), y ∈ Z → ∃ (W : Opens X) (_ : W ≤ Z), y ∈ W ∧
      ∃ T : Finset (X : Type u), (∀ j ∉ T, W ≤ deningerOffSupport (ρ j : C(X, ℝ))) ∧
        ∀ z ∈ W, ∑ j ∈ T, (ρ j : C(X, ℝ)) z = 1 := by
    intro Z y hy
    obtain ⟨N, hN, hfin⟩ := hlf y
    obtain ⟨N₀, hN₀N, hN₀open, hyN₀⟩ := mem_nhds_iff.1 hN
    refine ⟨⟨N₀, hN₀open⟩ ⊓ Z, inf_le_right, ⟨hyN₀, hy⟩, hfin.toFinset, ?_, ?_⟩
    · intro j hj z hz hzs
      exact hj (Set.Finite.mem_toFinset hfin |>.2 ⟨z, hzs, hN₀N hz.1⟩)
    · intro z hz
      refine (finsum_eq_sum_of_support_subset (fun j => (ρ j : C(X, ℝ)) z) ?_).symm.trans
        (hone z)
      intro j hj
      by_contra hjT
      have hzoff : z ∈ deningerOffSupport (ρ j : C(X, ℝ)) := by
        intro hzs
        exact hjT (Set.Finite.mem_toFinset hfin |>.2 ⟨z, hzs, hN₀N hz.1⟩)
      exact hzoff (subset_tsupport (fun y => ((ρ j : C(X, ℝ)) y)) hj)
  -- the corrections
  have hsumex : ∀ i : (X : Type u), ∃ E : ToType (S.X₁.1.obj (op (Vs i))),
      ∀ (W : Opens X) (hW : W ≤ Vs i) (T : Finset (X : Type u)),
        (∀ j ∉ T, deningerRes S.X₁ hW (e i j) = 0) →
        deningerRes S.X₁ hW E = ∑ j ∈ T, deningerRes S.X₁ hW (e i j) := by
    intro i
    refine deningerLocallyFiniteSum (e i) fun y hy => ?_
    obtain ⟨W, hWV, hyW, T, hT, -⟩ := hnbhd (Vs i) y hy
    exact ⟨W, hWV, hyW, T, fun j hj => he2 i j W hWV (hT j hj)⟩
  choose E hE using hsumex
  -- the corrected local lifts agree on overlaps
  have hagreeE : ∀ (i j : (X : Type u)) (Z : Opens X) (hi : Z ≤ Vs i) (hj : Z ≤ Vs j),
      deningerRes S.X₁ hi (E i) - deningerRes S.X₁ hj (E j)
        = deningerRes S.X₁ (le_inf hi hj) (c i j) := by
    intro i j Z hi hj
    have hcovZ : Z ≤ ⨆ y : {y : (X : Type u) // y ∈ Z}, (hnbhd Z y.1 y.2).choose := by
      intro y hy
      exact Opens.mem_iSup.2 ⟨⟨y, hy⟩, (hnbhd Z y hy).choose_spec.choose_spec.1⟩
    refine deningerRes_ext (F := S.X₁)
      (fun y : {y : (X : Type u) // y ∈ Z} => (hnbhd Z y.1 y.2).choose_spec.choose) hcovZ _ _
      fun y => ?_
    set W := (hnbhd Z y.1 y.2).choose with hWdef
    have hWZ : W ≤ Z := (hnbhd Z y.1 y.2).choose_spec.choose
    obtain ⟨T, hT, hTone⟩ := (hnbhd Z y.1 y.2).choose_spec.choose_spec.2
    have hWi : W ≤ Vs i := le_trans hWZ hi
    have hWj : W ≤ Vs j := le_trans hWZ hj
    -- each term of the two corrections differs by the multiple of the cocycle
    have hterm : ∀ k : (X : Type u),
        deningerRes S.X₁ hWi (e i k) - deningerRes S.X₁ hWj (e j k)
          = A.smul (ρ k) W (deningerRes S.X₁ (le_inf hWi hWj) (c i j)) := by
      intro k
      have hcov2 : W ≤ (W ⊓ Vs k) ⊔ (W ⊓ deningerOffSupport (ρ k : C(X, ℝ))) := by
        intro z hz
        by_cases hzs : z ∈ tsupport (fun y => ((ρ k : C(X, ℝ)) y))
        · exact Or.inl ⟨hz, hρsub k hzs⟩
        · exact Or.inr ⟨hz, hzs⟩
      refine deningerRes_ext_two (F := S.X₁) (inf_le_left : W ⊓ Vs k ≤ W)
        (inf_le_left : W ⊓ deningerOffSupport (ρ k : C(X, ℝ)) ≤ W) hcov2 _ _ ?_ ?_
      · -- on the support the difference is the bump times the cocycle
        have h1 : deningerRes S.X₁ (inf_le_left : W ⊓ Vs k ≤ W) (deningerRes S.X₁ hWi (e i k))
            = A.smul (ρ k) (W ⊓ Vs k)
              (deningerRes S.X₁ (le_inf (le_trans inf_le_left hWi) inf_le_right) (c i k)) := by
          rw [deningerRes_res, ← deningerRes_res (inf_le_left : Vs i ⊓ Vs k ≤ Vs i)
            (le_inf (le_trans (inf_le_left : W ⊓ Vs k ≤ W) hWi)
              (inf_le_right : W ⊓ Vs k ≤ Vs k)) (e i k),
            he1 i k, A.smul_res']
        have h2 : deningerRes S.X₁ (inf_le_left : W ⊓ Vs k ≤ W) (deningerRes S.X₁ hWj (e j k))
            = A.smul (ρ k) (W ⊓ Vs k)
              (deningerRes S.X₁ (le_inf (le_trans inf_le_left hWj) inf_le_right) (c j k)) := by
          rw [deningerRes_res, ← deningerRes_res (inf_le_left : Vs j ⊓ Vs k ≤ Vs j)
            (le_inf (le_trans (inf_le_left : W ⊓ Vs k ≤ W) hWj)
              (inf_le_right : W ⊓ Vs k ≤ Vs k)) (e j k),
            he1 j k, A.smul_res']
        rw [deningerRes_sub, h1, h2, ← A.smul_sub, A.smul_res',
          hcocycle i j k (W ⊓ Vs k) (le_trans inf_le_left hWi) (le_trans inf_le_left hWj)
            inf_le_right, deningerRes_res]
      · -- off the support of the bump both sides vanish
        have h1 : deningerRes S.X₁ (inf_le_left : W ⊓ deningerOffSupport (ρ k : C(X, ℝ)) ≤ W)
            (deningerRes S.X₁ hWi (e i k)) = 0 := by
          rw [deningerRes_res]
          exact he2 i k _ _ inf_le_right
        have h2 : deningerRes S.X₁ (inf_le_left : W ⊓ deningerOffSupport (ρ k : C(X, ℝ)) ≤ W)
            (deningerRes S.X₁ hWj (e j k)) = 0 := by
          rw [deningerRes_res]
          exact he2 j k _ _ inf_le_right
        rw [deningerRes_sub, h1, h2, sub_zero, A.smul_res',
          A.smul_eq_zero (ρ k) (W ⊓ deningerOffSupport (ρ k : C(X, ℝ))) _
            (fun z hz => deningerOffSupport_apply_eq_zero hz.2)]
    -- sum the terms and use that the partition sums to one
    have hEi : deningerRes S.X₁ hWi (E i) = ∑ k ∈ T, deningerRes S.X₁ hWi (e i k) :=
      hE i W hWi T fun k hk => he2 i k W hWi (hT k hk)
    have hEj : deningerRes S.X₁ hWj (E j) = ∑ k ∈ T, deningerRes S.X₁ hWj (e j k) :=
      hE j W hWj T fun k hk => he2 j k W hWj (hT k hk)
    have hgoal : deningerRes S.X₁ hWi (E i) - deningerRes S.X₁ hWj (E j)
        = deningerRes S.X₁ (le_inf hWi hWj) (c i j) := by
      rw [hEi, hEj, ← Finset.sum_sub_distrib]
      rw [Finset.sum_congr rfl fun k _ => hterm k, ← A.finset_sum_smul]
      rw [A.smul_congr (σ := ⟨1, A.one_mem⟩) (fun z hz => by
        show ((∑ k ∈ T, ρ k : ↥R) : C((X : Type u), ℝ)) z = (1 : C((X : Type u), ℝ)) z
        rw [AddSubmonoidClass.coe_finsetSum, ContinuousMap.coe_sum, Finset.sum_apply,
          hTone z hz]
        rfl), A.one_smul]
    rw [deningerRes_sub, deningerRes_res, deningerRes_res, deningerRes_res]
    exact hgoal
  -- the corrected local lifts
  set t : ∀ i : (X : Type u), ToType (S.X₂.1.obj (op (Vs i))) :=
    fun i => s i - ConcreteCategory.hom (S.f.1.app (op (Vs i))) (E i) with htdef
  have hagree : ∀ (i j : (X : Type u)) (Z : Opens X) (hi : Z ≤ Vs i) (hj : Z ≤ Vs j),
      deningerRes S.X₂ hi (t i) = deningerRes S.X₂ hj (t j) := by
    intro i j Z hi hj
    have hsdiff : deningerRes S.X₂ hi (s i) - deningerRes S.X₂ hj (s j)
        = ConcreteCategory.hom (S.f.1.app (op Z)) (deningerRes S.X₁ (le_inf hi hj) (c i j)) := by
      rw [← deningerRes_app S.f (le_inf hi hj) (c i j), hc, deningerRes_sub, deningerRes_res,
        deningerRes_res]
    have hEdiff : ConcreteCategory.hom (S.f.1.app (op Z))
          (deningerRes S.X₁ hi (E i) - deningerRes S.X₁ hj (E j))
        = ConcreteCategory.hom (S.f.1.app (op Z)) (deningerRes S.X₁ (le_inf hi hj) (c i j)) := by
      rw [hagreeE i j Z hi hj]
    rw [htdef]
    show deningerRes S.X₂ hi (s i - ConcreteCategory.hom (S.f.1.app (op (Vs i))) (E i))
      = deningerRes S.X₂ hj (s j - ConcreteCategory.hom (S.f.1.app (op (Vs j))) (E j))
    rw [deningerRes_sub, deningerRes_sub, deningerRes_app S.f hi (E i),
      deningerRes_app S.f hj (E j)]
    rw [map_sub] at hEdiff
    have key : deningerRes S.X₂ hi (s i) - deningerRes S.X₂ hj (s j)
        = ConcreteCategory.hom (S.f.1.app (op Z)) (deningerRes S.X₁ hi (E i))
          - ConcreteCategory.hom (S.f.1.app (op Z)) (deningerRes S.X₁ hj (E j)) := by
      rw [hsdiff, hEdiff]
    have hzero : (deningerRes S.X₂ hi (s i)
        - ConcreteCategory.hom (S.f.1.app (op Z)) (deningerRes S.X₁ hi (E i)))
        - (deningerRes S.X₂ hj (s j)
          - ConcreteCategory.hom (S.f.1.app (op Z)) (deningerRes S.X₁ hj (E j))) = 0 := by
      have hrearr : (deningerRes S.X₂ hi (s i)
          - ConcreteCategory.hom (S.f.1.app (op Z)) (deningerRes S.X₁ hi (E i)))
          - (deningerRes S.X₂ hj (s j)
            - ConcreteCategory.hom (S.f.1.app (op Z)) (deningerRes S.X₁ hj (E j)))
          = (deningerRes S.X₂ hi (s i) - deningerRes S.X₂ hj (s j))
            - (ConcreteCategory.hom (S.f.1.app (op Z)) (deningerRes S.X₁ hi (E i))
              - ConcreteCategory.hom (S.f.1.app (op Z)) (deningerRes S.X₁ hj (E j))) := by
        abel
      rw [hrearr, key, sub_self]
    exact sub_eq_zero.1 hzero
  -- glue
  have hcovtop' : (⊤ : Opens X) ≤ ⨆ i : (X : Type u), Vs i := fun x _ =>
    Opens.mem_iSup.2 ⟨x, hxV x⟩
  obtain ⟨b, hb⟩ :=
    deningerGlue' (F := S.X₂) (fun i => le_top) hcovtop' t
      (fun i j Z hi hj => hagree i j Z hi hj)
  refine ⟨b, ?_⟩
  refine deningerRes_ext (F := S.X₃) (fun i : (X : Type u) => (le_top : Vs i ≤ ⊤)) hcovtop' _ _
    fun i => ?_
  rw [deningerRes_app S.g (le_top : Vs i ≤ ⊤) b, hb i, htdef]
  show ConcreteCategory.hom (S.g.1.app (op (Vs i)))
      (s i - ConcreteCategory.hom (S.f.1.app (op (Vs i))) (E i)) = _
  have hfg : ConcreteCategory.hom (S.g.1.app (op (Vs i)))
      (ConcreteCategory.hom (S.f.1.app (op (Vs i))) (E i)) = 0 := by
    rw [← ConcreteCategory.comp_apply,
      show S.f.1.app (op (Vs i)) ≫ S.g.1.app (op (Vs i))
        = (S.f ≫ S.g).1.app (op (Vs i)) from rfl, S.zero]
    rfl
  rw [map_sub, hs i, hfg, sub_zero]

section Acyclic

open CategoryTheory.Abelian

universe w

variable {R : AddSubgroup C(X, ℝ)}
  [CategoryTheory.HasExt.{w} (TopCat.Sheaf AddCommGrpCat.{u} X)]

/-- **A fine sheaf on a paracompact space has no higher cohomology on the whole space.**  Degree one
dies because the sheaf of arbitrary sections of the stalks is flasque and global sections lift; every
higher degree is shifted down one step of the Godement resolution, whose kernels are again fine. -/
theorem deningerFine_ext_eq_zero (hpu : DeningerHasPartitions R) :
    ∀ (n : ℕ) (F : TopCat.Sheaf AddCommGrpCat.{u} X), DeningerFineAction F R →
      ∀ x : deningerSheafCohomology.{w} (⊤ : Opens X) F (n + 1), x = 0 := by
  intro n
  induction n with
  | zero =>
      intro F A x
      refine deningerExt_one_eq_zero_of_lift (deningerGodementShortExact F) ⊤
        ((deningerAcyclic_of_isFlasque (deningerGodementSheaf_isFlasque F)).on ⊤)
        (fun g => deningerFine_sections_surjective (deningerGodementShortExact F) A hpu g) x
  | succ m ih =>
      intro F A x
      exact deningerExt_eq_zero_of_shift (deningerGodementShortExact F) ⊤
        ((deningerAcyclic_of_isFlasque (deningerGodementSheaf_isFlasque F)).on ⊤) m
        (ih _ A.godementQuotient) x

/-- **A fine sheaf is acyclic on the whole space.** -/
theorem deningerFine_acyclicOn (hpu : DeningerHasPartitions R)
    {F : TopCat.Sheaf AddCommGrpCat.{u} X} (A : DeningerFineAction F R) :
    DeningerAcyclicOn.{w} F (⊤ : Opens X) :=
  fun n x => deningerFine_ext_eq_zero hpu n F A x

end Acyclic

end RHTower
