import GaloisForLFunctions.HTGeometry.DifferentialVariationalBlockDecomposition

/-!
# The block estimate: slow relative growth over a slow subspace is slow growth

This leaf closes the properness question left open by the relative growth tower.  The statement is
elementary but it is the reason no "parabolic accumulation" can occur in the variational building:

> **Block estimate.**  If `W` is a `σ`-invariant subspace all of whose vectors are slow, then every
> vector that is slow *modulo* `W` is slow.

In an adapted lattice `L = (L ⊓ W) ⊕ (L ⊓ U)` the matrix of `σ` is block triangular, and the orbit of
a complement vector `u₀` unrolls as `σⁿ(u₀) = uₙ + Σ_{j<n} σ^{n-1-j}(aⱼ)` with `uₙ ∈ U`, `aⱼ ∈ W`.
Relative slowness bounds `uₙ`, the splitting of the adapted lattice transfers that bound to `aⱼ`, and
uniform slowness on the finitely generated trace lattice `L ⊓ W` bounds each transported term.  The
accumulated sum then costs **nothing**: every one of its `n` summands lies in the *same* dilation, by
superadditivity of floor division, and a submodule is closed under addition.

Three consequences are recorded.

* `variationalRelativeAttractingCore_subset_variationalAttractingCore` — the estimate itself.
* `variationalRelativeAttractingSubspace_attractingSubspace` — **the canonical attracting subspace is
  already a fixed point of the relative tower.**  The tower of `DifferentialVariationalRelativeGrowth`
  therefore does not need to be iterated at all: `relAttr(F) = F` for `F` the attracting subspace,
  since `F ≤ relAttr(F)` always and the estimate gives the reverse inclusion.
* `exists_proper_invariant_relativeAttracting_fixed_of_translationLength_pos` — in the boundary phase
  `F` is proper, so the boundary datum is a *proper* `σ`-invariant subspace absorbing nothing from
  outside itself.

Nothing here uses a building, a boundary, or a CAT(0) structure; the whole argument is the
non-archimedean fact that a sum of `n` terms of a common size has that size.
-/

open scoped Differential BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {C K : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
  [IsConstantBase C K]

/-- Membership in a uniformizer dilation is a uniformizer bound. -/
theorem DiffOp.mem_leftScale_uniformizer_iff {r : ℕ}
    (L : DiffOp.CompletedPseudoDiffOpLattice K (Fin r)) (m : ℕ)
    (v : Fin r → DiffOp.CompletedPseudoDiffOp K) :
    v ∈ (DiffOp.leftScaleCompletedPseudoDiffOpLattice
        (DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (-(m : ℤ))) L).carrier ↔
      ((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (m : ℤ) :
        (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K) • v ∈ L.carrier := by
  constructor
  · intro h
    have hs := DiffOp.smul_mem_leftScale
      (DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (m : ℤ)) _ h
    rwa [DiffOp.leftScaleCompletedPseudoDiffOpLattice_mul, ← zpow_add, add_neg_cancel, zpow_zero,
      DiffOp.leftScaleCompletedPseudoDiffOpLattice_one] at hs
  · intro h
    have hs := DiffOp.smul_mem_leftScale
      (DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (-(m : ℤ))) L h
    rwa [smul_smul, ← Units.val_mul, ← zpow_add, neg_add_cancel, zpow_zero, Units.val_one,
      one_smul] at hs

set_option synthInstance.maxHeartbeats 1000000 in
/-- A uniformizer power keeps a valuation submodule invariant. -/
theorem DiffOp.uniformizer_smul_mem_submodule {r : ℕ}
    (P : Submodule (DiffOp.CompletedPseudoDiffOpInteger (K := K))
      (Fin r → DiffOp.CompletedPseudoDiffOp K)) (m : ℕ)
    {v : Fin r → DiffOp.CompletedPseudoDiffOp K} (hv : v ∈ P) :
    ((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (m : ℤ) :
      (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K) • v ∈ P := by
  have h := P.smul_mem (DiffOp.uniformizerInteger (K := K) ^ m) hv
  have heq : (DiffOp.uniformizerInteger (K := K) ^ m) • v =
      ((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (m : ℤ) :
        (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K) • v := by
    rw [← DiffOp.coe_uniformizerInteger_pow]
    rfl
  rwa [heq] at h

/-- The vector action preserves an invariant subspace at every power. -/
theorem DifferentialFieldAut.vecBuildingAction_pow_mem_subspace (σ : DifferentialFieldAut C K)
    {r : ℕ} (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (W : Submodule (DiffOp.CompletedPseudoDiffOp K) (Fin r → DiffOp.CompletedPseudoDiffOp K))
    (hinv : ∀ y ∈ W, σ.vecBuildingAction b y ∈ W) :
    ∀ (p : ℕ) (y : Fin r → DiffOp.CompletedPseudoDiffOp K), y ∈ W →
      (σ ^ p).vecBuildingAction b y ∈ W := by
  intro p
  induction p with
  | zero =>
      intro y hy
      rw [pow_zero, DifferentialFieldAut.vecBuildingAction_one]
      exact hy
  | succ p ih =>
      intro y hy
      rw [← σ.vecBuildingAction_succ_left p b y]
      exact hinv _ (ih y hy)

/-- The accumulated block stays in the invariant subspace. -/
theorem variationalBlockSum_mem_subspace (σ : DifferentialFieldAut C K) {r : ℕ}
    (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (W : Submodule (DiffOp.CompletedPseudoDiffOp K) (Fin r → DiffOp.CompletedPseudoDiffOp K))
    (hinv : ∀ y ∈ W, σ.vecBuildingAction b y ∈ W)
    (a : ℕ → Fin r → DiffOp.CompletedPseudoDiffOp K) (ha : ∀ j, a j ∈ W) (n : ℕ) :
    variationalBlockSum σ b a n ∈ W :=
  Submodule.sum_mem _ fun j _ =>
    σ.vecBuildingAction_pow_mem_subspace b W hinv _ _ (ha j)

/-- **Uniform rate bound on a finitely generated slow submodule.** -/
theorem exists_uniform_slow_shift_of_fg (σ : DifferentialFieldAut C K) {r : ℕ}
    (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (L : DiffOp.CompletedPseudoDiffOpLattice K (Fin r))
    (T : Submodule (DiffOp.CompletedPseudoDiffOpInteger (K := K))
      (Fin r → DiffOp.CompletedPseudoDiffOp K)) (hT : T.FG) (c : ℕ)
    (hsub : (T : Set (Fin r → DiffOp.CompletedPseudoDiffOp K)) ⊆ variationalSlowSet σ b L c) :
    ∃ γ : ℕ, ∀ p : ℕ, ∀ y ∈ T, (σ ^ p).vecBuildingAction b y ∈
      (DiffOp.leftScaleCompletedPseudoDiffOpLattice
        (DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (-(((p / c : ℕ) + γ : ℕ) : ℤ)))
        L).carrier := by
  classical
  obtain ⟨s, hs⟩ := hT
  have hev : ∀ᶠ p : ℕ in Filter.atTop, ∀ v ∈ s,
      (σ ^ p).vecBuildingAction b v ∈ (DiffOp.leftScaleCompletedPseudoDiffOpLattice
        (DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (-((p / c : ℕ) : ℤ)))
        L).carrier := by
    refine (Filter.eventually_all_finset s).2 fun v hv => ?_
    have hvT : v ∈ T := by rw [← hs]; exact Submodule.subset_span hv
    exact hsub hvT
  obtain ⟨P, hP⟩ := Filter.eventually_atTop.1 hev
  obtain ⟨γ₀, hγ₀⟩ := DiffOp.exists_nat_finset_mem_leftScale L
    ((Finset.range P ×ˢ s).image fun q => (σ ^ q.1).vecBuildingAction b q.2)
  refine ⟨γ₀, fun p y hy => ?_⟩
  have hgen : ∀ v ∈ s, (σ ^ p).vecBuildingAction b v ∈
      (DiffOp.leftScaleCompletedPseudoDiffOpLattice
        (DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^
          (-(((p / c : ℕ) + γ₀ : ℕ) : ℤ))) L).carrier := by
    intro v hv
    by_cases hp : P ≤ p
    · refine DiffOp.leftScale_uniformizer_zpow_carrier_antitone L ?_ (hP p hp v hv)
      exact neg_le_neg (by exact_mod_cast Nat.le_add_right (p / c) γ₀)
    · have hmem : (σ ^ p).vecBuildingAction b v ∈
          (Finset.range P ×ˢ s).image fun q => (σ ^ q.1).vecBuildingAction b q.2 :=
        Finset.mem_image.2 ⟨(p, v), Finset.mem_product.2
          ⟨Finset.mem_range.2 (by omega), hv⟩, rfl⟩
      refine DiffOp.leftScale_uniformizer_zpow_carrier_antitone L ?_ (hγ₀ _ hmem)
      exact neg_le_neg (by exact_mod_cast Nat.le_add_left γ₀ (p / c))
  have hmap : Submodule.map ((σ ^ p).vecBuildingActionMap b) T ≤
      (DiffOp.leftScaleCompletedPseudoDiffOpLattice
        (DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^
          (-(((p / c : ℕ) + γ₀ : ℕ) : ℤ))) L).carrier := by
    rw [← hs, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨v, hv, rfl⟩
    exact hgen v hv
  exact hmap ⟨y, hy, rfl⟩

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 1000000 in
/-- **The block estimate.**  Over a slow invariant subspace, slow relative growth is absolute slow
growth: the accumulated off-diagonal block costs nothing in rate. -/
theorem variationalRelativeAttractingCore_subset_variationalAttractingCore
    (σ : DifferentialFieldAut C K) {r : ℕ}
    (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (L : DiffOp.CompletedPseudoDiffOpLattice K (Fin r))
    (W : Submodule (DiffOp.CompletedPseudoDiffOp K) (Fin r → DiffOp.CompletedPseudoDiffOp K))
    (hinvW : ∀ y ∈ W, σ.vecBuildingAction b y ∈ W)
    (hW : (W : Set (Fin r → DiffOp.CompletedPseudoDiffOp K)) ⊆ variationalAttractingCore σ b L) :
    variationalRelativeAttractingCore σ b L W ⊆ variationalAttractingCore σ b L := by
  classical
  obtain ⟨U, hcompl⟩ := Submodule.exists_isCompl W
  have hWU : W ⊔ U = ⊤ := hcompl.sup_eq_top
  have hdisj : Disjoint W U := hcompl.disjoint
  set L' := adaptedTraceLattice L W U hWU with hL'def
  have hW' : (W : Set (Fin r → DiffOp.CompletedPseudoDiffOp K)) ⊆
      variationalAttractingCore σ b L' := by
    rw [← variationalAttractingCore_base_independent σ b L L']
    exact hW
  have hTUle : subspaceTraceLattice L U ≤ L'.carrier := le_sup_right
  have hkey : ∀ u₀ ∈ U, u₀ ∈ variationalRelativeAttractingCore σ b L' W →
      u₀ ∈ variationalAttractingCore σ b L' := by
    intro u₀ hu₀ hu₀rel
    rw [variationalAttractingCore, Set.mem_iInter]
    intro c
    set d := 2 * (c + 1) with hddef
    obtain ⟨uu, aa, hu0, hUmem, hWmem, hrecur, hunroll⟩ :=
      exists_variationalBlockDecomposition σ b W U hWU hu₀
    have hblockW : ∀ n, variationalBlockSum σ b aa n ∈ W :=
      variationalBlockSum_mem_subspace σ b W hinvW aa hWmem
    have hrelu : u₀ ∈ variationalRelativeSlowSet σ b L' W d := by
      have h := Set.mem_iInter.1 hu₀rel (2 * c + 1)
      rwa [show 2 * c + 1 + 1 = d from by omega] at h
    obtain ⟨J, hJ⟩ := Filter.eventually_atTop.1 hrelu
    -- the complement components are slow, eventually
    have hstepU : ∀ j, J ≤ j →
        ((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ ((j / d : ℕ) : ℤ) :
          (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K) • uu j ∈
          subspaceTraceLattice L U := by
      intro j hj
      have h1 := hJ j hj
      have h2 : uu j ∈ variationalRelativeTarget L' W (j / d) := by
        have heq : uu j = (σ ^ j).vecBuildingAction b u₀ - variationalBlockSum σ b aa j := by
          rw [hunroll j]; abel
        rw [heq]
        exact Submodule.sub_mem _ h1 (Submodule.mem_sup_right (hblockW j))
      obtain ⟨l, hl, w, hw, hlw⟩ := Submodule.mem_sup.1 h2
      have hlmem : ((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ ((j / d : ℕ) : ℤ) :
          (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K) • l ∈ L'.carrier :=
        (DiffOp.mem_leftScale_uniformizer_iff L' (j / d) l).1 hl
      obtain ⟨w₁, u₁, hsplit, hw₁, hu₁, hw₁T, hu₁T⟩ :=
        exists_split_of_uniformizer_smul_mem_adaptedTraceLattice L W U hWU (j / d) hlmem
      have hsub : uu j - u₁ = w₁ + w := by rw [← hlw, hsplit]; abel
      have hmemW : uu j - u₁ ∈ W := by rw [hsub]; exact W.add_mem hw₁ hw
      have hmemU : uu j - u₁ ∈ U := U.sub_mem (hUmem j) hu₁
      have hzero : uu j - u₁ = 0 := Submodule.disjoint_def.1 hdisj _ hmemW hmemU
      rw [sub_eq_zero.1 hzero]
      exact hu₁T
    -- the finitely many early components are confined by one constant
    obtain ⟨k₀, hk₀⟩ := DiffOp.exists_nat_finset_mem_leftScale L ((Finset.range J).image uu)
    have hsmallU : ∀ j, j < J →
        ((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ ((k₀ : ℕ) : ℤ) :
          (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K) • uu j ∈
          subspaceTraceLattice L U := by
      intro j hj
      have hmem : uu j ∈ (Finset.range J).image uu :=
        Finset.mem_image.2 ⟨j, Finset.mem_range.2 hj, rfl⟩
      refine Submodule.mem_inf.2 ⟨(DiffOp.mem_leftScale_uniformizer_iff L k₀ (uu j)).1
        (hk₀ _ hmem), ?_⟩
      exact U.smul_mem _ (hUmem j)
    have huniU : ∀ j,
        ((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (((j / d + k₀ : ℕ) : ℕ) : ℤ) :
          (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K) • uu j ∈
          subspaceTraceLattice L U := by
      intro j
      by_cases hj : J ≤ j
      · have h := DiffOp.uniformizer_smul_mem_submodule (subspaceTraceLattice L U) k₀
          (hstepU j hj)
        rwa [smul_smul, ← Units.val_mul, ← zpow_add,
          show ((k₀ : ℕ) : ℤ) + ((j / d : ℕ) : ℤ) = (((j / d + k₀ : ℕ) : ℕ) : ℤ) from by
            push_cast; ring] at h
      · have h := DiffOp.uniformizer_smul_mem_submodule (subspaceTraceLattice L U) (j / d)
          (hsmallU j (by omega))
        rwa [smul_smul, ← Units.val_mul, ← zpow_add,
          show ((j / d : ℕ) : ℤ) + ((k₀ : ℕ) : ℤ) = (((j / d + k₀ : ℕ) : ℕ) : ℤ) from by
            push_cast; ring] at h
    -- boundedness of one step of the action on the adapted lattice
    obtain ⟨β, hβ⟩ := DiffOp.exists_nat_carrier_le_leftScale_uniformizer L'
      (σ.latticeBuildingAction b L')
    -- the off-diagonal terms are slow
    have hAA : ∀ j,
        ((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^
          (((j / d + (k₀ + β) : ℕ) : ℕ) : ℤ) :
          (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K) • aa j ∈
          subspaceTraceLattice L W := by
      intro j
      have h1 : ((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^
          (((j / d + k₀ : ℕ) : ℕ) : ℤ) :
          (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K) • uu j ∈
          L'.carrier := hTUle (huniU j)
      have h3 := σ.vecBuildingAction_mem b L' h1
      have h4 : σ.vecBuildingAction b
          (((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^
            (((j / d + k₀ : ℕ) : ℕ) : ℤ) :
            (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K) • uu j) =
          ((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^
            (((j / d + k₀ : ℕ) : ℕ) : ℤ) :
            (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K) •
            σ.vecBuildingAction b (uu j) := by
        rw [σ.vecBuildingAction_smul b,
          σ.mapCompletedPseudoRingEquiv_uniformizer_zpow (((j / d + k₀ : ℕ) : ℕ) : ℤ)]
      rw [h4] at h3
      have h5 := hβ h3
      have h6 : ((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^
          (((j / d + (k₀ + β) : ℕ) : ℕ) : ℤ) :
          (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K) •
          σ.vecBuildingAction b (uu j) ∈ L'.carrier := by
        have h7 := (DiffOp.mem_leftScale_uniformizer_iff L' β _).1 h5
        rwa [smul_smul, ← Units.val_mul, ← zpow_add,
          show ((β : ℕ) : ℤ) + (((j / d + k₀ : ℕ) : ℕ) : ℤ) =
            (((j / d + (k₀ + β) : ℕ) : ℕ) : ℤ) from by push_cast; ring] at h7
      obtain ⟨w₂, u₂, hsplit2, hw₂, hu₂, hw₂T, hu₂T⟩ :=
        exists_split_of_uniformizer_smul_mem_adaptedTraceLattice L W U hWU
          (j / d + (k₀ + β)) h6
      have hrec := hrecur j
      have hsub2 : aa j - w₂ = u₂ - uu (j + 1) := by
        have hsum : aa j + uu (j + 1) = w₂ + u₂ := by rw [← hrec, hsplit2]
        linear_combination (norm := abel) hsum
      have hmemW2 : aa j - w₂ ∈ W := W.sub_mem (hWmem j) hw₂
      have hmemU2 : aa j - w₂ ∈ U := by rw [hsub2]; exact U.sub_mem hu₂ (hUmem (j + 1))
      have hzero2 : aa j - w₂ = 0 := Submodule.disjoint_def.1 hdisj _ hmemW2 hmemU2
      rw [sub_eq_zero.1 hzero2]
      exact hw₂T
    -- uniform slowness on the trace lattice of `W`
    have hTWslow : (subspaceTraceLattice L W : Set (Fin r → DiffOp.CompletedPseudoDiffOp K)) ⊆
        variationalSlowSet σ b L' d := by
      intro y hy
      have hyW : y ∈ W := subspaceTraceLattice_le_subspace L W hy
      have h := Set.mem_iInter.1 (hW' hyW) (2 * c + 1)
      rwa [show 2 * c + 1 + 1 = d from by omega] at h
    obtain ⟨γ, hγ⟩ := exists_uniform_slow_shift_of_fg σ b L' (subspaceTraceLattice L W)
      (subspaceTraceLattice_fg L W) d hTWslow
    have hblock : ∀ n, variationalBlockSum σ b aa n ∈
        (DiffOp.leftScaleCompletedPseudoDiffOpLattice
          (DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^
            (-(((n / d : ℕ) + (k₀ + β) + γ : ℕ) : ℤ))) L').carrier := fun n =>
      variationalBlockSum_mem σ b L' (subspaceTraceLattice L W) d γ (k₀ + β) hγ aa hAA n
    have hucomp : ∀ n, uu n ∈
        (DiffOp.leftScaleCompletedPseudoDiffOpLattice
          (DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^
            (-(((n / d : ℕ) + (k₀ + β) + γ : ℕ) : ℤ))) L').carrier := by
      intro n
      have h := (DiffOp.mem_leftScale_uniformizer_iff L' (n / d + k₀) (uu n)).2
        (hTUle (huniU n))
      refine DiffOp.leftScale_uniformizer_zpow_carrier_antitone L' ?_ h
      exact neg_le_neg (by exact_mod_cast (by omega : n / d + k₀ ≤ n / d + (k₀ + β) + γ))
    refine Filter.eventually_atTop.2 ⟨d * ((k₀ + β) + γ), fun n hn => ?_⟩
    have hsum : (σ ^ n).vecBuildingAction b u₀ ∈
        (DiffOp.leftScaleCompletedPseudoDiffOpLattice
          (DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^
            (-(((n / d : ℕ) + (k₀ + β) + γ : ℕ) : ℤ))) L').carrier := by
      rw [hunroll n]
      exact Submodule.add_mem _ (hucomp n) (hblock n)
    refine DiffOp.leftScale_uniformizer_zpow_carrier_antitone L' ?_ hsum
    have hstep : n / d + ((k₀ + β) + γ) ≤ n / (c + 1) := by
      refine nat_div_two_mul_add_le (c := c) (k := (k₀ + β) + γ) (n := n) ?_
      rw [← hddef]; exact hn
    exact neg_le_neg (by exact_mod_cast (by omega : n / d + (k₀ + β) + γ ≤ n / (c + 1)))
  -- every vector splits into a `W`-part and a complement part, and both are slow
  intro x hx
  have hx' : x ∈ variationalRelativeAttractingCore σ b L' W := by
    rw [← variationalRelativeAttractingCore_base_independent σ b L L' W]
    exact hx
  have hxmem : x ∈ variationalAttractingCore σ b L' := by
    have hxtop : x ∈ (⊤ : Submodule (DiffOp.CompletedPseudoDiffOp K)
      (Fin r → DiffOp.CompletedPseudoDiffOp K)) := Submodule.mem_top
    rw [← hWU] at hxtop
    obtain ⟨w, hw, u, hu, hwu⟩ := Submodule.mem_sup.1 hxtop
    have hwrel : w ∈ variationalRelativeAttractingSubspace σ b L' W :=
      le_variationalRelativeAttractingSubspace σ b L' hinvW hw
    have hxrel : x ∈ variationalRelativeAttractingSubspace σ b L' W := by
      rw [← SetLike.mem_coe, variationalRelativeAttractingSubspace_carrier]
      exact hx'
    have hurel : u ∈ variationalRelativeAttractingSubspace σ b L' W := by
      have hueq : u = x - w := by rw [← hwu]; abel
      rw [hueq]
      exact Submodule.sub_mem _ hxrel hwrel
    have hurel' : u ∈ variationalRelativeAttractingCore σ b L' W := by
      rw [← variationalRelativeAttractingSubspace_carrier σ b L' W]
      exact hurel
    rw [variationalAttractingCore, Set.mem_iInter]
    intro c
    have h1 : w ∈ variationalSlowSubmodule σ b L' (c + 1) := Set.mem_iInter.1 (hW' hw) c
    have h2 : u ∈ variationalSlowSubmodule σ b L' (c + 1) :=
      Set.mem_iInter.1 (hkey u hu hurel') c
    rw [← hwu]
    exact (variationalSlowSubmodule σ b L' (c + 1)).add_mem h1 h2
  rw [variationalAttractingCore_base_independent σ b L L']
  exact hxmem

/-- A full relative core over a slow invariant subspace forces a full absolute core. -/
theorem variationalAttractingCore_eq_univ_of_block (σ : DifferentialFieldAut C K) {r : ℕ}
    (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (L : DiffOp.CompletedPseudoDiffOpLattice K (Fin r))
    (W : Submodule (DiffOp.CompletedPseudoDiffOp K) (Fin r → DiffOp.CompletedPseudoDiffOp K))
    (hinvW : ∀ y ∈ W, σ.vecBuildingAction b y ∈ W)
    (hW : (W : Set (Fin r → DiffOp.CompletedPseudoDiffOp K)) ⊆ variationalAttractingCore σ b L)
    (hrel : variationalRelativeAttractingCore σ b L W = Set.univ) :
    variationalAttractingCore σ b L = Set.univ :=
  Set.eq_univ_of_forall fun x =>
    variationalRelativeAttractingCore_subset_variationalAttractingCore σ b L W hinvW hW
      (by rw [hrel]; trivial)

/-- **The canonical attracting subspace is already a fixed point of the relative tower.**  Nothing
outside it is asymptotically absorbed by it. -/
theorem variationalRelativeAttractingSubspace_attractingSubspace
    (σ : DifferentialFieldAut C K) {r : ℕ}
    (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (L : DiffOp.CompletedPseudoDiffOpLattice K (Fin r)) :
    variationalRelativeAttractingSubspace σ b L (variationalAttractingSubspace σ b L) =
      variationalAttractingSubspace σ b L := by
  refine le_antisymm ?_ (le_variationalRelativeAttractingSubspace σ b L
    (fun _ hv => variationalAttractingSubspace_invariant σ b L hv))
  intro x hx
  have hx' : x ∈ variationalRelativeAttractingCore σ b L (variationalAttractingSubspace σ b L) := by
    rw [← variationalRelativeAttractingSubspace_carrier σ b L]
    exact hx
  exact variationalRelativeAttractingCore_subset_variationalAttractingCore σ b L
    (variationalAttractingSubspace σ b L)
    (fun _ hv => variationalAttractingSubspace_invariant σ b L hv)
    (fun _ hv => hv) hx'

/-- **The boundary datum.**  In the boundary phase the canonical attracting subspace is a proper
`σ`-invariant subspace whose relative attracting subspace is itself. -/
theorem exists_proper_invariant_relativeAttracting_fixed_of_translationLength_pos
    (σ : DifferentialFieldAut C K) {r : ℕ}
    (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (L : DiffOp.CompletedPseudoDiffOpLattice K (Fin r))
    (hpos : 0 < differentialVariationalEuclideanTranslationLength b (Quotient.mk _ L) σ) :
    ∃ F : Submodule (DiffOp.CompletedPseudoDiffOp K) (Fin r → DiffOp.CompletedPseudoDiffOp K),
      F ≠ ⊤ ∧ (∀ v ∈ F, σ.vecBuildingAction b v ∈ F) ∧
        variationalRelativeAttractingSubspace σ b L F = F :=
  ⟨variationalAttractingSubspace σ b L,
    (variationalAttractingSubspace_ne_top_iff_translationLength_pos σ b L).2 hpos,
    fun _ hv => variationalAttractingSubspace_invariant σ b L hv,
    variationalRelativeAttractingSubspace_attractingSubspace σ b L⟩

end

end GaloisForLFunctions.HTGeometry
