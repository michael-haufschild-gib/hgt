import GaloisForLFunctions.HTGeometry.DifferentialVariationalGrowthStabilization

/-!
# Relative growth filtration modulo an invariant subspace

Transversality of the boundary pair needs the growth theory not just of the coordinate space but of
its quotients by invariant subspaces.  Rather than transport the semilinear action to a quotient,
this leaf runs the whole filtration *relative* to a fixed subspace `W`, entirely inside the
coordinate space: the target of the growth condition is enlarged from the uniformizer dilation
`π^{-m} L` to

```text
variationalRelativeTarget L W m = (π^{-m} L).carrier ⊔ W
```

Because `W` is a subspace over the completed skew field, it is stable under every dilation, so the
absolute arguments port verbatim: the relative slow sets are valuation-ring submodules, their
uniformizer saturations are subspaces, the two sandwich inclusions hold, and the descending chain of
saturations stabilizes.

```text
exists_variationalRelativeSlowSet_eq_attractingCore
    ∃ c₀ ≥ 1, ∀ m ≥ c₀, relative slow set at rate 1/m = relative attracting core
variationalRelativeAttractingSubspace, variationalRelativeAttractingSubspace_carrier
variationalRelativeAttractingSubspace_invariant
le_variationalRelativeAttractingSubspace
```

When `W` is `σ`-invariant the relative attracting core is a `σ`-invariant subspace containing `W`,
so iterating the construction gives an ascending chain, which stabilizes because the coordinate
space is Noetherian over the completed skew field:

```text
exists_variationalRelativeAttractingSubspace_fixedPoint
    ∃ W ⊇ W₀ σ-invariant with variationalRelativeAttractingSubspace σ b L W = W
```

Its relative attracting core is *itself*: nothing outside `W` is asymptotically absorbed into `W`.
Read through the quotient, this says the induced action on the quotient by `W` has trivial
attracting core — the uniform expansion that the slope splitting's contraction estimate consumes.
-/

open scoped Differential BigOperators


namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {C K : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
  [IsConstantBase C K]

set_option synthInstance.maxHeartbeats 1000000 in
/-- Target of the relative growth condition: a uniformizer dilation of the base lattice enlarged
by a fixed subspace. -/
def variationalRelativeTarget {r : ℕ}
    (L : DiffOp.CompletedPseudoDiffOpLattice K (Fin r))
    (W : Submodule (DiffOp.CompletedPseudoDiffOp K) (Fin r → DiffOp.CompletedPseudoDiffOp K))
    (m : ℕ) : Submodule (DiffOp.CompletedPseudoDiffOpInteger (K := K))
      (Fin r → DiffOp.CompletedPseudoDiffOp K) :=
  (DiffOp.leftScaleCompletedPseudoDiffOpLattice
    (DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (-(m : ℤ))) L).carrier ⊔
    W.restrictScalars (DiffOp.CompletedPseudoDiffOpInteger (K := K))

theorem variationalRelativeTarget_mono {r : ℕ}
    (L : DiffOp.CompletedPseudoDiffOpLattice K (Fin r))
    (W : Submodule (DiffOp.CompletedPseudoDiffOp K) (Fin r → DiffOp.CompletedPseudoDiffOp K))
    {m m' : ℕ} (h : m ≤ m') :
    variationalRelativeTarget L W m ≤ variationalRelativeTarget L W m' := by
  refine sup_le_sup_right ?_ _
  exact DiffOp.leftScale_uniformizer_zpow_carrier_antitone L (by omega)

theorem subspace_le_variationalRelativeTarget {r : ℕ}
    (L : DiffOp.CompletedPseudoDiffOpLattice K (Fin r))
    (W : Submodule (DiffOp.CompletedPseudoDiffOp K) (Fin r → DiffOp.CompletedPseudoDiffOp K))
    (m : ℕ) {v : Fin r → DiffOp.CompletedPseudoDiffOp K} (hv : v ∈ W) :
    v ∈ variationalRelativeTarget L W m :=
  Submodule.mem_sup_right hv

/-- Uniformizer dilation of the relative target. -/
theorem uniformizer_smul_mem_variationalRelativeTarget {r : ℕ}
    (L : DiffOp.CompletedPseudoDiffOpLattice K (Fin r))
    (W : Submodule (DiffOp.CompletedPseudoDiffOp K) (Fin r → DiffOp.CompletedPseudoDiffOp K))
    (m z : ℕ) {v : Fin r → DiffOp.CompletedPseudoDiffOp K}
    (hv : v ∈ variationalRelativeTarget L W m) :
    ((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (-(z : ℤ)) :
      (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K) • v ∈
      variationalRelativeTarget L W (z + m) := by
  obtain ⟨a, ha, w, hw, rfl⟩ := Submodule.mem_sup.1 hv
  rw [smul_add]
  refine Submodule.add_mem _ ?_ (Submodule.mem_sup_right (W.smul_mem _ hw))
  refine Submodule.mem_sup_left ?_
  have hscaled := DiffOp.smul_mem_leftScale
    (DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (-(z : ℤ))) _ ha
  rw [DiffOp.leftScaleCompletedPseudoDiffOpLattice_mul, ← zpow_add] at hscaled
  have hexp : (-(z : ℤ)) + (-(m : ℤ)) = -((z + m : ℕ) : ℤ) := by push_cast; ring
  rwa [hexp] at hscaled

/-- Vectors whose variational orbit stays in the relative target at rate at most `1/c`. -/
def variationalRelativeSlowSet (σ : DifferentialFieldAut C K) {r : ℕ}
    (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (L : DiffOp.CompletedPseudoDiffOpLattice K (Fin r))
    (W : Submodule (DiffOp.CompletedPseudoDiffOp K) (Fin r → DiffOp.CompletedPseudoDiffOp K))
    (c : ℕ) : Set (Fin r → DiffOp.CompletedPseudoDiffOp K) :=
  {v | ∀ᶠ n : ℕ in Filter.atTop,
    (σ ^ n).vecBuildingAction b v ∈ variationalRelativeTarget L W (n / c)}

set_option synthInstance.maxHeartbeats 400000 in
/-- The relative slow set is a submodule over the completed valuation ring. -/
def variationalRelativeSlowSubmodule (σ : DifferentialFieldAut C K) {r : ℕ}
    (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (L : DiffOp.CompletedPseudoDiffOpLattice K (Fin r))
    (W : Submodule (DiffOp.CompletedPseudoDiffOp K) (Fin r → DiffOp.CompletedPseudoDiffOp K))
    (c : ℕ) : Submodule (DiffOp.CompletedPseudoDiffOpInteger (K := K))
      (Fin r → DiffOp.CompletedPseudoDiffOp K) where
  carrier := variationalRelativeSlowSet σ b L W c
  add_mem' := by
    intro v w hv hw
    filter_upwards [hv, hw] with n hvn hwn
    have hadd : (σ ^ n).vecBuildingAction b (v + w) =
        (σ ^ n).vecBuildingAction b v + (σ ^ n).vecBuildingAction b w :=
      map_add ((σ ^ n).vecBuildingActionMap b) v w
    rw [hadd]
    exact Submodule.add_mem _ hvn hwn
  zero_mem' := by
    filter_upwards with n
    have hz : (σ ^ n).vecBuildingAction b 0 = 0 :=
      map_zero ((σ ^ n).vecBuildingActionMap b)
    rw [hz]
    exact Submodule.zero_mem _
  smul_mem' := by
    intro a v hv
    filter_upwards [hv] with n hvn
    have hs : (σ ^ n).vecBuildingAction b (a • v) =
        (DiffOp.mapCompletedPseudoIntegerEquiv (σ ^ n).toRingEquiv (σ ^ n).deriv_comm a) •
          (σ ^ n).vecBuildingAction b v :=
      map_smulₛₗ ((σ ^ n).vecBuildingActionMap b) a v
    rw [hs]
    exact Submodule.smul_mem _ _ hvn

@[simp] theorem mem_variationalRelativeSlowSubmodule (σ : DifferentialFieldAut C K) {r : ℕ}
    (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (L : DiffOp.CompletedPseudoDiffOpLattice K (Fin r))
    (W : Submodule (DiffOp.CompletedPseudoDiffOp K) (Fin r → DiffOp.CompletedPseudoDiffOp K))
    (c : ℕ) (v : Fin r → DiffOp.CompletedPseudoDiffOp K) :
    v ∈ variationalRelativeSlowSubmodule σ b L W c ↔
      v ∈ variationalRelativeSlowSet σ b L W c := Iff.rfl

/-- The fixed subspace lies in every relative slow set. -/
theorem subspace_subset_variationalRelativeSlowSet (σ : DifferentialFieldAut C K) {r : ℕ}
    (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (L : DiffOp.CompletedPseudoDiffOpLattice K (Fin r))
    {W : Submodule (DiffOp.CompletedPseudoDiffOp K) (Fin r → DiffOp.CompletedPseudoDiffOp K)}
    (hW : ∀ v ∈ W, σ.vecBuildingAction b v ∈ W) (c : ℕ) :
    (W : Set (Fin r → DiffOp.CompletedPseudoDiffOp K)) ⊆
      variationalRelativeSlowSet σ b L W c := by
  have hpow : ∀ (k : ℕ) (u : Fin r → DiffOp.CompletedPseudoDiffOp K), u ∈ W →
      (σ ^ (k + 1)).vecBuildingAction b u ∈ W := by
    intro k
    induction k with
    | zero =>
        intro u hu
        rw [pow_one]
        exact hW u hu
    | succ k ih =>
        intro u hu
        rw [DifferentialFieldAut.vecBuildingAction_pow_succ]
        exact ih _ (hW u hu)
  intro v hv
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  refine subspace_le_variationalRelativeTarget L W _ ?_
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  exact hpow k v hv


/-- Relative slow sets shrink as the rate index grows. -/
theorem variationalRelativeSlowSet_antitone (σ : DifferentialFieldAut C K) {r : ℕ}
    (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (L : DiffOp.CompletedPseudoDiffOpLattice K (Fin r))
    (W : Submodule (DiffOp.CompletedPseudoDiffOp K) (Fin r → DiffOp.CompletedPseudoDiffOp K))
    {c c' : ℕ} (hc : 1 ≤ c) (hcc : c ≤ c') :
    variationalRelativeSlowSet σ b L W c' ⊆ variationalRelativeSlowSet σ b L W c := by
  intro v hv
  filter_upwards [hv] with n hn
  exact variationalRelativeTarget_mono L W (Nat.div_le_div_left hcc hc) hn

/-- Dilating by a uniformizer power moves a vector one rate index down. -/
theorem uniformizer_smul_mem_variationalRelativeSlowSet (σ : DifferentialFieldAut C K) {r : ℕ}
    (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (L : DiffOp.CompletedPseudoDiffOpLattice K (Fin r))
    (W : Submodule (DiffOp.CompletedPseudoDiffOp K) (Fin r → DiffOp.CompletedPseudoDiffOp K))
    {c : ℕ} (hc : 2 ≤ c) (z : ℕ)
    {v : Fin r → DiffOp.CompletedPseudoDiffOp K}
    (hv : v ∈ variationalRelativeSlowSet σ b L W c) :
    ((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (-(z : ℤ)) :
      (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K) • v ∈
      variationalRelativeSlowSet σ b L W (c - 1) := by
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.1 hv
  refine Filter.eventually_atTop.2 ⟨M + c * z * (c - 1) + c, fun n hn => ?_⟩
  have hbase := hM n (by omega)
  rw [(σ ^ n).vecBuildingAction_smul b,
    (σ ^ n).mapCompletedPseudoRingEquiv_uniformizer_zpow (-(z : ℤ))]
  have hscaled := uniformizer_smul_mem_variationalRelativeTarget L W (n / c) z hbase
  refine variationalRelativeTarget_mono L W ?_ hscaled
  have hq : (n / c) * c ≤ n := Nat.div_mul_le_self _ _
  have hid : (n / c) * (c - 1) + (n / c) = (n / c) * c := by
    cases c with
    | zero => omega
    | succ m =>
        simp only [Nat.succ_sub_one]
        have : (n / (m + 1)) * (m + 1) = (n / (m + 1)) * m + n / (m + 1) := by ring
        omega
  have hzc : z * (c - 1) ≤ n / c := by
    rw [Nat.le_div_iff_mul_le (show 0 < c by omega)]
    have hcomm : z * (c - 1) * c = c * z * (c - 1) := by ring
    omega
  rw [Nat.le_div_iff_mul_le (show 0 < c - 1 by omega)]
  have hdist : (z + n / c) * (c - 1) = z * (c - 1) + (n / c) * (c - 1) := by ring
  omega

set_option synthInstance.maxHeartbeats 400000 in
/-- Vectors that some uniformizer power pushes into a relative slow set. -/
def variationalRelativeSlowSaturation (σ : DifferentialFieldAut C K) {r : ℕ}
    (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (L : DiffOp.CompletedPseudoDiffOpLattice K (Fin r))
    (W : Submodule (DiffOp.CompletedPseudoDiffOp K) (Fin r → DiffOp.CompletedPseudoDiffOp K))
    (c : ℕ) :
    Submodule (DiffOp.CompletedPseudoDiffOp K) (Fin r → DiffOp.CompletedPseudoDiffOp K) where
  carrier := {v | ∃ z : ℕ,
    ((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (z : ℤ) :
      (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K) • v ∈
      variationalRelativeSlowSet σ b L W c}
  add_mem' := by
    rintro v w ⟨zv, hzv⟩ ⟨zw, hzw⟩
    have hsplit : ∀ (y : Fin r → DiffOp.CompletedPseudoDiffOp K) (e : ℕ),
        e ≤ max zv zw →
        ((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (e : ℤ) :
          (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K) • y ∈
          variationalRelativeSlowSet σ b L W c →
        ((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ ((max zv zw : ℕ) : ℤ) :
          (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K) • y ∈
          variationalRelativeSlowSet σ b L W c := by
      intro y e he hy
      have hfac : ((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^
            ((max zv zw : ℕ) : ℤ) : (DiffOp.CompletedPseudoDiffOp K)ˣ) :
            DiffOp.CompletedPseudoDiffOp K) • y =
          ((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ ((max zv zw - e : ℕ) : ℤ) :
            (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K) •
            (((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (e : ℤ) :
              (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K) • y) := by
        rw [smul_smul, ← Units.val_mul, ← zpow_add]
        congr 3
        omega
      rw [hfac]
      exact (variationalRelativeSlowSubmodule σ b L W c).smul_mem
        ⟨_, DiffOp.uniformizer_natPow_mem_integer (K := K) (max zv zw - e)⟩ hy
    refine ⟨max zv zw, ?_⟩
    rw [smul_add]
    exact (variationalRelativeSlowSubmodule σ b L W c).add_mem
      (hsplit v zv (le_max_left _ _) hzv) (hsplit w zw (le_max_right _ _) hzw)
  zero_mem' := ⟨0, by
    rw [smul_zero]
    exact (variationalRelativeSlowSubmodule σ b L W c).zero_mem⟩
  smul_mem' := by
    rintro a v ⟨z, hz⟩
    obtain ⟨t, ht⟩ := DiffOp.exists_uniformizer_left_scale_mem_integer a
    refine ⟨((z : ℤ) + t).toNat, ?_⟩
    set d : ℕ := (((((z : ℤ) + t).toNat : ℕ) : ℤ) - ((z : ℤ) + t)).toNat with hd
    have hsum : (d : ℤ) + ((z : ℤ) + t) = ((((z : ℤ) + t).toNat : ℕ) : ℤ) := by
      simp only [hd]
      omega
    rw [smul_smul, DiffOp.uniformizer_shift_factorization (K := K) z d t _ a hsum,
      ← smul_smul]
    refine (variationalRelativeSlowSubmodule σ b L W c).smul_mem ⟨_, ?_⟩ hz
    exact mul_mem (DiffOp.uniformizer_natPow_mem_integer (K := K) d)
      (DiffOp.uniformizer_conj_mem_integer (K := K) (z : ℤ) ht)

theorem variationalRelativeSlowSet_subset_saturation (σ : DifferentialFieldAut C K) {r : ℕ}
    (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (L : DiffOp.CompletedPseudoDiffOpLattice K (Fin r))
    (W : Submodule (DiffOp.CompletedPseudoDiffOp K) (Fin r → DiffOp.CompletedPseudoDiffOp K))
    (c : ℕ) :
    variationalRelativeSlowSet σ b L W c ⊆
      (variationalRelativeSlowSaturation σ b L W c : Set _) := by
  intro v hv
  refine ⟨0, ?_⟩
  rw [Nat.cast_zero, zpow_zero, Units.val_one, one_smul]
  exact hv

theorem variationalRelativeSlowSaturation_subset_slowSet (σ : DifferentialFieldAut C K) {r : ℕ}
    (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (L : DiffOp.CompletedPseudoDiffOpLattice K (Fin r))
    (W : Submodule (DiffOp.CompletedPseudoDiffOp K) (Fin r → DiffOp.CompletedPseudoDiffOp K))
    {c : ℕ} (hc : 2 ≤ c) :
    (variationalRelativeSlowSaturation σ b L W c : Set _) ⊆
      variationalRelativeSlowSet σ b L W (c - 1) := by
  rintro v ⟨z, hz⟩
  have hshift := uniformizer_smul_mem_variationalRelativeSlowSet σ b L W hc z hz
  have hcancel : ((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (-(z : ℤ)) :
        (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K) •
      (((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (z : ℤ) :
        (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K) • v) = v := by
    rw [smul_smul, ← Units.val_mul, ← zpow_add, neg_add_cancel, zpow_zero, Units.val_one,
      one_smul]
  rwa [hcancel] at hshift

theorem variationalRelativeSlowSaturation_antitone (σ : DifferentialFieldAut C K) {r : ℕ}
    (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (L : DiffOp.CompletedPseudoDiffOpLattice K (Fin r))
    (W : Submodule (DiffOp.CompletedPseudoDiffOp K) (Fin r → DiffOp.CompletedPseudoDiffOp K))
    {c c' : ℕ} (hc : 1 ≤ c) (hcc : c ≤ c') :
    variationalRelativeSlowSaturation σ b L W c' ≤
      variationalRelativeSlowSaturation σ b L W c := by
  rintro v ⟨z, hz⟩
  exact ⟨z, variationalRelativeSlowSet_antitone σ b L W hc hcc hz⟩

/-- The relative attracting core. -/
def variationalRelativeAttractingCore (σ : DifferentialFieldAut C K) {r : ℕ}
    (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (L : DiffOp.CompletedPseudoDiffOpLattice K (Fin r))
    (W : Submodule (DiffOp.CompletedPseudoDiffOp K) (Fin r → DiffOp.CompletedPseudoDiffOp K)) :
    Set (Fin r → DiffOp.CompletedPseudoDiffOp K) :=
  ⋂ c : ℕ, variationalRelativeSlowSet σ b L W (c + 1)

/-- **The relative growth filtration stabilizes.** -/
theorem exists_variationalRelativeSlowSet_eq_attractingCore (σ : DifferentialFieldAut C K)
    {r : ℕ} (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (L : DiffOp.CompletedPseudoDiffOpLattice K (Fin r))
    (W : Submodule (DiffOp.CompletedPseudoDiffOp K) (Fin r → DiffOp.CompletedPseudoDiffOp K)) :
    ∃ c₀ : ℕ, 1 ≤ c₀ ∧ ∀ m, c₀ ≤ m →
      variationalRelativeSlowSet σ b L W m = variationalRelativeAttractingCore σ b L W := by
  classical
  let f : ℕ →o (Submodule (DiffOp.CompletedPseudoDiffOp K)
      (Fin r → DiffOp.CompletedPseudoDiffOp K))ᵒᵈ :=
    { toFun := fun k => OrderDual.toDual (variationalRelativeSlowSaturation σ b L W (k + 1))
      monotone' := by
        intro k k' hkk
        exact OrderDual.toDual_le_toDual.2
          (variationalRelativeSlowSaturation_antitone σ b L W (by omega) (by omega)) }
  obtain ⟨n₀, hn₀⟩ := IsArtinian.monotone_stabilizes f
  have hsat : ∀ m, n₀ + 1 ≤ m →
      variationalRelativeSlowSaturation σ b L W m =
        variationalRelativeSlowSaturation σ b L W (n₀ + 1) := by
    intro m hm
    have hthis := hn₀ (m - 1) (by omega)
    have hm1 : m - 1 + 1 = m := by omega
    have h2 : variationalRelativeSlowSaturation σ b L W (n₀ + 1) =
        variationalRelativeSlowSaturation σ b L W (m - 1 + 1) := hthis
    rw [hm1] at h2
    exact h2.symm
  have hstable : ∀ m, n₀ + 2 ≤ m →
      variationalRelativeSlowSet σ b L W m =
        (variationalRelativeSlowSaturation σ b L W (n₀ + 1) : Set _) := by
    intro m hm
    apply Set.Subset.antisymm
    · rw [← hsat m (by omega)]
      exact variationalRelativeSlowSet_subset_saturation σ b L W m
    · rw [← hsat (m + 1) (by omega)]
      have := variationalRelativeSlowSaturation_subset_slowSet σ b L W
        (c := m + 1) (by omega)
      simpa using this
  refine ⟨n₀ + 2, by omega, fun m hm => ?_⟩
  rw [hstable m hm]
  apply Set.Subset.antisymm
  · intro v hv
    rw [variationalRelativeAttractingCore, Set.mem_iInter]
    intro c
    rcases le_or_gt (n₀ + 2) (c + 1) with hc | hc
    · rw [hstable (c + 1) hc]
      exact hv
    · refine variationalRelativeSlowSet_antitone σ b L W (by omega)
        (show c + 1 ≤ n₀ + 2 by omega) ?_
      rw [hstable (n₀ + 2) (by omega)]
      exact hv
  · intro v hv
    have hmem := Set.mem_iInter.1 hv (n₀ + 1)
    rw [show n₀ + 1 + 1 = n₀ + 2 from rfl] at hmem
    rw [← hstable (n₀ + 2) (by omega)]
    exact hmem


/-- The relative attracting core as a subspace over the completed skew field. -/
def variationalRelativeAttractingSubspace (σ : DifferentialFieldAut C K) {r : ℕ}
    (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (L : DiffOp.CompletedPseudoDiffOpLattice K (Fin r))
    (W : Submodule (DiffOp.CompletedPseudoDiffOp K) (Fin r → DiffOp.CompletedPseudoDiffOp K)) :
    Submodule (DiffOp.CompletedPseudoDiffOp K) (Fin r → DiffOp.CompletedPseudoDiffOp K) :=
  ⨅ c : ℕ, variationalRelativeSlowSaturation σ b L W (c + 1)

theorem variationalRelativeAttractingSubspace_carrier (σ : DifferentialFieldAut C K) {r : ℕ}
    (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (L : DiffOp.CompletedPseudoDiffOpLattice K (Fin r))
    (W : Submodule (DiffOp.CompletedPseudoDiffOp K) (Fin r → DiffOp.CompletedPseudoDiffOp K)) :
    (variationalRelativeAttractingSubspace σ b L W :
        Set (Fin r → DiffOp.CompletedPseudoDiffOp K)) =
      variationalRelativeAttractingCore σ b L W := by
  obtain ⟨c₀, hc₀, hstab⟩ := exists_variationalRelativeSlowSet_eq_attractingCore σ b L W
  apply Set.Subset.antisymm
  · intro v hv
    have h1 : v ∈ variationalRelativeSlowSaturation σ b L W (c₀ + 1) :=
      (Submodule.mem_iInf _).1 hv c₀
    have h2 := variationalRelativeSlowSaturation_subset_slowSet σ b L W
      (c := c₀ + 1) (by omega) h1
    rw [show c₀ + 1 - 1 = c₀ by omega] at h2
    rw [← hstab c₀ le_rfl]
    exact h2
  · intro v hv
    rw [SetLike.mem_coe, variationalRelativeAttractingSubspace, Submodule.mem_iInf _]
    intro c
    exact variationalRelativeSlowSet_subset_saturation σ b L W (c + 1)
      (Set.mem_iInter.1 hv c)

/-- The fixed subspace sits inside its relative attracting subspace. -/
theorem le_variationalRelativeAttractingSubspace (σ : DifferentialFieldAut C K) {r : ℕ}
    (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (L : DiffOp.CompletedPseudoDiffOpLattice K (Fin r))
    {W : Submodule (DiffOp.CompletedPseudoDiffOp K) (Fin r → DiffOp.CompletedPseudoDiffOp K)}
    (hW : ∀ v ∈ W, σ.vecBuildingAction b v ∈ W) :
    W ≤ variationalRelativeAttractingSubspace σ b L W := by
  intro v hv
  have : v ∈ variationalRelativeAttractingCore σ b L W := by
    rw [variationalRelativeAttractingCore, Set.mem_iInter]
    intro c
    exact subspace_subset_variationalRelativeSlowSet σ b L hW (c + 1) hv
  rw [← SetLike.mem_coe, variationalRelativeAttractingSubspace_carrier]
  exact this

/-- The relative attracting core is invariant under the automorphism. -/
theorem variationalRelativeAttractingSubspace_invariant (σ : DifferentialFieldAut C K) {r : ℕ}
    (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (L : DiffOp.CompletedPseudoDiffOpLattice K (Fin r))
    (W : Submodule (DiffOp.CompletedPseudoDiffOp K) (Fin r → DiffOp.CompletedPseudoDiffOp K))
    {v : Fin r → DiffOp.CompletedPseudoDiffOp K}
    (hv : v ∈ variationalRelativeAttractingSubspace σ b L W) :
    σ.vecBuildingAction b v ∈ variationalRelativeAttractingSubspace σ b L W := by
  rw [← SetLike.mem_coe, variationalRelativeAttractingSubspace_carrier] at hv ⊢
  rw [variationalRelativeAttractingCore, Set.mem_iInter] at hv ⊢
  intro c
  have hv2 : v ∈ variationalRelativeSlowSet σ b L W (2 * c + 2) := by
    have h := hv (2 * c + 1)
    have hidx : 2 * c + 1 + 1 = 2 * c + 2 := by omega
    rwa [hidx] at h
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.1 hv2
  refine Filter.eventually_atTop.2 ⟨M, fun n hn => ?_⟩
  have hshift := hM (n + 1) (by omega)
  rw [← DifferentialFieldAut.vecBuildingAction_pow_succ]
  refine variationalRelativeTarget_mono L W ?_ hshift
  have hdm : ((n + 1) / (2 * c + 2)) * (2 * c + 2) ≤ n + 1 := Nat.div_mul_le_self _ _
  have hexp : ((n + 1) / (2 * c + 2)) * (2 * c + 2) =
      2 * (((n + 1) / (2 * c + 2)) * (c + 1)) := by ring
  rw [Nat.le_div_iff_mul_le (show 0 < c + 1 by omega)]
  omega

/-- **The relative tower stabilizes.**  There is a `σ`-invariant subspace above the attracting
subspace whose own relative attracting core is trivial: nothing outside it is asymptotically
absorbed by it. -/
theorem exists_variationalRelativeAttractingSubspace_fixedPoint (σ : DifferentialFieldAut C K)
    {r : ℕ} (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (L : DiffOp.CompletedPseudoDiffOpLattice K (Fin r))
    (W₀ : Submodule (DiffOp.CompletedPseudoDiffOp K) (Fin r → DiffOp.CompletedPseudoDiffOp K))
    (hW₀ : ∀ v ∈ W₀, σ.vecBuildingAction b v ∈ W₀) :
    ∃ W : Submodule (DiffOp.CompletedPseudoDiffOp K) (Fin r → DiffOp.CompletedPseudoDiffOp K),
      W₀ ≤ W ∧ (∀ v ∈ W, σ.vecBuildingAction b v ∈ W) ∧
        variationalRelativeAttractingSubspace σ b L W = W := by
  classical
  let step : Submodule (DiffOp.CompletedPseudoDiffOp K)
      (Fin r → DiffOp.CompletedPseudoDiffOp K) →
      Submodule (DiffOp.CompletedPseudoDiffOp K) (Fin r → DiffOp.CompletedPseudoDiffOp K) :=
    fun W => variationalRelativeAttractingSubspace σ b L W
  let tower : ℕ → Submodule (DiffOp.CompletedPseudoDiffOp K)
      (Fin r → DiffOp.CompletedPseudoDiffOp K) := fun n => step^[n] W₀
  have hinv : ∀ n, ∀ v ∈ tower n, σ.vecBuildingAction b v ∈ tower n := by
    intro n
    induction n with
    | zero => exact hW₀
    | succ n _ =>
        intro v hv
        have hv' : v ∈ step (step^[n] W₀) := by
          rw [← Function.iterate_succ_apply' step n W₀]
          exact hv
        have hout : σ.vecBuildingAction b v ∈ step (step^[n] W₀) :=
          variationalRelativeAttractingSubspace_invariant σ b L _ hv'
        show σ.vecBuildingAction b v ∈ step^[n + 1] W₀
        rw [Function.iterate_succ_apply' step n W₀]
        exact hout
  have hmono : ∀ n, tower n ≤ tower (n + 1) := by
    intro n
    show step^[n] W₀ ≤ step^[n + 1] W₀
    rw [Function.iterate_succ_apply' step n W₀]
    exact le_variationalRelativeAttractingSubspace σ b L (hinv n)
  have hmono' : Monotone tower := monotone_nat_of_le_succ hmono
  obtain ⟨n₀, hn₀⟩ := monotone_stabilizes_iff_noetherian.2 inferInstance ⟨tower, hmono'⟩
  refine ⟨tower n₀, ?_, hinv n₀, ?_⟩
  · exact hmono' (Nat.zero_le n₀)
  · have h : tower n₀ = tower (n₀ + 1) := hn₀ (n₀ + 1) (by omega)
    have h2 : tower (n₀ + 1) = step (tower n₀) := Function.iterate_succ_apply' step n₀ W₀
    rw [h2] at h
    exact h.symm

end

end GaloisForLFunctions.HTGeometry
