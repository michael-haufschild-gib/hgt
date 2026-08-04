import GaloisForLFunctions.HilbertMetric.SymmetricFockShadow

/-!
# Supermodularity of linear-family deficiency

For a finite-dimensional linear-map family, send a subspace to the span of
all its images and define deficiency as input dimension minus image-span
dimension.  This deficiency is supermodular on the subspace lattice.  The
result is the lattice mechanism behind canonical maximal shrunk subspaces in
operator scaling.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Span of every image of `U` under a linear-map family. -/
def linearFamilyShadow
    {𝕜 X Y J : Type*}
    [DivisionRing 𝕜]
    [AddCommGroup X] [Module 𝕜 X]
    [AddCommGroup Y] [Module 𝕜 Y]
    (A : J → X →ₗ[𝕜] Y) (U : Submodule 𝕜 X) : Submodule 𝕜 Y :=
  ⨆ j, U.map (A j)

/-- Family shadow preserves joins of input subspaces. -/
theorem linearFamilyShadow_sup
    {𝕜 X Y J : Type*}
    [DivisionRing 𝕜]
    [AddCommGroup X] [Module 𝕜 X]
    [AddCommGroup Y] [Module 𝕜 Y]
    (A : J → X →ₗ[𝕜] Y) (U W : Submodule 𝕜 X) :
    linearFamilyShadow A (U ⊔ W) =
      linearFamilyShadow A U ⊔ linearFamilyShadow A W := by
  simp only [linearFamilyShadow, Submodule.map_sup, iSup_sup_eq]

/-- Family shadow of an intersection lies in the intersection of shadows. -/
theorem linearFamilyShadow_inf_le
    {𝕜 X Y J : Type*}
    [DivisionRing 𝕜]
    [AddCommGroup X] [Module 𝕜 X]
    [AddCommGroup Y] [Module 𝕜 Y]
    (A : J → X →ₗ[𝕜] Y) (U W : Submodule 𝕜 X) :
    linearFamilyShadow A (U ⊓ W) ≤
      linearFamilyShadow A U ⊓ linearFamilyShadow A W := by
  apply le_inf
  · apply iSup_le
    intro j
    exact (Submodule.map_mono inf_le_left).trans
      (le_iSup (fun k => U.map (A k)) j)
  · apply iSup_le
    intro j
    exact (Submodule.map_mono inf_le_right).trans
      (le_iSup (fun k => W.map (A k)) j)

/-- Integer deficiency of one subspace under a linear-map family. -/
def linearFamilyDefect
    {𝕜 X Y J : Type*}
    [DivisionRing 𝕜]
    [AddCommGroup X] [Module 𝕜 X]
    [AddCommGroup Y] [Module 𝕜 Y]
    [FiniteDimensional 𝕜 X] [FiniteDimensional 𝕜 Y]
    (A : J → X →ₗ[𝕜] Y) (U : Submodule 𝕜 X) : ℤ :=
  (Module.finrank 𝕜 U : ℤ) -
    (Module.finrank 𝕜 (linearFamilyShadow A U) : ℤ)

/-- Hall expansion for every input subspace. -/
def LinearFamilyHall
    {𝕜 X Y J : Type*}
    [DivisionRing 𝕜]
    [AddCommGroup X] [Module 𝕜 X]
    [AddCommGroup Y] [Module 𝕜 Y]
    [FiniteDimensional 𝕜 X] [FiniteDimensional 𝕜 Y]
    (A : J → X →ₗ[𝕜] Y) : Prop :=
  ∀ U : Submodule 𝕜 X,
    Module.finrank 𝕜 U ≤ Module.finrank 𝕜 (linearFamilyShadow A U)

/-- Hall expansion is exactly nonpositivity of deficiency on every
subspace. -/
theorem linearFamilyHall_iff_defect_nonpos
    {𝕜 X Y J : Type*}
    [DivisionRing 𝕜]
    [AddCommGroup X] [Module 𝕜 X]
    [AddCommGroup Y] [Module 𝕜 Y]
    [FiniteDimensional 𝕜 X] [FiniteDimensional 𝕜 Y]
    (A : J → X →ₗ[𝕜] Y) :
    LinearFamilyHall A ↔
      ∀ U : Submodule 𝕜 X, linearFamilyDefect A U ≤ 0 := by
  constructor
  · intro hHall U
    have h := hHall U
    dsimp [linearFamilyDefect]
    omega
  · intro hdefect U
    have h := hdefect U
    dsimp [linearFamilyDefect] at h
    omega

@[simp]
theorem linearFamilyShadow_bot
    {𝕜 X Y J : Type*}
    [DivisionRing 𝕜]
    [AddCommGroup X] [Module 𝕜 X]
    [AddCommGroup Y] [Module 𝕜 Y]
    (A : J → X →ₗ[𝕜] Y) :
    linearFamilyShadow A (⊥ : Submodule 𝕜 X) = ⊥ := by
  simp [linearFamilyShadow]

@[simp]
theorem linearFamilyDefect_bot
    {𝕜 X Y J : Type*}
    [DivisionRing 𝕜]
    [AddCommGroup X] [Module 𝕜 X]
    [AddCommGroup Y] [Module 𝕜 Y]
    [FiniteDimensional 𝕜 X] [FiniteDimensional 𝕜 Y]
    (A : J → X →ₗ[𝕜] Y) :
    linearFamilyDefect A (⊥ : Submodule 𝕜 X) = 0 := by
  simp [linearFamilyDefect]

/-- Linear-family deficiency is supermodular on the subspace lattice. -/
theorem linearFamilyDefect_supermodular
    {𝕜 X Y J : Type*}
    [DivisionRing 𝕜]
    [AddCommGroup X] [Module 𝕜 X]
    [AddCommGroup Y] [Module 𝕜 Y]
    [FiniteDimensional 𝕜 X] [FiniteDimensional 𝕜 Y]
    (A : J → X →ₗ[𝕜] Y) (U W : Submodule 𝕜 X) :
    linearFamilyDefect A U + linearFamilyDefect A W ≤
      linearFamilyDefect A (U ⊔ W) + linearFamilyDefect A (U ⊓ W) := by
  have hX := Submodule.finrank_sup_add_finrank_inf_eq U W
  have hY := Submodule.finrank_sup_add_finrank_inf_eq
    (linearFamilyShadow A U) (linearFamilyShadow A W)
  have hmono : Module.finrank 𝕜 (linearFamilyShadow A (U ⊓ W)) ≤
      Module.finrank 𝕜
        ((linearFamilyShadow A U ⊓ linearFamilyShadow A W) :
          Submodule 𝕜 Y) :=
    Submodule.finrank_mono (linearFamilyShadow_inf_le A U W)
  have hsup : Module.finrank 𝕜 (linearFamilyShadow A (U ⊔ W)) =
      Module.finrank 𝕜
        ((linearFamilyShadow A U ⊔ linearFamilyShadow A W) :
          Submodule 𝕜 Y) := by
    rw [linearFamilyShadow_sup]
  dsimp [linearFamilyDefect]
  omega

/-- Family deficiency is bounded above by ambient input dimension. -/
theorem linearFamilyDefect_le_finrank
    {𝕜 X Y J : Type*}
    [DivisionRing 𝕜]
    [AddCommGroup X] [Module 𝕜 X]
    [AddCommGroup Y] [Module 𝕜 Y]
    [FiniteDimensional 𝕜 X] [FiniteDimensional 𝕜 Y]
    (A : J → X →ₗ[𝕜] Y) (U : Submodule 𝕜 X) :
    linearFamilyDefect A U ≤ (Module.finrank 𝕜 X : ℤ) := by
  have hU : Module.finrank 𝕜 U ≤ Module.finrank 𝕜 X :=
    Submodule.finrank_le U
  have hshadow :
      0 ≤ (Module.finrank 𝕜 (linearFamilyShadow A U) : ℤ) := by
    omega
  dsimp [linearFamilyDefect]
  omega

/-- A finite-dimensional linear family has a defect maximizer whose dimension
is maximal among all defect maximizers. -/
theorem exists_linearFamilyDefect_maxFinrank_maximizer
    {𝕜 X Y J : Type*}
    [DivisionRing 𝕜]
    [AddCommGroup X] [Module 𝕜 X]
    [AddCommGroup Y] [Module 𝕜 Y]
    [FiniteDimensional 𝕜 X] [FiniteDimensional 𝕜 Y]
    (A : J → X →ₗ[𝕜] Y) :
    ∃ U : Submodule 𝕜 X,
      (∀ V : Submodule 𝕜 X,
        linearFamilyDefect A V ≤ linearFamilyDefect A U) ∧
      (∀ V : Submodule 𝕜 X,
        linearFamilyDefect A V = linearFamilyDefect A U →
          Module.finrank 𝕜 V ≤ Module.finrank 𝕜 U) := by
  let defects : Set ℤ := Set.range (linearFamilyDefect A)
  have hdefects_nonempty : defects.Nonempty :=
    Set.range_nonempty (linearFamilyDefect A)
  have hdefects_bdd : BddAbove defects := by
    refine ⟨(Module.finrank 𝕜 X : ℤ), ?_⟩
    rintro d ⟨U, rfl⟩
    exact linearFamilyDefect_le_finrank A U
  have hmax_mem : sSup defects ∈ defects :=
    Int.csSup_mem hdefects_nonempty hdefects_bdd
  obtain ⟨U₀, hdefectU₀⟩ := hmax_mem
  have hmax₀ : ∀ V : Submodule 𝕜 X,
      linearFamilyDefect A V ≤ linearFamilyDefect A U₀ := by
    intro V
    rw [hdefectU₀]
    exact le_csSup hdefects_bdd ⟨V, rfl⟩
  let ranks : Set ℕ := {r | ∃ V : Submodule 𝕜 X,
    linearFamilyDefect A V = linearFamilyDefect A U₀ ∧
      Module.finrank 𝕜 V = r}
  have hranks_nonempty : ranks.Nonempty :=
    ⟨Module.finrank 𝕜 U₀, U₀, rfl, rfl⟩
  have hranks_bdd : BddAbove ranks := by
    refine ⟨Module.finrank 𝕜 X, ?_⟩
    rintro r ⟨V, -, rfl⟩
    exact Submodule.finrank_le V
  have hrank_mem : sSup ranks ∈ ranks :=
    Nat.sSup_mem hranks_nonempty hranks_bdd
  obtain ⟨U, hdefectU, hrankU⟩ := hrank_mem
  refine ⟨U, ?_, ?_⟩
  · intro V
    rw [hdefectU]
    exact hmax₀ V
  · intro V hdefectV
    rw [hrankU]
    exact le_csSup hranks_bdd ⟨V, hdefectV.trans hdefectU, rfl⟩

/-- A maximum-defect subspace of maximum dimension contains every defect
maximizer.  Thus maximum deficiency has one canonical largest witness. -/
theorem linearFamilyDefect_maxFinrank_maximizer_is_greatest
    {𝕜 X Y J : Type*}
    [DivisionRing 𝕜]
    [AddCommGroup X] [Module 𝕜 X]
    [AddCommGroup Y] [Module 𝕜 Y]
    [FiniteDimensional 𝕜 X] [FiniteDimensional 𝕜 Y]
    (A : J → X →ₗ[𝕜] Y) (U : Submodule 𝕜 X)
    (hmax : ∀ V : Submodule 𝕜 X,
      linearFamilyDefect A V ≤ linearFamilyDefect A U)
    (hmaxFinrank : ∀ V : Submodule 𝕜 X,
      linearFamilyDefect A V = linearFamilyDefect A U →
        Module.finrank 𝕜 V ≤ Module.finrank 𝕜 U) :
    ∀ V : Submodule 𝕜 X,
      linearFamilyDefect A V = linearFamilyDefect A U → V ≤ U := by
  intro V hV
  have hsuper := linearFamilyDefect_supermodular A U V
  have hsup_le := hmax (U ⊔ V)
  have hinf_le := hmax (U ⊓ V)
  have hsup_eq :
      linearFamilyDefect A (U ⊔ V) = linearFamilyDefect A U := by
    omega
  have hrank : Module.finrank 𝕜 ((U ⊔ V) : Submodule 𝕜 X) ≤
      Module.finrank 𝕜 U :=
    hmaxFinrank (U ⊔ V) hsup_eq
  have heq : U = U ⊔ V :=
    Submodule.eq_of_le_of_finrank_le le_sup_left hrank
  exact le_sup_right.trans_eq heq.symm

/-- The largest defect maximizer exists and is unique. -/
theorem existsUnique_linearFamilyDefect_greatestMaximizer
    {𝕜 X Y J : Type*}
    [DivisionRing 𝕜]
    [AddCommGroup X] [Module 𝕜 X]
    [AddCommGroup Y] [Module 𝕜 Y]
    [FiniteDimensional 𝕜 X] [FiniteDimensional 𝕜 Y]
    (A : J → X →ₗ[𝕜] Y) :
    ∃! U : Submodule 𝕜 X,
      (∀ V : Submodule 𝕜 X,
        linearFamilyDefect A V ≤ linearFamilyDefect A U) ∧
      (∀ V : Submodule 𝕜 X,
        linearFamilyDefect A V = linearFamilyDefect A U → V ≤ U) := by
  obtain ⟨U, hmax, hmaxFinrank⟩ :=
    exists_linearFamilyDefect_maxFinrank_maximizer A
  have hgreatest :=
    linearFamilyDefect_maxFinrank_maximizer_is_greatest
      A U hmax hmaxFinrank
  refine ⟨U, ⟨hmax, hgreatest⟩, ?_⟩
  intro W hW
  have hdefect : linearFamilyDefect A U = linearFamilyDefect A W :=
    le_antisymm (hW.1 U) (hmax W)
  exact le_antisymm (hgreatest W hdefect.symm) (hW.2 U hdefect)

/-- Once `U` maximizes deficiency, the entire all-subspaces Hall condition is
equivalent to the single scalar equation `defect U = 0`. -/
theorem linearFamilyHall_iff_maximizer_defect_eq_zero
    {𝕜 X Y J : Type*}
    [DivisionRing 𝕜]
    [AddCommGroup X] [Module 𝕜 X]
    [AddCommGroup Y] [Module 𝕜 Y]
    [FiniteDimensional 𝕜 X] [FiniteDimensional 𝕜 Y]
    (A : J → X →ₗ[𝕜] Y) (U : Submodule 𝕜 X)
    (hmax : ∀ V : Submodule 𝕜 X,
      linearFamilyDefect A V ≤ linearFamilyDefect A U) :
    LinearFamilyHall A ↔ linearFamilyDefect A U = 0 := by
  rw [linearFamilyHall_iff_defect_nonpos]
  constructor
  · intro hHall
    have hnonpos := hHall U
    have hnonneg := hmax (⊥ : Submodule 𝕜 X)
    simp only [linearFamilyDefect_bot] at hnonneg
    omega
  · intro hzero V
    rw [hzero] at hmax
    exact hmax V

/-- Every automorphism preserving family deficiency fixes the canonical
largest defect maximizer. -/
theorem linearFamilyDefect_greatestMaximizer_map_eq_of_invariant
    {𝕜 X Y J : Type*}
    [DivisionRing 𝕜]
    [AddCommGroup X] [Module 𝕜 X]
    [AddCommGroup Y] [Module 𝕜 Y]
    [FiniteDimensional 𝕜 X] [FiniteDimensional 𝕜 Y]
    (A : J → X →ₗ[𝕜] Y) (U : Submodule 𝕜 X)
    (g : X ≃ₗ[𝕜] X)
    (hgreatest : ∀ V : Submodule 𝕜 X,
      linearFamilyDefect A V = linearFamilyDefect A U → V ≤ U)
    (hinvariant : ∀ V : Submodule 𝕜 X,
      linearFamilyDefect A (V.map (g : X →ₗ[𝕜] X)) =
        linearFamilyDefect A V) :
    U.map (g : X →ₗ[𝕜] X) = U := by
  have hle : U.map (g : X →ₗ[𝕜] X) ≤ U :=
    hgreatest _ (hinvariant U)
  exact Submodule.eq_of_le_of_finrank_eq hle
    (LinearEquiv.finrank_map_eq g U)

/-- A simultaneous input/output automorphism that permutes the operator
family carries the shadow of a subspace to the shadow of its image. -/
theorem linearFamilyShadow_map_equiv_of_covariant
    {𝕜 X Y J : Type*}
    [DivisionRing 𝕜]
    [AddCommGroup X] [Module 𝕜 X]
    [AddCommGroup Y] [Module 𝕜 Y]
    (A : J → X →ₗ[𝕜] Y)
    (gX : X ≃ₗ[𝕜] X) (gY : Y ≃ₗ[𝕜] Y) (σ : J ≃ J)
    (hcov : ∀ j,
      (A (σ j)).comp (gX : X →ₗ[𝕜] X) =
        (gY : Y →ₗ[𝕜] Y).comp (A j))
    (U : Submodule 𝕜 X) :
    linearFamilyShadow A (U.map (gX : X →ₗ[𝕜] X)) =
      (linearFamilyShadow A U).map (gY : Y →ₗ[𝕜] Y) := by
  unfold linearFamilyShadow
  apply le_antisymm
  · apply iSup_le
    intro k
    obtain ⟨j, rfl⟩ := σ.surjective k
    rw [← Submodule.map_comp, hcov j, Submodule.map_comp]
    exact Submodule.map_mono (le_iSup (fun i => U.map (A i)) j)
  · rw [Submodule.map_iSup]
    apply iSup_le
    intro j
    rw [← Submodule.map_comp, ← hcov j, Submodule.map_comp]
    exact le_iSup
      (fun k => (U.map (gX : X →ₗ[𝕜] X)).map (A k)) (σ j)

/-- Simultaneous covariance of a family preserves every subspace defect. -/
theorem linearFamilyDefect_map_equiv_of_covariant
    {𝕜 X Y J : Type*}
    [DivisionRing 𝕜]
    [AddCommGroup X] [Module 𝕜 X]
    [AddCommGroup Y] [Module 𝕜 Y]
    [FiniteDimensional 𝕜 X] [FiniteDimensional 𝕜 Y]
    (A : J → X →ₗ[𝕜] Y)
    (gX : X ≃ₗ[𝕜] X) (gY : Y ≃ₗ[𝕜] Y) (σ : J ≃ J)
    (hcov : ∀ j,
      (A (σ j)).comp (gX : X →ₗ[𝕜] X) =
        (gY : Y →ₗ[𝕜] Y).comp (A j))
    (U : Submodule 𝕜 X) :
    linearFamilyDefect A (U.map (gX : X →ₗ[𝕜] X)) =
      linearFamilyDefect A U := by
  unfold linearFamilyDefect
  rw [linearFamilyShadow_map_equiv_of_covariant A gX gY σ hcov U,
    LinearEquiv.finrank_map_eq, LinearEquiv.finrank_map_eq]

/-- The canonical largest defect maximizer is invariant under every
simultaneous covariance of the operator family. -/
theorem linearFamilyDefect_greatestMaximizer_map_eq_of_covariant
    {𝕜 X Y J : Type*}
    [DivisionRing 𝕜]
    [AddCommGroup X] [Module 𝕜 X]
    [AddCommGroup Y] [Module 𝕜 Y]
    [FiniteDimensional 𝕜 X] [FiniteDimensional 𝕜 Y]
    (A : J → X →ₗ[𝕜] Y) (U : Submodule 𝕜 X)
    (gX : X ≃ₗ[𝕜] X) (gY : Y ≃ₗ[𝕜] Y) (σ : J ≃ J)
    (hgreatest : ∀ V : Submodule 𝕜 X,
      linearFamilyDefect A V = linearFamilyDefect A U → V ≤ U)
    (hcov : ∀ j,
      (A (σ j)).comp (gX : X →ₗ[𝕜] X) =
        (gY : Y →ₗ[𝕜] Y).comp (A j)) :
    U.map (gX : X →ₗ[𝕜] X) = U := by
  exact linearFamilyDefect_greatestMaximizer_map_eq_of_invariant
    A U gX hgreatest
      (linearFamilyDefect_map_equiv_of_covariant A gX gY σ hcov)

/-- Linear span of the operators in a family. -/
def linearFamilyOperatorSpan
    {𝕜 X Y J : Type*}
    [Field 𝕜]
    [AddCommGroup X] [Module 𝕜 X]
    [AddCommGroup Y] [Module 𝕜 Y]
    (A : J → X →ₗ[𝕜] Y) : Submodule 𝕜 (X →ₗ[𝕜] Y) :=
  Submodule.span 𝕜 (Set.range A)

/-- Every operator in the family span sends a vector of `U` into the family
shadow of `U`. -/
theorem linearFamilyOperatorSpan_apply_mem_shadow
    {𝕜 X Y J : Type*}
    [Field 𝕜]
    [AddCommGroup X] [Module 𝕜 X]
    [AddCommGroup Y] [Module 𝕜 Y]
    (A : J → X →ₗ[𝕜] Y) (U : Submodule 𝕜 X)
    {T : X →ₗ[𝕜] Y} (hT : T ∈ linearFamilyOperatorSpan A)
    {x : X} (hx : x ∈ U) :
    T x ∈ linearFamilyShadow A U := by
  unfold linearFamilyOperatorSpan at hT
  refine Submodule.span_induction
    (p := fun T _ => T x ∈ linearFamilyShadow A U) ?_ ?_ ?_ ?_ hT
  · intro S hS
    obtain ⟨j, rfl⟩ := hS
    exact (le_iSup (fun k => U.map (A k)) j)
      (Submodule.mem_map_of_mem hx)
  · simp
  · intro S T hS hT hSmem hTmem
    simpa using (linearFamilyShadow A U).add_mem hSmem hTmem
  · intro c S hS hSmem
    simpa using (linearFamilyShadow A U).smul_mem c hSmem

/-- The family shadow is equivariant whenever simultaneous conjugation in
both directions preserves the linear span of the operator family.  Unlike
permutation covariance, this covers continuous mixing of generators. -/
theorem linearFamilyShadow_map_equiv_of_spanCovariant
    {𝕜 X Y J : Type*}
    [Field 𝕜]
    [AddCommGroup X] [Module 𝕜 X]
    [AddCommGroup Y] [Module 𝕜 Y]
    (A : J → X →ₗ[𝕜] Y)
    (gX : X ≃ₗ[𝕜] X) (gY : Y ≃ₗ[𝕜] Y)
    (hforward : ∀ j,
      (((gY : Y →ₗ[𝕜] Y).comp (A j)).comp
          (gX.symm : X →ₗ[𝕜] X)) ∈ linearFamilyOperatorSpan A)
    (hbackward : ∀ j,
      (((gY.symm : Y →ₗ[𝕜] Y).comp (A j)).comp
          (gX : X →ₗ[𝕜] X)) ∈ linearFamilyOperatorSpan A)
    (U : Submodule 𝕜 X) :
    linearFamilyShadow A (U.map (gX : X →ₗ[𝕜] X)) =
      (linearFamilyShadow A U).map (gY : Y →ₗ[𝕜] Y) := by
  unfold linearFamilyShadow
  apply le_antisymm
  · apply iSup_le
    intro j
    rintro y ⟨x, hx, rfl⟩
    obtain ⟨u, hu, hux⟩ := hx
    subst x
    let T : X →ₗ[𝕜] Y :=
      ((gY.symm : Y →ₗ[𝕜] Y).comp (A j)).comp
        (gX : X →ₗ[𝕜] X)
    have hTu : T u ∈ linearFamilyShadow A U :=
      linearFamilyOperatorSpan_apply_mem_shadow A U (hbackward j) hu
    refine ⟨T u, hTu, ?_⟩
    simp [T]
  · rw [Submodule.map_iSup]
    apply iSup_le
    intro j
    rintro y ⟨z, hz, rfl⟩
    obtain ⟨u, hu, huz⟩ := hz
    subst z
    let T : X →ₗ[𝕜] Y :=
      ((gY : Y →ₗ[𝕜] Y).comp (A j)).comp
        (gX.symm : X →ₗ[𝕜] X)
    have hgxu : (gX : X →ₗ[𝕜] X) u ∈
        U.map (gX : X →ₗ[𝕜] X) :=
      Submodule.mem_map_of_mem hu
    have hTgxu : T (gX u) ∈
        linearFamilyShadow A (U.map (gX : X →ₗ[𝕜] X)) :=
      linearFamilyOperatorSpan_apply_mem_shadow A _ (hforward j) hgxu
    simpa [T, linearFamilyShadow] using hTgxu

/-- Span covariance preserves family defect even when generators mix by
arbitrary invertible linear combinations. -/
theorem linearFamilyDefect_map_equiv_of_spanCovariant
    {𝕜 X Y J : Type*}
    [Field 𝕜]
    [AddCommGroup X] [Module 𝕜 X]
    [AddCommGroup Y] [Module 𝕜 Y]
    [FiniteDimensional 𝕜 X] [FiniteDimensional 𝕜 Y]
    (A : J → X →ₗ[𝕜] Y)
    (gX : X ≃ₗ[𝕜] X) (gY : Y ≃ₗ[𝕜] Y)
    (hforward : ∀ j,
      (((gY : Y →ₗ[𝕜] Y).comp (A j)).comp
          (gX.symm : X →ₗ[𝕜] X)) ∈ linearFamilyOperatorSpan A)
    (hbackward : ∀ j,
      (((gY.symm : Y →ₗ[𝕜] Y).comp (A j)).comp
          (gX : X →ₗ[𝕜] X)) ∈ linearFamilyOperatorSpan A)
    (U : Submodule 𝕜 X) :
    linearFamilyDefect A (U.map (gX : X →ₗ[𝕜] X)) =
      linearFamilyDefect A U := by
  unfold linearFamilyDefect
  rw [linearFamilyShadow_map_equiv_of_spanCovariant
      A gX gY hforward hbackward U,
    LinearEquiv.finrank_map_eq, LinearEquiv.finrank_map_eq]

/-- The canonical largest Hall obstruction is fixed under continuous
span-preserving symmetries of the operator family. -/
theorem linearFamilyDefect_greatestMaximizer_map_eq_of_spanCovariant
    {𝕜 X Y J : Type*}
    [Field 𝕜]
    [AddCommGroup X] [Module 𝕜 X]
    [AddCommGroup Y] [Module 𝕜 Y]
    [FiniteDimensional 𝕜 X] [FiniteDimensional 𝕜 Y]
    (A : J → X →ₗ[𝕜] Y) (U : Submodule 𝕜 X)
    (gX : X ≃ₗ[𝕜] X) (gY : Y ≃ₗ[𝕜] Y)
    (hgreatest : ∀ V : Submodule 𝕜 X,
      linearFamilyDefect A V = linearFamilyDefect A U → V ≤ U)
    (hforward : ∀ j,
      (((gY : Y →ₗ[𝕜] Y).comp (A j)).comp
          (gX.symm : X →ₗ[𝕜] X)) ∈ linearFamilyOperatorSpan A)
    (hbackward : ∀ j,
      (((gY.symm : Y →ₗ[𝕜] Y).comp (A j)).comp
          (gX : X →ₗ[𝕜] X)) ∈ linearFamilyOperatorSpan A) :
    U.map (gX : X →ₗ[𝕜] X) = U := by
  exact linearFamilyDefect_greatestMaximizer_map_eq_of_invariant
    A U gX hgreatest
      (linearFamilyDefect_map_equiv_of_spanCovariant
        A gX gY hforward hbackward)

end

end GaloisForLFunctions.HTGeometry
