import GaloisForLFunctions.RHTower.Deninger.DeningerCalderonWittAllCrossPrimeArithmeticSourceCompletion
import GaloisForLFunctions.RHTower.CompleteResolutionCofinalConditioningLaw

/-!
# Closed-relation saturation of the cross-prime arithmetic core

The actual ordered Calderón--Witt witness span is dense in its cross-prime
`ℓ²` completion, while the old all-prime oriented boundary vanishes on that
entire span.  The earlier continuous-extension no-go therefore has a
strictly stronger closed-graph form.

Any closed linear relation which contains the zero graph on a dense source
core is the full source space times its vertical fibre.  Applied to the
Calderón--Witt completion, a single-valued relation is exactly the zero
graph, and every closable partial operator agreeing with the old boundary
has zero closure.

Thus unboundedness, graph norms, or relation-valued completion cannot turn
the old vertical boundary into the missing horizontal arithmetic
annihilator.  A surviving transgression must already act nontrivially on
finite actual witnesses, or must change the source topology and arithmetic
relation before the `ℓ²` completion is formed.
-/

open Complex Function Set Topology

namespace RHTower

noncomputable section

/-- A closed linear relation containing the zero graph on a dense submodule
is exactly the full source space times its vertical fibre. -/
theorem closedLinearRelation_eq_top_prod_vertical_of_dense_zeroCore
    {𝕜 X Y : Type*}
    [Ring 𝕜] [TopologicalSpace 𝕜]
    [AddCommGroup X] [Module 𝕜 X] [TopologicalSpace X] [ContinuousAdd X]
    [AddCommGroup Y] [Module 𝕜 Y] [TopologicalSpace Y]
    (R : Submodule 𝕜 (X × Y))
    (hclosed : IsClosed (R : Set (X × Y)))
    (D : Submodule 𝕜 X) (hDdense : Dense (D : Set X))
    (hzero : ∀ x ∈ D, (x, (0 : Y)) ∈ R) :
    R = (⊤ : Submodule 𝕜 X).prod (linearRelationVerticalFiber R) := by
  let Z : Submodule 𝕜 X :=
    R.comap (LinearMap.inl 𝕜 X Y)
  have hZclosed : IsClosed (Z : Set X) := by
    change IsClosed ((fun x : X => (x, (0 : Y))) ⁻¹' (R : Set (X × Y)))
    exact hclosed.preimage (continuous_id.prodMk continuous_const)
  have hDZ : (D : Set X) ⊆ Z := by
    intro x hx
    exact hzero x hx
  have hZtop : Z = ⊤ := by
    apply top_unique
    intro x _
    apply closure_minimal hDZ hZclosed
    rw [hDdense.closure_eq]
    exact Set.mem_univ x
  have hallzero (x : X) : (x, (0 : Y)) ∈ R := by
    have hx : x ∈ Z := by
      rw [hZtop]
      exact Submodule.mem_top
    exact hx
  apply le_antisymm
  · intro z hz
    change z.1 ∈ (⊤ : Submodule 𝕜 X) ∧
      z.2 ∈ linearRelationVerticalFiber R
    refine ⟨Submodule.mem_top, ?_⟩
    change ((0 : X), z.2) ∈ R
    have hsub : z - (z.1, (0 : Y)) ∈ R :=
      Submodule.sub_mem R hz (hallzero z.1)
    have heq : z - (z.1, (0 : Y)) = ((0 : X), z.2) := by
      apply Prod.ext <;> simp
    rw [heq] at hsub
    exact hsub
  · intro z hz
    change z.1 ∈ (⊤ : Submodule 𝕜 X) ∧
      z.2 ∈ linearRelationVerticalFiber R at hz
    change (z.1, z.2) ∈ R
    have hadd : (z.1, (0 : Y)) + ((0 : X), z.2) ∈ R :=
      Submodule.add_mem R (hallzero z.1) hz.2
    have heq : (z.1, (0 : Y)) + ((0 : X), z.2) = z := by
      apply Prod.ext <;> simp
    rw [heq] at hadd
    exact hadd

/-- Every output of such a relation is already vertical over the zero source
and is attained over every source point. -/
theorem closedLinearRelation_mem_vertical_of_dense_zeroCore
    {𝕜 X Y : Type*}
    [Ring 𝕜] [TopologicalSpace 𝕜]
    [AddCommGroup X] [Module 𝕜 X] [TopologicalSpace X] [ContinuousAdd X]
    [AddCommGroup Y] [Module 𝕜 Y] [TopologicalSpace Y]
    (R : Submodule 𝕜 (X × Y))
    (hclosed : IsClosed (R : Set (X × Y)))
    (D : Submodule 𝕜 X) (hDdense : Dense (D : Set X))
    (hzero : ∀ x ∈ D, (x, (0 : Y)) ∈ R)
    {x : X} {w : Y} (hxw : (x, w) ∈ R) :
    w ∈ linearRelationVerticalFiber R ∧ ∀ x' : X, (x', w) ∈ R := by
  have hR := closedLinearRelation_eq_top_prod_vertical_of_dense_zeroCore
    R hclosed D hDdense hzero
  have hw : w ∈ linearRelationVerticalFiber R := by
    rw [hR] at hxw
    exact (Submodule.mem_prod.mp hxw).2
  refine ⟨hw, fun x' => ?_⟩
  rw [hR]
  exact Submodule.mem_prod.mpr ⟨Submodule.mem_top, hw⟩

/-- **Nonselectivity.** Such a relation has the same output fibre over every
source point, so its outputs carry no information about the input. -/
theorem closedLinearRelation_outputFiber_const_of_dense_zeroCore
    {𝕜 X Y : Type*}
    [Ring 𝕜] [TopologicalSpace 𝕜]
    [AddCommGroup X] [Module 𝕜 X] [TopologicalSpace X] [ContinuousAdd X]
    [AddCommGroup Y] [Module 𝕜 Y] [TopologicalSpace Y]
    (R : Submodule 𝕜 (X × Y))
    (hclosed : IsClosed (R : Set (X × Y)))
    (D : Submodule 𝕜 X) (hDdense : Dense (D : Set X))
    (hzero : ∀ x ∈ D, (x, (0 : Y)) ∈ R) (x x' : X) :
    {w : Y | (x, w) ∈ R} = {w : Y | (x', w) ∈ R} := by
  ext w
  constructor
  · intro hw
    exact (closedLinearRelation_mem_vertical_of_dense_zeroCore R hclosed D
      hDdense hzero hw).2 x'
  · intro hw
    exact (closedLinearRelation_mem_vertical_of_dense_zeroCore R hclosed D
      hDdense hzero hw).2 x

/-- Every closed relation extending the zero old boundary on the actual
cross-prime arithmetic witness span is a product with its vertical fibre. -/
theorem deningerCalderonWittCrossPrimeClosedRelation_eq_top_prod_vertical
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
    (R : Submodule ℂ
      (DeningerCalderonWittCrossPrimePacketHilbert × W))
    (hclosed : IsClosed
      (R : Set (DeningerCalderonWittCrossPrimePacketHilbert × W)))
    (hsource : ∀ x : deningerCalderonWittCrossPrimeAlgebraicSourceSpan,
      (deningerCalderonWittCrossPrimeSourceSpanToPacketHilbert x,
        (0 : W)) ∈ R) :
    R = (⊤ : Submodule ℂ DeningerCalderonWittCrossPrimePacketHilbert).prod
      (linearRelationVerticalFiber R) := by
  apply closedLinearRelation_eq_top_prod_vertical_of_dense_zeroCore
    R hclosed
    (LinearMap.range
      deningerCalderonWittCrossPrimeSourceSpanToPacketHilbert)
  · exact deningerCalderonWittCrossPrimeSourceSpanToPacketHilbert_denseRange
  · intro z hz
    obtain ⟨x, rfl⟩ := hz
    exact hsource x

/-- A single-valued closed relation extending the old zero boundary on the
actual arithmetic witness core is the full zero graph. -/
theorem
    deningerCalderonWittCrossPrimeClosedRelation_eq_zeroGraph_of_singleValued
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
    (R : Submodule ℂ
      (DeningerCalderonWittCrossPrimePacketHilbert × W))
    (hclosed : IsClosed
      (R : Set (DeningerCalderonWittCrossPrimePacketHilbert × W)))
    (hsource : ∀ x : deningerCalderonWittCrossPrimeAlgebraicSourceSpan,
      (deningerCalderonWittCrossPrimeSourceSpanToPacketHilbert x,
        (0 : W)) ∈ R)
    (hsingle : ∀ y : W,
      ((0 : DeningerCalderonWittCrossPrimePacketHilbert), y) ∈ R → y = 0) :
    R = (⊤ : Submodule ℂ DeningerCalderonWittCrossPrimePacketHilbert).prod ⊥ := by
  rw [deningerCalderonWittCrossPrimeClosedRelation_eq_top_prod_vertical
    R hclosed hsource]
  congr 1
  apply le_antisymm
  · intro y hy
    rw [Submodule.mem_bot]
    exact hsingle y hy
  · exact bot_le

/-- Any nonzero output of such a relation is pure vertical ambiguity: it
occurs already over the zero source and over every source point. -/
theorem deningerCalderonWittCrossPrimeClosedRelation_output_is_vertical
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
    (R : Submodule ℂ
      (DeningerCalderonWittCrossPrimePacketHilbert × W))
    (hclosed : IsClosed
      (R : Set (DeningerCalderonWittCrossPrimePacketHilbert × W)))
    (hsource : ∀ x : deningerCalderonWittCrossPrimeAlgebraicSourceSpan,
      (deningerCalderonWittCrossPrimeSourceSpanToPacketHilbert x,
        (0 : W)) ∈ R)
    {x : DeningerCalderonWittCrossPrimePacketHilbert} {w : W}
    (hxw : (x, w) ∈ R) :
    ((0 : DeningerCalderonWittCrossPrimePacketHilbert), w) ∈ R ∧
      ∀ x' : DeningerCalderonWittCrossPrimePacketHilbert, (x', w) ∈ R := by
  refine closedLinearRelation_mem_vertical_of_dense_zeroCore R hclosed
    (LinearMap.range
      deningerCalderonWittCrossPrimeSourceSpanToPacketHilbert)
    deningerCalderonWittCrossPrimeSourceSpanToPacketHilbert_denseRange
    ?_ hxw
  intro z hz
  obtain ⟨x, rfl⟩ := hz
  exact hsource x

/-- **No selective annihilator.** Passing from operators to closed linear
relations cannot make the old oriented boundary source-selective: the output
fibre is the same over every packet. -/
theorem deningerCalderonWittCrossPrimeClosedRelation_outputFiber_const
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
    (R : Submodule ℂ
      (DeningerCalderonWittCrossPrimePacketHilbert × W))
    (hclosed : IsClosed
      (R : Set (DeningerCalderonWittCrossPrimePacketHilbert × W)))
    (hsource : ∀ x : deningerCalderonWittCrossPrimeAlgebraicSourceSpan,
      (deningerCalderonWittCrossPrimeSourceSpanToPacketHilbert x,
        (0 : W)) ∈ R)
    (x x' : DeningerCalderonWittCrossPrimePacketHilbert) :
    {w : W | (x, w) ∈ R} = {w : W | (x', w) ∈ R} := by
  refine closedLinearRelation_outputFiber_const_of_dense_zeroCore R hclosed
    (LinearMap.range
      deningerCalderonWittCrossPrimeSourceSpanToPacketHilbert)
    deningerCalderonWittCrossPrimeSourceSpanToPacketHilbert_denseRange
    ?_ x x'
  intro z hz
  obtain ⟨y, rfl⟩ := hz
  exact hsource y

/-- Every closable partial operator agreeing with the zero old boundary on
the dense actual arithmetic witness core has the full zero operator as its
closure. -/
theorem deningerCalderonWittCrossPrimeClosableExtension_closure_eq_zero
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
    (T : DeningerCalderonWittCrossPrimePacketHilbert →ₗ.[ℂ] W)
    (hT : T.IsClosable)
    (hsourceDomain :
      ∀ x : deningerCalderonWittCrossPrimeAlgebraicSourceSpan,
        deningerCalderonWittCrossPrimeSourceSpanToPacketHilbert x ∈ T.domain)
    (hsourceZero :
      ∀ x : deningerCalderonWittCrossPrimeAlgebraicSourceSpan,
        T ⟨deningerCalderonWittCrossPrimeSourceSpanToPacketHilbert x,
          hsourceDomain x⟩ = 0) :
    T.closure = 0 := by
  apply LinearPMap.eq_of_eq_graph
  have hsource :
      ∀ x : deningerCalderonWittCrossPrimeAlgebraicSourceSpan,
        (deningerCalderonWittCrossPrimeSourceSpanToPacketHilbert x,
          (0 : W)) ∈ T.closure.graph := by
    intro x
    have hx :
        (deningerCalderonWittCrossPrimeSourceSpanToPacketHilbert x,
          (0 : W)) ∈ T.graph := by
      have hmem := T.mem_graph
        ⟨deningerCalderonWittCrossPrimeSourceSpanToPacketHilbert x,
          hsourceDomain x⟩
      simpa [hsourceZero x] using hmem
    rw [← hT.graph_closure_eq_closure_graph]
    exact T.graph.le_topologicalClosure hx
  have hgraph :=
    deningerCalderonWittCrossPrimeClosedRelation_eq_zeroGraph_of_singleValued
      T.closure.graph hT.closure_isClosed hsource
      (fun y hy => T.closure.graph_fst_eq_zero_snd hy rfl)
  rw [hgraph]
  ext z
  simp [LinearPMap.mem_graph_iff, eq_comm]

end

end RHTower
