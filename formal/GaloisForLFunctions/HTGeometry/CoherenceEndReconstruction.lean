import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Prod
import Mathlib.Data.Set.Finite.Lattice

/-!
# Coherence-end reconstruction

Finite-defect pair coherence recovers a projective Boolean or finite-clock vertex tail exactly
under the finite-boundary one-ended condition.  Cartesian products of two infinite preconnected
graphs satisfy that condition, yielding a rigorous tensor-stabilization law.
-/

namespace GaloisForLFunctions.HTGeometry

open Set

universe u

variable {V : Type u}

/-- Ordered edges crossing the cut determined by `A`. -/
def edgeBoundary (G : SimpleGraph V) (A : Set V) : Set (V × V) :=
  {e | G.Adj e.1 e.2 ∧
    ((e.1 ∈ A ∧ e.2 ∉ A) ∨ (e.1 ∉ A ∧ e.2 ∈ A))}

/-- The Boolean pair coherence displayed on an ordered pair. -/
def booleanEdgeCoherence (ε : V → Bool) (e : V × V) : Bool :=
  Bool.xor (ε e.1) (ε e.2)

/-- Ordered graph edges on which two Boolean coherence fields disagree. -/
def booleanEdgeDisagreement (G : SimpleGraph V) (ε δ : V → Bool) : Set (V × V) :=
  {e | G.Adj e.1 e.2 ∧ booleanEdgeCoherence ε e ≠ booleanEdgeCoherence δ e}

/-- **Domain-wall identity.**  Two Boolean pair-coherence fields disagree exactly on the
edge boundary of the set on which the vertex orientations disagree. -/
theorem booleanEdgeDisagreement_eq_edgeBoundary
    (G : SimpleGraph V) (ε δ : V → Bool) :
    booleanEdgeDisagreement G ε δ = edgeBoundary G {v | ε v ≠ δ v} := by
  ext e
  cases hε₁ : ε e.1 <;> cases hδ₁ : δ e.1 <;>
    cases hε₂ : ε e.2 <;> cases hδ₂ : δ e.2 <;>
    simp [booleanEdgeDisagreement, booleanEdgeCoherence, edgeBoundary,
      hε₁, hδ₁, hε₂, hδ₂]

/-- The exact finite-boundary form of one-endedness needed by coherence reconstruction. -/
def FiniteBoundaryOneEnded (G : SimpleGraph V) : Prop :=
  ∀ A : Set V, (edgeBoundary G A).Finite → A.Finite ∨ Aᶜ.Finite

/-- Equality of Boolean orientations outside a finite vertex set, up to one global complement. -/
def BooleanProjectiveFiniteEquivalent (ε δ : V → Bool) : Prop :=
  {v | ε v ≠ δ v}.Finite ∨ {v | ε v = δ v}.Finite

/-- Equality of Boolean pair-coherence fields outside a finite ordered-edge set. -/
def BooleanEdgeTailEquivalent (G : SimpleGraph V) (ε δ : V → Bool) : Prop :=
  (booleanEdgeDisagreement G ε δ).Finite

theorem complement_disagreementSet (ε δ : V → Bool) :
    {v | ε v ≠ δ v}ᶜ = {v | ε v = δ v} := by
  ext v
  simp

/-- Finite-boundary one-endedness is exactly faithfulness of finite-defect Boolean edge
coherence on projective vertex tails. -/
theorem finiteBoundaryOneEnded_iff_booleanEdgeTail_faithful (G : SimpleGraph V) :
    FiniteBoundaryOneEnded G ↔
      ∀ ε δ : V → Bool,
        BooleanEdgeTailEquivalent G ε δ → BooleanProjectiveFiniteEquivalent ε δ := by
  constructor
  · intro hG ε δ hedge
    rw [BooleanEdgeTailEquivalent, booleanEdgeDisagreement_eq_edgeBoundary] at hedge
    rcases hG {v | ε v ≠ δ v} hedge with hfinite | hcofinite
    · exact Or.inl hfinite
    · exact Or.inr (by simpa only [complement_disagreementSet] using hcofinite)
  · intro hfaithful A hboundary
    classical
    let ε : V → Bool := fun v => if v ∈ A then true else false
    let δ : V → Bool := fun _ => false
    have hdisagreement : {v | ε v ≠ δ v} = A := by
      ext v
      simp [ε, δ]
    have hagreement : {v | ε v = δ v} = Aᶜ := by
      ext v
      simp [ε, δ]
    have hedge : BooleanEdgeTailEquivalent G ε δ := by
      rw [BooleanEdgeTailEquivalent, booleanEdgeDisagreement_eq_edgeBoundary,
        hdisagreement]
      exact hboundary
    rcases hfaithful ε δ hedge with h | h
    · exact Or.inl (by simpa only [hdisagreement] using h)
    · exact Or.inr (by simpa only [hagreement] using h)

/-- An edge-invariant vertex label is constant on a preconnected graph. -/
theorem eq_of_preconnected_of_adjInvariant {α : Type*} {G : SimpleGraph V}
    (hG : G.Preconnected) (f : V → α)
    (hf : ∀ ⦃u v⦄, G.Adj u v → f u = f v) (u v : V) :
    f u = f v := by
  have huv := hG u v
  rw [SimpleGraph.reachable_iff_reflTransGen] at huv
  induction huv with
  | refl => rfl
  | tail _ hxy ih => exact ih.trans (hf hxy)

/-- Exact Boolean edge coherence on a preconnected graph determines the orientation up to one
global complement. -/
theorem booleanEdgeCoherence_eq_projective_of_preconnected
    {G : SimpleGraph V} (hG : G.Preconnected) (ε δ : V → Bool)
    (hcoh : ∀ ⦃u v⦄, G.Adj u v →
      Bool.xor (ε u) (ε v) = Bool.xor (δ u) (δ v)) :
    ε = δ ∨ ε = fun v => !(δ v) := by
  let relative : V → Bool := fun v => Bool.xor (ε v) (δ v)
  have hinvariant : ∀ ⦃u v⦄, G.Adj u v → relative u = relative v := by
    intro u v huv
    specialize hcoh huv
    cases hεu : ε u <;> cases hδu : δ u <;>
      cases hεv : ε v <;> cases hδv : δ v <;>
      simp_all [relative]
  cases isEmpty_or_nonempty V with
  | inl hempty =>
      left
      funext v
      exact isEmptyElim v
  | inr hnonempty =>
      let v₀ : V := Classical.choice hnonempty
      have hconstant : ∀ v, relative v = relative v₀ :=
        fun v => eq_of_preconnected_of_adjInvariant hG relative hinvariant v v₀
      by_cases hbase : ε v₀ = δ v₀
      · left
        funext v
        have hrel₀ : relative v₀ = false := by
          change Bool.xor (ε v₀) (δ v₀) = false
          rw [hbase]
          cases δ v₀ <;> rfl
        have hv : relative v = false := (hconstant v).trans hrel₀
        change Bool.xor (ε v) (δ v) = false at hv
        cases hε : ε v <;> cases hδ : δ v <;> simp_all
      · right
        funext v
        have hrel₀ : relative v₀ = true := by
          change Bool.xor (ε v₀) (δ v₀) = true
          cases hε : ε v₀ <;> cases hδ : δ v₀ <;> simp_all
        have hv : relative v = true := (hconstant v).trans hrel₀
        change Bool.xor (ε v) (δ v) = true at hv
        cases hε : ε v <;> cases hδ : δ v <;> simp_all

/-- Ordered graph edges across which a vertex label changes. -/
def edgeVariation {α : Type*} (G : SimpleGraph V) (f : V → α) : Set (V × V) :=
  {e | G.Adj e.1 e.2 ∧ f e.1 ≠ f e.2}

/-- A finite-valued label has a projective tail when it is constant away from finitely many
vertices. -/
def EventuallyConstant {α : Type*} (f : V → α) : Prop :=
  ∃ a, {v | f v ≠ a}.Finite

theorem edgeBoundary_fiber_subset_edgeVariation {α : Type*}
    (G : SimpleGraph V) (f : V → α) (a : α) :
    edgeBoundary G {v | f v = a} ⊆ edgeVariation G f := by
  intro e he
  rcases he with ⟨hadj, hcross | hcross⟩
  · refine ⟨hadj, fun heq => hcross.2 ?_⟩
    change f e.1 = a ∧ f e.2 ≠ a at hcross
    change f e.2 = a
    exact heq ▸ hcross.1
  · refine ⟨hadj, fun heq => hcross.1 ?_⟩
    change f e.1 ≠ a ∧ f e.2 = a at hcross
    change f e.1 = a
    exact heq.symm ▸ hcross.2

/-- On a finite-boundary one-ended graph, every finite-valued field with only finitely many
changing edges is eventually constant.  This is the finite-clock reconstruction mechanism. -/
theorem eventuallyConstant_of_finite_edgeVariation
    {α : Type*} [Fintype α] [Infinite V]
    {G : SimpleGraph V} (hG : FiniteBoundaryOneEnded G) (f : V → α)
    (hvariation : (edgeVariation G f).Finite) :
    EventuallyConstant f := by
  classical
  have hfiberBoundary : ∀ a : α, (edgeBoundary G {v | f v = a}).Finite :=
    fun a => hvariation.subset (edgeBoundary_fiber_subset_edgeVariation G f a)
  have hfiberDichotomy : ∀ a : α,
      {v | f v = a}.Finite ∨ {v | f v = a}ᶜ.Finite :=
    fun a => hG {v | f v = a} (hfiberBoundary a)
  by_contra hnot
  simp only [EventuallyConstant, not_exists] at hnot
  have hfiberFinite : ∀ a : α, {v | f v = a}.Finite := by
    intro a
    exact (hfiberDichotomy a).resolve_right (by
      intro hcofinite
      apply hnot a
      have hset : {v | f v = a}ᶜ = {v | f v ≠ a} := by
        ext v
        simp
      simpa only [hset] using hcofinite)
  have hunionFinite : (⋃ a : α, {v | f v = a}).Finite :=
    Set.finite_iUnion hfiberFinite
  have hcover : (⋃ a : α, {v | f v = a}) = (Set.univ : Set V) := by
    ext v
    simp
  rw [hcover] at hunionFinite
  exact Set.infinite_univ hunionFinite

/-- Additive oriented pair coherence.  For the finite clock `ZMod m`, this is the exponent of
`u(i) * conjugate (u(j))`. -/
def additiveEdgeCoherence {A : Type*} [AddGroup A]
    (u : V → A) (e : V × V) : A :=
  u e.1 - u e.2

/-- Ordered graph edges on which two additive coherence fields disagree. -/
def additiveEdgeDisagreement {A : Type*} [AddGroup A]
    (G : SimpleGraph V) (u v : V → A) : Set (V × V) :=
  {e | G.Adj e.1 e.2 ∧ additiveEdgeCoherence u e ≠ additiveEdgeCoherence v e}

/-- The finite-clock domain-wall identity: coherence disagreement is exactly variation of the
relative phase. -/
theorem additiveEdgeDisagreement_eq_edgeVariation
    {A : Type*} [AddCommGroup A]
    (G : SimpleGraph V) (u v : V → A) :
    additiveEdgeDisagreement G u v = edgeVariation G (fun x => u x - v x) := by
  ext e
  have heq :
      (u e.1 - u e.2 = v e.1 - v e.2) ↔
        (u e.1 - v e.1 = u e.2 - v e.2) :=
    sub_eq_sub_iff_sub_eq_sub
  change
    (G.Adj e.1 e.2 ∧ u e.1 - u e.2 ≠ v e.1 - v e.2) ↔
      (G.Adj e.1 e.2 ∧ u e.1 - v e.1 ≠ u e.2 - v e.2)
  exact and_congr_right fun _ => not_congr heq

/-- Finite-defect additive edge coherence on a finite clock determines the relative phase outside
a finite vertex set whenever the graph has the finite-boundary one-ended property. -/
theorem additiveEdgeTail_reconstruct_of_finiteBoundaryOneEnded
    {A : Type*} [AddCommGroup A] [Fintype A] [Infinite V]
    {G : SimpleGraph V} (hG : FiniteBoundaryOneEnded G) (u v : V → A)
    (hcoherence : (additiveEdgeDisagreement G u v).Finite) :
    EventuallyConstant (fun x => u x - v x) := by
  apply eventuallyConstant_of_finite_edgeVariation hG
  simpa only [← additiveEdgeDisagreement_eq_edgeVariation] using hcoherence

/-- A two-level label realizing a prescribed vertex cut. -/
noncomputable def twoLevelLabel {A : Type*} [Zero A]
    (a : A) (S : Set V) (v : V) : A := by
  classical
  exact if v ∈ S then a else 0

theorem edgeVariation_twoLevelLabel
    {A : Type*} [Zero A] (G : SimpleGraph V) (S : Set V) (a : A) (ha : a ≠ 0) :
    edgeVariation G (twoLevelLabel a S) = edgeBoundary G S := by
  classical
  ext e
  by_cases h₁ : e.1 ∈ S <;> by_cases h₂ : e.2 ∈ S <;>
    simp [edgeVariation, edgeBoundary, twoLevelLabel, h₁, h₂, ha, ha.symm]

/-- **Finite-clock faithfulness criterion.**  For every nontrivial finite additive clock, the
finite-boundary one-ended property is exactly finite-defect reconstruction of relative phase up
to an eventually constant global clock value. -/
theorem finiteBoundaryOneEnded_iff_additiveEdgeTail_faithful
    {A : Type*} [AddCommGroup A] [Fintype A] [Nontrivial A] [Infinite V]
    (G : SimpleGraph V) :
    FiniteBoundaryOneEnded G ↔
      ∀ u v : V → A, (additiveEdgeDisagreement G u v).Finite →
        EventuallyConstant (fun x => u x - v x) := by
  constructor
  · intro hG u v hfinite
    exact additiveEdgeTail_reconstruct_of_finiteBoundaryOneEnded hG u v hfinite
  · intro hfaithful S hboundary
    classical
    obtain ⟨a, ha⟩ := exists_ne (0 : A)
    let u : V → A := twoLevelLabel a S
    let v : V → A := fun _ => 0
    have hcoherence : (additiveEdgeDisagreement G u v).Finite := by
      rw [additiveEdgeDisagreement_eq_edgeVariation]
      have hrelative : (fun x => u x - v x) = u := by
        funext x
        simp [v]
      rw [hrelative]
      change (edgeVariation G (twoLevelLabel a S)).Finite
      rw [edgeVariation_twoLevelLabel G S a ha]
      exact hboundary
    obtain ⟨c, hc⟩ := hfaithful u v hcoherence
    by_cases hc0 : c = 0
    · left
      have hset : {x | u x - v x ≠ c} = S := by
        ext x
        simp [u, v, twoLevelLabel, hc0, ha]
      simpa only [hset] using hc
    · right
      apply hc.subset
      intro x hx
      change x ∉ S at hx
      change u x - v x ≠ c
      simpa [u, v, twoLevelLabel, hx] using (Ne.symm hc0)

/-- Vertices incident to an ordered edge in `F`. -/
def edgeEndpointSupport {X : Type*} (F : Set (X × X)) : Set X :=
  Prod.fst '' F ∪ Prod.snd '' F

theorem edgeEndpointSupport_finite {X : Type*} {F : Set (X × X)} (hF : F.Finite) :
    (edgeEndpointSupport F).Finite :=
  (hF.image Prod.fst).union (hF.image Prod.snd)

/-- First-coordinate projection of the endpoints of an ordered edge family. -/
def edgeFirstCoordinateSupport {X Y : Type*} (F : Set ((X × Y) × (X × Y))) : Set X :=
  Prod.fst '' edgeEndpointSupport F

/-- Second-coordinate projection of the endpoints of an ordered edge family. -/
def edgeSecondCoordinateSupport {X Y : Type*} (F : Set ((X × Y) × (X × Y))) : Set Y :=
  Prod.snd '' edgeEndpointSupport F

theorem edgeFirstCoordinateSupport_finite {X Y : Type*}
    {F : Set ((X × Y) × (X × Y))} (hF : F.Finite) :
    (edgeFirstCoordinateSupport F).Finite :=
  (edgeEndpointSupport_finite hF).image Prod.fst

theorem edgeSecondCoordinateSupport_finite {X Y : Type*}
    {F : Set ((X × Y) × (X × Y))} (hF : F.Finite) :
    (edgeSecondCoordinateSupport F).Finite :=
  (edgeEndpointSupport_finite hF).image Prod.snd

theorem exists_not_mem_of_finite {X : Type*} [Infinite X]
    {S : Set X} (hS : S.Finite) : ∃ x, x ∉ S := by
  by_contra h
  simp only [not_exists, not_not] at h
  have hSuniv : S = Set.univ := Set.eq_univ_of_forall h
  rw [hSuniv] at hS
  exact Set.infinite_univ hS

/-- Boolean membership label of a set. -/
noncomputable def cutLabel {X : Type*} (S : Set X) (x : X) : Bool := by
  classical
  exact if x ∈ S then true else false

theorem cutLabel_eq_iff {X : Type*} (S : Set X) (x y : X) :
    cutLabel S x = cutLabel S y ↔ (x ∈ S ↔ y ∈ S) := by
  classical
  by_cases hx : x ∈ S <;> by_cases hy : y ∈ S <;>
    simp [cutLabel, hx, hy]

theorem cutLabel_adjInvariant_right_of_not_mem_firstSupport
    {W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (A : Set (V × W)) (g : V)
    (hg : g ∉ edgeFirstCoordinateSupport (edgeBoundary (G □ H) A)) :
    ∀ ⦃h₁ h₂⦄, H.Adj h₁ h₂ →
      cutLabel A (g, h₁) = cutLabel A (g, h₂) := by
  intro h₁ h₂ hadj
  rw [cutLabel_eq_iff]
  constructor
  · intro h₁A
    by_contra h₂A
    apply hg
    refine ⟨(g, h₁), ?_, rfl⟩
    apply Or.inl
    refine ⟨((g, h₁), (g, h₂)), ?_, rfl⟩
    exact ⟨SimpleGraph.boxProd_adj_right.mpr hadj, Or.inl ⟨h₁A, h₂A⟩⟩
  · intro h₂A
    by_contra h₁A
    apply hg
    refine ⟨(g, h₁), ?_, rfl⟩
    apply Or.inl
    refine ⟨((g, h₁), (g, h₂)), ?_, rfl⟩
    exact ⟨SimpleGraph.boxProd_adj_right.mpr hadj, Or.inr ⟨h₁A, h₂A⟩⟩

theorem cutLabel_adjInvariant_left_of_not_mem_secondSupport
    {W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (A : Set (V × W)) (h : W)
    (hh : h ∉ edgeSecondCoordinateSupport (edgeBoundary (G □ H) A)) :
    ∀ ⦃g₁ g₂⦄, G.Adj g₁ g₂ →
      cutLabel A (g₁, h) = cutLabel A (g₂, h) := by
  intro g₁ g₂ hadj
  rw [cutLabel_eq_iff]
  constructor
  · intro h₁A
    by_contra h₂A
    apply hh
    refine ⟨(g₁, h), ?_, rfl⟩
    apply Or.inl
    refine ⟨((g₁, h), (g₂, h)), ?_, rfl⟩
    exact ⟨SimpleGraph.boxProd_adj_left.mpr hadj, Or.inl ⟨h₁A, h₂A⟩⟩
  · intro h₂A
    by_contra h₁A
    apply hh
    refine ⟨(g₁, h), ?_, rfl⟩
    apply Or.inl
    refine ⟨((g₁, h), (g₂, h)), ?_, rfl⟩
    exact ⟨SimpleGraph.boxProd_adj_left.mpr hadj, Or.inr ⟨h₁A, h₂A⟩⟩

/-- **Tensor stabilization.**  The Cartesian product of two infinite preconnected graphs has the
finite-boundary one-ended property.  Thus every finite-valued relative phase with finitely many
defective product-edge coherences is eventually constant. -/
theorem finiteBoundaryOneEnded_boxProd
    {W : Type*} [Infinite V] [Infinite W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    (hG : G.Preconnected) (hH : H.Preconnected) :
    FiniteBoundaryOneEnded (G □ H) := by
  intro A hboundary
  let SG : Set V := edgeFirstCoordinateSupport (edgeBoundary (G □ H) A)
  let SH : Set W := edgeSecondCoordinateSupport (edgeBoundary (G □ H) A)
  have hSG : SG.Finite := by
    dsimp [SG]
    exact edgeFirstCoordinateSupport_finite hboundary
  have hSH : SH.Finite := by
    dsimp [SH]
    exact edgeSecondCoordinateSupport_finite hboundary
  obtain ⟨g₀, hg₀⟩ := exists_not_mem_of_finite hSG
  obtain ⟨h₀, hh₀⟩ := exists_not_mem_of_finite hSH
  have hright : ∀ g ∉ SG, ∀ h₁ h₂ : W,
      cutLabel A (g, h₁) = cutLabel A (g, h₂) := by
    intro g hg h₁ h₂
    apply eq_of_preconnected_of_adjInvariant hH (fun h => cutLabel A (g, h))
    exact cutLabel_adjInvariant_right_of_not_mem_firstSupport A g (by
      simpa only [SG] using hg)
  have hleft : ∀ h ∉ SH, ∀ g₁ g₂ : V,
      cutLabel A (g₁, h) = cutLabel A (g₂, h) := by
    intro h hh g₁ g₂
    apply eq_of_preconnected_of_adjInvariant hG (fun g => cutLabel A (g, h))
    exact cutLabel_adjInvariant_left_of_not_mem_secondSupport A h (by
      simpa only [SH] using hh)
  have houtside : ∀ x : V × W, x ∉ SG ×ˢ SH →
      cutLabel A x = cutLabel A (g₀, h₀) := by
    intro x hx
    rcases x with ⟨g, h⟩
    by_cases hg : g ∈ SG
    · have hh : h ∉ SH := by
        intro hh
        exact hx ⟨hg, hh⟩
      exact (hleft h hh g g₀).trans (hright g₀ hg₀ h h₀)
    · exact (hright g hg h h₀).trans (hleft h₀ hh₀ g g₀)
  have hrectangle : (SG ×ˢ SH).Finite := hSG.prod hSH
  by_cases hbase : (g₀, h₀) ∈ A
  · right
    apply hrectangle.subset
    intro x hx
    change x ∉ A at hx
    by_contra hxrectangle
    have hlabel := houtside x hxrectangle
    rw [cutLabel_eq_iff] at hlabel
    exact hx (hlabel.mpr hbase)
  · left
    apply hrectangle.subset
    intro x hx
    by_contra hxrectangle
    have hlabel := houtside x hxrectangle
    rw [cutLabel_eq_iff] at hlabel
    exact hbase (hlabel.mp hx)

end GaloisForLFunctions.HTGeometry

