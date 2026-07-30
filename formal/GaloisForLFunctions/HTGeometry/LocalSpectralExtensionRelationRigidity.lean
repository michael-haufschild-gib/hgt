import GaloisForLFunctions.HTGeometry.PrimeLogCauchySeamRank
import GaloisForLFunctions.HTGeometry.ReducedH0Components

/-!
# Relation rigidity for local spectral extensions

This file isolates the algebraic and graph-theoretic core of the endpoint-extension
argument for generic local spectral rank.

After second-order perturbation, a putative eigenbranch relation produces a finite
partial-fraction identity with distinct poles.  Clearing denominators forces every
edge coefficient to vanish.  With at least three states in the attached local
factor, those cross-layer edge equalities propagate through every connected
transition graph and leave only the constant, trace-direction relation.
-/

open Polynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Common-denominator numerator of a finite simple-pole packet over an arbitrary
finite index type. -/
def distinctNodePacketNumerator
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (z c : ι → ℂ) : ℂ[X] :=
  ∑ i, C (c i) *
    ∏ j ∈ Finset.univ.erase i, (C (z j) - X)

/-- Evaluation at one pole isolates exactly its coefficient. -/
theorem distinctNodePacketNumerator_eval_node
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (z c : ι → ℂ) (i : ι) :
    (distinctNodePacketNumerator z c).eval (z i) =
      c i * ∏ j ∈ Finset.univ.erase i, (z j - z i) := by
  rw [distinctNodePacketNumerator]
  simp only [eval_finsetSum, eval_mul, eval_C, eval_prod, eval_sub, eval_X]
  rw [Finset.sum_eq_single i]
  · intro j _ hji
    rw [Finset.prod_eq_zero
      (Finset.mem_erase.mpr
        ⟨fun h => hji h.symm, Finset.mem_univ i⟩)]
    · ring
    · exact sub_self _
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/-- One nonzero coefficient at a pole not shared by any other term already
forces the cleared packet numerator to be nonzero.  No separation assumption
is needed among the remaining poles. -/
theorem distinctNodePacketNumerator_ne_zero_of_unique_node
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (z c : ι → ℂ) (i : ι)
    (hci : c i ≠ 0)
    (hi : ∀ j, j ≠ i → z j ≠ z i) :
    distinctNodePacketNumerator z c ≠ 0 := by
  intro hzero
  have heval :=
    congrArg (fun P : ℂ[X] => P.eval (z i)) hzero
  have hisolated :
      c i * ∏ j ∈ Finset.univ.erase i, (z j - z i) = 0 := by
    simpa [distinctNodePacketNumerator_eval_node] using heval
  have hprod :
      ∏ j ∈ Finset.univ.erase i, (z j - z i) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    apply sub_ne_zero.mpr
    exact hi j (Finset.mem_erase.mp hj).1
  exact (mul_ne_zero hci hprod) hisolated

/-- Distinct poles make the cleared simple-pole numerator injective in its
coefficient packet. -/
theorem distinctNodePacketNumerator_eq_zero_iff
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (z c : ι → ℂ) (hz : Function.Injective z) :
    distinctNodePacketNumerator z c = 0 ↔ c = 0 := by
  constructor
  · intro hzero
    funext i
    have heval :=
      congrArg (fun P : ℂ[X] => P.eval (z i)) hzero
    have hisolated :
        c i * ∏ j ∈ Finset.univ.erase i, (z j - z i) = 0 := by
      simpa [distinctNodePacketNumerator_eval_node] using heval
    have hprod :
        ∏ j ∈ Finset.univ.erase i, (z j - z i) ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro j hj
      exact sub_ne_zero.mpr
        (fun h => (Finset.mem_erase.mp hj).1 (hz h))
    exact (mul_eq_zero.mp hisolated).resolve_right hprod
  · rintro rfl
    simp [distinctNodePacketNumerator]

/-- A simple-pole identity on any infinite pole-free set clears to the zero
packet numerator.  No meromorphic continuation is assumed: finite polynomial
root rigidity is enough. -/
theorem distinctNodePacketNumerator_eq_zero_of_rational_identity
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (z c : ι → ℂ) (S : Set ℂ) (hS : S.Infinite)
    (havoid : ∀ w ∈ S, ∀ i, w ≠ z i)
    (hidentity :
      ∀ w ∈ S, ∑ i, c i / (z i - w) = 0) :
    distinctNodePacketNumerator z c = 0 := by
  apply Polynomial.eq_zero_of_infinite_isRoot
  apply hS.mono
  intro w hw
  have hne (i : ι) : z i - w ≠ 0 :=
    sub_ne_zero.mpr (havoid w hw i).symm
  have heval :
      (distinctNodePacketNumerator z c).eval w = 0 := by
    rw [distinctNodePacketNumerator]
    simp only [eval_finsetSum, eval_mul, eval_C, eval_prod, eval_sub,
      eval_X]
    calc
      ∑ i, c i * ∏ j ∈ Finset.univ.erase i, (z j - w) =
          (∑ i, c i / (z i - w)) * ∏ j, (z j - w) := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro i hi
            rw [← Finset.mul_prod_erase Finset.univ
              (fun j => z j - w) (Finset.mem_univ i)]
            field_simp [hne i]
      _ = 0 := by rw [hidentity w hw, zero_mul]
  exact heval

/-- A possible repeated zero-gap contribution cannot hide any residue at
distinct nonzero shifted poles. -/
theorem coefficients_eq_zero_of_shifted_rational_identity_with_zeroPole
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (pole coefficient : ι → ℂ) (zeroCoefficient : ℂ)
    (S : Set ℂ) (hS : S.Infinite)
    (hpole : Function.Injective pole)
    (hpole_ne : ∀ i, pole i ≠ 0)
    (havoidZero : ∀ z ∈ S, z ≠ 0)
    (havoid : ∀ z ∈ S, ∀ i, z ≠ -pole i)
    (hidentity :
      ∀ z ∈ S,
        zeroCoefficient / z +
          ∑ i, coefficient i / (z + pole i) = 0) :
    coefficient = 0 := by
  let extendedPole : Option ι → ℂ
    | none => 0
    | some i => -pole i
  let extendedCoefficient : Option ι → ℂ
    | none => -zeroCoefficient
    | some i => -coefficient i
  have hextendedPole : Function.Injective extendedPole := by
    intro x y hxy
    cases x with
    | none =>
        cases y with
        | none => rfl
        | some j =>
            exfalso
            exact hpole_ne j (neg_eq_zero.mp hxy.symm)
    | some i =>
        cases y with
        | none =>
            exfalso
            exact hpole_ne i (neg_eq_zero.mp hxy)
        | some j =>
            simpa [extendedPole] using hpole (neg_injective hxy)
  have hextendedAvoid :
      ∀ z ∈ S, ∀ o, z ≠ extendedPole o := by
    intro z hz o
    cases o with
    | none => simpa [extendedPole] using havoidZero z hz
    | some i => simpa [extendedPole] using havoid z hz i
  have hextendedIdentity :
      ∀ z ∈ S,
        ∑ o : Option ι,
          extendedCoefficient o / (extendedPole o - z) = 0 := by
    intro z hz
    rw [Fintype.sum_option]
    simp only [extendedCoefficient, extendedPole]
    have hzero :
        -zeroCoefficient / (0 - z) =
          zeroCoefficient / z := by
      rw [zero_sub, neg_div_neg_eq]
    have hterm (i : ι) :
        -coefficient i / (-pole i - z) =
          coefficient i / (z + pole i) := by
      rw [show -pole i - z = -(z + pole i) by ring,
        neg_div_neg_eq]
    rw [hzero]
    simp_rw [hterm]
    exact hidentity z hz
  have hextendedZero :
      extendedCoefficient = 0 := by
    exact
      (distinctNodePacketNumerator_eq_zero_iff
        extendedPole extendedCoefficient hextendedPole).1
        (distinctNodePacketNumerator_eq_zero_of_rational_identity
          extendedPole extendedCoefficient S hS
          hextendedAvoid hextendedIdentity)
  funext i
  have hi := congrFun hextendedZero (some i)
  simpa [extendedCoefficient] using neg_eq_zero.mp hi

/-- A cleared second-order residue identity with distinct poles and nonzero
transition weights forces every cross-layer relation coefficient to vanish. -/
theorem crossLayer_eq_of_distinctPole_identity
    {ι α ρ : Type*} [Fintype ι] [DecidableEq ι]
    (pole weight : ι → ℂ) (source target : ι → α)
    (coefficient : α → ρ → ℂ) (r s : ρ)
    (hpole : Function.Injective pole)
    (hweight : ∀ i, weight i ≠ 0)
    (hidentity :
      distinctNodePacketNumerator pole
        (fun i =>
          (coefficient (source i) r -
            coefficient (target i) s) * weight i) = 0) :
    ∀ i,
      coefficient (source i) r =
        coefficient (target i) s := by
  have hcoeff :=
    (distinctNodePacketNumerator_eq_zero_iff
      pole
      (fun i =>
        (coefficient (source i) r -
          coefficient (target i) s) * weight i)
      hpole).mp hidentity
  intro i
  have hi := congrFun hcoeff i
  simp only [Pi.zero_apply] at hi
  exact sub_eq_zero.mp ((mul_eq_zero.mp hi).resolve_right (hweight i))

/-- An actual simple-pole response identity on any infinite admissible
parameter set forces every cross-layer coefficient equality. -/
theorem crossLayer_eq_of_rational_identity
    {ι α ρ : Type*} [Fintype ι] [DecidableEq ι]
    (pole weight : ι → ℂ) (source target : ι → α)
    (coefficient : α → ρ → ℂ) (r s : ρ)
    (S : Set ℂ) (hS : S.Infinite)
    (hpole : Function.Injective pole)
    (hweight : ∀ i, weight i ≠ 0)
    (havoid : ∀ w ∈ S, ∀ i, w ≠ pole i)
    (hidentity :
      ∀ w ∈ S,
        ∑ i,
          ((coefficient (source i) r -
              coefficient (target i) s) * weight i) /
            (pole i - w) = 0) :
    ∀ i,
      coefficient (source i) r =
        coefficient (target i) s := by
  apply crossLayer_eq_of_distinctPole_identity
    pole weight source target coefficient r s hpole hweight
  exact distinctNodePacketNumerator_eq_zero_of_rational_identity
    pole
    (fun i =>
      (coefficient (source i) r -
        coefficient (target i) s) * weight i)
    S hS havoid hidentity

/-- Interaction-lift graph: an old-system transition is lifted precisely
when the attached local label changes. -/
def crossLayerLiftGraph
    {α : Type*} (G : SimpleGraph α) (ρ : Type*) :
    SimpleGraph (α × ρ) where
  Adj x y := G.Adj x.1 y.1 ∧ x.2 ≠ y.2
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1.ne rfl⟩

noncomputable instance crossLayerLiftGraph.instDecidableRel
    {α ρ : Type*} (G : SimpleGraph α) :
    DecidableRel (crossLayerLiftGraph G ρ).Adj :=
  Classical.decRel _

@[simp] theorem crossLayerLiftGraph_adj
    {α ρ : Type*} (G : SimpleGraph α)
    (a b : α) (r s : ρ) :
    (crossLayerLiftGraph G ρ).Adj (a, r) (b, s) ↔
      G.Adj a b ∧ r ≠ s :=
  Iff.rfl

/-- Cross-layer coefficient equalities are exactly the component-constant
zero-cochains of the interaction-lift graph. -/
theorem crossLayerEquality_iff_mem_componentConstant
    {α ρ : Type*}
    (G : SimpleGraph α)
    (coefficient : α → ρ → ℂ) :
    (∀ ⦃a b⦄, G.Adj a b →
        ∀ ⦃r s⦄, r ≠ s →
          coefficient a r = coefficient b s) ↔
      (fun p : α × ρ => coefficient p.1 p.2) ∈
        GaloisForLFunctions.componentConstant
          (crossLayerLiftGraph G ρ) ℂ := by
  constructor
  · intro h x y hxy
    exact h hxy.1 hxy.2
  · intro h a b hab r s hrs
    exact h (a, r) (b, s) ⟨hab, hrs⟩

/-- Relation space carried by the interaction lift, defined for arbitrary
possibly infinite system and local-label types. -/
def crossLayerRelationSpace
    {α : Type*} (G : SimpleGraph α) (ρ : Type*) :
    Submodule ℂ (α × ρ → ℂ) :=
  GaloisForLFunctions.componentConstant
    (crossLayerLiftGraph G ρ) ℂ

/-- **Infinite interaction-lift classification.** For every system graph
and every local alphabet, with no finiteness assumption, response-compatible
relation packets are exactly arbitrary functions on connected components of
the interaction lift. -/
def crossLayerRelationComponentEquiv
    {α : Type*} (G : SimpleGraph α) (ρ : Type*) :
    crossLayerRelationSpace G ρ ≃ₗ[ℂ]
      ((crossLayerLiftGraph G ρ).ConnectedComponent → ℂ) :=
  GaloisForLFunctions.componentConstantEquiv
    (crossLayerLiftGraph G ρ) ℂ

/-- Ordered transitions carried by an old-system interaction graph. -/
def OrientedTransition
    {α : Type*} (G : SimpleGraph α) :=
  {p : α × α // G.Adj p.1 p.2}

noncomputable instance OrientedTransition.instFintype
    {α : Type*} [Fintype α] (G : SimpleGraph α) :
    Fintype (OrientedTransition G) := by
  unfold OrientedTransition
  letI : DecidablePred (fun p : α × α => G.Adj p.1 p.2) :=
    Classical.decPred _
  infer_instance

noncomputable instance OrientedTransition.instDecidableEq
    {α : Type*} (G : SimpleGraph α) :
    DecidableEq (OrientedTransition G) :=
  Classical.decEq _

/-- Pole attached to an oriented transition. -/
def orientedTransitionPole
    {α : Type*} (G : SimpleGraph α) (energy : α → ℂ) :
    OrientedTransition G → ℂ :=
  fun p => energy p.1.1 - energy p.1.2

/-- **Pole-packet/cohomology equivalence.** With distinct transition gaps and
nonzero interaction weights, vanishing of every opposite-layer
second-order pole packet on any infinite admissible set is equivalent to the
coefficient packet being a component-constant zero-cochain on the
interaction lift. -/
theorem crossLayerPolePackets_vanish_iff_mem_componentConstant
    {α ρ : Type*} [Fintype α] [Fintype ρ]
    [DecidableEq α] [DecidableEq ρ]
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (energy : α → ℂ)
    (weight : OrientedTransition G → ρ → ρ → ℂ)
    (coefficient : α → ρ → ℂ)
    (S : Set ℂ) (hS : S.Infinite)
    (hpole : Function.Injective (orientedTransitionPole G energy))
    (hweight :
      ∀ p r s, r ≠ s → weight p r s ≠ 0)
    (havoid :
      ∀ w ∈ S, ∀ p, w ≠ orientedTransitionPole G energy p) :
    (∀ r s, r ≠ s →
        ∀ w ∈ S,
          ∑ p : OrientedTransition G,
            ((coefficient p.1.1 r -
                coefficient p.1.2 s) * weight p r s) /
              (orientedTransitionPole G energy p - w) = 0) ↔
      (fun p : α × ρ => coefficient p.1 p.2) ∈
        GaloisForLFunctions.componentConstant
          (crossLayerLiftGraph G ρ) ℂ := by
  rw [← crossLayerEquality_iff_mem_componentConstant G coefficient]
  constructor
  · intro h a b hab r s hrs
    let p : OrientedTransition G := ⟨(a, b), hab⟩
    exact crossLayer_eq_of_rational_identity
      (orientedTransitionPole G energy)
      (fun e => weight e r s)
      (fun e => e.1.1) (fun e => e.1.2)
      coefficient r s S hS hpole
      (fun e => hweight e r s hrs)
      havoid (h r s hrs) p
  · intro h r s hrs w hw
    apply Finset.sum_eq_zero
    intro p hp
    rw [h p.2 hrs, sub_self, zero_mul, zero_div]

/-- **Interaction-lift cohomology law.** The space of cross-layer
second-order relation packets modulo the trace direction has dimension
exactly the number of connected components of the interaction lift minus
one. -/
theorem finrank_crossLayerRelationQuotient
    {α ρ : Type*} [Fintype α] [Fintype ρ]
    [DecidableEq α] [DecidableEq ρ] [Nonempty α] [Nonempty ρ]
    (G : SimpleGraph α) [DecidableRel G.Adj] :
    Module.finrank ℂ
        (GaloisForLFunctions.componentConstant
              (crossLayerLiftGraph G ρ) ℂ ⧸
          (ℂ ∙
            (⟨fun _ => (1 : ℂ),
              GaloisForLFunctions.one_mem_componentConstant
                (crossLayerLiftGraph G ρ) ℂ⟩ :
              GaloisForLFunctions.componentConstant
                (crossLayerLiftGraph G ρ) ℂ))) =
      Fintype.card
          (crossLayerLiftGraph G ρ).ConnectedComponent - 1 := by
  exact GaloisForLFunctions.finrank_reducedH0
    (crossLayerLiftGraph G ρ) ℂ

/-- Having a third local label distinct from any prescribed pair.  This is
the exact combinatorial property used by the `q ≥ 3` extension step. -/
def HasSpareLabel (ρ : Type*) : Prop :=
  ∀ r s : ρ, ∃ t : ρ, t ≠ r ∧ t ≠ s

/-- Every finite local alphabet of cardinality at least three has a spare
label. -/
theorem hasSpareLabel_of_three_le_card
    (ρ : Type*) [Fintype ρ] [DecidableEq ρ]
    (hcard : 3 ≤ Fintype.card ρ) :
    HasSpareLabel ρ := by
  intro r s
  by_contra h
  push Not at h
  have hsub : (Finset.univ : Finset ρ) ⊆ {r, s} := by
    intro t ht
    by_cases htr : t = r
    · simp [htr]
    · simp [h t htr]
  have hle := Finset.card_le_card hsub
  have hpair : ({r, s} : Finset ρ).card ≤ 2 := by
    exact (Finset.card_insert_le r {s}).trans_eq (by simp)
  rw [Finset.card_univ] at hle
  omega

/-- For a local factor with a spare label, cross-layer equality on every
transition edge already makes all coefficients within one old-system block
equal. -/
theorem crossLayerEquality_same_source
    {α ρ β : Type*}
    (G : SimpleGraph α) (coefficient : α → ρ → β)
    (hspare : HasSpareLabel ρ)
    (hneighbour : ∀ a, ∃ b, G.Adj a b)
    (hcross :
      ∀ ⦃a b⦄, G.Adj a b →
        ∀ ⦃r s⦄, r ≠ s →
          coefficient a r = coefficient b s) :
    ∀ a r s, coefficient a r = coefficient a s := by
  intro a r s
  obtain ⟨b, hab⟩ := hneighbour a
  obtain ⟨t, htr, hts⟩ := hspare r s
  calc
    coefficient a r = coefficient b t :=
      hcross hab htr.symm
    _ = coefficient a s :=
      hcross hab.symm hts

/-- **Connected extension relation rigidity.**  If every transition edge
identifies coefficients in different local layers and the attached local
factor has a spare label, then a connected old-system transition graph
leaves only the constant coefficient packet. -/
theorem crossLayerEquality_constant
    {α ρ β : Type*} [Nonempty ρ]
    (G : SimpleGraph α) (coefficient : α → ρ → β)
    (hspare : HasSpareLabel ρ)
    (hneighbour : ∀ a, ∃ b, G.Adj a b)
    (hconnected : G.Preconnected)
    (hcross :
      ∀ ⦃a b⦄, G.Adj a b →
        ∀ ⦃r s⦄, r ≠ s →
          coefficient a r = coefficient b s) :
    ∀ a r b s, coefficient a r = coefficient b s := by
  let r₀ : ρ := Classical.arbitrary ρ
  have hsame :
      ∀ a r s, coefficient a r = coefficient a s :=
    crossLayerEquality_same_source
      G coefficient hspare hneighbour hcross
  have hedge :
      ∀ ⦃a b⦄, G.Adj a b →
        coefficient a r₀ = coefficient b r₀ := by
    intro a b hab
    obtain ⟨s, hsr₀, _⟩ := hspare r₀ r₀
    calc
      coefficient a r₀ = coefficient b s :=
        hcross hab hsr₀.symm
      _ = coefficient b r₀ :=
        hsame b s r₀
  intro a r b s
  have hblocks :
      coefficient a r₀ = coefficient b r₀ := by
    obtain ⟨p⟩ := hconnected a b
    induction p with
    | nil => rfl
    | cons hadj q ih =>
        exact (hedge hadj).trans ih
  calc
    coefficient a r = coefficient a r₀ := hsame a r r₀
    _ = coefficient b r₀ := hblocks
    _ = coefficient b s := hsame b r₀ s

/-- With a spare local label, connected old transition geometry makes the
entire interaction lift connected. -/
theorem crossLayerLiftGraph_preconnected_of_spareLabel
    {α ρ : Type*} [Nonempty ρ]
    (G : SimpleGraph α)
    (hspare : HasSpareLabel ρ)
    (hneighbour : ∀ a, ∃ b, G.Adj a b)
    (hconnected : G.Preconnected) :
    (crossLayerLiftGraph G ρ).Preconnected := by
  intro x y
  apply SimpleGraph.ConnectedComponent.exact
  have hconstant :=
    crossLayerEquality_constant G
      (fun a r =>
        (crossLayerLiftGraph G ρ).connectedComponentMk (a, r))
      hspare hneighbour hconnected
      (fun {_ _} hab {_ _} hrs =>
        SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
          ((crossLayerLiftGraph_adj G _ _ _ _).2 ⟨hab, hrs⟩))
  exact hconstant x.1 x.2 y.1 y.2

/-- A triangle removes the Boolean parity obstruction: cross-layer equality
then propagates through every connected old-system transition graph and
leaves only the constant relation. -/
theorem crossLayerEquality_constant_bool_of_triangle
    {α β : Type*}
    (G : SimpleGraph α) (coefficient : α → Bool → β)
    (hconnected : G.Preconnected)
    {a b c : α}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hca : G.Adj c a)
    (hcross :
      ∀ ⦃u v⦄, G.Adj u v →
        ∀ ⦃r s : Bool⦄, r ≠ s →
          coefficient u r = coefficient v s) :
    ∀ u r v s, coefficient u r = coefficient v s := by
  have hrootFalseTrue :
      coefficient a false = coefficient a true := by
    calc
      coefficient a false = coefficient b true :=
        hcross hab (by decide)
      _ = coefficient c false :=
        hcross hbc (by decide)
      _ = coefficient a true :=
        hcross hca (by decide)
  have hroot :
      ∀ r, coefficient a r = coefficient a false := by
    intro r
    cases r
    · rfl
    · exact hrootFalseTrue.symm
  have hedge :
      ∀ ⦃u v⦄, G.Adj u v →
        (∀ r, coefficient u r = coefficient a false) →
        ∀ s, coefficient v s = coefficient a false := by
    intro u v huv hu s
    calc
      coefficient v s = coefficient u (!s) :=
        (hcross huv (Bool.not_ne_self s)).symm
      _ = coefficient a false := hu (!s)
  have hwalk :
      ∀ ⦃u v⦄ (p : G.Walk u v),
        (∀ r, coefficient u r = coefficient a false) →
        ∀ s, coefficient v s = coefficient a false := by
    intro u v p
    induction p with
    | nil =>
        intro hu
        exact hu
    | cons huv p ih =>
        intro hu
        exact ih (hedge huv hu)
  intro u r v s
  obtain ⟨pu⟩ := hconnected a u
  obtain ⟨pv⟩ := hconnected a v
  exact (hwalk pu hroot r).trans (hwalk pv hroot s).symm

/-- A connected old transition graph containing a triangle has connected
Boolean interaction lift. -/
theorem crossLayerLiftGraph_bool_preconnected_of_triangle
    {α : Type*}
    (G : SimpleGraph α) (hconnected : G.Preconnected)
    {a b c : α}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hca : G.Adj c a) :
    (crossLayerLiftGraph G Bool).Preconnected := by
  intro x y
  apply SimpleGraph.ConnectedComponent.exact
  have hconstant :=
    crossLayerEquality_constant_bool_of_triangle G
      (fun u r =>
        (crossLayerLiftGraph G Bool).connectedComponentMk (u, r))
      hconnected hab hbc hca
      (fun {_ _} huv {_ _} hrs =>
        SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
          ((crossLayerLiftGraph_adj G _ _ _ _).2 ⟨huv, hrs⟩))
  exact hconstant x.1 x.2 y.1 y.2

end

end GaloisForLFunctions.HTGeometry
