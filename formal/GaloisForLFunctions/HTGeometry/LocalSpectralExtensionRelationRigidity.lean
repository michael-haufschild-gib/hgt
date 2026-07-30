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

end

end GaloisForLFunctions.HTGeometry
