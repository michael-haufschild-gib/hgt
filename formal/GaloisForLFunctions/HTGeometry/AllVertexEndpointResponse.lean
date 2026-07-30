import GaloisForLFunctions.HTGeometry.LocalTwoLayerSpectralResponse

/-!
# Two-step response for all-vertex endpoint propagation

When a new local factor is attached at one old site, an observable at any
other old site acquires cross-layer transitions through a two-step channel:

1. one transition visible at the attachment site;
2. one transition visible at the old observer site.

The first-order response is a finite partial-fraction packet in the new
onsite layer shift.  Maximal projective rank makes the selected attachment
pole unique even though arbitrary collisions are allowed among all remaining
channels.  Its nonzero residue therefore makes the cleared response
polynomial nonzero.

This is the algebraic no-cancellation core needed to preserve observable
transition graphs at every old vertex during leaf attachment.
-/

open Polynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Pole labels of the two parts of an old-observer cross-layer response.
The left packet first uses the attachment transition; the right packet first
uses the observer transition. -/
def twoStepEndpointPacketPole
    {I : Type*} (energy : I → ℝ) (a b : I) :
    Sum I I → ℂ
  | Sum.inl d => (energy d - energy a : ℝ)
  | Sum.inr d => (energy b - energy d : ℝ)

/-- Residues of the two-step old-observer response, with signs chosen for
the common denominator convention `pole - shift`. -/
def twoStepEndpointPacketCoefficient
    {I : Type*} (attachment observer : Matrix I I ℂ)
    (a b : I) : Sum I I → ℂ
  | Sum.inl d => -(attachment a d * observer d b)
  | Sum.inr d => observer a d * attachment d b

/-- The pole of a nontrivial selected two-step channel is not shared by any
other term in the full response packet.  No separation among the remaining
poles is assumed. -/
theorem twoStepEndpointPacketPole_selected_unique
    {I : Type*} [Fintype I] [DecidableEq I]
    (energy : I → ℝ) (hmax : MaximallyProjectiveEnergy energy)
    {a g b : I} (hag : a ≠ g) (hgb : g ≠ b) :
    ∀ j, j ≠ Sum.inl g →
      twoStepEndpointPacketPole energy a b j ≠
        twoStepEndpointPacketPole energy a b (Sum.inl g) := by
  intro j hj
  cases j with
  | inl d =>
      simp only [twoStepEndpointPacketPole]
      intro hgap
      have hgapReal :
          energy d - energy a = energy g - energy a :=
        Complex.ofReal_injective hgap
      have hdg : energy d = energy g := by
        linarith
      have hdg' :=
        maximallyProjectiveEnergy_injective energy hmax hdg
      subst d
      exact hj rfl
  | inr d =>
      simp only [twoStepEndpointPacketPole]
      intro hgap
      have hgapReal :
          energy b - energy d = energy g - energy a :=
        Complex.ofReal_injective hgap
      by_cases hbd : b = d
      · subst d
        have henergy : energy g = energy a := by
          linarith
        exact hag
          ((maximallyProjectiveEnergy_injective energy hmax) henergy).symm
      · let p : {x : I × I // x.1 ≠ x.2} :=
          ⟨(g, a), hag.symm⟩
        let q : {x : I × I // x.1 ≠ x.2} :=
          ⟨(b, d), hbd⟩
        have hpq :
            (fun x : {x : I × I // x.1 ≠ x.2} =>
              energy x.1.1 - energy x.1.2) p =
            (fun x : {x : I × I // x.1 ≠ x.2} =>
              energy x.1.1 - energy x.1.2) q := by
          simpa [p, q] using hgapReal.symm
        have heq :=
          maximallyProjectiveEnergy_orientedGap_injective energy hmax hpq
        have hgb' : g = b := by
          simpa [p, q] using congrArg (fun x => x.1.1) heq
        exact hgb hgb'

/-- **Two-step endpoint no-cancellation law.**  A nonzero attachment channel
`a → g` followed by a nonzero observer channel `g → b` forces the cleared
cross-layer response packet to be nonzero.  Every other attachment and
observer matrix element remains arbitrary. -/
theorem twoStepEndpointPacketNumerator_ne_zero
    {I : Type*} [Fintype I] [DecidableEq I]
    (energy : I → ℝ) (hmax : MaximallyProjectiveEnergy energy)
    (attachment observer : Matrix I I ℂ)
    {a g b : I} (hag : a ≠ g) (hgb : g ≠ b)
    (hattachment : attachment a g ≠ 0)
    (hobserver : observer g b ≠ 0) :
    distinctNodePacketNumerator
      (twoStepEndpointPacketPole energy a b)
      (twoStepEndpointPacketCoefficient attachment observer a b) ≠ 0 := by
  intro hzero
  have heval :=
    congrArg (fun P : ℂ[X] =>
      P.eval
        (twoStepEndpointPacketPole energy a b (Sum.inl g))) hzero
  have hisolated :
      twoStepEndpointPacketCoefficient attachment observer a b
          (Sum.inl g) *
        ∏ j ∈ Finset.univ.erase (Sum.inl g),
          (twoStepEndpointPacketPole energy a b j -
            twoStepEndpointPacketPole energy a b (Sum.inl g)) = 0 := by
    simpa [distinctNodePacketNumerator_eval_node] using heval
  have hcoefficient :
      twoStepEndpointPacketCoefficient attachment observer a b
          (Sum.inl g) ≠ 0 := by
    simp only [twoStepEndpointPacketCoefficient, neg_ne_zero]
    exact mul_ne_zero hattachment hobserver
  have hprod :
      ∏ j ∈ Finset.univ.erase (Sum.inl g),
          (twoStepEndpointPacketPole energy a b j -
            twoStepEndpointPacketPole energy a b (Sum.inl g)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    apply sub_ne_zero.mpr
    exact twoStepEndpointPacketPole_selected_unique
      energy hmax hag hgb j (Finset.mem_erase.mp hj).1
  exact (mul_ne_zero hcoefficient hprod) hisolated

/-- The actual finite simple-pole packet associated with the two-step
endpoint response. -/
def twoStepEndpointPacketResponse
    {I : Type*} [Fintype I]
    (energy : I → ℝ) (attachment observer : Matrix I I ℂ)
    (a b : I) (shift : ℂ) : ℂ :=
  ∑ j : Sum I I,
    twoStepEndpointPacketCoefficient attachment observer a b j /
      (twoStepEndpointPacketPole energy a b j - shift)

/-- Expanded perturbative form of the same response: the first sum moves
through the attachment channel before applying the observer, while the
second applies them in the opposite order. -/
theorem twoStepEndpointPacketResponse_eq
    {I : Type*} [Fintype I]
    (energy : I → ℝ) (attachment observer : Matrix I I ℂ)
    (a b : I) (shift : ℂ) :
    twoStepEndpointPacketResponse
        energy attachment observer a b shift =
      (∑ d,
        attachment a d * observer d b /
          (shift + energy a - energy d)) +
      ∑ d,
        observer a d * attachment d b /
          (-shift + energy b - energy d) := by
  rw [twoStepEndpointPacketResponse, Fintype.sum_sum_type]
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro d hd
    simp only [twoStepEndpointPacketCoefficient,
      twoStepEndpointPacketPole]
    push_cast
    rw [show
      (energy d : ℂ) - energy a - shift =
        -(shift + energy a - energy d) by ring,
      neg_div_neg_eq]
  · apply Finset.sum_congr rfl
    intro d hd
    congr 1
    simp only [twoStepEndpointPacketPole]
    push_cast
    ring

/-- A nonzero two-step channel is observable at some collision-free onsite
layer shift.  This turns the nonzero cleared numerator into an admissible
physical parameter witness without selecting or suppressing any other
matrix entry. -/
theorem exists_twoStepEndpointPacketResponse_ne_zero
    {I : Type*} [Fintype I] [DecidableEq I]
    (energy : I → ℝ) (hmax : MaximallyProjectiveEnergy energy)
    (attachment observer : Matrix I I ℂ)
    {a g b : I} (hag : a ≠ g) (hgb : g ≠ b)
    (hattachment : attachment a g ≠ 0)
    (hobserver : observer g b ≠ 0) :
    ∃ shift : ℂ,
      (∀ j,
        shift ≠ twoStepEndpointPacketPole energy a b j) ∧
      twoStepEndpointPacketResponse
        energy attachment observer a b shift ≠ 0 := by
  let pole := twoStepEndpointPacketPole energy a b
  let coefficient :=
    twoStepEndpointPacketCoefficient attachment observer a b
  let S : Set ℂ := (Set.range pole)ᶜ
  have hS : S.Infinite :=
    (Set.finite_range pole).infinite_compl
  have hnum :
      distinctNodePacketNumerator pole coefficient ≠ 0 := by
    exact twoStepEndpointPacketNumerator_ne_zero
      energy hmax attachment observer hag hgb hattachment hobserver
  by_contra hnone
  push Not at hnone
  have hidentity :
      ∀ shift ∈ S,
        ∑ j, coefficient j / (pole j - shift) = 0 := by
    intro shift hshift
    apply hnone shift
    intro j heq
    exact hshift ⟨j, heq.symm⟩
  have hzero :
      distinctNodePacketNumerator pole coefficient = 0 := by
    apply distinctNodePacketNumerator_eq_zero_of_rational_identity
      pole coefficient S hS
    · intro shift hshift j heq
      exact hshift ⟨j, heq.symm⟩
    · exact hidentity
  exact hnum hzero

/-- The nonzero response may be witnessed at a real physical shift; in fact
one can choose a nonnegative integer shift outside the finite collision set.
-/
theorem exists_natCast_twoStepEndpointPacketResponse_ne_zero
    {I : Type*} [Fintype I] [DecidableEq I]
    (energy : I → ℝ) (hmax : MaximallyProjectiveEnergy energy)
    (attachment observer : Matrix I I ℂ)
    {a g b : I} (hag : a ≠ g) (hgb : g ≠ b)
    (hattachment : attachment a g ≠ 0)
    (hobserver : observer g b ≠ 0) :
    ∃ n : ℕ,
      (∀ j,
        (n : ℂ) ≠ twoStepEndpointPacketPole energy a b j) ∧
      twoStepEndpointPacketResponse
        energy attachment observer a b n ≠ 0 := by
  let pole := twoStepEndpointPacketPole energy a b
  let coefficient :=
    twoStepEndpointPacketCoefficient attachment observer a b
  let R : Set ℂ := Set.range (fun n : ℕ => (n : ℂ))
  let S : Set ℂ := R \ Set.range pole
  have hR : R.Infinite :=
    Set.infinite_range_of_injective Nat.cast_injective
  have hS : S.Infinite :=
    hR.sdiff (Set.finite_range pole)
  have hnum :
      distinctNodePacketNumerator pole coefficient ≠ 0 := by
    exact twoStepEndpointPacketNumerator_ne_zero
      energy hmax attachment observer hag hgb hattachment hobserver
  by_contra hnone
  push Not at hnone
  have hidentity :
      ∀ shift ∈ S,
        ∑ j, coefficient j / (pole j - shift) = 0 := by
    intro shift hshift
    rcases hshift.1 with ⟨n, rfl⟩
    apply hnone n
    intro j heq
    exact hshift.2 ⟨j, heq.symm⟩
  have hzero :
      distinctNodePacketNumerator pole coefficient = 0 := by
    apply distinctNodePacketNumerator_eq_zero_of_rational_identity
      pole coefficient S hS
    · intro shift hshift j heq
      exact hshift.2 ⟨j, heq.symm⟩
    · exact hidentity
  exact hnum hzero

end

end GaloisForLFunctions.HTGeometry
