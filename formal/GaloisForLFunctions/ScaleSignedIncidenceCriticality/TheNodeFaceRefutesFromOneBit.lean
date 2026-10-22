import GaloisForLFunctions.ScaleSignedIncidenceCriticality.ThePrimePowersAreTheLeastPositiveNodeSet
import GaloisForLFunctions.ScaleSignedIncidenceCriticality.TheRefutationCalculusIsCompleteOnBothFaces

/-!
# The node face refutes from one bit

The refutation calculus is complete on the zero side and on the prime side: if RH fails, bounded data
certify it (`TheRefutationCalculusIsCompleteOnBothFaces`). On the incidence face the statement is
sharper still, because the classification of the positive node sets is a principal up-set
(`ThePrimePowersAreTheLeastPositiveNodeSet`): the whole face is decided by *membership*.

The reading `membershipReading m` is one bit: whether the prime power `m` lies in the node set. If
it does not, every node set with the same bit also omits `m`, and omitting one prime power destroys
zero-pole positivity (`not_zeroPoleBlindPositiveOn_deleteNode`). Hence
`refutes_membershipReading_of_notMem`: **one bit refutes.** And the refutation is complete
(`zeroPoleBlindPositiveOn_iff_no_membership_refutes`): a node set is positive exactly when no
single-prime-power bit refutes it.

`theNodeFaceAsymmetry` states the resulting asymmetry, which is extreme on this face: refuting costs
one bit, while confirming costs **all** of them — the floor `½` of
`TheNodeFaceUnitIsAReciprocalPrimePower` says no asymptotic reading, however much it sees of the
node set, replaces the infinitely many individual bits.

This is the incidence counterpart of `RefutationIsFiniteConfirmationIsNot`, and the sharpest form of
the field's slogan that the gate is incidence and never density: the datum that decides the negative
side is a single membership, and the datum that decides the positive side is the whole prime-power
set.
-/

open Set

namespace GaloisForLFunctions.ScaleSignedIncidenceCriticality

open GaloisForLFunctions.BiScaleUncertainty

set_option autoImplicit false

/-! ### 1. One bit of membership -/

/-- The one-bit reading: whether the prime power `m` is a node. -/
def membershipReading (m : ℕ) (𝒩 : Set ℕ) : Prop := m ∈ 𝒩

/-- **One bit refutes.** A node set missing a prime power is refuted by that bit alone. -/
theorem refutes_membershipReading_of_notMem {m : ℕ} (hm : IsPrimePow m) {𝒩 : Set ℕ}
    (hmem : m ∉ 𝒩) : Refutes (membershipReading m) ZeroPoleBlindPositiveOn 𝒩 := by
  intro ℳ hℳ hpos
  have hmemℳ : m ∉ ℳ := by
    intro h
    exact hmem ((mem_shadow_iff.mp hℳ) ▸ h : membershipReading m 𝒩)
  have hdiff : deleteNode m ℳ = ℳ := Set.sdiff_singleton_eq_self hmemℳ
  exact not_zeroPoleBlindPositiveOn_deleteNode hm ℳ (by rw [hdiff]; exact hpos)

/-! ### 2. Completeness of the one-bit refutation -/

/-- **Completeness.** Under RH a node set is zero-pole positive exactly when no single
prime-power bit refutes it. -/
theorem zeroPoleBlindPositiveOn_iff_no_membership_refutes (hRH : RiemannHypothesis)
    (𝒩 : Set ℕ) :
    ZeroPoleBlindPositiveOn 𝒩 ↔
      ¬ ∃ m : ℕ, IsPrimePow m ∧ Refutes (membershipReading m) ZeroPoleBlindPositiveOn 𝒩 := by
  refine ⟨fun hpos hex => ?_, fun h => ?_⟩
  · obtain ⟨m, -, href⟩ := hex
    exact not_of_refutes href hpos
  · refine (zeroPoleBlindPositiveOn_iff_primePowers_subset hRH 𝒩).mpr fun m hm => ?_
    by_contra hmem
    exact h ⟨m, hm, refutes_membershipReading_of_notMem hm hmem⟩

/-! ### 3. The asymmetry -/

/-- **The node face's asymmetry is extreme.** Refuting takes one bit; confirming takes all of them,
since no asymptotic reading of the node set certifies anything below the trivial `½`. -/
theorem theNodeFaceAsymmetry (hRH : RiemannHypothesis) :
    (∀ (m : ℕ) (𝒩 : Set ℕ), IsPrimePow m → m ∉ 𝒩 →
        Refutes (membershipReading m) ZeroPoleBlindPositiveOn 𝒩) ∧
      (∀ 𝒩 : Set ℕ, ZeroPoleBlindPositiveOn 𝒩 ↔
        ¬ ∃ m : ℕ, IsPrimePow m ∧ Refutes (membershipReading m) ZeroPoleBlindPositiveOn 𝒩) ∧
      ∀ (O : Type) (r : Set ℕ → O), AsymptoticReading r →
        resolutionLimit nodeScale r {n : ℕ | IsPrimePow n} = 1 / 2 :=
  ⟨fun _ _ hm hmem => refutes_membershipReading_of_notMem hm hmem,
    zeroPoleBlindPositiveOn_iff_no_membership_refutes hRH,
    fun _ _ h => resolutionLimit_nodeScale_asymptoticReading h⟩

end GaloisForLFunctions.ScaleSignedIncidenceCriticality
