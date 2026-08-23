import GaloisForLFunctions.HTGeometry.PrimeWordSupportSelector

/-!
# Primitive-disconnected finite prime grammar

The Euler logarithm has connected primitive contributions at one prime only.  Products supported
at distinct primes are commutative tensor composites, not new connected primitives.  This file
records that syntax in the free commutative monoid of finite prime-exponent packets.

The main theorem, `disjointPrimeTensor_not_connected`, says that the tensor sum of two nonzero
packets with disjoint prime support has support cardinality at least two.  In particular, two
distinct prime powers cannot become one connected primitive.  This is the commutative-monoid
counterpart of `PrimeLoopMixedWordObstruction` and `PrimeWordSupportSelector`: it permits higher
coherence between prime sectors without introducing a mixed connected Euler word.

This finite grammar does not construct analytic completion, Gamma boundary data, an equivariant
error spectrum, or an RH endpoint.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Finite exponent packet in the free commutative monoid on rational primes. -/
abbrev PrimeExponentPacket := Nat.Primes →₀ ℕ

/-- A connected prime-power packet has exactly one occupied prime label. -/
def IsConnectedPrimePowerPacket (q : PrimeExponentPacket) : Prop :=
  q.support.card = 1

/-- Two nonempty packets form a genuinely disconnected tensor when their prime supports are disjoint. -/
def IsDisjointPrimeTensor (a b : PrimeExponentPacket) : Prop :=
  Disjoint a.support b.support ∧ a ≠ 0 ∧ b ≠ 0

/-- The packet for one prime power `p^e`. -/
def primePowerPacket (p : Nat.Primes) (e : ℕ) : PrimeExponentPacket :=
  Finsupp.single p e

/-- Natural-number exponents cannot cancel, so tensor support is exactly support union. -/
theorem primeExponentPacket_support_add
    (a b : PrimeExponentPacket) :
    (a + b).support = a.support ∪ b.support := by
  classical
  ext p
  simp only [Finsupp.mem_support_iff, Finsupp.add_apply, Finset.mem_union]
  omega

theorem primePowerPacket_support
    (p : Nat.Primes) {e : ℕ} (he : e ≠ 0) :
    (primePowerPacket p e).support = {p} := by
  classical
  ext q
  simp [primePowerPacket, he]

/-- Every positive power at one prime is a connected primitive packet. -/
theorem primePowerPacket_connected
    (p : Nat.Primes) {e : ℕ} (he : e ≠ 0) :
    IsConnectedPrimePowerPacket (primePowerPacket p e) := by
  rw [IsConnectedPrimePowerPacket, primePowerPacket_support p he]
  simp

/-- A tensor of two nonempty disjoint prime sectors occupies at least two primes. -/
theorem two_le_support_card_of_isDisjointPrimeTensor
    {a b : PrimeExponentPacket} (h : IsDisjointPrimeTensor a b) :
    2 ≤ (a + b).support.card := by
  rw [primeExponentPacket_support_add,
    Finset.card_union_of_disjoint h.1]
  have ha : 0 < a.support.card :=
    Finset.card_pos.mpr (Finsupp.support_nonempty_iff.mpr h.2.1)
  have hb : 0 < b.support.card :=
    Finset.card_pos.mpr (Finsupp.support_nonempty_iff.mpr h.2.2)
  omega

/-- Disjoint nonzero tensor factors cannot be reclassified as one connected Euler primitive. -/
theorem disjointPrimeTensor_not_connected
    {a b : PrimeExponentPacket} (h : IsDisjointPrimeTensor a b) :
    ¬ IsConnectedPrimePowerPacket (a + b) := by
  intro hc
  have htwo := two_le_support_card_of_isDisjointPrimeTensor h
  unfold IsConnectedPrimePowerPacket at hc
  omega

theorem distinctPrimePowers_form_disjointTensor
    {p q : Nat.Primes} (hpq : p ≠ q) {e f : ℕ} (he : e ≠ 0) (hf : f ≠ 0) :
    IsDisjointPrimeTensor (primePowerPacket p e) (primePowerPacket q f) := by
  constructor
  · rw [primePowerPacket_support p he, primePowerPacket_support q hf]
    simpa [Finset.disjoint_singleton]
  · constructor
    · intro hzero
      have h := congrArg (fun z : PrimeExponentPacket => z p) hzero
      simp [primePowerPacket, he] at h
    · intro hzero
      have h := congrArg (fun z : PrimeExponentPacket => z q) hzero
      simp [primePowerPacket, hf] at h

/-- Two nonzero powers at distinct primes form a disconnected composite, never one primitive. -/
theorem distinctPrimePowerTensor_not_connected
    {p q : Nat.Primes} (hpq : p ≠ q) {e f : ℕ} (he : e ≠ 0) (hf : f ≠ 0) :
    ¬ IsConnectedPrimePowerPacket
      (primePowerPacket p e + primePowerPacket q f) :=
  disjointPrimeTensor_not_connected
    (distinctPrimePowers_form_disjointTensor hpq he hf)

end

end GaloisForLFunctions.HTGeometry
