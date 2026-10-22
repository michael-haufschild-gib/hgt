import GaloisForLFunctions.RHTower.Deninger.DeningerArithCurvePoints
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Algebra.Ring.Subring.Basic

/-!
# The structure ring of an open set of the arithmetic curve

A rational number is regular on an open set of the arithmetic curve exactly when its valuation is
nonnegative at every prime in that set; the ultrametric inequality makes these rationals a subring.
It is a unit of that subring exactly when all those valuations vanish, since the inverse is regular
precisely when the valuations are nonpositive.

* `deningerArithRing` : the ring of regular functions on an open set.
* `deningerArithRing_isUnit_iff` : its units are the rationals with vanishing valuations.
-/

namespace RHTower

open TopologicalSpace

/-- The ring of regular functions on an open set of the arithmetic curve: the rationals whose
valuation is nonnegative at every prime of the set. -/
def deningerArithRing (U : Opens deningerArithBase) : Subring ℚ where
  carrier := {q : ℚ | ∀ p : Nat.Primes, deningerClosedPt p ∈ U → 0 ≤ padicValRat (p : ℕ) q}
  zero_mem' := by
    intro p _
    rw [padicValRat.zero]
  one_mem' := by
    intro p _
    rw [padicValRat.one]
  add_mem' := by
    intro a b ha hb p hp
    haveI : Fact ((p : ℕ)).Prime := ⟨p.2⟩
    by_cases h : a + b = 0
    · rw [h, padicValRat.zero]
    · exact le_trans (le_min (ha p hp) (hb p hp)) (padicValRat.min_le_padicValRat_add h)
  neg_mem' := by
    intro a ha p hp
    rw [padicValRat.neg]
    exact ha p hp
  mul_mem' := by
    intro a b ha hb p hp
    haveI : Fact ((p : ℕ)).Prime := ⟨p.2⟩
    by_cases h : a = 0
    · rw [h, zero_mul, padicValRat.zero]
    by_cases h' : b = 0
    · rw [h', mul_zero, padicValRat.zero]
    · rw [padicValRat.mul h h']
      exact add_nonneg (ha p hp) (hb p hp)

theorem deningerArithRing_mem_iff (U : Opens deningerArithBase) (q : ℚ) :
    q ∈ deningerArithRing U ↔
      ∀ p : Nat.Primes, deningerClosedPt p ∈ U → 0 ≤ padicValRat (p : ℕ) q := Iff.rfl

/-- **A regular function is a unit exactly when all its valuations vanish.** -/
theorem deningerArithRing_isUnit_iff (U : Opens deningerArithBase) (r : deningerArithRing U) :
    IsUnit r ↔ ((r : ℚ) ≠ 0 ∧
      ∀ p : Nat.Primes, deningerClosedPt p ∈ U → padicValRat (p : ℕ) (r : ℚ) = 0) := by
  constructor
  · intro hru
    obtain ⟨s, hs⟩ := hru.exists_right_inv
    have hs' : (r : ℚ) * (s : ℚ) = 1 := by
      have h := congrArg (fun z : deningerArithRing U => (z : ℚ)) hs
      push_cast at h
      exact h
    have hr0 : (r : ℚ) ≠ 0 := by
      intro h
      rw [h, zero_mul] at hs'
      exact zero_ne_one hs'
    have hs0 : (s : ℚ) ≠ 0 := by
      intro h
      rw [h, mul_zero] at hs'
      exact zero_ne_one hs'
    refine ⟨hr0, fun p hp => ?_⟩
    haveI : Fact ((p : ℕ)).Prime := ⟨p.2⟩
    have hsum : padicValRat (p : ℕ) (r : ℚ) + padicValRat (p : ℕ) (s : ℚ) = 0 := by
      rw [← padicValRat.mul hr0 hs0, hs', padicValRat.one]
    have h1 : 0 ≤ padicValRat (p : ℕ) (r : ℚ) := r.2 p hp
    have h2 : 0 ≤ padicValRat (p : ℕ) (s : ℚ) := s.2 p hp
    omega
  · rintro ⟨hr0, hval⟩
    have hinv : (r : ℚ)⁻¹ ∈ deningerArithRing U := by
      intro p hp
      haveI : Fact ((p : ℕ)).Prime := ⟨p.2⟩
      rw [padicValRat.inv, hval p hp, neg_zero]
    refine isUnit_iff_exists_inv.2 ⟨⟨(r : ℚ)⁻¹, hinv⟩, ?_⟩
    refine Subtype.ext ?_
    show (r : ℚ) * (r : ℚ)⁻¹ = 1
    exact mul_inv_cancel₀ hr0

end RHTower
