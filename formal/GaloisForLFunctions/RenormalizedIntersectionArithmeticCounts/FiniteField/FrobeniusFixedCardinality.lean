import GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts.FiniteField.FrobeniusDescent
import Mathlib.Dynamics.PeriodicPts.Defs

/-!
# Gcd-controlled Frobenius fixed fields

The fixed subfield of the `p^k`-power map in a finite extension of degree `N`
over `𝔽_p` has `p^gcd(N,k)` elements. Intersections of fixed subfields correspond
to gcds of the exponents. Periodicity gives the gcd reduction; an actual
finite-field embedding identifies the resulting fixed elements.
-/

noncomputable section

namespace GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts

variable (p : ℕ) [Fact p.Prime]

/-- Frobenius periodicity is exactly the corresponding prime-power equation. -/
theorem isPeriodicPt_frobenius_iff {K : Type*} [CommSemiring K] [CharP K p]
    (k : ℕ) (x : K) :
    Function.IsPeriodicPt (frobenius K p) k x ↔ x ^ p ^ k = x := by
  simp only [Function.IsPeriodicPt, Function.IsFixedPt, iterate_frobenius]

/-- A Frobenius fixed point is fixed at every multiple of its exponent. -/
theorem frobenius_fixed_of_dvd {K : Type*} [CommSemiring K] [CharP K p]
    {m n : ℕ} (h : m ∣ n) {x : K} (hx : x ^ p ^ m = x) : x ^ p ^ n = x := by
  obtain ⟨j, rfl⟩ := h
  exact (isPeriodicPt_frobenius_iff p _ x).mp
    (((isPeriodicPt_frobenius_iff p m x).mpr hx).mul_const j)

/-- Simultaneous Frobenius fixed points are precisely the gcd fixed points. -/
theorem frobenius_fixed_gcd_iff {K : Type*} [CommSemiring K] [CharP K p]
    (m n : ℕ) (x : K) :
    x ^ p ^ Nat.gcd m n = x ↔ x ^ p ^ m = x ∧ x ^ p ^ n = x := by
  constructor
  · intro h
    exact ⟨frobenius_fixed_of_dvd p (Nat.gcd_dvd_left m n) h,
      frobenius_fixed_of_dvd p (Nat.gcd_dvd_right m n) h⟩
  · rintro ⟨hm, hn⟩
    exact (isPeriodicPt_frobenius_iff p _ x).mp
      (((isPeriodicPt_frobenius_iff p m x).mpr hm).gcd
        ((isPeriodicPt_frobenius_iff p n x).mpr hn))

variable (K : Type*) [Field K] [CharP K p]

/-- The actual subfield fixed by a power of Frobenius. -/
def frobeniusFixedSubfield (k : ℕ) : Subfield K :=
  (iterateFrobenius K p k).eqLocusField (RingHom.id _)

/-- Membership is the defining power equation. -/
theorem mem_frobeniusFixedSubfield (k : ℕ) (x : K) :
    x ∈ frobeniusFixedSubfield p K k ↔ x ^ p ^ k = x := Iff.rfl

/-- Intersecting two fixed subfields takes the gcd of their exponents. -/
theorem frobeniusFixedSubfield_inf (m n : ℕ) :
    frobeniusFixedSubfield p K m ⊓ frobeniusFixedSubfield p K n =
      frobeniusFixedSubfield p K (Nat.gcd m n) := by
  ext x
  exact (frobenius_fixed_gcd_iff p m n x).symm

variable [Finite K] [Algebra (ZMod p) K]

omit [CharP K p] in
/-- Frobenius raised to the prime-field degree fixes every element. -/
theorem finiteField_frobenius_full_period (x : K) :
    x ^ p ^ Module.finrank (ZMod p) K = x := by
  letI := Fintype.ofFinite K
  rw [FiniteField.pow_finrank_eq_natCard, Nat.card_eq_fintype_card]
  exact FiniteField.pow_card x

/-- A divisor of the prime-field degree gives a fixed subfield of exactly that degree. -/
theorem frobeniusFixedSubfield_card_of_dvd (k : ℕ) (hk : 0 < k)
    (hd : k ∣ Module.finrank (ZMod p) K) :
    Nat.card (frobeniusFixedSubfield p K k) = p ^ k := by
  letI : NeZero k := ⟨hk.ne'⟩
  let E := FiniteField.Extension (ZMod p) p k
  letI := Fintype.ofFinite E
  have hE : Module.finrank (ZMod p) E = k := by
    simpa only [Module.finrank_self, one_mul] using FiniteField.finrank_zmod_extension (ZMod p) p k
  obtain ⟨e⟩ := FiniteField.nonempty_algHom_of_finrank_dvd
    (F := ZMod p) (K := E) (L := K) (by rw [hE]; exact hd)
  have hc := Nat.card_congr (finiteFieldFrobeniusFixedEquiv (ZMod p) E K e)
  simp only [finiteField_frobenius_pow_apply, hE, ZMod.card] at hc
  change Nat.card {x : K // x ^ p ^ k = x} = p ^ k
  rw [← hc]
  exact (FiniteField.natCard_extension (ZMod p) p k).trans (by rw [Nat.card_zmod])

/-- Every Frobenius fixed subfield has the gcd-predicted cardinality, including exponent zero. -/
theorem frobeniusFixedSubfield_card (k : ℕ) :
    Nat.card (frobeniusFixedSubfield p K k) = p ^ Nat.gcd (Module.finrank (ZMod p) K) k := by
  have hiff (x : K) : x ^ p ^ k = x ↔ x ^ p ^ Nat.gcd (Module.finrank (ZMod p) K) k = x := by
    constructor
    · intro hx
      exact (frobenius_fixed_gcd_iff p _ k x).mpr ⟨finiteField_frobenius_full_period p K x, hx⟩
    · intro hx
      exact ((frobenius_fixed_gcd_iff p _ k x).mp hx).2
  have he : frobeniusFixedSubfield p K k ≃
      frobeniusFixedSubfield p K (Nat.gcd (Module.finrank (ZMod p) K) k) :=
    Equiv.subtypeEquivRight hiff
  rw [Nat.card_congr he]
  exact frobeniusFixedSubfield_card_of_dvd p K _
    (Nat.gcd_pos_of_pos_left k Module.finrank_pos) (Nat.gcd_dvd_left _ _)

/-- The size of an intersection of arbitrary Frobenius fixed subfields. -/
theorem frobeniusFixedSubfield_inf_card (m n : ℕ) :
    Nat.card ↥(frobeniusFixedSubfield p K m ⊓ frobeniusFixedSubfield p K n) =
      p ^ Nat.gcd (Module.finrank (ZMod p) K) (Nat.gcd m n) := by
  rw [frobeniusFixedSubfield_inf, frobeniusFixedSubfield_card]

end GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
