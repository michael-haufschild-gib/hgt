import GaloisForLFunctions.HTGeometry.AiryTowerFactorization
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Nat.Factorization.Basic

/-!
# Exact enumeration of Airy towers

For prime-power ramification, ordered factorizations are compositions of the exponent.  This file
constructs the equivalence itself and derives the exact cardinality, rather than recording only a
numerical recurrence.
-/

namespace GaloisForLFunctions
namespace IrregularStokes

namespace OrderedFactorization

/-- Factorization exponent of a list product is the sum of the factor exponents. -/
theorem factorization_prod_apply (p : ℕ) (l : List ℕ) (hnz : ∀ a ∈ l, a ≠ 0) :
    l.prod.factorization p = (l.map fun a => a.factorization p).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
      have ha : a ≠ 0 := hnz a (by simp)
      have hl : ∀ b ∈ l, b ≠ 0 := fun b hb => hnz b (by simp [hb])
      have hprod : l.prod ≠ 0 := by
        apply List.prod_ne_zero
        intro hzero
        exact hl 0 hzero rfl
      rw [List.prod_cons, Nat.factorization_mul ha hprod]
      simp [ih hl]

/-- Products of same-base powers add their exponents. -/
theorem prod_map_pow (p : ℕ) (l : List ℕ) :
    (l.map fun b => p ^ b).prod = p ^ l.sum := by
  induction l with
  | nil => simp
  | cons b l ih => simp [ih, pow_add]

/-- Every factor of an ordered factorization of a prime power is the corresponding power of that
prime. -/
theorem factor_eq_prime_pow {p k : ℕ} (hp : p.Prime) (f : OrderedFactorization (p ^ k))
    {a : ℕ} (ha : a ∈ f.factors) :
    a = p ^ (a.factorization p) := by
  have hdvd : a ∣ p ^ k := by
    rw [← f.prod_eq]
    exact List.dvd_prod ha
  obtain ⟨b, _hbk, rfl⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  rw [Nat.factorization_pow_self hp]

/-- Map a prime-power ordered factorization to the composition of its prime exponents. -/
def toPrimeComposition {p k : ℕ} (hp : p.Prime) (f : OrderedFactorization (p ^ k)) :
    Composition k where
  blocks := f.factors.map fun a => a.factorization p
  blocks_pos := by
    intro b hb
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb
    by_contra hzero
    have hfactor := f.factor_eq_prime_pow hp ha
    rw [Nat.eq_zero_of_not_pos hzero, pow_zero] at hfactor
    have hge := f.factor_ge_two a ha
    omega
  blocks_sum := by
    have hnz : ∀ a ∈ f.factors, a ≠ 0 := by
      intro a ha
      exact Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_two (f.factor_ge_two a ha))
    rw [← factorization_prod_apply p f.factors hnz, f.prod_eq]
    exact Nat.factorization_pow_self hp

/-- A composition of a positive exponent gives an ordered factorization of the prime power. -/
def ofPrimeComposition {p k : ℕ} (hp : p.Prime) (hk : 0 < k) (c : Composition k) :
    OrderedFactorization (p ^ k) where
  factors := c.blocks.map fun b => p ^ b
  nonempty := by
    intro hnil
    have hblocks : c.blocks = [] := List.map_eq_nil_iff.mp hnil
    have := c.blocks_sum
    rw [hblocks] at this
    simp at this
    omega
  factor_ge_two := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    exact hp.two_le.trans (Nat.le_pow (c.blocks_pos hb))
  prod_eq := by
    rw [prod_map_pow, c.blocks_sum]

/-- Prime-power factorizations and positive compositions are mutually inverse. -/
def primePowerEquivComposition {p k : ℕ} (hp : p.Prime) (hk : 0 < k) :
    OrderedFactorization (p ^ k) ≃ Composition k where
  toFun := toPrimeComposition hp
  invFun := ofPrimeComposition hp hk
  left_inv := by
    intro f
    apply OrderedFactorization.ext
    simp only [ofPrimeComposition, toPrimeComposition]
    rw [List.map_map]
    have hmap : List.map (fun a => p ^ (a.factorization p)) f.factors =
        List.map id f.factors := by
      exact List.map_congr_left fun a ha => (f.factor_eq_prime_pow hp ha).symm
    change List.map (fun a => p ^ (a.factorization p)) f.factors = f.factors
    simpa only [List.map_id_fun, id_eq] using hmap
  right_inv := by
    intro c
    apply Composition.ext
    simp only [toPrimeComposition, ofPrimeComposition, List.map_map]
    have hmap : List.map (fun b => (p ^ b).factorization p) c.blocks =
        List.map id c.blocks := by
      exact List.map_congr_left fun _b _hb => Nat.factorization_pow_self hp
    change List.map (fun b => (p ^ b).factorization p) c.blocks = c.blocks
    simpa only [List.map_id_fun, id_eq] using hmap

/-- Exact prime-power Airy-tower count. -/
theorem card_primePower (p k : ℕ) (hp : p.Prime) (hk : 0 < k) :
    Nat.card (OrderedFactorization (p ^ k)) = 2 ^ (k - 1) := by
  rw [Nat.card_congr (primePowerEquivComposition hp hk)]
  rw [Nat.card_eq_fintype_card]
  exact composition_card k

end OrderedFactorization

end IrregularStokes
end GaloisForLFunctions
