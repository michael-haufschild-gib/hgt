import GaloisForLFunctions.RHTower.Sieve.OmegaMGF

/-!
# The smallest prime factors form a small divisor

If `T` consists of the smallest elements of a finite set `S` of naturals, then the geometric mean
of `T` is at most the geometric mean of `S`, in the integral form

`(∏_{p ∈ T} p) ^ #S ≤ (∏_{p ∈ S} p) ^ #T`.

Applied to `S = ` the prime factors of `n` exceeding a cut and `T = ` the `J` smallest of them,
this says that once `n` has at least `c · J` such prime factors, the product of the `J` smallest is
at most `n ^ (1/c)`.  That is the device which keeps the divisor range small enough for the
one-unit-per-divisor sieve error to be summable, and hence lets the large-prime part of the
distinct prime count be transferred at no cost in the exponent.
-/

namespace RHTower.Sieve

open Finset Nat

/-- **Integral geometric-mean inequality.**  If every element of `T` is at most every element of
`S \ T`, the product over `T` is smaller in the geometric-mean sense. -/
theorem prod_pow_card_le_prod_pow_card {S T : Finset ℕ} (hTS : T ⊆ S)
    (hle : ∀ p ∈ T, ∀ q ∈ S \ T, p ≤ q) :
    (∏ p ∈ T, p) ^ S.card ≤ (∏ p ∈ S, p) ^ T.card := by
  classical
  have hcard : (S \ T).card + T.card = S.card := Finset.card_sdiff_add_card_eq_card hTS
  have hkey : (∏ p ∈ T, p) ^ (S \ T).card ≤ (∏ q ∈ S \ T, q) ^ T.card := by
    have hleft : (∏ p ∈ T, p) ^ (S \ T).card = ∏ _q ∈ S \ T, ∏ p ∈ T, p := by
      rw [Finset.prod_const]
    have hright : (∏ q ∈ S \ T, q) ^ T.card = ∏ q ∈ S \ T, q ^ T.card := by
      rw [Finset.prod_pow]
    rw [hleft, hright]
    refine Finset.prod_le_prod' ?_
    intro q hq
    calc ∏ p ∈ T, p ≤ ∏ _p ∈ T, q := Finset.prod_le_prod' fun p hp => hle p hp q hq
      _ = q ^ T.card := by rw [Finset.prod_const]
  calc (∏ p ∈ T, p) ^ S.card
      = (∏ p ∈ T, p) ^ T.card * (∏ p ∈ T, p) ^ (S \ T).card := by
        rw [← pow_add, ← hcard]
        ring_nf
    _ ≤ (∏ p ∈ T, p) ^ T.card * (∏ q ∈ S \ T, q) ^ T.card :=
        Nat.mul_le_mul le_rfl hkey
    _ = ((∏ q ∈ S \ T, q) * ∏ p ∈ T, p) ^ T.card := by
        rw [← mul_pow]
        ring_nf
    _ = (∏ p ∈ S, p) ^ T.card := by rw [Finset.prod_sdiff hTS]

/-- **Small-divisor extraction.**  If `S` has at least `c` times as many elements as `T`, and `T`
consists of the smallest of them, the product over `T` has its `c`-th power bounded by any bound on
the product over `S`. -/
theorem pow_prod_le_of_card_mul_le {S T : Finset ℕ} (hTS : T ⊆ S)
    (hle : ∀ p ∈ T, ∀ q ∈ S \ T, p ≤ q) (hSpos : ∀ p ∈ S, 0 < p) (hT : T.Nonempty) {c n : ℕ}
    (hc : c * T.card ≤ S.card) (hn : (∏ p ∈ S, p) ≤ n) :
    (∏ p ∈ T, p) ^ c ≤ n := by
  classical
  have hTcard : T.card ≠ 0 := Finset.card_ne_zero_of_mem hT.choose_spec
  have hstep : ((∏ p ∈ T, p) ^ c) ^ T.card ≤ n ^ T.card := by
    calc ((∏ p ∈ T, p) ^ c) ^ T.card = (∏ p ∈ T, p) ^ (c * T.card) := by rw [← pow_mul]
      _ ≤ (∏ p ∈ T, p) ^ S.card := by
          refine Nat.pow_le_pow_right ?_ hc
          exact Finset.prod_pos fun p hp => hSpos p (hTS hp)
      _ ≤ (∏ p ∈ S, p) ^ T.card := prod_pow_card_le_prod_pow_card hTS hle
      _ ≤ n ^ T.card := Nat.pow_le_pow_left hn _
  exact (Nat.pow_le_pow_iff_left hTcard).1 hstep

end RHTower.Sieve
