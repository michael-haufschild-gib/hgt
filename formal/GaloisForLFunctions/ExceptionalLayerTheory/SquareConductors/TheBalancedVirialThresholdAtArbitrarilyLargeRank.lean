import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheWalshSpectrumOfAOneExchangeMidpoint
import Mathlib.NumberTheory.Bertrand
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# The virial threshold on balanced composites of arbitrarily large rank

For any composite cofactor with at least two distinct prime factors, every
prime strictly between half the cofactor and the cofactor gives a distinct
one-exchange midpoint. Bertrand's theorem supplies such a prime at every
cofactor. At odd ranks tending to infinity these balanced examples recover
the same sharp coupling as a single prime block.
-/

open Finset Filter Topology
noncomputable section
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

private theorem twice_proper_divisor {a m : ℕ} (hlt : a < m) (hd : a∣m) : 2*a ≤ m := by
  obtain ⟨c,rfl⟩ := hd
  have hc : 2≤c := by
    by_contra! h
    interval_cases c <;> simp_all
  simpa only [Nat.mul_comm a 2] using Nat.mul_le_mul_left a hc

private theorem cofactor_not_prime {m : ℕ} (hm : 2 ≤ m.primeFactors.card) : ¬m.Prime := by
  intro h
  simpa only [h.primeFactors,card_singleton] using hm

/-- A prime in the upper half of a composite cofactor is the unique
largest prime of the resulting midpoint integer. -/
theorem upper_half_prime_is_largest {m p : ℕ} (hm : 2 ≤ m.primeFactors.card)
    (hp : p.Prime) (h₁ : p < m) (h₂ : m<2*p) :
    p ∈ (p*m).primeFactors ∧ ∀ q ∈ (p*m).primeFactors, q≤p := by
  have factors := Nat.primeFactors_mul hp.ne_zero (by omega : m≠0)
  rw [factors,hp.primeFactors,singleton_union]
  refine ⟨mem_insert_self ..,fun q hq => ?_⟩
  rcases mem_insert.mp hq with rfl|hq
  · rfl
  have hd := (Nat.mem_primeFactors.mp hq).2.1
  have hlt : q < m := (Nat.le_of_dvd (by omega) hd).lt_of_ne (fun h =>
    cofactor_not_prime hm (h ▸ Nat.prime_of_mem_primeFactors hq))
  have h := twice_proper_divisor hlt hd
  omega

/-- Different prime and cofactor pairs from these half intervals give
different integers, even when the intervals overlap. -/
theorem upper_half_prime_completion_injective {m n p q : ℕ}
    (hm : 2 ≤ m.primeFactors.card) (hn : 2≤n.primeFactors.card)
    (hp : p.Prime) (hq : q.Prime) (hp₁ : p < m) (hp₂ : m<2*p)
    (hq₁ : q<n) (hq₂ : n<2*q) (he : p*m=q*n) : p=q ∧ m=n := by
  obtain ⟨hpP,hpmax⟩ := upper_half_prime_is_largest hm hp hp₁ hp₂
  obtain ⟨hqP,hqmax⟩ := upper_half_prime_is_largest hn hq hq₁ hq₂
  rw [he] at hpP hpmax
  obtain rfl := le_antisymm (hqmax p hpP) (hpmax q hqP)
  exact ⟨rfl,Nat.eq_of_mul_eq_mul_left hp.pos he⟩

private theorem upper_half_completion_data {m p : ℕ} (hp : p.Prime) (h₁ : p < m) (h₂ : m<2*p) :
    let k := p*m
    p ∈ k.primeFactors ∧ k.primeFactors.erase p = m.primeFactors ∧
      k.primeFactors.card=m.primeFactors.card+1 ∧
      (p^k.factorization p)^2<k ∧ k<(2*p^k.factorization p)^2 := by
  intro k
  have hn : ¬ p∣m := fun hd => h₂.not_ge (twice_proper_divisor h₁ hd)
  have hnot : p∉m.primeFactors := fun h => hn (Nat.dvd_of_mem_primeFactors h)
  have hm : m≠0 := by omega
  have hf : k.primeFactors=insert p m.primeFactors := by
    rw [show k=p*m from rfl,Nat.primeFactors_mul hp.ne_zero hm,hp.primeFactors,singleton_union]
  have he : k.factorization p=1 := by
    rw [show k=p*m from rfl,Nat.factorization_mul hp.ne_zero hm,Finsupp.add_apply,
      hp.factorization_self,Nat.factorization_eq_zero_of_not_dvd hn,add_zero]
  rw [hf,erase_insert hnot,card_insert_of_notMem hnot,he,pow_one]
  refine ⟨mem_insert_self ..,rfl,rfl,?_,?_⟩
  · rw [pow_two]
    exact Nat.mul_lt_mul_of_pos_left h₁ hp.pos
  · calc k < p*(2*p) := Nat.mul_lt_mul_of_pos_left h₂ hp.pos
         _ ≤ (2*p)^2 := by nlinarith only [Nat.zero_le (p*p)]

/-- Every prime in the upper cofactor half produces the universal negative
price when the cofactor has a positive even number of prime factors. -/
theorem upper_half_prime_completion_price {m p : ℕ} (hr : 2 ≤ m.primeFactors.card)
    (he : Even m.primeFactors.card) (hp : p.Prime) (h₁ : p < m) (h₂ : m<2*p) :
    unitaryHalfWeight (p*m) = -2 := by
  obtain ⟨hp',hB,_,hl,hu⟩ := upper_half_completion_data hp h₁ h₂
  exact unitary_half_weight_one_exchange hp' hl hu (hB ▸ he)
    (hB ▸ card_pos.mp (by omega : 0 < m.primeFactors.card))

private theorem upper_half_prime_exists {m : ℕ} (hm : 2 ≤ m.primeFactors.card) :
    ∃ p : ℕ, p.Prime ∧ p < m ∧ m<2*p := by
  have hm' : 1 < m := Nat.nonempty_primeFactors.mp (card_pos.mp (by omega))
  obtain ⟨p,hp,hl,hu⟩ := Nat.exists_prime_lt_and_le_two_mul (m/2) (by omega)
  have hne : p≠m := fun h => cofactor_not_prime hm (h ▸ hp)
  exact ⟨p,hp,by omega,by omega⟩

private theorem upper_half_at_odd_rank (j : ℕ) :
    ∃ k p : ℕ, k.primeFactors.card=2*j+5 ∧ p∈k.primeFactors ∧
      (p^k.factorization p)^2<k ∧ k<(2*p^k.factorization p)^2 ∧
      (∀ q∈k.primeFactors, (q^k.factorization q)^2<k) ∧ unitaryHalfWeight k = -2 := by
  obtain ⟨s,hs,_,_⟩ := balanced_minus_two_at_every_odd_rank (j+1)
  obtain ⟨S,hS,hc⟩ := exists_subset_card_eq (by omega : 2*j+4≤s.primeFactors.card)
  let m := ∏ q ∈ S, q
  have hm : m.primeFactors=S := Nat.primeFactors_prod (fun _ hq => Nat.prime_of_mem_primeFactors (hS hq))
  have hr : m.primeFactors.card=2*j+4 := hm ▸ hc
  obtain ⟨p,hp,h₁,h₂⟩ := upper_half_prime_exists (by omega : 2 ≤ m.primeFactors.card)
  let k := p*m
  obtain ⟨hpk,_,hcard,hl,hu⟩ := upper_half_completion_data hp h₁ h₂
  have hneg : unitaryHalfWeight k = -2 :=
    upper_half_prime_completion_price (by omega) ⟨j+2,by omega⟩ hp h₁ h₂
  refine ⟨k,p,by change (p*m).primeFactors.card=_; omega,hpk,hl,hu,?_,hneg⟩
  intro q hq
  obtain ⟨hqp,hqd,hk⟩ := Nat.mem_primeFactors.mp hq
  rcases lt_trichotomy ((q^k.factorization q)^2) k with h|h|h
  · exact h
  · have hh := congrArg (fun n : ℕ => n.factorization q) h
    rw [←pow_mul,Nat.factorization_pow_self hqp] at hh
    have := hqp.factorization_pos_of_dvd hk hqd
    omega
  · have hh := unitary_half_weight_dominant (Nat.nonempty_primeFactors.mp ⟨q,hq⟩) hq h
    rw [hneg] at hh
    split_ifs at hh

private def normalizedExchange (γ : ℝ) (r : ℕ) : ℝ :=
  30*γ-3+8*(γ*((r:ℝ)^3+7*r^2+7*r-30)-r^2-r+4)/2^r

private theorem exchange_limit (γ : ℝ) :
    Tendsto (normalizedExchange γ) atTop (𝓝 (30*γ-3)) := by
  have mono (j : ℕ) := tendsto_pow_const_div_const_pow_of_one_lt j (by norm_num : (1:ℝ)<2)
  have h := (((mono 3).const_mul (8*γ)).add ((mono 2).const_mul (56*γ-8))).add
    (((mono 1).const_mul (56*γ-8)).add ((mono 0).const_mul (32-240*γ)))
  have ht := h.const_add (30*γ-3)
  simp only [mul_zero,add_zero] at ht
  apply ht.congr
  intro r
  simp only [normalizedExchange,pow_one,pow_zero,div_eq_mul_inv]
  ring

/-- Even after imposing balance, a prescribed lower rank, and price minus
two, every subcritical coupling produces a negative arithmetic energy. -/
theorem balanced_high_rank_virial_threshold (γ : ℝ) (R : ℕ) :
    (∀ k : ℕ, R≤k.primeFactors.card → Odd k.primeFactors.card →
      (∀ q∈k.primeFactors, (q^k.factorization q)^2<k) → unitaryHalfWeight k = -2 →
      0≤unitaryVirialEnergy γ k) ↔ 1/10≤γ := by
  constructor
  · intro h
    by_contra! hc
    have negative := (exchange_limit γ).eventually_lt_const (by linarith only [hc] : 30*γ-3<0)
    obtain ⟨N,hN⟩ := eventually_atTop.mp negative
    obtain ⟨k,p,hr,hp,hl,hu,hb,hm⟩ := upper_half_at_odd_rank (N+R)
    let r := k.primeFactors.card
    have he := one_exchange_virial_closed_form hp hl hu (by omega) γ
    have hbad := hN r (by dsimp only [r]; omega)
    have hgood := h k (by omega) ⟨N+R+2,by omega⟩ hb hm
    have hn : unitaryVirialEnergy γ k = ((2:ℝ)^r)^2*normalizedExchange γ r := by
      rw [he]
      change (2:ℝ)^(2*r)*(30*γ-3)+_ = _
      rw [Nat.mul_comm 2 r,pow_mul]
      unfold normalizedExchange
      field_simp
      ring
    rw [hn] at hgood
    exact (mul_neg_of_pos_of_neg (by positivity : 0<((2:ℝ)^r)^2) hbad).not_ge hgood
  · exact fun h k _ _ _ _ => (unitaryVirialEnergy_nonneg_iff γ).mpr h k

#print axioms upper_half_prime_completion_injective
#print axioms upper_half_prime_completion_price
#print axioms balanced_high_rank_virial_threshold
end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
