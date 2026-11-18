import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheCompleteUpperProductTail
import GaloisForLFunctions.ExceptionalLayerTheory.TheInnerWeightOnLargePrimeMultiples

/-!
# Divisor inversion at a sharp product boundary

The first primes at a fixed product have identical inner jump. Their mass is
the complete divisor logarithm less four disjoint omissions. Throughout a
terminal block with product above the square-root cutoff, at most two primes
can enter as the cofactor cap grows.
-/

noncomputable section
open Finset ArithmeticFunction
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- Ordinary first primes of product q whose complementary factor passes the cap. -/
def productFirstPrimes (b q : ℕ) : Finset ℕ :=
  q.divisors.filter fun p => p.Prime ∧ 4 < p ∧ p.Coprime (q / p) ∧ q / p ≤ b

/-- The inner jump common to all admissible first primes. -/
def productInnerWeight (q : ℕ) : ℝ :=
  innerJump 1 q + if q.Prime then 1 else 0

private theorem firstPrime_inner {p v : ℕ} (hp : p.Prime) (hp4 : 4 < p) (hv : 0 < v) :
    innerJump 1 v = productInnerWeight (p * v) := by
  have he : (p * v).Prime ↔ v = 1 := by
    constructor
    · intro h
      have hh := (Nat.prime_dvd_prime_iff_eq hp h).mp (dvd_mul_right p v)
      exact Nat.eq_of_mul_eq_mul_left hp.pos (by simpa only [Nat.mul_one] using hh.symm :
        p * v = p * 1)
    · rintro rfl
      simpa only [Nat.mul_one] using hp
  simp only [productInnerWeight, innerJump_prime_multiple le_rfl hp hp4 hv, he, sub_add_cancel]

/-- The four complementary divisor masses use disjoint predicates. The nonprime
mass is supported on proper powers by the definition of the Mangoldt function. -/
def omittedProductLog (b q : ℕ) : ℝ :=
  (∑ d ∈ q.divisors with ¬ d.Prime, vonMangoldt d) +
  (∑ d ∈ q.divisors with d.Prime ∧ d ≤ 4, vonMangoldt d) +
  (∑ d ∈ q.divisors with d.Prime ∧ 4 < d ∧ ¬ d.Coprime (q / d), vonMangoldt d) +
  (∑ d ∈ q.divisors with d.Prime ∧ 4 < d ∧ d.Coprime (q / d) ∧ b < q / d, vonMangoldt d)

/-- Exact divisor completion with the original upper cofactor cap. -/
theorem productFirstPrimes_log (b q : ℕ) :
    (∑ p ∈ productFirstPrimes b q, vonMangoldt p) = Real.log q - omittedProductLog b q := by
  apply eq_sub_iff_add_eq.mpr
  rw [← vonMangoldt_sum, omittedProductLog, productFirstPrimes]
  simp only [sum_filter, ← sum_add_distrib]
  apply sum_congr rfl
  intro d _
  by_cases h : d.Prime
  · by_cases hs : 4 < d
    · by_cases hc : d.Coprime (q / d)
      · by_cases hb : q / d ≤ b <;> simp [h, hs, hc, hb, Nat.not_le_of_lt hs, lt_iff_not_ge]
      · simp [h, hs, hc, Nat.not_le_of_lt hs]
    · simp [h, hs, le_of_not_gt hs]
  · simp [h]

private theorem slice_over_products {p : ℕ} (hp : p.Prime) (hp4 : 4 < p) (k Y b : ℕ) (f : ℕ → ℝ) :
    (∑ v ∈ Ioc (Y/p) (min (k/p) b) with p.Coprime v, innerJump 1 v * f (p*v)) =
      ∑ q ∈ Ioc Y k with p ∣ q,
        if p.Coprime (q / p) ∧ q / p ≤ b then
          productInnerWeight q * f q else 0 := by
  rw [sum_divisible_Ioc hp.pos]
  simp only [Nat.mul_div_cancel_left _ hp.pos, ← sum_filter]
  apply sum_congr _ fun v hv => ?_
  · ext v
    simp only [mem_filter, mem_Ioc, le_min_iff]
    tauto
  · have hv0 : 0 < v := (Nat.zero_le (Y/p)).trans_lt (mem_Ioc.mp (mem_filter.mp hv).1).1
    rw [firstPrime_inner hp hp4 hv0]

/-- Reindex the actual row by product. Both the moving lower horizon and the
cofactor cap can be chosen independently at every conductor. -/
theorem capped_product_divisor_sum (k Y b : ℕ) (f : ℕ → ℝ) :
    (ordinaryFactorTail 4 k fun p => ∑ v ∈ Ioc (Y/p) (min (k/p) b) with p.Coprime v,
      innerJump 1 v * f (p*v)) =
      ∑ q ∈ Ioc Y k, productInnerWeight q * (Real.log q - omittedProductLog b q) * f q := by
  unfold ordinaryFactorTail
  let P := (Ioc 4 k).filter Nat.Prime
  let w := fun q => productInnerWeight q * f q
  have hs (p : ℕ) (hp : p ∈ P) :
      vonMangoldt p * (∑ v ∈ Ioc (Y/p) (min (k/p) b) with p.Coprime v, innerJump 1 v * f (p*v)) =
        ∑ q ∈ Ioc Y k, if p ∣ q ∧ p.Coprime (q/p) ∧ q/p ≤ b then vonMangoldt p * w q else 0 := by
    rw [slice_over_products (mem_filter.mp hp).2 (mem_Ioc.mp (mem_filter.mp hp).1).1, sum_filter, mul_sum]
    apply sum_congr rfl
    intro q _
    by_cases hd : p ∣ q <;> by_cases hc : p.Coprime (q/p) ∧ q/p ≤ b <;> simp [hd, hc, w]
  rw [sum_congr rfl hs, sum_comm]
  apply sum_congr rfl
  intro q hq
  have h0 := (Nat.zero_le Y).trans_lt (mem_Ioc.mp hq).1
  have he : P.filter (fun p => p ∣ q ∧ p.Coprime (q/p) ∧ q/p ≤ b) = productFirstPrimes b q := by
    ext p
    simp only [P, productFirstPrimes, mem_filter, mem_Ioc, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨⟨h4, _⟩, hp⟩, hd, hc, hb⟩
      exact ⟨⟨hd, h0.ne'⟩, hp, h4, hc, hb⟩
    · rintro ⟨⟨hd, _⟩, hp, h4, hc, hb⟩
      exact ⟨⟨⟨h4, (Nat.le_of_dvd h0 hd).trans (mem_Ioc.mp hq).2⟩, hp⟩, hd, hc, hb⟩
  rw [← sum_filter, he, ← sum_mul, productFirstPrimes_log]
  dsimp only [w]
  ring

/-- The original quotient weight at both sharp cutoffs. -/
theorem capped_row_divisor_inversion (k Y b : ℕ) :
    ordinaryFactorTail 4 k (cappedCoprimeSlice 1 1 k Y b) =
      ∑ q ∈ Ioc Y k, productInnerWeight q * (Real.log q - omittedProductLog b q) *
        centeredPrimeWeight 1 (k / q) := by
  change (ordinaryFactorTail 4 k fun p => ∑ v ∈ Ioc (Y/p) (min (k/p) b) with p.Coprime v,
    innerJump 1 v * centeredPrimeWeight 1 (k/p/v)) = _
  simpa only [Nat.div_div_eq_div_mul] using capped_product_divisor_sum k Y b (fun q => centeredPrimeWeight 1 (k / q))

/-- The divisor expansion on the original spline, including every horizon. -/
theorem capped_spline_divisor_inversion (U b n : ℕ) :
    cappedUpperProductReading U b n =
      splineCountReading n (fun k => ∑ q ∈ Ioc (max (productLower 1 k) U) k,
        productInnerWeight q * (Real.log q - omittedProductLog b q) *
          centeredPrimeWeight 1 (k / q)) := by
  simp only [cappedUpperProductReading, capped_row_divisor_inversion]

private theorem firstPrime_product {p b q : ℕ} (hp : p ∈ productFirstPrimes b q) :
    p * (q / p) = q := by
  rw [Nat.mul_comm, Nat.div_mul_cancel (Nat.mem_divisors.mp (mem_filter.mp hp).1).1]

private theorem cofactor_contains_other {p r b q : ℕ} (hp : p ∈ productFirstPrimes b q)
    (hr : r ∈ productFirstPrimes b q) (hne : r ≠ p) : r ∣ q / p := by
  have hd := (Nat.mem_divisors.mp (mem_filter.mp hr).1).1
  rw [← firstPrime_product hp] at hd
  exact ((mem_filter.mp hr).2.1.dvd_mul.mp hd).resolve_left fun h =>
    hne ((Nat.prime_dvd_prime_iff_eq (mem_filter.mp hr).2.1 (mem_filter.mp hp).2.1).mp h)

private theorem firstPrime_large {p b q : ℕ} (h : b * b.sqrt < q)
    (hp : p ∈ productFirstPrimes b q) : b.sqrt < p := by
  by_contra! hle
  have hh := Nat.mul_le_mul hle (mem_filter.mp hp).2.2.2.2
  rw [firstPrime_product hp, Nat.mul_comm b.sqrt b] at hh
  exact h.not_ge hh

/-- Only two cofactor entries can occur, even when the fixed product is below b². -/
theorem productFirstPrimes_card {b q : ℕ} (h : b * b.sqrt < q) :
    (productFirstPrimes b q).card ≤ 2 := by
  by_contra! hh
  obtain ⟨p,r,s,hp,hr,hs,hpr,hps,hrs⟩ := two_lt_card_iff.mp hh
  have hcop := (Nat.coprime_primes (mem_filter.mp hr).2.1 (mem_filter.mp hs).2.1).mpr hrs
  have hd := hcop.mul_dvd_of_dvd_of_dvd (cofactor_contains_other hp hr hpr.symm)
    (cofactor_contains_other hp hs hps.symm)
  have hv : 0 < q / p := Nat.div_pos (Nat.le_of_dvd ((Nat.zero_le _).trans_lt h)
    (Nat.mem_divisors.mp (mem_filter.mp hp).1).1) (mem_filter.mp hp).2.1.pos
  have hu := (Nat.le_of_dvd hv hd).trans (mem_filter.mp hp).2.2.2.2
  have hl := Nat.mul_le_mul (firstPrime_large h hr : b.sqrt + 1 ≤ r)
    (firstPrime_large h hs : b.sqrt + 1 ≤ s)
  have hsq := Nat.sqrt_lt'.mp (Nat.lt_succ_self b.sqrt)
  exact hsq.not_ge (by simpa only [sq] using hl.trans hu)

/-- If two primes enter, the remaining integer t satisfies q t ≤ b². -/
theorem productFirstPrimes_two_cofactor {p r b q : ℕ} (hp : p ∈ productFirstPrimes b q)
    (hr : r ∈ productFirstPrimes b q) (hne : r ≠ p) :
    ∃ t : ℕ, q = p*r*t ∧ r*t ≤ b ∧ p*t ≤ b ∧ q*t ≤ b^2 := by
  obtain ⟨t, ht⟩ := cofactor_contains_other hp hr hne
  have hq : q = p*r*t := calc
    q = p*(q/p) := (firstPrime_product hp).symm
    _ = p*r*t := by rw [ht, Nat.mul_assoc]
  have hleft : r*t ≤ b := ht ▸ (mem_filter.mp hp).2.2.2.2
  have hrq : q / r = p*t := by
    rw [hq, show p*r*t = r*(p*t) by ring, Nat.mul_div_cancel_left _ (mem_filter.mp hr).2.1.pos]
  have hright : p*t ≤ b := hrq ▸ (mem_filter.mp hr).2.2.2.2
  exact ⟨t,hq,hleft,hright,by
    rw [hq, sq, show p*r*t*t = (r*t)*(p*t) by ring]
    exact Nat.mul_le_mul hleft hright⟩

/-- Inside any terminal block ending at b, the prime mass changes only at
the at most two thresholds q/p. -/
theorem productFirstPrimes_entries {b q : ℕ} (h : b*b.sqrt < q) :
    ∃ S : Finset ℕ, S.card ≤ 2 ∧ ∀ n ≤ b,
      productFirstPrimes n q = S.filter (fun p => q/p ≤ n) := by
  refine ⟨productFirstPrimes b q, productFirstPrimes_card h, fun n hn => ?_⟩
  ext p
  simp only [productFirstPrimes, mem_filter]
  exact ⟨fun ⟨hd,hp,h4,hc,hv⟩ => ⟨⟨hd,hp,h4,hc,hv.trans hn⟩,hv⟩,
    fun ⟨⟨hd,hp,h4,hc,_⟩,hv⟩ => ⟨hd,hp,h4,hc,hv⟩⟩

/-- Above the power cutoff n^α, two admissible first primes leave a third
factor strictly below n^(2-α), including the floor endpoint. -/
theorem two_first_primes_above_power {p r n q : ℕ} {α : ℝ} (hn : 0 < n)
    (hcut : ⌊(n:ℝ)^α⌋₊ < q) (hp : p ∈ productFirstPrimes n q)
    (hr : r ∈ productFirstPrimes n q) (hne : r ≠ p) :
    ∃ t : ℕ, q = p*r*t ∧ (t:ℝ) < (n:ℝ)^(2-α) := by
  obtain ⟨t,hq,_,_,ht⟩ := productFirstPrimes_two_cofactor hp hr hne
  have hn' : (0:ℝ) < n := Nat.cast_pos.mpr hn
  have hpow := Real.rpow_pos_of_pos hn' α
  have hlarge := (Nat.floor_lt hpow.le).mp hcut
  have hpos : 0 < t := by
    by_contra! h
    have := Nat.eq_zero_of_le_zero h
    simp [this] at hq
    omega
  have hprod : (n:ℝ)^α * t < (n:ℝ)^2 :=
    (mul_lt_mul_of_pos_right hlarge (Nat.cast_pos.mpr hpos)).trans_le (by exact_mod_cast ht)
  have he : (n:ℝ)^α * (n:ℝ)^(2-α) = (n:ℝ)^2 := by
    rw [← Real.rpow_add hn', show α + (2 - α) = 2 by ring, Real.rpow_two]
  rw [← he] at hprod
  exact ⟨t,hq, (mul_lt_mul_iff_right₀ hpow).mp hprod⟩

private theorem quotient_cell_sum {q j a d : ℕ} (hq : 0 < q) (had : a ≤ d)
    (ha : j*q ≤ a) (hd : d ≤ (j+1)*q) (w : ℕ → ℝ) :
    (∑ k ∈ Ico a d, centeredPrimeWeight 1 (k/q) * (w k - w (k+1))) =
      centeredPrimeWeight 1 j * (w a - w d) := by
  have he (k : ℕ) (hk : k ∈ Ico a d) : k/q = j := by
    obtain ⟨hl,hu⟩ := mem_Ico.mp hk
    exact le_antisymm (Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul hq).mpr (hu.trans_le hd)))
      ((Nat.le_div_iff_mul_le hq).mpr (ha.trans hl))
  have telescope (b : ℕ) (hab : a ≤ b) : ∑ k ∈ Ico a b, (w k - w (k+1)) = w a - w b := by
    induction b, hab using Nat.le_induction with
    | base => simp
    | succ b hab ih => rw [sum_Ico_succ_top hab, ih]; ring
  calc _ = ∑ k ∈ Ico a d, centeredPrimeWeight 1 j * (w k - w (k+1)) :=
           sum_congr rfl fun k hk => by rw [he k hk]
       _ = _ := by rw [← mul_sum, telescope d had]

/-- Two adjacent quotient cells at a fixed product. The common sample has the
jump of the quotient weight. The first and last samples retain their signs. -/
theorem adjacent_product_cells {q j a d : ℕ} (hq : 0 < q)
    (ha : j*q ≤ a) (hac : a ≤ (j+1)*q) (hcd : (j+1)*q ≤ d)
    (hd : d ≤ (j+2)*q) (n : ℕ) :
    (∑ k ∈ Ico a ((j+1)*q), centeredPrimeWeight 1 (k/q) *
      (sampledSpline n k - sampledSpline n (k+1))) +
    (∑ k ∈ Ico ((j+1)*q) d, centeredPrimeWeight 1 (k/q) *
      (sampledSpline n k - sampledSpline n (k+1))) =
    centeredPrimeWeight 1 j * sampledSpline n a +
      (centeredPrimeWeight 1 (j+1) - centeredPrimeWeight 1 j) * sampledSpline n ((j+1)*q) -
      centeredPrimeWeight 1 (j+1) * sampledSpline n d := by
  rw [quotient_cell_sum hq hac ha le_rfl, quotient_cell_sum hq hcd le_rfl hd]
  ring

#print axioms adjacent_product_cells
#print axioms capped_spline_divisor_inversion
#print axioms two_first_primes_above_power
#print axioms productFirstPrimes_two_cofactor
#print axioms productFirstPrimes_entries
end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
