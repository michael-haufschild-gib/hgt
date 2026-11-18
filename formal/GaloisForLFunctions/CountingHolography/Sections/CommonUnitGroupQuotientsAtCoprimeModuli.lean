import Mathlib.Data.Nat.Totient
import Mathlib.GroupTheory.Index
import Mathlib.NumberTheory.ArithmeticFunction.Carmichael
import Mathlib.Tactic

/-! # Common unit group quotients at coprime moduli

Prime powers in a modulus contribute their own prime to the principal
unit group. For coprime moduli those two contributions are coprime.
Thus every common quotient order divides the product of the residue
field unit orders. Passing from the modulus to its full unit count
loses at most a factor equal to the largest permitted prime.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections

open Finset

/-- Product of the unit orders of the residue fields at the distinct primes of u. -/
def residueUnitOrder (u : ℕ) : ℕ := ∏ p ∈ u.primeFactors, (p-1)

private def primePowerPart (u : ℕ) := u / ∏ p ∈ u.primeFactors, p

private theorem primePowerPart_dvd (u : ℕ) : primePowerPart u ∣ u :=
  ⟨_,(Nat.div_mul_cancel (Nat.prod_primeFactors_dvd u)).symm⟩

private theorem totient_split (u : ℕ) : u.totient=primePowerPart u*residueUnitOrder u :=
  Nat.totient_eq_div_primeFactors_mul u

/-- Coprime principal orders cannot increase a common divisor beyond
the product of the two residue orders. -/
theorem gcd_dvd_residue_product {a b : ℕ} (hc : a.Coprime b) (u v : ℕ) :
    (a*u).gcd (b*v) ∣ u*v := by
  let d := (a*u).gcd (b*v)
  have h₁ : d ∣ a*(u*v) := by
    simpa only [mul_assoc] using (Nat.gcd_dvd_left (a*u) (b*v)).trans (dvd_mul_right (a*u) v)
  have h₂ : d ∣ b*(u*v) := by
    simpa only [mul_assoc,mul_comm v u] using (Nat.gcd_dvd_right (a*u) (b*v)).trans (dvd_mul_right (b*v) u)
  have h := Nat.dvd_gcd h₁ h₂
  simpa only [Nat.gcd_mul_right,hc.gcd_eq_one,one_mul,mul_one] using h

/-- Every common divisor of the two totients is already paid for by
the distinct residue primes, with no dependence on their multiplicities. -/
theorem gcd_totient_dvd_residueUnitOrders {u v : ℕ} (hc : u.Coprime v) :
    u.totient.gcd v.totient ∣ residueUnitOrder u*residueUnitOrder v := by
  rw [totient_split u,totient_split v]
  exact gcd_dvd_residue_product (hc.of_dvd (primePowerPart_dvd u) (primePowerPart_dvd v)) _ _

private theorem totient_power_succ (u k : ℕ) : (u^(k+1)).totient=u^k*u.totient := by
  rw [Nat.totient_eq_div_primeFactors_mul (u^(k+1)),Nat.primeFactors_pow u (Nat.succ_ne_zero k),
    pow_succ,Nat.mul_div_assoc _ (Nat.prod_primeFactors_dvd u),Nat.totient_eq_div_primeFactors_mul u,mul_assoc]

private theorem power_totient_exponent {u : ℕ} (hu : 0<u) (k p : ℕ) :
    (u^(k+1)).totient.factorization p=k*u.factorization p+u.totient.factorization p := by
  rw [totient_power_succ,Nat.factorization_mul (pow_ne_zero _ hu.ne') (Nat.totient_pos.mpr hu).ne',
    Nat.factorization_pow,Finsupp.add_apply,Finsupp.smul_apply,smul_eq_mul]

/-- Once the powers exceed the opposite totient orders, every common
prime exponent stabilizes. At a prime of either modulus only the opposite
residue group can supply its exponent. Elsewhere the smaller exponent survives. -/
theorem saturated_gcd_unit_orders {u v i j p : ℕ} (hu : 0<u) (hv : 0<v) (hc : u.Coprime v)
    (hp : p.Prime) (hi : v.totient ≤ i) (hj : u.totient ≤ j) :
    (((u^(i+1)).totient.gcd (v^(j+1)).totient).factorization p)=
      if p∣u then v.totient.factorization p else if p∣v then u.totient.factorization p
      else min (u.totient.factorization p) (v.totient.factorization p) := by
  rw [Nat.factorization_gcd (Nat.totient_pos.mpr (pow_pos hu _)).ne' (Nat.totient_pos.mpr (pow_pos hv _)).ne']
  change min ((u^(i+1)).totient.factorization p) ((v^(j+1)).totient.factorization p)=_
  rw [power_totient_exponent hu,power_totient_exponent hv]
  have hval (m : ℕ) : m.factorization p≤m :=
    Nat.factorization_le_of_le_pow (Nat.lt_pow_self hp.one_lt).le
  by_cases hpu : p∣u
  · have hpv : ¬p∣v := fun h => hp.not_dvd_one (hc.gcd_eq_one ▸ Nat.dvd_gcd hpu h)
    rw [if_pos hpu,Nat.factorization_eq_zero_of_not_dvd hpv,mul_zero,zero_add,min_eq_right]
    exact ((hval _).trans hi).trans ((Nat.le_mul_of_pos_right i
      (hp.factorization_pos_of_dvd hu.ne' hpu)).trans (Nat.le_add_right _ _))
  rw [if_neg hpu,Nat.factorization_eq_zero_of_not_dvd hpu,mul_zero,zero_add]
  by_cases hpv : p∣v
  · rw [if_pos hpv,min_eq_left]
    exact ((hval _).trans hj).trans ((Nat.le_mul_of_pos_right j
      (hp.factorization_pos_of_dvd hv.ne' hpv)).trans (Nat.le_add_right _ _))
  rw [if_neg hpv,Nat.factorization_eq_zero_of_not_dvd hpv,mul_zero,zero_add]

/-- The order of the image of any homomorphism of the actual unit groups
divides the product of the residue field unit orders. -/
theorem unitHom_range_dvd_residueUnitOrders {u v : ℕ} (hu : 0<u) (hv : 0<v) (hc : u.Coprime v)
    (f : (ZMod u)ˣ →* (ZMod v)ˣ) :
    Nat.card f.range ∣ residueUnitOrder u*residueUnitOrder v := by
  letI : NeZero u := ⟨hu.ne'⟩
  letI : NeZero v := ⟨hv.ne'⟩
  have hU : Nat.card (ZMod u)ˣ=u.totient := by rw [Nat.card_eq_fintype_card,ZMod.card_units_eq_totient]
  have hV : Nat.card (ZMod v)ˣ=v.totient := by rw [Nat.card_eq_fintype_card,ZMod.card_units_eq_totient]
  exact (Nat.dvd_gcd (hU ▸ Subgroup.card_range_dvd f) (hV ▸ f.range.card_subgroup_dvd_card)).trans
    (gcd_totient_dvd_residueUnitOrders hc)

/-- Multiplying p/(p−1) over any subset of the integers from two through
L costs at most L. Filling in all missing factors gives a telescoping product. -/
private theorem prime_product_le_residue_product (S : Finset ℕ) {L : ℕ} (hL : 1≤L)
    (hS : S⊆Icc 2 L) : (∏ p ∈ S, p)≤L*∏ p ∈ S, (p-1) := by
  induction L, hL using Nat.le_induction generalizing S with
  | base =>
    have he : S=∅ := eq_empty_iff_forall_notMem.mpr fun p hp => by
      have hh := mem_Icc.mp (hS hp)
      omega
    simp [he]
  | succ m hm ih =>
    by_cases h : m+1∈S
    · let T := S.erase (m+1)
      have ht : T⊆Icc 2 m := by
        intro p hp
        obtain ⟨hne,hmem⟩ := mem_erase.mp hp
        obtain ⟨hlo,hhi⟩ := mem_Icc.mp (hS hmem)
        exact mem_Icc.mpr ⟨hlo,by omega⟩
      have he : S=insert (m+1) T := (insert_erase h).symm
      rw [he,prod_insert (notMem_erase _ _),prod_insert (notMem_erase _ _),Nat.add_sub_cancel]
      exact Nat.mul_le_mul_left _ (ih T ht)
    · have ht : S⊆Icc 2 m := by
        intro p hp
        obtain ⟨hlo,hhi⟩ := mem_Icc.mp (hS hp)
        exact mem_Icc.mpr ⟨hlo,by have hne : p≠m+1 := fun e => h (e ▸ hp); omega⟩
      exact (ih S ht).trans (Nat.mul_le_mul_right _ (Nat.le_succ m))

/-- The cardinality of the unit group of a positive integer with no
prime factor above L is within a factor L of that integer. -/
theorem le_cutoff_mul_totient {u L : ℕ} (hL : 1≤L)
    (hp : ∀ p ∈ u.primeFactors, p≤L) : u ≤ L*u.totient := by
  have hS (p : ℕ) (h : p∈u.primeFactors) := mem_Icc.mpr ⟨(Nat.prime_of_mem_primeFactors h).two_le,hp p h⟩
  have h := Nat.mul_le_mul_left (primePowerPart u) (prime_product_le_residue_product u.primeFactors hL hS)
  have he : primePowerPart u*(∏ p ∈ u.primeFactors,p)=u := Nat.div_mul_cancel (Nat.prod_primeFactors_dvd u)
  rw [he] at h
  rw [totient_split]
  exact h.trans_eq (by unfold residueUnitOrder; ring)

/-- The principal part of a prime-power modulus divides twice the
Carmichael exponent. The extra factor two occurs only at the prime two. -/
private theorem primePower_dvd_twice_carmichael {p : ℕ} (hp : p.Prime) (k : ℕ) :
    p^k ∣ 2*ArithmeticFunction.carmichael (p^(k+1)) := by
  by_cases h : p=2
  · subst p
    by_cases hsmall : k+1≤2
    · rw [ArithmeticFunction.carmichael_two_pow_of_le_two hsmall,Nat.add_sub_cancel]
      exact dvd_mul_left _ _
    · rw [ArithmeticFunction.two_mul_carmichael_two_pow_of_three_le_eq_totient (by omega),
        Nat.totient_prime_pow Nat.prime_two (Nat.succ_pos k)]
      simp
  · rw [ArithmeticFunction.carmichael_pow_of_prime_ne_two _ hp h,
      Nat.totient_prime_pow hp (Nat.succ_pos k)]
    exact (dvd_mul_right (p^k) _).trans (dvd_mul_left _ _)

/-- The modulus divides twice the product of its distinct primes times
the largest order of a unit. No estimate for the distribution of primes
in arithmetic progressions enters this bound. -/
theorem dvd_twice_radical_mul_carmichael {u : ℕ} (hu : 0<u) :
    u ∣ (∏ p ∈ u.primeFactors, p)*(2*ArithmeticFunction.carmichael u) := by
  apply (Nat.dvd_iff_prime_pow_dvd_dvd _ u).mpr
  intro p k hp hk
  cases k with
  | zero => simp
  | succ k =>
    have hpu : p ∣ u := (show p ∣ p^(k+1) by rw [pow_succ]; exact dvd_mul_left _ _).trans hk
    have hrad := dvd_prod_of_mem id (Nat.mem_primeFactors.mpr ⟨hp,hpu,hu.ne'⟩)
    have hpow := (primePower_dvd_twice_carmichael hp k).trans
      (Nat.mul_dvd_mul_left 2 (ArithmeticFunction.carmichael_dvd hk))
    rw [pow_succ']
    exact Nat.mul_dvd_mul hrad hpow

private theorem carmichael_dvd_mul_of_residue_orders_dvd {u L : ℕ} (hu : 0<u)
    (hL : ∀ p ∈ u.primeFactors, p-1 ∣ L) : ArithmeticFunction.carmichael u ∣ u*L := by
  letI : NeZero u := ⟨hu.ne'⟩
  rw [ArithmeticFunction.carmichael_factorization u,Finset.lcm_dvd_iff]
  intro p h
  have hp := Nat.prime_of_mem_primeFactors h
  have he := hp.factorization_pos_of_dvd hu.ne' (Nat.dvd_of_mem_primeFactors h)
  have hpow : p^(u.factorization p-1) ∣ u :=
    (pow_dvd_pow p (Nat.sub_le _ 1)).trans (Nat.ordProj_dvd u p)
  refine (ArithmeticFunction.carmichael_dvd_totient _).trans ?_
  rw [Nat.totient_prime_pow hp he]
  exact Nat.mul_dvd_mul hpow (hL p h)

/-- Every common cyclic quotient order divides a single least common
multiple of residue-field orders. Prime powers in the moduli supply no
further common exponent. -/
theorem gcd_carmichael_dvd_residue_lcm {u v : ℕ} (hu : 0<u) (hv : 0<v) (hc : u.Coprime v) :
    (ArithmeticFunction.carmichael u).gcd (ArithmeticFunction.carmichael v) ∣
      (u.primeFactors ∪ v.primeFactors).lcm (fun p => p-1) := by
  let L := (u.primeFactors ∪ v.primeFactors).lcm (fun p => p-1)
  let d := (ArithmeticFunction.carmichael u).gcd (ArithmeticFunction.carmichael v)
  have h₁ : d ∣ u*L := (Nat.gcd_dvd_left _ _).trans
    (carmichael_dvd_mul_of_residue_orders_dvd hu (fun _ h => dvd_lcm (mem_union_left _ h)))
  have h₂ : d ∣ v*L := (Nat.gcd_dvd_right _ _).trans
    (carmichael_dvd_mul_of_residue_orders_dvd hv (fun _ h => dvd_lcm (mem_union_right _ h)))
  simpa only [Nat.gcd_mul_right,hc.gcd_eq_one,one_mul,mul_one] using Nat.dvd_gcd h₁ h₂

/-- A single cyclic subgroup of the residue unit group contains at least
the modulus divided by twice the product of its distinct primes. -/
theorem exists_unit_large_order {u : ℕ} (hu : 0<u) :
    ∃ a : (ZMod u)ˣ, u ≤ (∏ p ∈ u.primeFactors, p)*(2*orderOf a) := by
  letI : NeZero u := ⟨hu.ne'⟩
  obtain ⟨a,ha⟩ := Monoid.exists_orderOf_eq_exponent (Monoid.ExponentExists.of_finite (G := (ZMod u)ˣ))
  refine ⟨a,?_⟩
  have hrad : 0<∏ p ∈ u.primeFactors, p := prod_pos fun p h => (Nat.prime_of_mem_primeFactors h).pos
  have hord : 0<orderOf a := orderOf_pos a
  exact Nat.le_of_dvd (Nat.mul_pos hrad (Nat.mul_pos (by decide) hord))
    (by rw [ha,← ArithmeticFunction.carmichael_eq_exponent hu.ne']; exact dvd_twice_radical_mul_carmichael hu)

/-- A power of a cyclic generator belongs to the kernel as soon as its
image is annihilated. This bounds the whole image even for infinite targets. -/
theorem order_mul_range_dvd_gcd_mul_card {G H : Type*} [Group G] [Group H]
    (f : G →* H) (a : G) {M : ℕ} (hM : f a ^ M = 1) :
    orderOf a * Nat.card f.range ∣ (orderOf a).gcd M * Nat.card G := by
  let d := (orderOf a).gcd M
  have hker : a^d ∈ f.ker := by
    change f (a^d) = 1
    rw [map_pow]
    exact orderOf_dvd_iff_pow_eq_one.mp
      (Nat.dvd_gcd (orderOf_map_dvd f a) (orderOf_dvd_iff_pow_eq_one.mpr hM))
  have hpow : (a^d)^(Nat.card f.ker) = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp (f.ker.orderOf_dvd_natCard hker)
  rw [← pow_mul] at hpow
  have hdiv := Nat.mul_dvd_mul_right (orderOf_dvd_iff_pow_eq_one.mpr hpow) (Nat.card f.range)
  have hcard := f.ker.card_mul_index
  rw [Subgroup.index_ker] at hcard
  simpa only [mul_assoc,hcard,d] using hdiv

/-- Uniform divisibility for all images of bounded exponent. The residual
factor depends only on the distinct primes in the source modulus. -/
theorem unitHom_range_dvd_of_pow_eq_one {u M : ℕ} (hu : 0<u)
    {H : Type*} [Group H] (f : (ZMod u)ˣ →* H) (hM : ∀ x, (f x)^M=1) :
    Nat.card f.range ∣ (ArithmeticFunction.carmichael u).gcd M * (2*residueUnitOrder u) := by
  letI : NeZero u := ⟨hu.ne'⟩
  let unitExponent := ArithmeticFunction.carmichael u
  obtain ⟨a,ha⟩ := Monoid.exists_orderOf_eq_exponent (Monoid.ExponentExists.of_finite (G := (ZMod u)ˣ))
  have hord : orderOf a=unitExponent := ha.trans (ArithmeticFunction.carmichael_eq_exponent hu.ne').symm
  have hExponent : 0<unitExponent := hord ▸ orderOf_pos a
  have h := order_mul_range_dvd_gcd_mul_card f a (hM a)
  have hcard : Nat.card (ZMod u)ˣ=u.totient := by rw [Nat.card_eq_fintype_card,ZMod.card_units_eq_totient]
  rw [hord,hcard,totient_split] at h
  let A := ∏ p ∈ u.primeFactors, p
  have hA : 0<A := prod_pos fun p hp => (Nat.prime_of_mem_primeFactors hp).pos
  have hprod : A*primePowerPart u=u := by
    rw [mul_comm]; exact Nat.div_mul_cancel (Nat.prod_primeFactors_dvd u)
  have hpart : primePowerPart u ∣ 2*unitExponent := Nat.dvd_of_mul_dvd_mul_left hA
    (by rw [hprod]; exact dvd_twice_radical_mul_carmichael hu)
  apply Nat.dvd_of_mul_dvd_mul_left hExponent
  exact h.trans ((Nat.mul_dvd_mul_left (unitExponent.gcd M) (Nat.mul_dvd_mul_right hpart (residueUnitOrder u))).trans
    (dvd_of_eq (by ring)))

/-- For any number of copies of the opposite unit group, every joint image
order divides the same integer, including when the index type is infinite. -/
theorem unitHom_product_range_dvd {u v : ℕ} (hu : 0<u) (hv : 0<v) (hc : u.Coprime v)
    {ι : Type*} (f : (ZMod u)ˣ →* (ι → (ZMod v)ˣ)) :
    Nat.card f.range ∣ (u.primeFactors ∪ v.primeFactors).lcm (fun p => p-1) * (2*residueUnitOrder u) := by
  have hM (a : (ZMod u)ˣ) : (f a)^(ArithmeticFunction.carmichael v)=1 := by
    funext i
    exact ArithmeticFunction.pow_carmichael (f a i)
  exact (unitHom_range_dvd_of_pow_eq_one hu f hM).trans
    (Nat.mul_dvd_mul_right (gcd_carmichael_dvd_residue_lcm hu hv hc) _)

#print axioms order_mul_range_dvd_gcd_mul_card
#print axioms unitHom_range_dvd_of_pow_eq_one
#print axioms unitHom_product_range_dvd
#print axioms gcd_totient_dvd_residueUnitOrders
#print axioms saturated_gcd_unit_orders
#print axioms unitHom_range_dvd_residueUnitOrders
#print axioms le_cutoff_mul_totient
#print axioms dvd_twice_radical_mul_carmichael
#print axioms gcd_carmichael_dvd_residue_lcm
#print axioms exists_unit_large_order

end GaloisForLFunctions.CountingHolography.Sections
