import GaloisForLFunctions.RHTower.CCM.CCMFUSuzukiMobiusDivisorDilationChannels
import GaloisForLFunctions.RestrictedFactorizationCalculus.TheCenteredReadingBelowTheHyperbola

/-!
# Ordinary primes at the quotient endpoints

Transposing the deleted proper prime powers gives smaller unweighted
Möbius prefixes, all with the original frozen cutoff. The cofactor
floor and the integer smooth main term are preserved exactly.
-/

noncomputable section

open Finset ArithmeticFunction RHTower.CoprimeMobius
open scoped Classical
open GaloisForLFunctions.BezoutValuationIncidence

namespace GaloisForLFunctions.RestrictedFactorizationCalculus

open RoughReading

/-- Chebyshev weight of the ordinary primes strictly above the fixed cutoff. -/
def ordinaryPrimeReading (y t : ℕ) : ℝ :=
  ∑ p ∈ (Nat.primesLE t).filter (y<·),Real.log p

/-- The ordinary-prime reading centered at its exact quotient floor. -/
def centeredOrdinaryPrimeRemainder (y X : ℕ) : ℝ :=
  ∑ m ∈ freeSet y (X/y),row y m*
    (ordinaryPrimeReading y (X/m)-(y:ℝ)*(⌊((X:ℝ)/y)/m⌋:ℝ))

/-- The Mangoldt kernel on surviving proper powers. -/
def roughProperPowerWeight (y d : ℕ) : ℝ :=
  if 1<d ∧ y<d ∧ ¬ d.Prime ∧ IsFree (banned y) d then vonMangoldt d else 0

private theorem split_reading (y t : ℕ) :
    roughPrimePowerReading y t-ordinaryPrimeReading y t=
      ∑ d ∈ Icc 1 t,roughProperPowerWeight y d := by
  have seteq : (Nat.primesLE t).filter (y<·)=(Icc 1 t).filter (fun d => d.Prime ∧ y<d) := by
    ext d
    simp only [mem_filter,Nat.mem_primesLE,mem_Icc]
    exact ⟨fun ⟨⟨dt,hp⟩,dy⟩ => ⟨⟨hp.pos,dt⟩,hp,dy⟩,fun ⟨hi,hp,dy⟩ => ⟨⟨hi.2,hp⟩,dy⟩⟩
  rw [roughPrimePowerReading,freeSet,ordinaryPrimeReading,seteq,sum_filter,sum_filter,←sum_sub_distrib]
  apply sum_congr rfl
  intro d hd
  by_cases hp : d.Prime
  · have good : IsFree (banned y) d ↔ y<d := by
      simpa only [banned,Set.mem_setOf_eq,not_le] using isFree_prime (banned y) hp
    simp [roughProperPowerWeight,hp,good,vonMangoldt_apply_prime hp]
  by_cases good : IsFree (banned y) d
  · by_cases one : d=1
    · subst d; simp [roughProperPowerWeight]
    have pos := (mem_Icc.mp hd).1
    have minp : d.minFac ∈ d.primeFactors := Nat.mem_primeFactors.mpr
      ⟨Nat.minFac_prime one,Nat.minFac_dvd _,good.1⟩
    have high : y<d := (lt_of_not_ge (show ¬d.minFac ≤ y from good.2 _ minp)).trans_le
      (Nat.le_of_dvd pos (Nat.minFac_dvd _))
    simp [roughProperPowerWeight,hp,good,high,show 1<d by omega]
  · simp [roughProperPowerWeight,hp,good]

/-- The difference of the two centered readings is an exact sum of
smaller frozen rows indexed by the omitted proper powers. -/
theorem proper_powers_as_smaller_frozen_rows {y : ℕ} (hy : 0<y) (X : ℕ) :
    centeredPrimePowerRemainder y X-centeredOrdinaryPrimeRemainder y X=
      ∑ d ∈ Icc 1 X,roughProperPowerWeight y d*coprimeMoebiusSum (primorial y) (X/d) := by
  let F := fun m d : ℕ => row y m*roughProperPowerWeight y d
  have each (m : ℕ) : row y m*
      (roughPrimePowerReading y (X/m)-(y:ℝ)*(⌊((X:ℝ)/y)/m⌋:ℝ))-
      row y m*(ordinaryPrimeReading y (X/m)-(y:ℝ)*(⌊((X:ℝ)/y)/m⌋:ℝ))=
      ∑ d ∈ Icc 1 (X/m),F m d := by
    rw [←mul_sub,sub_sub_sub_cancel_right,split_reading,mul_sum]
  have extend : (∑ m ∈ freeSet y (X/y),∑ d ∈ Icc 1 (X/m),F m d)=
      ∑ m ∈ Icc 1 X,∑ d ∈ Icc 1 (X/m),F m d := by
    apply sum_subset ((filter_subset ..).trans (Icc_subset_Icc_right (Nat.div_le_self ..)))
    intro m hm outside
    have mp := (mem_Icc.mp hm).1
    by_cases past : X/y < m
    · have product := (Nat.div_lt_iff_lt_mul hy).mp past
      have bound : X/m<y := (Nat.div_lt_iff_lt_mul mp).mpr (by simpa only [Nat.mul_comm] using product)
      apply sum_eq_zero
      intro d hd
      simp [F,roughProperPowerWeight,show ¬y<d from (not_lt.mpr ((mem_Icc.mp hd).2.trans bound.le))]
    · have bad : ¬IsFree (banned y) m := fun h => outside (mem_filter.mpr ⟨mem_Icc.mpr
          ⟨mp,le_of_not_gt past⟩,h⟩)
      simp [F,row_value,bad]
  rw [centeredPrimePowerRemainder,centeredOrdinaryPrimeRemainder,←sum_sub_distrib,
    sum_congr rfl (fun m _ => each m),extend,RHTower.sum_hyperbola_swap_real X F]
  apply sum_congr rfl
  intro d _
  rw [coprimeMoebiusSum,mul_sum]
  apply sum_congr rfl
  intro m hm
  change row y m*roughProperPowerWeight y d=_
  rw [primorial_indicator_eq_deleted_mobius y m (mem_Icc.mp hm).1,mul_comm]

/-- Exact logarithmic identity with the ordinary-prime reading, the
full smooth population, and the delayed proper-power correction. -/
theorem exact_centered_ordinary_prime_reading {y : ℕ} (hy : 0<y) (X : ℕ) :
    (∑ n ∈ Icc 1 X,row y n*Real.log n)+centeredOrdinaryPrimeRemainder y X+
      (∑ d ∈ Icc 1 X,roughProperPowerWeight y d*coprimeMoebiusSum (primorial y) (X/d))=
      -(y:ℝ)*(RHTower.Sieve.smoothUpTo (Nat.primesLE y) (X/y)).card := by
  linarith only [proper_powers_as_smaller_frozen_rows hy X,exact_centered_prime_power_remainder hy X]


open scoped ArithmeticFunction.Moebius

private theorem restrict_the_ordinary_prime_weight (y : ℕ) :
    roughOrdinaryPrimeWeight y=roughRestriction y (roughOrdinaryPrimeWeight 0) := by
  ext n
  rw [roughRestriction_apply]
  change (if n.Prime ∧ y<n then Real.log n else 0)=
    if IsFree (banned y) n then (if n.Prime ∧ 0<n then Real.log n else 0) else 0
  by_cases prime : n.Prime
  · have eq : IsFree (banned y) n ↔ y<n := by
      simpa only [banned,Set.mem_setOf_eq,not_le] using isFree_prime (banned y) prime
    simp [prime,prime.pos,eq]
  · simp [prime]

/-- The coefficient of an ordinary-prime quotient head is a signed sum
over the distinct prime factors of its index, with its roughness test frozen. -/
theorem ordinary_prime_floor_coefficient (y d : ℕ) :
    roughFloorCoefficient y (roughOrdinaryPrimeWeight y) d =
      if IsFree (banned y) d then ∑ p ∈ d.primeFactors,(μ (d/p):ℝ)*Real.log p else 0 := by
  rw [roughFloorCoefficient,restrict_the_ordinary_prime_weight y]
  change (roughRestriction y (μ : ArithmeticFunction ℝ)*roughRestriction y (roughOrdinaryPrimeWeight 0)) d=_
  rw [show roughRestriction y (μ : ArithmeticFunction ℝ)*roughRestriction y (roughOrdinaryPrimeWeight 0)=
    roughRestriction y ((μ : ArithmeticFunction ℝ)*roughOrdinaryPrimeWeight 0) from
      (GaloisForLFunctions.SelbergClass.DirichletSeries.primeRestrict_mul ..).symm,roughRestriction_apply]
  split_ifs with hd
  · rw [Nat.primeFactors_eq_to_filter_divisors_prime,sum_filter,mul_comm,ArithmeticFunction.mul_apply]
    simp only [ArithmeticFunction.intCoe_apply]
    rw [Nat.sum_divisorsAntidiagonal (fun p m => roughOrdinaryPrimeWeight 0 p * (μ m : ℝ))]
    apply sum_congr rfl
    intro p _
    change (if p.Prime ∧ 0<p then Real.log p else 0)*(μ (d/p):ℝ)=_
    by_cases hp : p.Prime
    · simp only [hp,hp.pos,and_self,if_true,mul_comm]
    · simp [hp]
  · rfl

private theorem ordinary_coefficient_on_squarefree (d : ℕ) (square : Squarefree d) :
    (∑ p ∈ d.primeFactors,(μ (d/p):ℝ)*Real.log p)= -(μ d:ℝ)*Real.log d := by
  have neg (p : ℕ) (hp : p∈d.primeFactors) : (μ (d/p):ℝ)= -(μ d:ℝ) := by
    obtain ⟨prime,dvd,_⟩ := Nat.mem_primeFactors.mp hp
    have eq := Nat.mul_div_cancel' dvd
    have cop := Nat.coprime_of_squarefree_mul (eq.symm ▸ square)
    have val := ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime cop
    rw [eq,ArithmeticFunction.moebius_apply_prime prime] at val
    exact_mod_cast (show μ (d/p)= -(μ d) by linarith only [val])
  have factor : (∑ p ∈ d.primeFactors,(μ (d/p):ℝ)*Real.log p) =
      ∑ p ∈ d.primeFactors, (-(μ d:ℝ))*Real.log p :=
    sum_congr rfl (fun p hp => congrArg (· * Real.log p) (neg p hp))
  rw [factor,←mul_sum]
  have logs : Real.log (d:ℝ)=∑ p ∈ d.primeFactors,Real.log p := by
    conv_lhs => rw [←Nat.prod_primeFactors_of_squarefree square,Nat.cast_prod]
    exact Real.log_prod (fun p hp => Nat.cast_ne_zero.mpr (Nat.prime_of_mem_primeFactors hp).ne_zero)
  rw [logs]

/-- A squarefree rough index has the same logarithmic coefficient for
ordinary primes as for the full Mangoldt reading. -/
theorem ordinary_head_on_a_squarefree_rough_index {y d : ℕ} (rough : IsFree (banned y) d) (sq : Squarefree d) :
    roughFloorCoefficient y (roughOrdinaryPrimeWeight y) d= -(μ d:ℝ)*Real.log d := by
  rw [ordinary_prime_floor_coefficient,if_pos rough,ordinary_coefficient_on_squarefree d sq]

/-- If deleting a single prime from a nonsquarefree integer gives a
squarefree quotient, that prime occurs exactly twice and is its only repetition. -/
private theorem recover_the_repeated_prime {n p : ℕ} (prime : p.Prime) (dvd : p ∣ n)
    (bad : ¬Squarefree n) (clean : Squarefree (n/p)) :
    ∃ r,Squarefree r ∧ ¬p ∣ r ∧ n=p^2*r := by
  have eq := Nat.mul_div_cancel' dvd
  have again : p ∣ n/p := by
    by_contra nd
    exact bad (eq ▸ (Nat.squarefree_mul_iff.mpr ⟨prime.coprime_iff_not_dvd.mpr nd,prime.squarefree,clean⟩))
  obtain ⟨r,hr⟩ := again
  have pair := Nat.squarefree_mul_iff.mp (hr ▸ clean)
  refine ⟨r,pair.2.2,prime.coprime_iff_not_dvd.mp pair.1,?_⟩
  calc n = p*(n/p) := eq.symm
       _ = _ := by rw [hr]; ring

/-- At a rough index where a prime occurs exactly twice, its coefficient is
minus the Möbius value of the remaining part times the log of that prime. -/
theorem ordinary_head_at_one_doubled_prime {y p r : ℕ} (prime : p.Prime)
    (nd : ¬p ∣ r) (free : IsFree (banned y) (p^2*r)) :
    roughFloorCoefficient y (roughOrdinaryPrimeWeight y) (p^2*r)= -(μ r:ℝ)*Real.log p := by
  let n := p^2*r
  have form : n=p*(p*r) := by dsimp only [n]; ring
  have div : n/p=p*r := by rw [form,Nat.mul_div_cancel_left _ prime.pos]
  have mem : p∈n.primeFactors := Nat.mem_primeFactors.mpr ⟨prime,by rw [form]; exact dvd_mul_right p _,free.1⟩
  rw [ordinary_prime_floor_coefficient,if_pos free]
  change (∑ q ∈ n.primeFactors,(μ (n/q):ℝ)*Real.log q)=_
  rw [sum_eq_single p]
  · rw [div,ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (prime.coprime_iff_not_dvd.mpr nd),
      ArithmeticFunction.moebius_apply_prime prime]
    push_cast; ring
  · intro q hq ne
    obtain ⟨qp,qd,_⟩ := Nat.mem_primeFactors.mp hq
    have cop : (p*p).Coprime q := (Nat.coprime_primes prime qp |>.mpr ne.symm).mul_left
      (Nat.coprime_primes prime qp |>.mpr ne.symm)
    have twice : p*p ∣ q*(n/q) := by rw [Nat.mul_div_cancel' qd]; exact ⟨r,by dsimp only [n]; ring⟩
    have nc : ¬Squarefree (n/q) := fun s =>
      Nat.squarefree_iff_prime_squarefree.mp s p prime (cop.dvd_of_dvd_mul_left twice)
    rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree nc]; simp
  · exact fun h => (h mem).elim

/-- On nonsquarefree indices every nonzero ordinary-prime coefficient
comes from one doubled prime times a coprime squarefree remainder. -/
theorem support_of_the_nonsquarefree_ordinary_head {y n : ℕ} (ns : ¬Squarefree n)
    (active : roughFloorCoefficient y (roughOrdinaryPrimeWeight y) n ≠ 0) :
    IsFree (banned y) n ∧ ∃ p r,p.Prime ∧ Squarefree r ∧ ¬p ∣ r ∧ n=p^2*r := by
  rw [ordinary_prime_floor_coefficient] at active
  split_ifs at active with free
  · obtain ⟨p,hp,term⟩ := exists_ne_zero_of_sum_ne_zero active
    have sq : Squarefree (n/p) := by
      by_contra bad; exact term (by rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree bad]; simp)
    obtain ⟨pr,dvd,_⟩ := Nat.mem_primeFactors.mp hp
    obtain ⟨r,rs,nd,shape⟩ := recover_the_repeated_prime pr dvd ns sq
    exact ⟨free,p,r,pr,rs,nd,shape⟩
  · contradiction

#print axioms ordinary_prime_floor_coefficient
#print axioms ordinary_head_on_a_squarefree_rough_index
#print axioms ordinary_head_at_one_doubled_prime
#print axioms support_of_the_nonsquarefree_ordinary_head

#print axioms exact_centered_ordinary_prime_reading
#print axioms proper_powers_as_smaller_frozen_rows

end GaloisForLFunctions.RestrictedFactorizationCalculus
