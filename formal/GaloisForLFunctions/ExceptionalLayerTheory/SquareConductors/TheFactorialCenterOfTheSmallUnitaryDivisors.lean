import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheParityOfTheSmallUnitaryDivisors
import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheTotientTermInTheReflectedCompositePrice
import GaloisForLFunctions.RHTower.Sieve.DifferentiatedBarbanVehovScaledKernels
import Mathlib.Algebra.BigOperators.Associated

/-!
# The progression center of the smaller unitary divisors

Choosing whole prime-power blocks is equivalent to writing k = em with
(e,m) = 1. The smaller side starts at m = e. This exact endpoint is retained
when the primitive condition is expanded into logarithmic progressions.
-/

noncomputable section
open Finset ArithmeticFunction
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

private theorem subset_factor_pos {k : ℕ} {S : Finset ℕ} (hs : S ⊆ k.primeFactors) :
    0 < primePowerSubset k S :=
  prod_pos fun _ hp => pow_pos (Nat.prime_of_mem_primeFactors (hs hp)).pos _

private theorem subset_complement_eq {k : ℕ} (hk : 0 < k) {S : Finset ℕ}
    (hs : S ⊆ k.primeFactors) :
    primePowerSubset k S*primePowerSubset k (k.primeFactors \ S)=k := by
  unfold primePowerSubset
  rw [mul_comm,prod_sdiff hs]
  exact (Nat.prod_primeFactors_pow_factorization hk.ne').symm

private theorem subset_complement_coprime {k : ℕ} {S : Finset ℕ} (hs : S ⊆ k.primeFactors) :
    (primePowerSubset k S).Coprime (primePowerSubset k (k.primeFactors \ S)) := by
  apply Nat.Coprime.prod_left
  intro p hp
  apply Nat.Coprime.prod_right
  intro q hq
  apply Nat.Coprime.pow
  exact (Nat.coprime_primes (Nat.prime_of_mem_primeFactors (hs hp))
    (Nat.prime_of_mem_primeFactors (mem_sdiff.mp hq).1)).mpr (fun he => (mem_sdiff.mp hq).2 (he ▸ hp))

private theorem support_of_subset {k : ℕ} {S : Finset ℕ} (hs : S ⊆ k.primeFactors) :
    (primePowerSubset k S).primeFactors=S := by
  ext p
  constructor
  · intro hp
    obtain ⟨hp',hd,_⟩ := Nat.mem_primeFactors.mp hp
    unfold primePowerSubset at hd
    obtain ⟨q,hq,hdiv⟩ := hp'.prime.exists_mem_finset_dvd hd
    have he := (Nat.prime_dvd_prime_iff_eq hp' (Nat.prime_of_mem_primeFactors (hs hq))).mp
      (hp'.dvd_of_dvd_pow hdiv)
    simpa only [he] using hq
  · intro hp
    obtain ⟨hp',hd,hk⟩ := Nat.mem_primeFactors.mp (hs hp)
    exact Nat.mem_primeFactors.mpr ⟨hp',(dvd_pow_self p (hp'.factorization_pos_of_dvd hk hd).ne').trans
      (dvd_prod_of_mem (fun q => q^k.factorization q) hp),(subset_factor_pos hs).ne'⟩

private theorem reconstruct_unitary {k d : ℕ} (hk : 0 < k) (hd : d ∣ k)
    (hc : d.Coprime (k/d)) : primePowerSubset k d.primeFactors=d := by
  have hm := Nat.mul_div_cancel' hd
  have hdp : 0 < d := Nat.pos_of_dvd_of_pos hd hk
  have hrp : 0 < k/d := Nat.div_pos (Nat.le_of_dvd hk hd) hdp
  calc primePowerSubset k d.primeFactors = ∏ p ∈ d.primeFactors,p^d.factorization p := by
         apply prod_congr rfl
         intro p hp
         obtain ⟨hpr,hpd,_⟩ := Nat.mem_primeFactors.mp hp
         have hn := hpr.coprime_iff_not_dvd.mp (hc.of_dvd_left hpd)
         have hfac := congrArg (fun n : ℕ => n.factorization p) hm
         simp only [Nat.factorization_mul hdp.ne' hrp.ne',Finsupp.add_apply,
           Nat.factorization_eq_zero_of_not_dvd hn,add_zero] at hfac
         rw [hfac]
       _ = d := (Nat.prod_primeFactors_pow_factorization hdp.ne').symm

/-- Any function of the smaller block count may be summed on ordinary
divisors with the unitary coprimality test and the exact square-root cut. -/
theorem small_unitary_sum_on_divisors {M : Type*} [AddCommMonoid M] (w : ℕ → M)
    {k : ℕ} (hk : 0 < k) :
    (∑ S ∈ smallUnitarySubsets k,w S.card)=
      ∑ d ∈ k.divisors.filter (fun d => d.Coprime (k/d) ∧ d^2 ≤ k),w d.primeFactors.card := by
  apply sum_nbij' (primePowerSubset k) Nat.primeFactors
  · intro S hS
    obtain ⟨hpow,hsm⟩ := mem_filter.mp hS
    have hs := mem_powerset.mp hpow
    have hm := subset_complement_eq hk hs
    have hdiv := Nat.mul_div_cancel_left (primePowerSubset k (k.primeFactors \ S)) (subset_factor_pos hs)
    rw [hm] at hdiv
    have hf := Nat.mul_le_mul_left (primePowerSubset k S) hsm
    rw [hm,←pow_two] at hf
    exact mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨⟨_,hm.symm⟩,hk.ne'⟩,
      hdiv.symm ▸ subset_complement_coprime hs,hf⟩
  · intro d hd
    obtain ⟨hdiv,hcop,hsq⟩ := mem_filter.mp hd
    have hsub := Nat.primeFactors_mono (Nat.mem_divisors.mp hdiv).1 hk.ne'
    have hr := reconstruct_unitary hk (Nat.mem_divisors.mp hdiv).1 hcop
    have hm := subset_complement_eq hk hsub
    rw [hr] at hm
    apply mem_filter.mpr
    refine ⟨mem_powerset.mpr hsub,?_⟩
    rw [hr]
    have hdp := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hdiv).1 hk
    exact Nat.le_of_mul_le_mul_left ((pow_two d).symm.le.trans (hsq.trans hm.symm.le)) hdp
  · exact fun S hS => support_of_subset (mem_powerset.mp (mem_filter.mp hS).1)
  · exact fun d hd => reconstruct_unitary hk (Nat.mem_divisors.mp (mem_filter.mp hd).1).1 (mem_filter.mp hd).2.1
  · intro S hS
    rw [support_of_subset (mem_powerset.mp (mem_filter.mp hS).1)]

#print axioms small_unitary_sum_on_divisors

/-- Sum of full logarithms of multiples of a positive step through a cutoff. -/
def progressionLogFactorial (l T : ℕ) : ℝ :=
  ((T/l:ℕ):ℝ)*Real.log l+Real.log ((T/l).factorial:ℕ)

private theorem log_scaled_sum (l : ℕ) (hl : 0 < l) (q : ℕ) :
    (∑ j ∈ Icc 1 q,Real.log (l*j:ℕ))=
      (q:ℝ)*Real.log l+Real.log (q.factorial:ℕ) := by
  have hterm (j : ℕ) (hj : j ∈ Icc 1 q) :
      Real.log (l*j:ℕ)=Real.log l+Real.log j := by
    have hj0 := (mem_Icc.mp hj).1
    rw [Nat.cast_mul,Real.log_mul (by positivity) (by positivity)]
  rw [sum_congr rfl hterm,sum_add_distrib,sum_const,nsmul_eq_mul,Nat.card_Icc,
    Nat.add_one_sub_one,_root_.RHTower.Sieve.sum_Icc_log_eq_log_factorial]

private theorem primitive_scaled_prefix {e n : ℕ} (he : 0 < e) (hn : 0 < n) (T : ℕ) :
    (∑ m ∈ (Icc 1 (T/e)).filter ((e*n).Coprime ·),Real.log (e*m:ℕ))=
      ∑ d ∈ (e*n).divisors,(moebius d:ℝ)*progressionLogFactorial (e*d) T := by
  classical
  rw [sum_filter]
  calc _ = ∑ m ∈ Icc 1 (T/e),∑ d ∈ (e*n).divisors,
               if d ∣ m then (moebius d:ℝ)*Real.log (e*m:ℕ) else 0 := by
             apply sum_congr rfl
             intro m _
             rw [show (if (e*n).Coprime m then Real.log (e*m:ℕ) else 0)=
               (if (e*n).Coprime m then (1:ℝ) else 0)*Real.log (e*m:ℕ) by split_ifs <;> simp,
               reflected_coprime_indicator (Nat.mul_pos he hn),sum_mul]
             exact sum_congr rfl fun d _ => by split_ifs <;> simp
       _ = _ := by
             rw [sum_comm]
             apply sum_congr rfl
             intro d hd
             have hd0 := Nat.pos_of_mem_divisors hd
             rw [←sum_filter,_root_.RHTower.Sieve.sum_filter_dvd_eq_sum_scaled hd0,←mul_sum]
             simp only [←Nat.mul_assoc,Nat.div_div_eq_mul,log_scaled_sum _ (Nat.mul_pos he hd0),
               progressionLogFactorial]

/-- The primitive multiples of a small unitary divisor start exactly at its
square. Each surviving progression contributes a difference of log-factorials. -/
theorem small_unitary_factorial_row {e n T : ℕ} (he : 0 < e) (hn : 0 < n) (hT : e^2 ≤ T) :
    (∑ m ∈ (Ioc ((e^2-1)/e) (T/e)).filter ((e*n).Coprime ·), Real.log (e*m:ℕ))=
      ∑ d ∈ (e*n).divisors,(moebius d:ℝ)*
        (progressionLogFactorial (e*d) T-progressionLogFactorial (e*d) (e^2-1)) := by
  let f (m : ℕ) := if (e*n).Coprime m then Real.log (e*m:ℕ) else 0
  have prefix (s : ℕ) : (∑ m ∈ Ioc 0 (s/e),f m)=
      ∑ d ∈ (e*n).divisors,(moebius d:ℝ)*progressionLogFactorial (e*d) s := by
    have hi : Icc 1 (s/e)=Ioc 0 (s/e) := by ext j; simp only [mem_Icc,mem_Ioc]; omega
    simpa only [sum_filter,hi,f] using primitive_scaled_prefix he hn s
  rw [sum_filter]
  change (∑ m ∈ Ioc ((e^2-1)/e) (T/e),f m)=_
  simp only [mul_sub,sum_sub_distrib]
  rw [←prefix T,←prefix (e^2-1)]
  exact eq_sub_of_add_eq' (sum_Ioc_consecutive f (Nat.zero_le _)
    (Nat.div_le_div_right ((Nat.sub_le _ _).trans hT)))

#print axioms small_unitary_factorial_row

/-- Positive row indices whose square is reached by the endpoint. -/
def smallDivisorIndices (T : ℕ) : Finset ℕ := (Icc 1 T).filter (fun e => e^2 ≤ T)

/-- Transpose the square-root divisor cutoff without losing its square endpoint. -/
private theorem transpose_small_divisors (T : ℕ) (f : ℕ → ℕ → ℝ) :
    (∑ k ∈ Icc 1 T,∑ e ∈ k.divisors.filter (fun e => e^2 ≤ k), f e k)=
      ∑ e ∈ smallDivisorIndices T,∑ k ∈ (Ioc (e^2-1) T).filter (e ∣ ·),f e k := by
  classical
  let S := smallDivisorIndices T
  have byK {k : ℕ} (hk : k ∈ Icc 1 T) :
      k.divisors.filter (fun e => e^2 ≤ k)=S.filter (fun e => e ∣ k ∧ e^2 ≤ k) := by
    ext e
    obtain ⟨hk0,hkT⟩ := mem_Icc.mp hk
    simp only [S,smallDivisorIndices,mem_filter,mem_Icc,Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hed,_⟩,he⟩
      exact ⟨⟨⟨Nat.pos_of_dvd_of_pos hed hk0,(Nat.le_of_dvd hk0 hed).trans hkT⟩,he.trans hkT⟩,hed,he⟩
    · rintro ⟨_,hed,he⟩
      exact ⟨⟨hed,Nat.ne_of_gt hk0⟩,he⟩
  have byE {e : ℕ} (he : e ∈ S) :
      (Icc 1 T).filter (fun k => e ∣ k ∧ e^2 ≤ k)=(Ioc (e^2-1) T).filter (e ∣ ·) := by
    have h0 := (mem_Icc.mp (mem_filter.mp he).1).1
    have h1 : 0 < e^2 := pow_pos h0 _
    ext k
    simp only [mem_filter,mem_Icc,mem_Ioc]
    omega
  calc _ = ∑ k ∈ Icc 1 T,∑ e ∈ S,if e ∣ k ∧ e^2 ≤ k then f e k else 0 :=
           sum_congr rfl fun k hk => by rw [byK hk,sum_filter]
       _ = _ := by
           rw [sum_comm]
           exact sum_congr rfl fun e he => by rw [←sum_filter,byE he]

/-- Finite factorial center for a general weight on the number of blocks of
the smaller unitary divisor. The inner Möbius sum removes primes dividing en. -/
theorem small_unitary_factorial_center (w : ℕ → ℝ) {n : ℕ} (hn : 0 < n) (T : ℕ) :
    (∑ k ∈ (Icc 1 T).filter (n.Coprime ·),
      (∑ S ∈ smallUnitarySubsets k,w S.card)*Real.log k)=
      ∑ e ∈ (smallDivisorIndices T).filter (n.Coprime ·),w e.primeFactors.card*
        ∑ d ∈ (e*n).divisors,(moebius d:ℝ)*
          (progressionLogFactorial (e*d) T-progressionLogFactorial (e*d) (e^2-1)) := by
  classical
  let f (e k : ℕ) := if n.Coprime k ∧ e.Coprime (k/e) then w e.primeFactors.card*Real.log k else 0
  rw [sum_filter]
  calc _ = ∑ k ∈ Icc 1 T,∑ e ∈ k.divisors.filter (fun e => e^2 ≤ k),f e k := by
             apply sum_congr rfl
             intro k hk
             rw [small_unitary_sum_on_divisors w (mem_Icc.mp hk).1]
             by_cases hc : n.Coprime k
             · simp only [if_pos hc,sum_mul,sum_filter,f,hc,true_and]
               apply sum_congr rfl
               intro e _
               by_cases hd : e.Coprime (k/e) <;> by_cases hs : e^2 ≤ k <;> simp [hd,hs]
             · simp [f,hc]
       _ = _ := by
             rw [transpose_small_divisors,sum_filter]
             apply sum_congr rfl
             intro e he
             have he0 := (mem_Icc.mp (mem_filter.mp he).1).1
             rw [_root_.RHTower.Sieve.sum_filter_dvd_Ioc_eq_sum_scaled he0]
             by_cases hc : n.Coprime e
             · rw [if_pos hc,←small_unitary_factorial_row he0 hn (mem_filter.mp he).2,sum_filter,mul_sum]
               apply sum_congr rfl
               intro j _
               simp only [f,Nat.coprime_mul_iff_right,Nat.coprime_mul_iff_left,hc,true_and,
                 Nat.mul_div_cancel_left _ he0,mul_ite,mul_zero,and_comm]
             · simp [f,Nat.coprime_mul_iff_right,hc]

#print axioms small_unitary_factorial_center

/-- Möbius sum through the square root, with ordinary divisors. -/
def halfMoebius (k : ℕ) : ℤ := ∑ d ∈ k.divisors.filter (fun d => d^2 ≤ k),moebius d

/-- On squarefree integers the ordinary and unitary divisor sums agree. -/
theorem half_moebius_squarefree {k : ℕ} (hs : Squarefree k) :
    halfMoebius k=unitaryHalfWeight k := by
  have hk := Nat.pos_of_ne_zero hs.ne_zero
  rw [halfMoebius,unitaryHalfWeight,small_unitary_sum_on_divisors _ hk]
  have heq : k.divisors.filter (fun d => d.Coprime (k/d) ∧ d^2 ≤ k)=
      k.divisors.filter (fun d => d^2 ≤ k) := by
    ext d
    simp only [mem_filter]
    constructor
    · exact fun h => ⟨h.1,h.2.2⟩
    · rintro ⟨hd,h⟩
      have hm := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)
      exact ⟨hd,Nat.coprime_of_squarefree_mul (by simpa only [hm] using hs),h⟩
  rw [heq]
  apply sum_congr rfl
  intro d hd
  have hsf := hs.squarefree_of_dvd (Nat.dvd_of_mem_divisors (mem_filter.mp hd).1)
  rw [moebius_apply_of_squarefree hsf,
    ←(cardDistinctFactors_eq_cardFactors_iff_squarefree hsf.ne_zero).mpr hsf,
    cardDistinctFactors_apply,←Nat.toFinset_factors,List.card_toFinset]

private theorem log_multiple_interval {l : ℕ} (hl : 0 < l) (A T : ℕ) (h : A ≤ T) :
    (∑ k ∈ (Ioc A T).filter (l ∣ ·),Real.log k)=
      progressionLogFactorial l T-progressionLogFactorial l A := by
  rw [_root_.RHTower.Sieve.sum_filter_dvd_Ioc_eq_sum_scaled hl]
  have pref (s : ℕ) : (∑ j ∈ Ioc 0 (s/l), Real.log (l*j:ℕ))=progressionLogFactorial l s := by
    have hi : Icc 1 (s/l)=Ioc 0 (s/l) := by ext j; simp only [mem_Icc,mem_Ioc]; omega
    rw [←hi,log_scaled_sum l hl,progressionLogFactorial]
  rw [←pref T,←pref A]
  exact eq_sub_of_add_eq' (sum_Ioc_consecutive _ (Nat.zero_le _) (Nat.div_le_div_right h))

/-- The ordinary half-Möbius center at every cutoff uses the lcm of the
small divisor and each divisor of the coprimality modulus. -/
theorem half_moebius_factorial_center {n : ℕ} (hn : 0 < n) (T : ℕ) :
    (∑ k ∈ (Icc 1 T).filter (n.Coprime ·),(halfMoebius k:ℝ)*Real.log k)=
      ∑ e ∈ smallDivisorIndices T,(moebius e:ℝ)*∑ d ∈ n.divisors,(moebius d:ℝ)*
        (progressionLogFactorial (e.lcm d) T-progressionLogFactorial (e.lcm d) (e^2-1)) := by
  classical
  let f (e k : ℕ) := (moebius e:ℝ)*(if n.Coprime k then Real.log k else 0)
  rw [sum_filter]
  calc _ = ∑ k ∈ Icc 1 T,∑ e ∈ k.divisors.filter (fun e => e^2 ≤ k),f e k := by
             apply sum_congr rfl
             intro k _
             by_cases h : n.Coprime k <;> simp [h,f,halfMoebius,Int.cast_sum,sum_mul]
       _ = _ := by
             rw [transpose_small_divisors]
             apply sum_congr rfl
             intro e he
             have he0 := (mem_Icc.mp (mem_filter.mp he).1).1
             have heT := (mem_filter.mp he).2
             simp only [f,←mul_sum]
             congr 1
             let I := Ioc (e^2-1) T
             calc _ = ∑ k ∈ I.filter (e ∣ ·),∑ d ∈ n.divisors,
                          if d ∣ k then (moebius d:ℝ)*Real.log k else 0 := by
                        apply sum_congr rfl
                        intro k _
                        rw [show (if n.Coprime k then Real.log k else 0)=
                          (if n.Coprime k then (1:ℝ) else 0)*Real.log k by split_ifs <;> simp,
                          reflected_coprime_indicator hn,sum_mul]
                        exact sum_congr rfl fun d _ => by split_ifs <;> simp
                  _ = _ := by
                        rw [sum_comm]
                        apply sum_congr rfl
                        intro d hd
                        have hd0 := Nat.pos_of_mem_divisors hd
                        have hij : (I.filter (e ∣ ·)).filter (d ∣ ·)=I.filter (e.lcm d ∣ ·) := by
                          ext k
                          simp only [mem_filter,Nat.lcm_dvd_iff]
                          tauto
                        rw [←sum_filter,hij,←mul_sum,log_multiple_interval (Nat.lcm_pos he0 hd0) _ _
                          ((Nat.sub_le _ _).trans heT)]

#print axioms half_moebius_squarefree
#print axioms half_moebius_factorial_center

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
