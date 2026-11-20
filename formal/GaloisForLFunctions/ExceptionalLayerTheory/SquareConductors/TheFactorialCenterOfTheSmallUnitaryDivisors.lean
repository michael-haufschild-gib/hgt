import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.WeightedSectionsOfTheUnitaryFactorPairs
import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheTotientTermInTheReflectedCompositePrice
import GaloisForLFunctions.RHTower.Sieve.DifferentiatedBarbanVehovScaledKernels
import Mathlib.Algebra.BigOperators.Associated
import GaloisForLFunctions.ArithmeticKreinLangerTheory.FinitePrimeHeckeAuxiliaryObstructions

/-!
# The progression center of the smaller unitary divisors

Choosing whole prime-power blocks is equivalent to writing k = em with
(e,m) = 1. The smaller side starts at m = e. This exact endpoint is retained
when the primitive condition is expanded into logarithmic progressions.
-/

noncomputable section
open Finset ArithmeticFunction
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- Any function of the smaller block count may be summed on ordinary
divisors with the unitary coprimality test and the exact square-root cut. -/
theorem small_unitary_sum_on_divisors {M : Type*} [AddCommMonoid M] (w : ℕ → M)
    {k : ℕ} (hk : 0 < k) :
    (∑ S ∈ smallUnitarySubsets k,w S.card)=
      ∑ d ∈ k.divisors.filter (fun d => d.Coprime (k/d) ∧ d^2 ≤ k),w d.primeFactors.card := by
  have cut : smallUnitarySubsets k=k.primeFactors.powerset.filter (fun S => (primePowerSubset k S)^2≤k) := by
    ext S
    simp only [smallUnitarySubsets,mem_filter,mem_powerset]
    exact and_congr_right fun sub => unitarySubset_small_iff_square hk sub
  rw [cut]
  exact unitary_sum_on_divisor_section hk (fun d => d^2≤k) (fun _ S => w S.card)


/-- Sum of full logarithms of multiples of a positive step through a cutoff. -/
def progressionLogFactorial (l T : ℕ) : ℝ :=
  ((T/l:ℕ):ℝ)*Real.log l+Real.log ((T/l).factorial:ℕ)

/-- The log integral on a progression has a uniform logarithmic endpoint
error, including an endpoint before the first multiple. -/
theorem progression_log_factorial_error {l : ℕ} (hl : 0 < l) (T : ℕ) :
    |progressionLogFactorial l T-(T:ℝ)/l*(Real.log T-1)| ≤ 3+4*Real.log T := by
  rcases eq_or_ne T 0 with rfl | hT
  · simp [progressionLogFactorial]
  have hT' := Nat.pos_of_ne_zero hT
  have hl' := (Nat.cast_pos (α:=ℝ)).mpr hl
  have hlogT := Real.log_nonneg ((Nat.one_le_cast (α:=ℝ)).mpr hT')
  have hlogl := Real.log_nonneg ((Nat.one_le_cast (α:=ℝ)).mpr hl)
  let t := (T:ℝ)/l
  have ht : 0 ≤ t := div_nonneg (Nat.cast_nonneg _) hl'.le
  by_cases hTl : T < l
  · have ht1 : t ≤ 1 := (div_le_one hl').mpr (by exact_mod_cast hTl.le)
    simp only [progressionLogFactorial,Nat.div_eq_of_lt hTl,Nat.cast_zero,zero_mul,
      Nat.factorial_zero,Nat.cast_one,Real.log_one,add_zero,zero_sub,abs_neg,abs_mul]
    change |t| * |Real.log T-1| ≤ _
    rw [abs_of_nonneg ht]
    have he := abs_sub (Real.log T) 1
    rw [abs_of_nonneg hlogT,abs_one] at he
    have hb := mul_le_mul ht1 he (abs_nonneg _) zero_le_one
    linarith only [hb,hlogT]
  · have hll := Real.log_le_log hl' ((Nat.cast_le (α:=ℝ)).mpr (le_of_not_gt hTl))
    have hq : ((T/l:ℕ):ℝ) ≤ t := Nat.cast_div_le
    have htq : t ≤ ((T/l:ℕ):ℝ)+1 := by
      apply (div_le_iff₀ hl').mpr
      exact_mod_cast (Nat.lt_mul_div_succ T hl).le.trans_eq (Nat.mul_comm l _)
    have he := ArithmeticKreinLangerTheory.abs_log_div_factorial_sub_le hT' hl
    change |Real.log ((T/l).factorial:ℕ)-t*(Real.log T-Real.log l-1)| ≤ _ at he
    have hlo := mul_le_mul_of_nonneg_right hq hlogl
    have hhi := mul_le_mul_of_nonneg_right htq hlogl
    change |((T/l:ℕ):ℝ)*Real.log l+Real.log ((T/l).factorial:ℕ)-t*(Real.log T-1)| ≤ _
    exact abs_le.mpr ⟨by linarith only [(abs_le.mp he).1,hhi,hll],
      by linarith only [(abs_le.mp he).2,hlo,hll,hlogT]⟩


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
             simp only [←Nat.mul_assoc,Nat.div_div_eq_div_mul,log_scaled_sum _ (Nat.mul_pos he hd0),
               progressionLogFactorial]

/-- The primitive multiples of a small unitary divisor start exactly at its
square. Each surviving progression contributes a difference of log-factorials. -/
theorem small_unitary_factorial_row {e n T : ℕ} (he : 0 < e) (hn : 0 < n) (hT : e^2 ≤ T) :
    (∑ m ∈ (Ioc ((e^2-1)/e) (T/e)).filter ((e*n).Coprime ·), Real.log (e*m:ℕ))=
      ∑ d ∈ (e*n).divisors,(moebius d:ℝ)*
        (progressionLogFactorial (e*d) T-progressionLogFactorial (e*d) (e^2-1)) := by
  let f (m : ℕ) := if (e*n).Coprime m then Real.log (e*m:ℕ) else 0
  have hpref (s : ℕ) : (∑ m ∈ Ioc 0 (s/e),f m)=
      ∑ d ∈ (e*n).divisors,(moebius d:ℝ)*progressionLogFactorial (e*d) s := by
    have hi : Icc 1 (s/e)=Ioc 0 (s/e) := by ext j; simp only [mem_Icc,mem_Ioc]; omega
    simpa only [sum_filter,hi,f] using primitive_scaled_prefix he hn s
  rw [sum_filter]
  change (∑ m ∈ Ioc ((e^2-1)/e) (T/e),f m)=_
  simp only [mul_sub,sum_sub_distrib]
  rw [←hpref T,←hpref (e^2-1)]
  exact eq_sub_of_add_eq' (sum_Ioc_consecutive f (Nat.zero_le _)
    (Nat.div_le_div_right ((Nat.sub_le _ _).trans hT)))


private theorem primitive_progression_density (e : ℕ) {m : ℕ} (hm : 0 < m) (x : ℝ) :
    x*m.totient/((e:ℝ)*m)=∑ d ∈ m.divisors,(moebius d:ℝ)*(x/(e*d:ℕ)) := by
  rw [show x*m.totient/((e:ℝ)*m)=(x/e)*((m.totient:ℝ)/m) by simp only [div_eq_mul_inv,mul_inv_rev]; ring,
    ←_root_.RHTower.Sieve.sum_moebius_div_divisors_eq_totient_div hm,mul_sum]
  exact sum_congr rfl fun d _ => by simp only [Nat.cast_mul,div_eq_mul_inv,mul_inv_rev]; ring

/-- Density of the primitive cofactor row is φ(en)/(e²n). The uniform
endpoint error costs at most one logarithm per divisor of en. -/
theorem primitive_scaled_log_density {e n : ℕ} (he : 0 < e) (hn : 0 < n) (T : ℕ) :
    |(∑ j ∈ (Icc 1 (T/e)).filter ((e*n).Coprime ·),Real.log (e*j:ℕ))-
      ((T:ℝ)*(Real.log T-1))*(e*n).totient/((e:ℝ)*(e*n:ℕ))| ≤
      ((e*n).divisors.card:ℝ)*(3+4*Real.log T) := by
  rw [primitive_scaled_prefix he hn,primitive_progression_density e (Nat.mul_pos he hn),
    ←sum_sub_distrib]
  apply (abs_sum_le_sum_abs _ _).trans
  calc _ ≤ ∑ _d ∈ (e*n).divisors,(3+4*Real.log T) := by
             apply sum_le_sum
             intro d hd
             rw [←mul_sub,abs_mul,show (T:ℝ)*(Real.log T-1)/(e*d:ℕ)=
               (T:ℝ)/(e*d:ℕ)*(Real.log T-1) by ring]
             have hμ : |(moebius d:ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one (n:=d)
             exact (mul_le_mul hμ (progression_log_factorial_error
               (Nat.mul_pos he (Nat.pos_of_mem_divisors hd)) T) (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
       _ = _ := by rw [sum_const,nsmul_eq_mul]


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
             · simp only [if_pos hc,sum_mul,sum_filter,f]
               apply sum_congr rfl
               intro e _
               split_ifs <;> simp_all
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
               have hcond : n.Coprime (e*j) ∧ e.Coprime ((e*j)/e) ↔ (e*n).Coprime j := by
                 rw [Nat.coprime_mul_iff_right,Nat.coprime_mul_iff_left,Nat.mul_div_cancel_left _ he0]
                 tauto
               simp only [f,hcond,mul_ite,mul_zero]
             · simp [f,Nat.coprime_mul_iff_right,hc]


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


end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
