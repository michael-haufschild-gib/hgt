import GaloisForLFunctions.RHTower.Sieve.MertensWindowSharp
import GaloisForLFunctions.RHTower.Sieve.SmoothSum
import GaloisForLFunctions.RHTower.Sieve.BivariateConvolutionSummatorySwap
import GaloisForLFunctions.RHTower.MertensFirst

/-!
# Smooth cofactors in every quotient interval of polynomial height

Multiplication by primes between s and s² extends a smooth dyadic
population by one power of s. Each resulting integer has at most j+1
possible multipliers at height 2sʲ. The reciprocal mass of the primes
pays for a fixed fraction throughout every bounded number of steps.
-/

noncomputable section

open Finset Filter RHTower.Sieve
open ArithmeticFunction hiding id

namespace GaloisForLFunctions.RestrictedFactorizationCalculus

/-- Positive integers in (T,2T] with every prime factor at most y. -/
def smoothQuotientInterval (y T : ℕ) :=
  (Ioc T (2*T)).filter (fun n => n.primeFactors ⊆ Nat.primesLE y)

private theorem base_smooth_interval {y T : ℕ} (small : 2*T ≤ y) :
    (smoothQuotientInterval y T).card=T := by
  have full : smoothQuotientInterval y T=Ioc T (2*T) := by
    apply filter_eq_self.mpr
    intro n hn p hp
    obtain ⟨lo,hi⟩ := mem_Ioc.mp hn
    exact Nat.mem_primesLE.mpr ⟨(Nat.le_of_dvd (Nat.zero_lt_of_lt lo)
      (Nat.dvd_of_mem_primeFactors hp)).trans (hi.trans small),Nat.prime_of_mem_primeFactors hp⟩
  rw [full,Nat.card_Ioc]
  omega

/-- At sufficiently large s the entire band (s,s²] has reciprocal
mass at least half its limiting value. -/
private theorem mass_for_smooth_multiplication :
    ∀ᶠ s : ℕ in atTop,Real.log 2/2 ≤ ∑ p ∈ bigPrimeSet s (s^2),1/(p:ℝ) := by
  let C := 2*mertensFirstConst+1/2
  have logtop : Tendsto (fun s : ℕ => Real.log (s:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop (2:ℕ),logtop.eventually_ge_atTop (4*|C|/Real.log 2)]
    with s hs bound
  have one : (1:ℝ)<s := by exact_mod_cast (show 1<s by omega)
  have pos := Real.log_pos one
  have log2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  have sq : s ≤ s^2 := by simpa only [pow_two] using Nat.le_mul_of_pos_left s (by omega)
  have bound' := (div_le_iff₀ log2).mp bound
  have err : |C|/Real.log s ≤ Real.log 2/4 := (div_le_iff₀ pos).mpr (by linarith only [bound'])
  have ls : Real.log ((s^2:ℕ):ℝ)=2*Real.log s := by rw [Nat.cast_pow,Real.log_pow]; norm_num
  have step := sum_inv_bigPrimeSet_ge_sharp hs sq
  change logLog (s^2)-logLog s-(C/Real.log ((s^2:ℕ):ℝ)+C/Real.log s) ≤ _ at step
  simp only [logLog,ls,Real.log_mul (by norm_num : (2:ℝ)≠0) pos.ne',add_sub_cancel_right] at step
  have oneErr : C/(2*Real.log s) ≤ |C|/Real.log s :=
    (div_le_div_of_nonneg_right (le_abs_self C) (by positivity)).trans
      (div_le_div_of_nonneg_left (abs_nonneg C) pos (by linarith only [pos]))
  have twoErr := div_le_div_of_nonneg_right (le_abs_self C) pos.le
  linarith only [step,oneErr,twoErr,err]

private theorem smooth_prime_multiplicity {s j n : ℕ} (hs : 2 ≤ s) (hn : 0<n) (size : n ≤ s^j) :
    ((bigPrimeSet s (s^2)).filter (· ∣ n)).card ≤ j := by
  let A := (bigPrimeSet s (s^2)).filter (· ∣ n)
  have sub : A ⊆ n.primeFactors := fun p hp => Nat.mem_primeFactors.mpr
    ⟨prime_of_mem_bigPrimeSet (mem_filter.mp hp).1,(mem_filter.mp hp).2,hn.ne'⟩
  have dvd := (prod_dvd_prod_of_subset A n.primeFactors id sub).trans (Nat.prod_primeFactors_dvd n)
  have power : s^A.card ≤ ∏ p ∈ A,p := by
    rw [←prod_const]
    exact prod_le_prod' (fun p hp => ((mem_Icc.mp (mem_filter.mp (mem_filter.mp hp).1).1).1).le)
  exact (pow_right_strictMono₀ (by omega : 1<s)).le_iff_le.mp (power.trans ((Nat.le_of_dvd hn dvd).trans size))

private theorem smooth_row_count {s T : ℕ} (p : ℕ) (hp : p ∈ bigPrimeSet s (s^2)) :
    (smoothQuotientInterval (2*s^2) (T/p)).card ≤
      ((smoothQuotientInterval (2*s^2) T).filter (p ∣ ·)).card := by
  -- A floor at the lower wall is exact for integer multiples.
  have pr := prime_of_mem_bigPrimeSet hp
  have pmax := (mem_Icc.mp (mem_filter.mp hp).1).2
  apply card_le_card_of_injOn (fun m => p*m)
  · intro m hm
    obtain ⟨hi,smooth⟩ := mem_filter.mp hm
    obtain ⟨lo,up⟩ := mem_Ioc.mp hi
    have lower : T<p*m := (Nat.div_lt_iff_lt_mul pr.pos).mp lo |>.trans_eq (mul_comm ..)
    have upper : p*m ≤ 2*T := calc
      p*m ≤ p*(2*(T/p)) := Nat.mul_le_mul_left _ up
      _ = 2*(p*(T/p)) := by ring
      _ ≤ _ := Nat.mul_le_mul_left 2 (Nat.mul_div_le ..)
    refine mem_filter.mpr ⟨mem_filter.mpr ⟨mem_Ioc.mpr ⟨lower,upper⟩,?_⟩,dvd_mul_right ..⟩
    rw [Nat.primeFactors_mul pr.ne_zero (Nat.zero_lt_of_lt lo).ne',pr.primeFactors]
    exact union_subset (singleton_subset_iff.mpr (Nat.mem_primesLE.mpr ⟨by omega,pr⟩)) smooth
  · intro _ _ _ _ eq
    exact Nat.eq_of_mul_eq_mul_left pr.pos eq

private theorem all_smooth_rows {s T j : ℕ} (hs : 2 ≤ s) (size : T ≤ s^j) :
    (∑ p ∈ bigPrimeSet s (s^2),(smoothQuotientInterval (2*s^2) (T/p)).card) ≤
      (j+1)*(smoothQuotientInterval (2*s^2) T).card := by
  let P := bigPrimeSet s (s^2)
  let I := smoothQuotientInterval (2*s^2) T
  have bound (n : ℕ) (hn : n ∈ I) : (P.filter (· ∣ n)).card ≤ j+1 := by
    obtain ⟨lo,hi⟩ := mem_Ioc.mp (mem_filter.mp hn).1
    apply smooth_prime_multiplicity hs (Nat.zero_lt_of_lt lo)
    rw [pow_succ,mul_comm]
    exact hi.trans (Nat.mul_le_mul hs size)
  have count : (∑ p ∈ P,(I.filter (p ∣ ·)).card)=∑ n ∈ I,(P.filter (· ∣ n)).card := by
    simp only [←sum_boole]
    rw [sum_comm]
  apply (sum_le_sum (fun p hp => smooth_row_count p hp)).trans
  change (∑ p ∈ P,(I.filter (p ∣ ·)).card) ≤ _
  rw [count]
  exact (sum_le_sum bound).trans_eq (by simp [mul_comm,I])

/-- For every fixed exponent j a positive fraction of every dyadic
quotient interval through sʲ has all its prime factors at most 2s².
The fraction is uniform in the lower wall, including walls below s. -/
theorem positive_smooth_population_at_all_polynomial_walls (j : ℕ) :
    ∃ c : ℝ,0<c ∧ ∀ᶠ s : ℕ in atTop,∀ T : ℕ,T ≤ s^j →
      c*T ≤ ((smoothQuotientInterval (2*s^2) T).card:ℝ) := by
  induction j with
  | zero =>
    refine ⟨1,zero_lt_one,?_⟩
    filter_upwards [eventually_ge_atTop (1:ℕ)] with s hs
    intro T ht
    rw [pow_zero] at ht
    have h : 1 ≤ s^2 := Nat.pow_pos hs _
    rw [base_smooth_interval (Nat.mul_le_mul_left 2 (ht.trans h)),one_mul]
  | succ j ih =>
    obtain ⟨c,hc,eventual⟩ := ih
    let δ := Real.log 2/2
    have hδ : 0<δ := half_pos (Real.log_pos (by norm_num))
    let C := min 1 (c*δ/(2*((j:ℝ)+2)))
    have hC : 0<C := lt_min zero_lt_one (div_pos (mul_pos hc hδ) (by positivity))
    refine ⟨C,hC,?_⟩
    filter_upwards [eventual,mass_for_smooth_multiplication,eventually_ge_atTop (2:ℕ)] with s prev mass hs
    intro T ht
    by_cases small : T ≤ s^2
    · rw [base_smooth_interval (Nat.mul_le_mul_left 2 small)]
      exact (mul_le_mul_of_nonneg_right (min_le_left ..) (Nat.cast_nonneg T)).trans_eq (one_mul _)
    let P := bigPrimeSet s (s^2)
    have row (p : ℕ) (hp : p ∈ P) : (c*T/2)*(1/(p:ℝ)) ≤
        ((smoothQuotientInterval (2*s^2) (T/p)).card:ℝ) := by
      have pr := prime_of_mem_bigPrimeSet hp
      obtain ⟨sp,pp⟩ := mem_Icc.mp (mem_filter.mp hp).1
      have divT : T/p ≤ s^j := by
        have m := Nat.mul_div_le T p
        by_contra! high
        have more := Nat.mul_lt_mul_of_pos_left high pr.pos
        have less := Nat.mul_le_mul_right (s^j) sp.le
        rw [pow_succ,mul_comm] at ht
        omega
      have bound := prev (T/p) divT
      have unit : 1 ≤ T/p := (Nat.le_div_iff_mul_le pr.pos).mpr (by simpa only [one_mul] using pp.trans (Nat.le_of_not_ge small))
      have twice : T ≤ 2*(p*(T/p)) := by
        have rem := Nat.mod_add_div T p
        have hr := Nat.mod_lt T pr.pos
        have gain := Nat.mul_le_mul_left p unit
        omega
      have pr0 : (0:ℝ)<p := Nat.cast_pos.mpr pr.pos
      have natbound : (T:ℝ) ≤ 2*((p:ℝ)*((T/p:ℕ):ℝ)) := by exact_mod_cast twice
      apply LE.le.trans _ bound
      rw [mul_one_div,div_le_iff₀ pr0]
      linarith only [mul_le_mul_of_nonneg_left natbound hc.le]
    have lower := (mul_le_mul_of_nonneg_left mass (by positivity : 0 ≤ c*T/2)).trans
      (by rw [mul_sum]; exact sum_le_sum row)
    have upper := (Nat.cast_le (α := ℝ)).mpr (all_smooth_rows hs ht)
    push_cast only [Nat.cast_sum,Nat.cast_mul,Nat.cast_succ] at upper
    have finish : (c*δ/(2*((j:ℝ)+2)))*T ≤ ((smoothQuotientInterval (2*s^2) T).card:ℝ) := by
      rw [div_mul_eq_mul_div,div_le_iff₀ (by positivity)]
      change c*T/2*δ ≤ _ at lower
      linarith only [lower,upper]
    exact (mul_le_mul_of_nonneg_right (min_le_right ..) (Nat.cast_nonneg T)).trans finish

/-- The log-weighted size of the entire smooth prefix is at most
T(log y+C). At the complementary prime powers the reciprocal Mangoldt
tail is absolutely bounded. -/
theorem uniform_logarithmic_upper_bound_for_smooth_population :
    ∃ C : ℝ,0<C ∧ ∀ y T : ℕ,1 ≤ y →
      ((smoothUpTo (Nat.primesLE y) T).card:ℝ)*Real.log T ≤ (T:ℝ)*(Real.log y+C) := by
  let L := 8+RHTower.Mertens.mertensTail
  let A := (Real.log 4+4)+L
  have Lpos : 0 ≤ L := by
    have h := RHTower.Mertens.tail_bounded 0
    simpa only [Icc_eq_empty_of_lt (by decide : 0<1),sum_empty] using h
  refine ⟨A+L+1,by dsimp only [A]; positivity,?_⟩
  intro y T hy
  let I := Icc 1 T
  let S := smoothUpTo (Nat.primesLE y) T
  let f := fun d : ℕ => (if d.Prime ∧ d ≤ y then Real.log d else 0)+RHTower.Mertens.notPrimeVonMangoldt d
  have pos (d : ℕ) : 0 ≤ f d := by
    dsimp only [f,RHTower.Mertens.notPrimeVonMangoldt]
    by_cases prime : d.Prime
    · simp only [prime,true_and,if_true,add_zero]
      split <;> first | exact Real.log_nonneg (Nat.one_le_cast.mpr prime.one_le) | exact le_rfl
    · simp only [prime,false_and,if_false,zero_add]; exact vonMangoldt_nonneg
  have sub : S ⊆ I := filter_subset ..
  have local (n : ℕ) (hn : n ∈ S) : Real.log n=∑ d ∈ n.divisors,f d := by
    rw [←(vonMangoldt_sum (n := n))]
    apply sum_congr rfl
    intro d hd
    by_cases prime : d.Prime
    · have hp := Nat.mem_primeFactors.mpr ⟨prime,(Nat.mem_divisors.mp hd).1,(Nat.mem_divisors.mp hd).2⟩
      have maxd := (Nat.mem_primesLE.mp ((mem_smoothUpTo.mp hn).2 hp)).1
      simp only [f,prime,maxd,and_self,if_true,RHTower.Mertens.notPrimeVonMangoldt,add_zero,vonMangoldt_apply_prime prime]
    · simp only [f,prime,false_and,if_false,RHTower.Mertens.notPrimeVonMangoldt,zero_add]
  have hyper : (∑ n ∈ I,∑ d ∈ n.divisors,f d)=∑ d ∈ I,f d*((T/d:ℕ):ℝ) := by
    have eq := RHTower.Sieve.sum_Icc_divisorsAntidiagonal_swap (fun d _ => f d) T
    simpa only [Nat.sum_divisorsAntidiagonal,sum_const,nsmul_eq_mul,mul_comm _ (f _),Nat.card_Icc,Nat.add_sub_cancel] using eq
  have coarse := sum_le_sum_of_subset_of_nonneg sub (fun n _ _ => sum_nonneg (fun d _ => pos d))
  rw [hyper,←sum_congr rfl local] at coarse
  have per (d : ℕ) (_ : d ∈ I) : f d*((T/d:ℕ):ℝ) ≤ (T:ℝ)*(f d/d) :=
    (mul_le_mul_of_nonneg_left Nat.cast_div_le (pos d)).trans_eq (by ring)
  have summed := sum_le_sum per
  rw [←mul_sum] at summed
  let P := (Icc 1 y).filter Nat.Prime
  have primePrice : (∑ d ∈ I,(if d.Prime ∧ d ≤ y then Real.log d else 0)/(d:ℝ)) ≤
      ∑ d ∈ P,Real.log d/(d:ℝ) := by
    let J := I.filter (fun d => d.Prime ∧ d ≤ y)
    have cost : (∑ d ∈ I,(if d.Prime ∧ d ≤ y then Real.log d else 0)/(d:ℝ))=
        ∑ d ∈ J,Real.log d/(d:ℝ) := by
      rw [sum_filter]; apply sum_congr rfl; intro d _
      by_cases h : d.Prime ∧ d ≤ y <;> simp only [h,if_true,if_false,zero_div]
    rw [cost]
    apply sum_le_sum_of_subset_of_nonneg
    · intro d hd
      obtain ⟨hi,hp,dy⟩ := mem_filter.mp hd
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨(mem_Icc.mp hi).1,dy⟩,hp⟩
    · intro d hd _
      exact div_nonneg (Real.log_nonneg (Nat.one_le_cast.mpr (mem_filter.mp hd).2.one_le)) (Nat.cast_nonneg d)
  have primeBound := (abs_le.mp (RHTower.Mertens.mertens_first_prime y hy)).2
  have total : (∑ d ∈ I,f d/(d:ℝ)) ≤ Real.log y+A+L := by
    simp only [f,add_div,sum_add_distrib]
    have prime : (∑ d ∈ P,Real.log d/(d:ℝ))-Real.log y ≤ A := primeBound
    linarith only [prime,primePrice,RHTower.Mertens.tail_bounded T]
  have charge := (coarse.trans summed).trans (mul_le_mul_of_nonneg_left total (Nat.cast_nonneg T))
  have variation : (∑ n ∈ S,(Real.log T-Real.log n)) ≤ T := by
    have lo := RHTower.Mertens.sum_log_ge T
    have bigger := sum_le_sum_of_subset_of_nonneg sub (fun n hi _ => sub_nonneg.mpr
      (Real.log_le_log (Nat.cast_pos.mpr (mem_Icc.mp hi).1) (Nat.cast_le.mpr (mem_Icc.mp hi).2)))
    change _ ≤ ∑ n ∈ Icc 1 T,(Real.log T-Real.log n) at bigger
    rw [sum_sub_distrib,sum_const,nsmul_eq_mul,Nat.card_Icc,Nat.add_sub_cancel] at bigger
    linarith only [bigger,lo]
  rw [sum_sub_distrib,sum_const,nsmul_eq_mul] at variation
  change (S.card:ℝ)*Real.log T ≤ _
  linarith only [variation,charge]

#print axioms uniform_logarithmic_upper_bound_for_smooth_population

#print axioms positive_smooth_population_at_all_polynomial_walls

end GaloisForLFunctions.RestrictedFactorizationCalculus
