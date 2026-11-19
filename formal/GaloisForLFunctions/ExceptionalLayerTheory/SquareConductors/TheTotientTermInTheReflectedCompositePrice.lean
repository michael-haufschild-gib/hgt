import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.ThePrimeMidpointInTwoAdjacentGcdHorizons
import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheSmallPrimeFactorsOfTheReflectedComposites
import GaloisForLFunctions.RHTower.Sieve.DivisorBound
import GaloisForLFunctions.RHTower.Sieve.TotientMoebiusNormalisation
import GaloisForLFunctions.RHTower.Sieve.SelbergInversion
import GaloisForLFunctions.RHTower.HarmonicStirlingExactBounds

/-!
# The totient term in the reflected composite price

Both intervals have endpoints divisible by the modulus. Möbius inversion
therefore gives a factorial ratio at integer arguments on each divisor.
Its linear term sums to a totient and its constant term cancels.
-/

noncomputable section
open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- Mean log price of moving a uniform integer from (2,3] to (3,4]. -/
def reflectedDensity : ℝ := 10 * Real.log 2 - 6 * Real.log 3

private def logPrefix (n : ℕ) : ℝ := ∑ a ∈ Icc 1 n, Real.log a

private def coprimeLogPrefix (n T : ℕ) : ℝ :=
  ∑ a ∈ (Icc 1 T).filter (n.Coprime ·), Real.log a

private def factorialGap (h : ℕ) : ℝ := logPrefix (4*h)-2*logPrefix (3*h)+logPrefix (2*h)

/-- Signed log price on all coprime integers, right interval minus left. -/
def reflectedCoprimePrice (n : ℕ) : ℝ :=
  coprimeLogPrefix n (4*n) - 2*coprimeLogPrefix n (3*n) + coprimeLogPrefix n (2*n)

/-- Signed log price on coprime composites, right interval minus left. -/
def reflectedCompositePrice (n : ℕ) : ℝ :=
  (∑ a ∈ (Ioc (3*n) (4*n)).filter (fun a => n.Coprime a ∧ ¬a.Prime), Real.log a) -
  (∑ a ∈ (Ioc (2*n) (3*n)).filter (fun a => n.Coprime a ∧ ¬a.Prime), Real.log a)

private theorem coprime_log_prefix (n T : ℕ) (hn : 0 < n) :
    coprimeLogPrefix n T =
      ∑ d ∈ n.divisors, (μ d : ℝ) * (((T/d : ℕ) : ℝ) * Real.log d + logPrefix (T/d)) := by
  classical
  have detector (a : ℕ) :
      (if n.Coprime a then (1:ℝ) else 0)=∑ d ∈ n.divisors, if d ∣ a then (μ d:ℝ) else 0 := by
    rw [←sum_filter]
    have hset : n.divisors.filter (· ∣ a) = (n.gcd a).divisors := by
      ext d
      simp only [mem_filter,Nat.mem_divisors,Nat.dvd_gcd_iff]
      exact ⟨fun h => ⟨⟨h.1.1,h.2⟩,(Nat.gcd_pos_of_pos_left a hn).ne'⟩,
        fun h => ⟨⟨h.1.1,hn.ne'⟩,h.1.2⟩⟩
    rw [hset,_root_.RHTower.Sieve.sum_divisors_moebius_real]
  rw [coprimeLogPrefix,sum_filter]
  calc _ = ∑ a ∈ Icc 1 T, ∑ d ∈ n.divisors, if d ∣ a then (μ d:ℝ)*Real.log a else 0 := by
             apply sum_congr rfl
             intro a _
             rw [show (if n.Coprime a then Real.log (a:ℝ) else 0)=
               (if n.Coprime a then (1:ℝ) else 0)*Real.log a by split_ifs <;> simp,
               detector,sum_mul]
             exact sum_congr rfl fun d _ => by split_ifs <;> simp
       _ = _ := by
             rw [sum_comm]
             apply sum_congr rfl
             intro d hd
             have hd0 := Nat.pos_of_mem_divisors hd
             rw [←sum_filter,_root_.RHTower.Sieve.sum_filter_dvd_eq_sum_scaled hd0, mul_add,logPrefix,mul_sum]
             have he (j : ℕ) (hj : j ∈ Icc 1 (T/d)) :
                 (μ d:ℝ)*Real.log (d*j:ℕ)=(μ d:ℝ)*Real.log d+(μ d:ℝ)*Real.log j := by
               have hj0 := (mem_Icc.mp hj).1
               rw [Nat.cast_mul,Real.log_mul (by positivity) (by positivity),mul_add]
             rw [sum_congr rfl he,sum_add_distrib,sum_const,nsmul_eq_mul,Nat.card_Icc]
             simp only [Nat.add_one_sub_one]
             ring

private theorem reflected_divisors {n : ℕ} (hn : 0 < n) :
    reflectedCoprimePrice n = ∑ d ∈ n.divisors, (μ d:ℝ)*factorialGap (n/d) := by
  simp only [reflectedCoprimePrice,coprime_log_prefix _ _ hn,mul_sum,←sum_sub_distrib,←sum_add_distrib]
  apply sum_congr rfl
  intro d hd
  have hdiv (k : ℕ) : k*n/d=k*(n/d) := Nat.mul_div_assoc k (Nat.dvd_of_mem_divisors hd)
  simp only [hdiv,Nat.cast_mul,Nat.cast_ofNat,factorialGap]
  ring

private def gapConstant : ℝ := (Real.log 4-2*Real.log 3+Real.log 2)/2

private theorem factorial_gap_error {h : ℕ} (hh : 0 < h) :
    |factorialGap h - reflectedDensity*h - gapConstant| ≤ 1 / (h:ℝ) := by
  let main (k : ℕ) := (k:ℝ)*Real.log k-k+Real.log k/2+Real.log (2*Real.pi)/2
  have herr (k : ℕ) (hk : 0 < k) :
      0 ≤ logPrefix k-main k ∧ logPrefix k-main k ≤ 1/(12*(k:ℝ)) := by
    obtain ⟨hl,hu⟩ := _root_.RHTower.sum_log_Icc_exact_stirling_bounds hk
    exact ⟨sub_nonneg.mpr hl,by dsimp only [logPrefix,main]; linarith only [hu]⟩
  have he (k : ℕ) (hk : 0 < k) : Real.log (k*h:ℕ)=Real.log k+Real.log h := by
    rw [Nat.cast_mul,Real.log_mul (by positivity) (by positivity)]
  have hlog : Real.log 4=2*Real.log 2 := by
    rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow]; norm_num
  have hm : main (4*h)-2*main (3*h)+main (2*h)=reflectedDensity*h+gapConstant := by
    dsimp only [main,reflectedDensity,gapConstant]
    rw [he 4 (by decide),he 3 (by decide),he 2 (by decide)]
    push_cast
    rw [hlog]
    ring
  obtain ⟨l2,u2⟩ := herr (2*h) (by omega)
  obtain ⟨l3,u3⟩ := herr (3*h) (by omega)
  obtain ⟨l4,u4⟩ := herr (4*h) (by omega)
  have hcap (k : ℕ) (hk : 1 ≤ k) : 1/(12*((k*h:ℕ):ℝ)) ≤ (1/(h:ℝ))/4 := by
    rw [Nat.cast_mul,div_div]
    apply one_div_le_one_div_of_le (by positivity)
    have hk' : (1:ℝ) ≤ k := by exact_mod_cast hk
    nlinarith only [mul_le_mul_of_nonneg_right hk' (Nat.cast_nonneg (α:=ℝ) h)]
  rw [factorialGap,abs_le]
  constructor <;> linarith only [l2,u2.trans (hcap 2 (by decide)),l3,u3.trans (hcap 3 (by decide)),
    l4,u4.trans (hcap 4 (by decide)),hm]

/-- Uniform sharp-endpoint normalization. The remaining bound is a
sum of reciprocal integer scales over the squarefree divisors. -/
theorem reflected_coprime_price_totient {n : ℕ} (hn : 1 < n) :
    |reflectedCoprimePrice n-reflectedDensity*n.totient| ≤
      ∑ d ∈ n.divisors, |(μ d:ℝ)| / ((n/d:ℕ):ℝ) := by
  have hn0 : 0 < n := by omega
  have hzero := _root_.RHTower.Sieve.sum_divisors_moebius_real n
  rw [if_neg (by omega : n ≠ 1)] at hzero
  have he : reflectedCoprimePrice n-reflectedDensity*n.totient =
      ∑ d ∈ n.divisors,(μ d:ℝ)*(factorialGap (n/d)-reflectedDensity*(n/d:ℕ)-gapConstant) := by
    rw [reflected_divisors hn0,_root_.RHTower.Sieve.totient_eq_sum_moebius_mul n hn0]
    simp only [mul_sub,sum_sub_distrib,←sum_mul,mul_sum]
    rw [hzero,zero_mul,sub_zero]
    congr 1
    exact sum_congr rfl fun d _ => by ring
  rw [he]
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro d hd
  have hd0 := Nat.pos_of_mem_divisors hd
  have hh := Nat.div_pos (Nat.le_of_dvd hn0 (Nat.dvd_of_mem_divisors hd)) hd0
  rw [abs_mul,div_eq_mul_one_div]
  exact mul_le_mul_of_nonneg_left (factorial_gap_error hh) (abs_nonneg _)

/-- Every prime in the two intervals is coprime to the center. Splitting
the primitive log price therefore recovers the midpoint product exactly. -/
theorem prime_midpoint_eq_reflected_composites {n : ℕ} (hn : 1 < n) :
    primeMidpointPrice n=reflectedCompositePrice n-reflectedCoprimePrice n := by
  let f (a : ℕ) : ℝ := if n.Coprime a then Real.log a else 0
  have interval (a b : ℕ) (hab : a ≤ b) :
      (∑ k ∈ Ioc a b,f k)=coprimeLogPrefix n b-coprimeLogPrefix n a := by
    have hi (x : ℕ) : Icc 1 x=Ioc 0 x := by ext j; simp only [mem_Icc,mem_Ioc]; omega
    simp only [coprimeLogPrefix,sum_filter,hi]
    linarith only [sum_Ioc_consecutive f (Nat.zero_le a) hab]
  have split (a b : ℕ) (ha : n ≤ a) :
      (∑ k ∈ Ioc a b,f k) = (∑ k ∈ (Ioc a b).filter Nat.Prime,Real.log k) +
        (∑ k ∈ (Ioc a b).filter (fun k => n.Coprime k ∧ ¬k.Prime),Real.log k) := by
    simp only [sum_filter,←sum_add_distrib]
    apply sum_congr rfl
    intro k hk
    by_cases hp : k.Prime
    · have hcop : n.Coprime k := (hp.coprime_iff_not_dvd.mpr (fun hd =>
          (ha.trans_lt (mem_Ioc.mp hk).1).not_ge (Nat.le_of_dvd (by omega) hd))).symm
      simp [f,hp,hcop]
    · simp [f,hp]
  dsimp only [primeMidpointPrice,reflectedCompositePrice,reflectedCoprimePrice]
  linarith only [interval (2*n) (3*n) (by omega),interval (3*n) (4*n) (by omega),
    split (2*n) (3*n) (by omega),split (3*n) (4*n) (by omega)]

/-- The centered log price of the coprime composites retains the ordinary
prime midpoint to subpower error at every integer endpoint. -/
theorem reflected_composite_price_error {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {n : ℕ}, 1 < n →
      |reflectedCompositePrice n-reflectedDensity*n.totient-primeMidpointPrice n| ≤ C*(n:ℝ)^ε := by
  refine ⟨|_root_.RHTower.Sieve.divisorBoundConst ε|,abs_nonneg _,?_⟩
  intro n hn
  have h := reflected_coprime_price_totient hn
  rw [prime_midpoint_eq_reflected_composites hn,
    show reflectedCompositePrice n-reflectedDensity*n.totient-(reflectedCompositePrice n-reflectedCoprimePrice n)=
      reflectedCoprimePrice n-reflectedDensity*n.totient by ring]
  apply h.trans
  calc _ ≤ ∑ _ ∈ n.divisors, (1:ℝ) := by
          apply sum_le_sum
          intro d hd
          have hq : 0 < n/d := Nat.div_pos (Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_divisors hd))
            (Nat.pos_of_mem_divisors hd)
          apply (div_le_self (abs_nonneg _) (Nat.one_le_cast.mpr hq)).trans
          exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
       _ = (n.divisors.card:ℝ) := by simp
       _ ≤ _ := (_root_.RHTower.Sieve.card_divisors_le_rpow hε (by omega : n ≠ 0)).trans
          (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))

/-- One upper comparison of the actual coprime composite price with its
totient density has the exact abscissa of the ordinary zeta zeros. -/
theorem reflected_composite_upper_spectrum_iff {b : ℝ} (hb : 1/2 ≤ b) :
    (∀ t : ℝ,b < t → t < 1 → ∃ C : ℝ,∀ n : ℕ,1 < n →
      reflectedCompositePrice n-reflectedDensity*n.totient ≤ C*(n:ℝ)^t) ↔
      _root_.RHTower.zetaZeroAbscissa ≤ b := by
  rw [←prime_midpoint_upper_spectrum_iff hb]
  constructor
  · intro h t ht ht1
    obtain ⟨A,hA⟩ := h t ht ht1
    obtain ⟨D,hD,hd⟩ := reflected_composite_price_error (show 0<t by linarith only [hb,ht])
    refine ⟨max (primeMidpointPrice 1) (A+D),fun n hn => ?_⟩
    rcases eq_or_lt_of_le hn with h1 | h1
    · subst n
      simpa only [Nat.cast_one,Real.one_rpow,mul_one] using le_max_left (primeMidpointPrice 1) (A+D)
    · apply le_trans _ (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (Nat.cast_nonneg n) t))
      rw [add_mul]
      linarith only [(abs_le.mp (hd h1)).1,hA n h1]
  · intro h t ht ht1
    obtain ⟨A,hA⟩ := h t ht ht1
    obtain ⟨D,hD,hd⟩ := reflected_composite_price_error (show 0<t by linarith only [hb,ht])
    refine ⟨A+D,fun n hn => ?_⟩
    rw [add_mul]
    linarith only [(abs_le.mp (hd hn)).2,hA n hn.le]

#print axioms reflected_composite_price_error
#print axioms reflected_composite_upper_spectrum_iff

#print axioms reflected_coprime_price_totient
#print axioms prime_midpoint_eq_reflected_composites

private theorem complete_factor_price (n : ℕ) :
    smallMidpointFactorPrice n (4*n)=reflectedCoprimePrice n := by
  let f (a : ℕ) : ℝ := if n.Coprime a then Real.log a else 0
  have hterm {a : ℕ} (ha : 0 < a) (hT : a ≤ 4*n) :
      coprimeSmallFactorLog n (4*n) a=f a := by
    classical
    by_cases hc : n.Coprime a
    · have he : (Icc 1 (4*n)).filter (· ∣ a)=a.divisors := by
        ext d
        simp only [mem_filter,mem_Icc,Nat.mem_divisors]
        exact ⟨fun hh => ⟨hh.2,ha.ne'⟩,fun hd => ⟨⟨Nat.pos_of_dvd_of_pos hd.1 ha,
          (Nat.le_of_dvd ha hd.1).trans hT⟩,hd.1⟩⟩
      change (∑ q ∈ Icc 1 (4*n),if n.Coprime a ∧ q ∣ a then vonMangoldt q else 0)=
        if n.Coprime a then Real.log a else 0
      rw [if_pos hc]
      calc _ = ∑ q ∈ Icc 1 (4*n), if q ∣ a then vonMangoldt q else 0 := by
                 apply sum_congr rfl
                 intro q _
                 by_cases hq : q ∣ a
                 · rw [if_pos ⟨hc,hq⟩,if_pos hq]
                 · rw [if_neg (fun h => hq h.2),if_neg hq]
           _ = _ := by rw [←sum_filter,he,vonMangoldt_sum]
    · simp [coprimeSmallFactorLog,f,hc]
  have hi (T : ℕ) : coprimeLogPrefix n T=∑ a ∈ Ioc 0 T,f a := by
    rw [coprimeLogPrefix,sum_filter,show Icc 1 T=Ioc 0 T by ext a; simp only [mem_Icc,mem_Ioc]; omega]
  have hsum (a b : ℕ) (hb : b ≤ 4*n) :
      (∑ k ∈ Ioc a b,coprimeSmallFactorLog n (4*n) k)=∑ k ∈ Ioc a b,f k := by
    apply sum_congr rfl
    intro k hk
    exact hterm (lt_of_le_of_lt (Nat.zero_le _) (mem_Ioc.mp hk).1) ((mem_Ioc.mp hk).2.trans hb)
  rw [small_midpoint_factor_price_eq_intervals,hsum _ _ (by omega),hsum _ _ (by omega)]
  simp only [reflectedCoprimePrice,hi]
  linarith only [sum_Ioc_consecutive f (Nat.zero_le (2*n)) (show 2*n ≤ 3*n by omega),
    sum_Ioc_consecutive f (Nat.zero_le (3*n)) (show 3*n ≤ 4*n by omega)]

/-- Logarithms of ordinary factors above P in the coprime composites,
counted over the exact cofactor intervals with the unit cofactor removed. -/
def largePrimeCofactorPrice (n P : ℕ) : ℝ :=
  ∑ p ∈ (Ioc P (4*n)).filter Nat.Prime, Real.log p * properCofactorMidpoint n p

private theorem prime_singleton_price {n P : ℕ} (hP : P ≤ 2*n) :
    (∑ p ∈ (Ioc P (4*n)).filter Nat.Prime,Real.log p *
      ((if p ∈ Ioc (3*n) (4*n) then (1:ℝ) else 0) -
       (if p ∈ Ioc (2*n) (3*n) then (1:ℝ) else 0))) = -primeMidpointPrice n := by
  let S := (Ioc P (4*n)).filter Nat.Prime
  have cost (a b : ℕ) (hPa : P ≤ a) (hb : b ≤ 4*n) :
      (∑ p ∈ S, Real.log p*(if p ∈ Ioc a b then (1:ℝ) else 0)) =
        ∑ p ∈ (Ioc a b).filter Nat.Prime,Real.log p := by
    have he : S.filter (· ∈ Ioc a b)=(Ioc a b).filter Nat.Prime := by
      ext p
      simp only [S,mem_filter,mem_Ioc]
      exact ⟨fun h => ⟨h.2,h.1.2⟩,fun h => ⟨⟨⟨hPa.trans_lt h.1.1,h.1.2.trans hb⟩,h.2⟩,h.1⟩⟩
    calc _ = ∑ p ∈ S, if p ∈ Ioc a b then Real.log p else 0 := by
               exact sum_congr rfl fun p _ => by split_ifs <;> simp
         _ = _ := by rw [←sum_filter,he]
  change (∑ p ∈ S,_) = _
  simp only [mul_sub,sum_sub_distrib,cost _ _ (by omega : P ≤ 3*n) (le_refl (4*n)),
    cost _ _ hP (by omega : 3*n ≤ 4*n),primeMidpointPrice]
  ring

/-- Exact remaining cost after removing the small factors. The only
further omission from the ordinary cofactor sum is the proper powers. -/
theorem large_prime_cofactor_price_exact {n P : ℕ} (hn : 0 < n) (hP : P ≤ 2*n) :
    largePrimeCofactorPrice n P-reflectedCoprimePrice n-primeMidpointPrice n =
      -(smallMidpointFactorPrice n P +
        ∑ q ∈ (Ioc P (4*n)).filter (fun q => ¬q.Prime),vonMangoldt q*coprimeMidpointMultipleCount n q) := by
  classical
  let f (q : ℕ) := vonMangoldt q*coprimeMidpointMultipleCount n q
  let S := (Ioc P (4*n)).filter Nat.Prime
  have small (k : ℕ) : smallMidpointFactorPrice n k = ∑ q ∈ Ioc 0 k,f q := by
    rw [smallMidpointFactorPrice,show Icc 1 k=Ioc 0 k by ext q; simp only [mem_Icc,mem_Ioc]; omega]
  have ht := sum_Ioc_consecutive f (Nat.zero_le P) (show P ≤ 4*n by omega)
  rw [←small,←small,complete_factor_price] at ht
  have hs := sum_filter_add_sum_filter_not (Ioc P (4*n)) Nat.Prime f
  have hc : (∑ p ∈ S,f p)=largePrimeCofactorPrice n P-primeMidpointPrice n := by
    rw [sub_eq_add_neg,←prime_singleton_price hP]
    dsimp only [largePrimeCofactorPrice]
    rw [←sum_add_distrib]
    apply sum_congr rfl
    intro p hp
    have hpr := (mem_filter.mp hp).2
    rw [f,vonMangoldt_apply_prime hpr,prime_midpoint_count_split hn hpr,mul_add]
  change (∑ p ∈ (Ioc P (4*n)).filter Nat.Prime, f p)=_ at hc
  change _ = -(smallMidpointFactorPrice n P + ∑ q ∈ (Ioc P (4*n)).filter (fun q => ¬q.Prime),f q)
  linarith only [ht,hs,hc]

#print axioms large_prime_cofactor_price_exact

/-- The entire remaining error costs only the small Mangoldt mass,
the proper-power mass, and the primitive log-density discrepancy. -/
theorem large_prime_cofactor_centering {n P : ℕ} (hn : 1 < n) (hP : P ≤ 2*n) :
    |largePrimeCofactorPrice n P-reflectedDensity*n.totient-primeMidpointPrice n| ≤
      (7*(P:ℝ)+(Chebyshev.psi (4*n:ℕ)-Chebyshev.theta (4*n:ℕ))+1)*squarefreeDivisorMass n := by
  have hn0 : 0 < n := by omega
  let S := (Ioc P (4*n)).filter (fun q => ¬q.Prime)
  have hS : S ⊆ (Ioc 0 (4*n)).filter (fun q => ¬q.Prime) := by
    intro q hq
    obtain ⟨hi,hpr⟩ := mem_filter.mp hq
    obtain ⟨hl,hu⟩ := mem_Ioc.mp hi
    exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨by omega,hu⟩,hpr⟩
  let R := ∑ q ∈ S,vonMangoldt q*coprimeMidpointMultipleCount n q
  have hr : |R| ≤ (Chebyshev.psi (4*n:ℕ)-Chebyshev.theta (4*n:ℕ))*squarefreeDivisorMass n :=
    midpoint_selected_proper_power_price hn0 S hS
  have hs : |smallMidpointFactorPrice n P| ≤ (7*(P:ℝ))*squarefreeDivisorMass n :=
    abs_small_midpoint_factor_price hn0 P
  have hb : |reflectedCoprimePrice n-reflectedDensity*n.totient| ≤ squarefreeDivisorMass n := by
    apply (reflected_coprime_price_totient hn).trans
    apply sum_le_sum
    intro d hd
    have hq := Nat.div_pos (Nat.le_of_dvd hn0 (Nat.dvd_of_mem_divisors hd)) (Nat.pos_of_mem_divisors hd)
    exact div_le_self (abs_nonneg _) (Nat.one_le_cast.mpr hq)
  have he := large_prime_cofactor_price_exact hn0 hP
  change _ = -(smallMidpointFactorPrice n P+R) at he
  rw [show largePrimeCofactorPrice n P-reflectedDensity*n.totient-primeMidpointPrice n =
      (reflectedCoprimePrice n-reflectedDensity*n.totient)-(smallMidpointFactorPrice n P+R) by linarith only [he]]
  have tri (x y : ℝ) : |x-y| ≤ |x|+|y| := by
    simpa only [sub_zero,zero_sub,abs_neg] using abs_sub_le x 0 y
  apply (tri _ _).trans ((add_le_add hb ((abs_add_le _ _).trans (add_le_add hs hr))).trans_eq ?_)
  ring

/-- At every power endpoint the omitted prime factors and proper powers
are paid on the cofactor mesh scale. -/
theorem large_prime_cofactor_price_on_powers {r : ℕ} (hr : 2 ≤ r) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℕ, 2 ≤ u →
      |largePrimeCofactorPrice (u^r) (u^(r-1))-reflectedDensity*(u^r).totient-primeMidpointPrice (u^r)| ≤
        C*(u^(r-1):ℕ)*(u:ℝ)^ε := by
  have ht : 0 < ε/(r:ℝ) := div_pos hε (Nat.cast_pos.mpr (by omega))
  obtain ⟨A,hA⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  let D := |_root_.RHTower.Sieve.divisorBoundConst (ε/(r:ℝ))|
  refine ⟨(8+2*|A|)*D,by dsimp only [D]; positivity,?_⟩
  intro u hu
  have hu0 : 0 < u := by omega
  let P := u^(r-1)
  let n := u^r
  have hn : 1 < n := one_lt_pow₀ (show 1<u by omega) (by omega)
  have he : P*u=n := by dsimp only [P,n]; rw [←pow_succ,show r-1+1=r by omega]
  have hPu : u ≤ P := by
    change u ≤ u^(r-1)
    simpa only [pow_one] using (Nat.pow_le_pow_right hu0 (show 1 ≤ r-1 by omega))
  have hPpos : 0 < P := pow_pos hu0 _
  have hPn : P ≤ n := by rw [←he]; exact Nat.le_mul_of_pos_right P hu0
  have hPs : (n:ℝ) ≤ (P:ℝ)^2 := by
    exact_mod_cast (show n ≤ P^2 by rw [←he,sq]; exact Nat.mul_le_mul_left P hPu)
  have hsq : Real.sqrt (4*n:ℕ) ≤ 2*(P:ℝ) := by
    rw [Nat.cast_mul,Nat.cast_ofNat,Real.sqrt_mul (by norm_num : (0:ℝ)≤4),show Real.sqrt 4=2 by norm_num]
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_iff.mpr ⟨Nat.cast_nonneg _,hPs⟩) (by norm_num)
  have hproper := (hA ((4*n:ℕ):ℝ)).trans (mul_le_mul (le_abs_self A) hsq (Real.sqrt_nonneg _) (abs_nonneg _))
  have hK : 7*(P:ℝ)+(Chebyshev.psi (4*n:ℕ)-Chebyshev.theta (4*n:ℕ))+1 ≤ (8+2*|A|)*P := by
    linarith only [hproper,(Nat.one_le_cast (α:=ℝ)).mpr hPpos]
  have hd := _root_.RHTower.Sieve.card_divisors_le_rpow ht (by omega : n ≠ 0)
  have hmass : squarefreeDivisorMass n ≤ D*(u:ℝ)^ε := by
    have hm := sum_le_sum (s:=n.divisors) (fun d _ =>
      (show |(μ d:ℝ)| ≤ 1 by exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n:=d)))
    simp only [sum_const,nsmul_eq_mul,mul_one] at hm
    rw [show n=u^r by rfl,Nat.cast_pow,←Real.rpow_natCast (u:ℝ) r,←Real.rpow_mul (Nat.cast_nonneg _),
      show (r:ℝ)*(ε/(r:ℝ))=ε by field_simp] at hd
    exact (hm.trans hd).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  apply (large_prime_cofactor_centering hn (by omega : P ≤ 2*n)).trans
  apply (mul_le_mul hK hmass (sum_nonneg fun _ _ => abs_nonneg _) (by positivity)).trans_eq
  ring

#print axioms large_prime_cofactor_centering
#print axioms large_prime_cofactor_price_on_powers

/-- The squared large-prime cut is obtained at b = 1/2; larger b moves
the same cut while retaining the signed cofactor intervals. -/
def reflectedPrimeCut (b : ℝ) (n : ℕ) : ℕ := ⌊2*(n:ℝ)^b⌋₊

/-- A prime above the power cut has cofactor strictly less than
2 n^(1-b), with no endpoint loss from integer rounding. -/
theorem cofactor_below_reflected_prime_cut {b : ℝ} {n p v : ℕ} (hn : 0 < n)
    (hp : reflectedPrimeCut b n < p) (hv : p*v ≤ 4*n) :
    (v:ℝ) < 2*(n:ℝ)^(1-b) := by
  have hn' : 0 < (n:ℝ) := Nat.cast_pos.mpr hn
  have hr : 0 < (n:ℝ)^b := Real.rpow_pos_of_pos hn' _
  have hp' : 2*(n:ℝ)^b < p := (Nat.floor_lt (by positivity)).mp hp
  have ht : (2*(n:ℝ)^(1-b))*(2*(n:ℝ)^b)=4*n := by
    rw [show 2*(n:ℝ)^(1-b)*(2*(n:ℝ)^b)=4*((n:ℝ)^(1-b)*(n:ℝ)^b) by ring,
      ←Real.rpow_add hn',sub_add_cancel,Real.rpow_one]
  by_cases hv0 : v=0
  · subst v; positivity
  have hlow := mul_lt_mul_of_pos_left hp' (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hv0))
  have hu : (p:ℝ)*v ≤ 4*n := by exact_mod_cast hv
  apply (mul_lt_mul_iff_left₀ (show 0 < 2*(n:ℝ)^b by positivity)).mp
  rw [ht]
  linarith only [hlow,hu]

/-- For every integer center, removing all ordinary prime factors up to
2 n^b costs at most n^(b+ε) in the centered joint price. At b=1/2 the
large prime is unique, and at b=5/6 only cofactors below 2 n^(1/6) remain. -/
theorem all_endpoint_large_cofactor_error {b ε : ℝ} (hb : 1/2 ≤ b) (hb1 : b ≤ 1) (hε : 0 < ε) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ n : ℕ, 1 < n →
      |largePrimeCofactorPrice n (reflectedPrimeCut b n)-reflectedDensity*n.totient-primeMidpointPrice n| ≤
        A*(n:ℝ)^(b+ε) := by
  obtain ⟨C,hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  let D := |_root_.RHTower.Sieve.divisorBoundConst ε|
  refine ⟨(15+2*|C|)*D,by dsimp only [D]; positivity,?_⟩
  intro n hn
  have hn0 : 0 < n := by omega
  have h1 := (Nat.one_le_cast (α:=ℝ)).mpr hn0
  have hpow : 1 ≤ (n:ℝ)^b := Real.one_le_rpow h1 (by linarith only [hb])
  have hcut : (reflectedPrimeCut b n:ℝ) ≤ 2*(n:ℝ)^b := Nat.floor_le (by positivity)
  have hlin : (n:ℝ)^b ≤ n := by simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le h1 hb1
  have hcap : reflectedPrimeCut b n ≤ 2*n := by
    have h : (reflectedPrimeCut b n:ℝ) ≤ 2*n := by linarith only [hcut,hlin]
    exact_mod_cast h
  have hs : Real.sqrt (4*n:ℕ) ≤ 2*(n:ℝ)^b := by
    rw [Nat.cast_mul,Nat.cast_ofNat,Real.sqrt_mul (by norm_num : (0:ℝ)≤4),show Real.sqrt 4=2 by norm_num,
      Real.sqrt_eq_rpow]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le h1 hb) (by norm_num)
  have hc := (hC ((4*n:ℕ):ℝ)).trans (mul_le_mul (le_abs_self C) hs (Real.sqrt_nonneg _) (abs_nonneg _))
  have hm : squarefreeDivisorMass n ≤ D*(n:ℝ)^ε := by
    have hh := sum_le_sum (s:=n.divisors) fun d _ =>
      (show |(μ d:ℝ)| ≤ 1 by exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n:=d))
    simp only [sum_const,nsmul_eq_mul,mul_one] at hh
    exact (hh.trans (_root_.RHTower.Sieve.card_divisors_le_rpow hε hn0.ne')).trans
      (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  have hcost : 7*(reflectedPrimeCut b n:ℝ)+(Chebyshev.psi (4*n:ℕ)-Chebyshev.theta (4*n:ℕ))+1 ≤
      (15+2*|C|)*(n:ℝ)^b := by linarith only [hcut,hpow,hc]
  apply (large_prime_cofactor_centering hn hcap).trans
  apply (mul_le_mul hcost hm (sum_nonneg fun _ _ => abs_nonneg _) (by positivity)).trans_eq
  rw [Real.rpow_add (Nat.cast_pos.mpr hn0)]
  ring

#print axioms cofactor_below_reflected_prime_cut
#print axioms all_endpoint_large_cofactor_error

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
