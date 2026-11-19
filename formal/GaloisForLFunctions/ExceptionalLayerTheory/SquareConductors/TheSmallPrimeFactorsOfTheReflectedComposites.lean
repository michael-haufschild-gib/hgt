import GaloisForLFunctions.RHTower.Sieve.CoprimeCounting
import GaloisForLFunctions.RHTower.Sieve.DivisorBound
import GaloisForLFunctions.RHTower.ZetaSymbolArchimedeanHorizon

/-!
# Small prime factors in the two coprime composite intervals

For each fixed prime power, Möbius inversion of the coprime cofactor
count leaves one difference of counts in adjacent intervals of equal
length. Every divisor contributes at most one endpoint.
-/

noncomputable section
open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

private def coprimePrefix (n k : ℕ) : ℝ :=
  (((Icc 1 k).filter (fun j => n.Coprime j)).card : ℝ)

/-- Multiples of q coprime to n in the right interval (3n,4n] minus
those in the left interval (2n,3n]. -/
def coprimeMidpointMultipleCount (n q : ℕ) : ℝ :=
  if n.Coprime q then
    coprimePrefix n (4*n/q)-2*coprimePrefix n (3*n/q)+coprimePrefix n (2*n/q) else 0

private def midpointDivision (n v : ℕ) : ℝ :=
  ((4*n/v:ℕ):ℝ)-2*((3*n/v:ℕ):ℝ)+((2*n/v:ℕ):ℝ)

private theorem division_gap {v : ℕ} (hv : 0 < v) (x n : ℕ) :
    (x+n)/v=x/v+n/v ∨ (x+n)/v=x/v+n/v+1 := by
  rw [Nat.add_div hv]
  split_ifs <;> omega

theorem abs_midpoint_division_le_one {v : ℕ} (hv : 0 < v) (n : ℕ) :
    |midpointDivision n v| ≤ 1 := by
  have h2 := division_gap hv (2*n) n
  have h3 := division_gap hv (3*n) n
  rw [show 2*n+n=3*n by omega] at h2
  rw [show 3*n+n=4*n by omega] at h3
  dsimp only [midpointDivision]
  rcases h3 with h | h <;> rw [h] <;> rcases h2 with h | h <;> rw [h] <;>
    push_cast <;> rw [abs_le] <;> constructor <;> linarith

/-- Exact divisor inversion at the three endpoints of one cofactor row. -/
theorem coprime_multiple_midpoint_inversion {n q : ℕ} (hn : 0 < n) (hcop : n.Coprime q) :
    coprimeMidpointMultipleCount n q=∑ d ∈ n.divisors,(μ d:ℝ)*midpointDivision n (q*d) := by
  rw [coprimeMidpointMultipleCount,if_pos hcop]
  simp only [coprimePrefix,_root_.RHTower.Sieve.coprimeCount_eq_sum_divisors hn,Nat.div_div_eq_div_mul,
    mul_sum,←sum_sub_distrib,←sum_add_distrib]
  exact sum_congr rfl fun d _ => by dsimp only [midpointDivision]; ring

private theorem real_abs_mu_le_one (d : ℕ) : |(μ d:ℝ)| ≤ 1 := by
  exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)

/-- Number of squarefree divisors, written as the absolute Möbius mass. -/
def squarefreeDivisorMass (n : ℕ) : ℝ := ∑ d ∈ n.divisors, |(μ d:ℝ)|

private theorem midpoint_count_bound {n q : ℕ} (hn : 0 < n) (hq : 0 < q) :
    |coprimeMidpointMultipleCount n q| ≤ squarefreeDivisorMass n := by
  by_cases hc : n.Coprime q
  · rw [coprime_multiple_midpoint_inversion hn hc]
    apply (abs_sum_le_sum_abs _ _).trans
    apply sum_le_sum
    intro d hd
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (abs_midpoint_division_le_one (Nat.mul_pos hq (Nat.pos_of_mem_divisors hd)) n)
  · simp only [coprimeMidpointMultipleCount,if_neg hc,abs_zero,squarefreeDivisorMass]
    exact sum_nonneg fun d _ => abs_nonneg _

/-- Absolute endpoint cost of any one divisor row, with its original sign
and primitive modulus. -/
theorem abs_coprime_midpoint_multiple_count {n q : ℕ} (hn : 0 < n) (hq : 0 < q) :
    |coprimeMidpointMultipleCount n q| ≤ ∑ d ∈ n.divisors, |(μ d:ℝ)| :=
  midpoint_count_bound hn hq

/-- Signed log price of all factors through P in the two coprime intervals. -/
def smallMidpointFactorPrice (n P : ℕ) : ℝ :=
  ∑ q ∈ Icc 1 P, vonMangoldt q*coprimeMidpointMultipleCount n q

/-- Each prime power through P costs at most one endpoint per squarefree
divisor of the center. The estimate is uniform in the prime cutoff. -/
theorem abs_small_midpoint_factor_price {n : ℕ} (hn : 0 < n) (P : ℕ) :
    |smallMidpointFactorPrice n P| ≤ (7*(P:ℝ))*∑ d ∈ n.divisors, |(μ d:ℝ)| := by
  apply (abs_sum_le_sum_abs _ _).trans
  calc (∑ q ∈ Icc 1 P,|vonMangoldt q*coprimeMidpointMultipleCount n q|) ≤
        ∑ q ∈ Icc 1 P,vonMangoldt q*squarefreeDivisorMass n := by
          apply sum_le_sum
          intro q hq
          rw [abs_mul,abs_of_nonneg vonMangoldt_nonneg]
          exact mul_le_mul_of_nonneg_left (midpoint_count_bound hn (mem_Icc.mp hq).1) vonMangoldt_nonneg
       _ ≤ _ := by
         rw [←sum_mul]
         exact mul_le_mul_of_nonneg_right (_root_.RHTower.sum_vonMangoldt_Icc_le_seven P) (sum_nonneg fun _ _ => abs_nonneg _)

/-- At centers u^r the small factors cost O(P u^ε), including the
original partial terminal and the prime-power factors. -/
theorem small_midpoint_factor_price_on_powers {r : ℕ} (hr : 0 < r) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, ∀ {u : ℕ}, 0 < u → ∀ P : ℕ, |smallMidpointFactorPrice (u^r) P| ≤ C*(P:ℝ)*(u:ℝ)^ε := by
  have hrr : 0 < (r:ℝ) := Nat.cast_pos.mpr hr
  let t := ε/(r:ℝ)
  have ht : 0 < t := div_pos hε hrr
  refine ⟨7*_root_.RHTower.Sieve.divisorBoundConst t,?_⟩
  intro u hu P
  have hn := pow_pos hu r
  have hcost := abs_small_midpoint_factor_price hn P
  have hm := sum_le_sum (s := (u^r).divisors) (fun d _ => real_abs_mu_le_one d)
  simp only [sum_const,nsmul_eq_mul,mul_one] at hm
  have hd := _root_.RHTower.Sieve.card_divisors_le_rpow ht hn.ne'
  rw [Nat.cast_pow,←Real.rpow_natCast (u:ℝ) r,←Real.rpow_mul (Nat.cast_nonneg _),
    show (r:ℝ)*t=ε by dsimp only [t]; field_simp] at hd
  exact hcost.trans ((mul_le_mul_of_nonneg_left (hm.trans hd) (by positivity)).trans_eq (by ring))

#print axioms coprime_multiple_midpoint_inversion
#print axioms abs_small_midpoint_factor_price
#print axioms small_midpoint_factor_price_on_powers

private theorem coprime_quotient_count {n q : ℕ} (hq : 0 < q) (T : ℕ) :
    (((Icc 1 T).filter (fun a => n.Coprime a ∧ q ∣ a)).card : ℝ) =
      if n.Coprime q then coprimePrefix n (T/q) else 0 := by
  classical
  by_cases h : n.Coprime q
  · rw [if_pos h]
    apply Nat.cast_inj.mpr
    apply card_nbij' (fun a => a/q) (fun j => q*j)
    · intro a ha
      obtain ⟨haI,hc,hd⟩ := mem_filter.mp ha
      have hmul : q*(a/q)=a := Nat.mul_div_cancel' hd
      have ha1 := (mem_Icc.mp haI).1
      rw [←hmul,Nat.coprime_mul_iff_right] at hc
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd ha1 hd) hq,
        Nat.div_le_div_right (mem_Icc.mp haI).2⟩,hc.2⟩
    · intro j hj
      obtain ⟨hjI,hcj⟩ := mem_filter.mp hj
      have hlow := Nat.mul_pos hq (mem_Icc.mp hjI).1
      have hhigh := (Nat.le_div_iff_mul_le hq).mp (mem_Icc.mp hjI).2
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hlow,by simpa only [Nat.mul_comm] using hhigh⟩,
        Nat.coprime_mul_iff_right.mpr ⟨h,hcj⟩,dvd_mul_right _ _⟩
    · intro a ha
      exact Nat.mul_div_cancel' (mem_filter.mp ha).2.2
    · intro j _
      exact Nat.mul_div_cancel_left j hq
  · rw [if_neg h,show (Icc 1 T).filter (fun a => n.Coprime a ∧ q ∣ a)=∅ by
        apply filter_eq_empty_iff.mpr
        intro a _ ha
        exact h (ha.1.of_dvd_right ha.2)]
    simp

/-- The logarithms from the selected small prime powers in one integer
of the coprime intervals. -/
def coprimeSmallFactorLog (n P a : ℕ) : ℝ :=
  ∑ q ∈ Icc 1 P,if n.Coprime a ∧ q ∣ a then vonMangoldt q else 0

private theorem coprime_small_factor_prefix (n P T : ℕ) :
    (∑ a ∈ Icc 1 T,coprimeSmallFactorLog n P a)=
      ∑ q ∈ Icc 1 P,vonMangoldt q*(if n.Coprime q then coprimePrefix n (T/q) else 0) := by
  classical
  rw [show (∑ a ∈ Icc 1 T,coprimeSmallFactorLog n P a)=
      ∑ q ∈ Icc 1 P,∑ a ∈ Icc 1 T, if n.Coprime a ∧ q ∣ a then vonMangoldt q else 0 by
    rw [sum_comm]; rfl]
  apply sum_congr rfl
  intro q hq
  rw [←sum_filter,sum_const,nsmul_eq_mul,coprime_quotient_count (mem_Icc.mp hq).1 T,mul_comm]

/-- The small-factor estimate is the actual signed difference across both
sharp integer intervals, including every endpoint multiple. -/
theorem small_midpoint_factor_price_eq_intervals (n P : ℕ) :
    smallMidpointFactorPrice n P=(∑ a ∈ Ioc (3*n) (4*n),coprimeSmallFactorLog n P a)-
      (∑ a ∈ Ioc (2*n) (3*n),coprimeSmallFactorLog n P a) := by
  have hi (u v : ℕ) (huv : u ≤ v) :
      (∑ a ∈ Ioc u v,coprimeSmallFactorLog n P a)=
        (∑ a ∈ Icc 1 v,coprimeSmallFactorLog n P a)-(∑ a ∈ Icc 1 u,coprimeSmallFactorLog n P a) := by
    have hs (w : ℕ) : Icc 1 w=Ioc 0 w := by ext a; simp only [mem_Icc,mem_Ioc]; omega
    simp only [hs]
    linarith only [sum_Ioc_consecutive (coprimeSmallFactorLog n P) (Nat.zero_le u) huv]
  rw [hi _ _ (by omega),hi _ _ (by omega)]
  simp only [coprime_small_factor_prefix,smallMidpointFactorPrice,←sum_sub_distrib]
  apply sum_congr rfl
  intro q _
  rw [coprimeMidpointMultipleCount]
  split_ifs <;> ring

/-- On a prime in the two intervals, the selected factors vanish up to
the left endpoint. Hence that entire signed price comes from composites. -/
theorem coprime_small_factor_log_on_prime {n P a : ℕ} (hsmall : P ≤ 2*n)
    (ha : 2*n < a) (hp : a.Prime) : coprimeSmallFactorLog n P a=0 := by
  apply sum_eq_zero
  intro q hq
  split_ifs with h
  · rcases (Nat.dvd_prime hp).mp h.2 with hh | hh
    · simp [hh]
    · have := (mem_Icc.mp hq).2; omega
  · rfl

/-- The combined signed price of the proper powers, even after a
selection of powers, costs the square-root prime-power mass. -/
theorem midpoint_selected_proper_power_price {n : ℕ} (hn : 0 < n) (S : Finset ℕ)
    (hS : S ⊆ (Ioc 0 (4*n)).filter (fun q => ¬q.Prime)) :
    |∑ q ∈ S,vonMangoldt q*coprimeMidpointMultipleCount n q| ≤
      (Chebyshev.psi (4*n:ℕ)-Chebyshev.theta (4*n:ℕ))*∑ d ∈ n.divisors, |(μ d:ℝ)| := by
  apply (abs_sum_le_sum_abs _ _).trans
  calc _ ≤ ∑ q ∈ S,vonMangoldt q*squarefreeDivisorMass n := by
             apply sum_le_sum
             intro q hq
             have hq0 := (mem_Ioc.mp (mem_filter.mp (hS hq)).1).1
             rw [abs_mul,abs_of_nonneg vonMangoldt_nonneg]
             exact mul_le_mul_of_nonneg_left (midpoint_count_bound hn hq0) vonMangoldt_nonneg
       _ ≤ _ := by
         rw [←sum_mul,Chebyshev.psi_sub_theta_eq_sum_not_prime,Nat.floor_natCast]
         exact mul_le_mul_of_nonneg_right (sum_le_sum_of_subset_of_nonneg hS (fun _ _ _ => vonMangoldt_nonneg))
           (sum_nonneg fun _ _ => abs_nonneg _)

#print axioms small_midpoint_factor_price_eq_intervals
#print axioms coprime_small_factor_log_on_prime
#print axioms midpoint_selected_proper_power_price

private def properCofactorPrefix (n w : ℕ) : ℝ :=
  (((Icc 2 w).filter (n.Coprime ·)).card : ℝ)

private theorem split_unit_cofactor (n w : ℕ) :
    coprimePrefix n w = properCofactorPrefix n w + (if 1 ≤ w then 1 else 0) := by
  classical
  cases w with
  | zero => simp [coprimePrefix,properCofactorPrefix]
  | succ w =>
    have he : Icc 1 (w+1)=insert 1 (Icc 2 (w+1)) := by
      ext v
      simp only [mem_Icc,mem_insert]
      omega
    have hnot : 1 ∉ (Icc 2 (w+1)).filter (n.Coprime ·) := by simp
    simp [coprimePrefix,properCofactorPrefix,he,filter_insert,hnot]

/-- Right-minus-left count of the coprime multiples with cofactor at
least two. The upper cofactor endpoint in each prefix is included. -/
def properCofactorMidpoint (n q : ℕ) : ℝ :=
  if n.Coprime q then
    properCofactorPrefix n (4*n/q)-2*properCofactorPrefix n (3*n/q)+properCofactorPrefix n (2*n/q)
  else 0

/-- Removing the unit cofactor from an ordinary-prime row removes exactly
its signed singleton at the two adjacent sharp intervals. -/
theorem prime_midpoint_count_split {n p : ℕ} (hn : 0 < n) (hp : p.Prime) :
    coprimeMidpointMultipleCount n p = properCofactorMidpoint n p +
      ((if p ∈ Ioc (3*n) (4*n) then (1:ℝ) else 0) -
       (if p ∈ Ioc (2*n) (3*n) then (1:ℝ) else 0)) := by
  have hdiv (k : ℕ) : 1 ≤ k/p ↔ p ≤ k := by
    rw [Nat.le_div_iff_mul_le hp.pos,one_mul]
  simp only [coprimeMidpointMultipleCount,properCofactorMidpoint,split_unit_cofactor,hdiv,mem_Ioc]
  by_cases hc : n.Coprime p
  · simp only [if_pos hc]
    by_cases h2 : p ≤ 2*n
    · simp [h2,show p ≤ 3*n by omega,show p ≤ 4*n by omega,
        show ¬ 3*n < p by omega,show ¬ 2*n < p by omega]
      ring
    · by_cases h3 : p ≤ 3*n
      · simp [h2,h3,show p ≤ 4*n by omega,show ¬ 3*n < p by omega,
          show 2*n < p by omega]
        ring
      · by_cases h4 : p ≤ 4*n
        all_goals
          simp [h2,h3,h4,show 3*n < p by omega,show 2*n < p by omega]
          ring
  · have hpd : p ∣ n := by
      by_contra h
      exact hc (hp.coprime_iff_not_dvd.mpr h).symm
    have hpn := Nat.le_of_dvd hn hpd
    simp [hc,show ¬3*n < p by omega,show ¬2*n < p by omega]

#print axioms prime_midpoint_count_split

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
