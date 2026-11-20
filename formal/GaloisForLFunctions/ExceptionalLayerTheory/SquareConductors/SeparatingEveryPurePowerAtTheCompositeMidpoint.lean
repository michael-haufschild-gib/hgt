import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheOddSmoothCompositesAtThePrimeMidpoint
import Mathlib.NumberTheory.Chebyshev

/-!
# Resolving the full logarithmic price of excluded prime powers

Prime powers of exponent j contribute j times the ordinary-prime
prefix at the j-th root of the cutoff, after dropping primes dividing
the center. The discarded primes cost at most log n per unweighted row.
An explicit truncation error is uniform in the center and the height.
-/

noncomputable section
open Finset Filter
open scoped Topology
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

def coprimeTheta (n : ℕ) (x : ℝ) :=
  ∑ p ∈ (Ioc 0 ⌊x⌋₊).filter Nat.Prime, if n.Coprime p then Real.log p else 0

def fullLogProperPrefix (n : ℕ) (x : ℝ) := ∑ k ∈ Ioc 0 ⌊x⌋₊, purePowerLog n k

/-- Dropping the prime divisors of n costs at most the logarithm of their
squarefree product, hence at most log n, at every height. -/
theorem coprime_theta_loss {n : ℕ} (hn : 0<n) (x : ℝ) :
    0≤Chebyshev.theta x-coprimeTheta n x ∧ Chebyshev.theta x-coprimeTheta n x≤Real.log n := by
  let S := (Ioc 0 ⌊x⌋₊).filter Nat.Prime
  have he : Chebyshev.theta x-coprimeTheta n x=∑ p ∈ S.filter (fun p => ¬n.Coprime p), Real.log p := by
    rw [sum_filter]
    unfold Chebyshev.theta coprimeTheta
    rw [←sum_sub_distrib]
    apply sum_congr rfl
    intro p _
    by_cases h : n.Coprime p
    · rw [if_pos h,if_neg (not_not_intro h),sub_self]
    · rw [if_neg h,if_pos h,sub_zero]
  rw [he]
  have hsub : S.filter (fun p => ¬n.Coprime p)⊆n.primeFactors := by
    intro p hp
    obtain ⟨h,hh⟩ := mem_filter.mp hp
    have hprime := (mem_filter.mp h).2
    refine Nat.mem_primeFactors.mpr ⟨hprime,?_,hn.ne'⟩
    by_contra hd
    exact hh (hprime.coprime_iff_not_dvd.mpr hd).symm
  refine ⟨sum_nonneg (fun p _ => Real.log_natCast_nonneg _),?_⟩
  apply (sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => Real.log_natCast_nonneg p)).trans
  have hprod := prod_pos (s:=n.primeFactors) (fun p hp => (Nat.prime_of_mem_primeFactors hp).pos)
  have h := Real.log_le_log (Nat.cast_pos.mpr hprod) (Nat.cast_le.mpr (Nat.le_of_dvd hn (Nat.prod_primeFactors_dvd n)))
  rwa [Nat.cast_prod,Real.log_prod (fun p hp => Nat.cast_ne_zero.mpr (Nat.prime_of_mem_primeFactors hp).ne_zero)] at h

private theorem coprime_theta_nonneg (n : ℕ) (x : ℝ) : 0≤coprimeTheta n x :=
  sum_nonneg fun p _ => by split <;> first | exact Real.log_natCast_nonneg p | exact le_rfl

/-- Exact separation by exponent. The weight is the logarithm of the
power itself, so the j-th row carries the multiplicity factor j. -/
theorem full_log_proper_power_rows (n : ℕ) {x : ℝ} (hx : 0≤x) (H : ℕ)
    (hH : ⌊Real.log x/Real.log 2⌋₊≤H) :
    fullLogProperPrefix n x=∑ j ∈ Icc 2 H, (j:ℝ)*coprimeTheta n (x^(1/(j:ℝ))) := by
  classical
  have he : fullLogProperPrefix n x=∑ k ∈ (Ioc 0 ⌊x⌋₊).filter IsPrimePow, purePowerLog n k := by
    rw [sum_filter,fullLogProperPrefix]
    apply sum_congr rfl
    intro k _
    by_cases h : IsPrimePow k
    · rw [if_pos h]
    · have h' : k.primeFactors.card≠1 := fun he => h (isPrimePow_iff_card_primeFactors_eq_one.mpr he)
      simp [h,purePowerLog,h']
  rw [he,Chebyshev.sum_PrimePow_eq_sum_sum' _ hx hH]
  have hr : Icc 2 H=(Icc 1 H).filter (fun j : ℕ => 2≤j) := by ext j; simp; omega
  rw [hr,sum_filter]
  refine sum_congr rfl fun j hj => ?_
  have hj₁ := (mem_Icc.mp hj).1
  by_cases hj₂ : 2≤j
  · rw [if_pos hj₂,coprimeTheta,mul_sum]
    apply sum_congr rfl
    intro p hp
    have h := (mem_filter.mp hp).2
    have hcard : (p^j).primeFactors.card=1 := by
      rw [Nat.primeFactors_prime_pow (by omega : j ≠ 0) h,card_singleton]
    have hnp : ¬(p^j).Prime := Nat.Prime.not_prime_pow hj₂
    by_cases hc : n.Coprime p
    · have hcp : n.Coprime (p^j) := (Nat.coprime_pow_right_iff hj₁ n p).mpr hc
      have hs : n.Coprime (p^j) ∧ ¬(p^j).Prime ∧ (p^j).primeFactors.card=1 := ⟨hcp,hnp,hcard⟩
      rw [purePowerLog,if_pos hs,if_pos hc,Nat.cast_pow,Real.log_pow]
    · have hcp : ¬n.Coprime (p^j) := fun ht => hc ((Nat.coprime_pow_right_iff hj₁ n p).mp ht)
      have hs : ¬(n.Coprime (p^j) ∧ ¬(p^j).Prime ∧ (p^j).primeFactors.card=1) := fun ht => hcp ht.1
      rw [purePowerLog,if_neg hs,if_neg hc,mul_zero]
  · obtain rfl : j=1 := by omega
    rw [if_neg hj₂]
    apply sum_eq_zero
    intro p hp
    simp [purePowerLog,(mem_filter.mp hp).2]

private theorem row_sum_bound {s : Finset ℕ} {N : ℕ} (hcard : s.card≤N)
    {B : ℝ} (hB : 0≤B) {f : ℕ → ℝ} (hf : ∀ j∈s, f j≤(N:ℝ)*B) :
    ∑ j ∈ s, f j ≤ (N:ℝ)^2*B := by
  have h := sum_le_sum hf
  rw [sum_const,nsmul_eq_mul] at h
  exact h.trans ((mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcard) (mul_nonneg (Nat.cast_nonneg _) hB)).trans_eq (by ring))

/-- The first J root-scale prime prefixes determine the proper-power
price up to the contribution from centers dividing n and a tail of
order x^(1/(J+1)) with at most two logarithms. -/
theorem full_log_proper_power_truncation {n J H : ℕ} (hn : 0<n) (hJ : 2≤J) (hJH : J≤H)
    {x : ℝ} (hx : 1≤x) (hH : ⌊Real.log x/Real.log 2⌋₊≤H) :
    |fullLogProperPrefix n x-∑ j ∈ Icc 2 J, (j:ℝ)*Chebyshev.theta (x^(1/(j:ℝ)))| ≤
      (J:ℝ)^2*Real.log n+(H:ℝ)^2*(Real.log 4*x^(1/((J:ℝ)+1))) := by
  let f := fun j : ℕ => (j:ℝ)*coprimeTheta n (x^(1/(j:ℝ)))
  let e := fun j : ℕ => (j:ℝ)*(Chebyshev.theta (x^(1/(j:ℝ)))-coprimeTheta n (x^(1/(j:ℝ))))
  let T := Real.log 4*x^(1/((J:ℝ)+1))
  have ht : 0≤T := mul_nonneg (Real.log_nonneg (by norm_num)) (Real.rpow_nonneg (zero_le_one.trans hx) _)
  have hien : ∀ j : ℕ, 0≤e j := fun j => mul_nonneg (Nat.cast_nonneg _) (coprime_theta_loss hn _).1
  have hfn : ∀ j : ℕ, 0≤f j := fun j => mul_nonneg (Nat.cast_nonneg _) (coprime_theta_nonneg n _)
  have hlow : ∑ j ∈ Icc 2 J, e j≤(J:ℝ)^2*Real.log n := by
    apply row_sum_bound (by rw [Nat.card_Icc]; omega) (Real.log_natCast_nonneg n)
    intro j hj
    exact mul_le_mul (Nat.cast_le.mpr (mem_Icc.mp hj).2) (coprime_theta_loss hn _).2
      (coprime_theta_loss hn _).1 (Nat.cast_nonneg _)
  have hhigh : ∑ j ∈ Ioc J H, f j≤(H:ℝ)^2*T := by
    apply row_sum_bound (by rw [Nat.card_Ioc]; omega) ht
    intro j hj
    have hlo := (mem_Ioc.mp hj).1
    have hj' : (J:ℝ)+1≤j := by exact_mod_cast hlo
    have he := one_div_le_one_div_of_le (by positivity : 0<(J:ℝ)+1) hj'
    have hb := (Chebyshev.theta_le_log4_mul_x (Real.rpow_nonneg (zero_le_one.trans hx) (1/(j:ℝ)))).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx he) (Real.log_nonneg (by norm_num : (1:ℝ)≤4)))
    exact mul_le_mul (Nat.cast_le.mpr (mem_Ioc.mp hj).2) ((sub_nonneg.mp (coprime_theta_loss hn _).1).trans hb)
      (coprime_theta_nonneg _ _) (Nat.cast_nonneg _)
  have decomp : fullLogProperPrefix n x-∑ j ∈ Icc 2 J, (j:ℝ)*Chebyshev.theta (x^(1/(j:ℝ))) =
      (∑ j ∈ Ioc J H, f j)-∑ j ∈ Icc 2 J, e j := by
    rw [full_log_proper_power_rows _ (zero_le_one.trans hx) H hH]
    change (∑ j ∈ Icc 2 H, f j)-_ = _
    have hset : Icc 2 H=Icc 2 J ∪ Ioc J H := by ext j; simp; omega
    have dis : Disjoint (Icc 2 J) (Ioc J H) := disjoint_left.mpr (fun _ hj ht => (mem_Ioc.mp ht).1.not_ge (mem_Icc.mp hj).2)
    have head : (∑ j ∈ Icc 2 J, (j:ℝ)*Chebyshev.theta (x^(1/(j:ℝ)))) =
        (∑ j ∈ Icc 2 J, f j)+∑ j ∈ Icc 2 J, e j := by
      rw [←sum_add_distrib]
      exact sum_congr rfl fun j _ => by dsimp only [e,f]; ring
    rw [hset,sum_union dis,head]
    ring
  rw [decomp,abs_le]
  have hn₁ := sum_nonneg (s:=Icc 2 J) fun j _ => hien j
  have hn₂ := sum_nonneg (s:=Ioc J H) fun j _ => hfn j
  change _ ∧ _≤(J:ℝ)^2*Real.log n+(H:ℝ)^2*T
  constructor <;> linarith only [hlow,hhigh,hn₁,hn₂]

/-- A fixed truncation admits every exponent strictly above the next
root scale. Two logarithms from the number of rows are absorbed in the
strict gap, uniformly over the cutoff and the coprimality center. -/
theorem uniform_full_log_truncation {J : ℕ} (hJ : 2≤J) {b : ℝ} (hb : 1/((J:ℝ)+1)<b) :
    ∃ C : ℝ, 0≤C ∧ ∀ n : ℕ, 0<n → ∀ x : ℝ, 1≤x →
      |fullLogProperPrefix n x-∑ j ∈ Icc 2 J, (j:ℝ)*Chebyshev.theta (x^(1/(j:ℝ)))| ≤
        (J:ℝ)^2*Real.log n+C*x^b := by
  let r := 1/((J:ℝ)+1)
  let d := (b-r)/2
  have hd : 0<d := half_pos (sub_pos.mpr hb)
  have hl : 0<Real.log 2 := Real.log_pos (by norm_num)
  let B := max (J:ℝ) (1/d/Real.log 2)
  have hjB : (J:ℝ)≤B := le_max_left _ _
  have hB : 0≤B := (Nat.cast_nonneg J).trans hjB
  refine ⟨B^2*Real.log 4,mul_nonneg (sq_nonneg _) (Real.log_nonneg (by norm_num)),fun n hn x hx => ?_⟩
  let H := max J ⌊Real.log x/Real.log 2⌋₊
  have h := full_log_proper_power_truncation hn hJ (le_max_left J _) hx (le_max_right J _)
  have hx0 := zero_lt_one.trans_le hx
  have hxpow := Real.rpow_nonneg hx0.le d
  have hH : (H:ℝ)≤B*x^d := by
    change ((max J ⌊Real.log x/Real.log 2⌋₊:ℕ):ℝ)≤_
    rw [Nat.cast_max]
    refine max_le (hjB.trans (le_mul_of_one_le_right hB (Real.one_le_rpow hx hd.le))) ?_
    apply (Nat.floor_le (div_nonneg (Real.log_nonneg hx) hl.le)).trans
    calc Real.log x/Real.log 2 ≤ (x^d/d)/Real.log 2 :=
           div_le_div_of_nonneg_right (Real.log_le_rpow_div hx0.le hd) hl.le
         _ = (1/d/Real.log 2)*x^d := by ring
         _ ≤ B*x^d := mul_le_mul_of_nonneg_right (le_max_right _ _) hxpow
  have hbound := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) hH 2)
    (mul_nonneg (Real.log_nonneg (by norm_num : (1:ℝ)≤4)) (Real.rpow_nonneg hx0.le r))
  have hpow : (x^d)^2*x^r=x^b := by
    rw [←Real.rpow_natCast _ 2,←Real.rpow_mul hx0.le,←Real.rpow_add hx0]
    congr 1
    dsimp only [d]
    push_cast
    ring
  have heq : (B*x^d)^2*(Real.log 4*x^r)=B^2*Real.log 4*x^b := by
    rw [←hpow,mul_pow]
    ring
  exact h.trans (add_le_add le_rfl (hbound.trans_eq heq))

/-- At the square row the full-log prime-power prefix equals twice the
ordinary-prime prefix at the square root, with a power-saving error
uniform in both the cutoff and the coprimality center. -/
theorem uniform_square_prefix_of_full_logs :
    ∃ C : ℝ, 0≤C ∧ ∀ n : ℕ, 0<n → ∀ x : ℝ, 1≤x →
      |fullLogProperPrefix n x-2*Chebyshev.theta (Real.sqrt x)|≤4*Real.log n+C*x^(5/12:ℝ) := by
  simpa only [Icc_self,sum_singleton,Nat.cast_ofNat,Real.sqrt_eq_rpow,show (2:ℝ)^2=4 by norm_num] using
    (uniform_full_log_truncation (J:=2) (by decide) (b:=5/12) (by norm_num))

#print axioms uniform_full_log_truncation
#print axioms full_log_proper_power_rows
#print axioms full_log_proper_power_truncation
#print axioms uniform_square_prefix_of_full_logs

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
