import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheParityOfTheSmallUnitaryDivisors
import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.ThePrimeMidpointInTwoAdjacentGcdHorizons
import Mathlib.Data.Nat.Factorization.PrimePow

/-!
# The odd smooth composites opposite the large-prime source

The same signed intervals can be read on composites with an odd number
of distinct primes and no prime-power block above their square root.
The omitted pure powers cost the proper-power Chebyshev mass times one log.
-/

noncomputable section
open Finset ArithmeticFunction
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- The prime powers of a surviving composite all lie below its square root. -/
def oddSmoothSupport (k : ℕ) : Prop :=
  Odd k.primeFactors.card ∧ 3 ≤ k.primeFactors.card ∧
    ∀ p ∈ k.primeFactors, (p^k.factorization p)^2 < k

/-- Right interval minus left interval, with the shared endpoint on the left. -/
def unitarySignedIntervals (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  (∑ k ∈ Ioc (3*n) (4*n), f k) - ∑ k ∈ Ioc (2*n) (3*n), f k

private def unitaryLog (k : ℕ) : ℝ := (unitaryHalfWeight k:ℝ)*Real.log k

/-- All-integer log center, weighted by the signed small unitary divisors. -/
def unitaryMidpointCenter (n : ℕ) : ℝ :=
  unitarySignedIntervals (fun k => if n.Coprime k then unitaryLog k else 0) n

open Classical in
/-- Signed price on odd balanced composites, preserving coprimality at the midpoint. -/
def oddSmoothCompositePrice (n : ℕ) : ℝ :=
  unitarySignedIntervals (fun k => if n.Coprime k ∧ oddSmoothSupport k then unitaryLog k else 0) n

/-- Full log price of a primitive proper prime power. -/
def purePowerLog (n k : ℕ) : ℝ :=
  if n.Coprime k ∧ ¬k.Prime ∧ k.primeFactors.card=1 then Real.log k else 0

/-- A composite contributing to the odd smooth price is disjoint from every
product in the original intervals carrying a prime above the square-root cut. -/
theorem odd_smooth_has_no_large_prime {n k p : ℕ} (hk : k ≤ 4*n)
    (h : oddSmoothSupport k) (hp : p.Prime) (hd : p ∣ k) (hk0 : 0 < k) : p^2 < 4*n := by
  have hmem := Nat.mem_primeFactors.mpr ⟨hp,hd,hk0.ne'⟩
  have hd' := dvd_pow_self p (hp.factorization_pos_of_dvd hk0.ne' hd).ne'
  have hle := Nat.le_of_dvd (pow_pos hp.pos _) hd'
  exact (Nat.pow_le_pow_left hle 2).trans_lt ((h.2.2 p hmem).trans_le hk)

/-- Exact price on the complementary population at every integer midpoint.
The only extra term counts proper pure powers. -/
theorem odd_smooth_prime_midpoint_exact {n : ℕ} (hn : 1 ≤ n) :
    primeMidpointPrice n=oddSmoothCompositePrice n-unitaryMidpointCenter n+
      unitarySignedIntervals (purePowerLog n) n := by
  classical
  have interval (a b : ℕ) (ha : n ≤ a) :
      (∑ k ∈ Ioc a b,if n.Coprime k then unitaryLog k else 0) =
        (∑ k ∈ (Ioc a b).filter Nat.Prime,Real.log k) +
        (∑ k ∈ Ioc a b,if n.Coprime k ∧ oddSmoothSupport k then unitaryLog k else 0) +
        ∑ k ∈ Ioc a b,purePowerLog n k := by
    rw [sum_filter,←sum_add_distrib,←sum_add_distrib]
    apply sum_congr rfl
    intro k hk
    have hnk := ha.trans_lt (mem_Ioc.mp hk).1
    have hk1 : 1 < k := by omega
    by_cases hp : k.Prime
    · have hcop := (hp.coprime_iff_not_dvd.mpr (fun hd => hnk.not_ge (Nat.le_of_dvd hn hd))).symm
      have hno : ¬oddSmoothSupport k := fun hs => by
        have hcard := hs.2.1
        rw [hp.primeFactors,card_singleton] at hcard
        omega
      simp [unitaryLog,unitary_half_weight_singleton hk1 hp.primeFactors,purePowerLog,hp,hno,hcop]
    · by_cases hcop : n.Coprime k
      · by_cases hone : k.primeFactors.card=1
        · obtain ⟨p,hs⟩ := card_eq_one.mp hone
          have hno : ¬oddSmoothSupport k := fun h => by have := h.2.1; omega
          simp [unitaryLog,unitary_half_weight_singleton hk1 hs,purePowerLog,hp,hcop,hone,hno]
        · by_cases h : oddSmoothSupport k
          · simp [purePowerLog,hp,hcop,hone,h]
          · have hz : unitaryHalfWeight k=0 := by
              by_contra hw
              exact h (unitary_half_weight_support hk1 hw hone)
            simp [purePowerLog,unitaryLog,hp,hcop,hone,h,hz]
      · simp [purePowerLog,hp,hcop]
  unfold primeMidpointPrice oddSmoothCompositePrice unitaryMidpointCenter unitarySignedIntervals
  linarith only [interval (2*n) (3*n) (by omega),interval (3*n) (4*n) (by omega)]

/-- Proper powers can be removed uniformly even though their price uses
the full logarithm of the power and not just the logarithm of its base. -/
theorem odd_smooth_midpoint_error {n : ℕ} (hn : 1 ≤ n) :
    |oddSmoothCompositePrice n-unitaryMidpointCenter n-primeMidpointPrice n| ≤
      (Real.log (4*n:ℕ)/Real.log 2)*(Chebyshev.psi (4*n:ℕ)-Chebyshev.theta (4*n:ℕ)) := by
  let X := 4*n
  let L := Real.log (X:ℝ)/Real.log 2
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL : 0 ≤ L := div_nonneg (Real.log_natCast_nonneg _) hlog2.le
  have hnneg (k : ℕ) : 0 ≤ purePowerLog n k := by
    unfold purePowerLog
    split_ifs <;> first | exact Real.log_natCast_nonneg _ | rfl
  have point {k : ℕ} (hk : k ≤ X) :
      purePowerLog n k ≤ if ¬k.Prime then L*vonMangoldt k else 0 := by
    unfold purePowerLog
    split_ifs with h hnp hnp
    · have hpow := isPrimePow_iff_card_primeFactors_eq_one.mpr h.2.2
      have hk1 := hpow.one_lt
      have hp := (Nat.minFac_prime (by omega : k ≠ 1)).two_le
      have hl := Real.log_le_log (by norm_num : (0:ℝ)<2) (by exact_mod_cast hp : (2:ℝ) ≤ k.minFac)
      have hlk : Real.log k ≤ Real.log (X:ℝ) := Real.log_le_log
        (Nat.cast_pos.mpr (by omega)) (Nat.cast_le.mpr hk)
      rw [vonMangoldt_apply,if_pos hpow]
      apply hlk.trans
      calc Real.log (X:ℝ) = L*Real.log 2 := (div_mul_cancel₀ _ hlog2.ne').symm
           _ ≤ _ := mul_le_mul_of_nonneg_left hl hL
    · exact (hnp h.2.1).elim
    · exact mul_nonneg hL vonMangoldt_nonneg
    · rfl
  have bound (a b : ℕ) (hb : b ≤ X) :
      (∑ k ∈ Ioc a b,purePowerLog n k) ≤ L*(Chebyshev.psi (X:ℝ)-Chebyshev.theta (X:ℝ)) := by
    rw [Chebyshev.psi_sub_theta_eq_sum_not_prime,Nat.floor_natCast,mul_sum,sum_filter]
    calc _ ≤ ∑ k ∈ Ioc 0 X,purePowerLog n k :=
             sum_le_sum_of_subset_of_nonneg (fun k hk => mem_Ioc.mpr
               ⟨(Nat.zero_le a).trans_lt (mem_Ioc.mp hk).1,(mem_Ioc.mp hk).2.trans hb⟩)
               (fun k _ _ => hnneg k)
         _ ≤ _ := sum_le_sum fun k hk => by
             simpa only [mul_ite,mul_zero] using point (mem_Ioc.mp hk).2
  have h1 := bound (2*n) (3*n) (by dsimp only [X]; omega)
  have h2 := bound (3*n) (4*n) le_rfl
  have hr := odd_smooth_prime_midpoint_exact hn
  unfold unitarySignedIntervals at hr
  apply abs_le.mpr
  constructor <;> linarith only [hr,h1,h2,
    sum_nonneg (s:=Ioc (2*n) (3*n)) (fun k _ => hnneg k),
    sum_nonneg (s:=Ioc (3*n) (4*n)) (fun k _ => hnneg k)]

#print axioms odd_smooth_has_no_large_prime
#print axioms odd_smooth_prime_midpoint_exact
#print axioms odd_smooth_midpoint_error

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
