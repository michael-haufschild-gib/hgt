import GaloisForLFunctions.HTGeometry.SquarefreeDensityLowerBound
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Mean cost of the higher dyadic ranks

At depths above one, restoring a missing cyclic factor contributes to
the excess rank only while another factor is still present. The exact
overlap length is controlled on the coprime square by a factorial
valuation. This gives a uniform correction to Dahan's mean log-count.
-/

noncomputable section
open Finset
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis.DyadicRanks

/-- Number of non-dyadic local factors whose two-primary exponent reaches k. -/
def layers {ι : Type*} (S : Finset ι) (e : ι → ℕ) (k : ℕ) :=
  (S.filter fun i => k ≤ e i).card

/-- Missing excess rank at depth k+2. The printed depth-one rank already
includes both local factors when s is positive. -/
def missed {ι : Type*} (S : Finset ι) (e : ι → ℕ) (s k : ℕ) :=
  (layers S e (k+2) + (if k+2 ≤ s then 1 else 0) - 1) - (layers S e (k+2) - 1)

theorem missed_eq {ι : Type*} (S : Finset ι) (e : ι → ℕ) (s k : ℕ) :
    missed S e s k = if k+2 ≤ min s (S.sup e) then 1 else 0 := by
  have hx : 0 < layers S e (k+2) ↔ k+2 ≤ S.sup e := by
    rw [Finset.le_sup_iff (by change 0<k+2; omega)]
    simp only [layers,card_pos,Finset.Nonempty,mem_filter,exists_prop]
  unfold missed
  by_cases hs : k+2 ≤ s <;> by_cases he : k+2≤S.sup e <;>
    simp only [le_min_iff,hs,he,ite_true,ite_false,and_true,and_false,true_and,false_and] <;> omega

/-- With all depth cutoffs included, precisely min(s,max e)−1 bits are
missing, truncated at zero. This formula also handles an empty odd part. -/
theorem total_missed {ι : Type*} (S : Finset ι) (e : ι → ℕ) (s K : ℕ) :
    ∑ k ∈ range K, missed S e s k = min K (min s (S.sup e)-1) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [sum_range_succ,ih,missed_eq]
    split <;> omega

/-- The maximum penalty at one coordinate is the valuation beyond the first factor of two. -/
def cost (n : ℕ) := padicValNat 2 n - 1

/-- Erasing the initial factor two on even integers leaves precisely the
factorial of the half interval. -/
theorem sum_cost (J : ℕ) : ∑ n ∈ Ioc 0 J, cost n = padicValNat 2 (J/2).factorial := by
  induction J with
  | zero => simp [cost]
  | succ J ih =>
    rw [sum_Ioc_succ_top (Nat.zero_le J),ih]
    by_cases he : 2 ∣ J+1
    · obtain ⟨w,hw⟩ := he
      have hw' : w = J/2+1 := by omega
      have hd : (J+1)/2 = J/2+1 := by omega
      have hn : w≠0 := by omega
      rw [hd,Nat.factorial_succ,padicValNat.mul (by omega : J/2+1 ≠ 0) (Nat.factorial_ne_zero _)]
      unfold cost
      rw [hw,padicValNat.mul (by norm_num : (2:ℕ)≠0) hn,padicValNat_self,hw']
      omega
    · have hd : (J+1)/2=J/2 := by omega
      rw [hd,cost,padicValNat.eq_zero_of_not_dvd he]
      omega

private def square (J : ℕ) := (Ioc 0 J) ×ˢ (Ioc 0 J)
def primitive (J : ℕ) := (square J).filter fun p => p.1.Coprime p.2

private theorem cost_coprime {u a : ℕ} (hu : 0<u) (ha : 0<a) (h : u.Coprime a) :
    cost (u*a) = cost u + cost a := by
  have hd : ¬2∣u ∨ ¬2∣a := by
    by_contra! hh
    exact (Nat.Prime.not_coprime_iff_dvd.mpr ⟨2,Nat.prime_two,hh⟩) h
  simp only [cost,padicValNat.mul hu.ne' ha.ne']
  rcases hd with hd | hd <;> rw [padicValNat.eq_zero_of_not_dvd hd] <;> omega

/-- A bound for arbitrary choices of the largest competing exponent at each
pair, uniform down to finite J. -/
theorem box_cost (J : ℕ) (height : ℕ × ℕ → ℕ) :
    ∑ p ∈ primitive J, (min (padicValNat 2 (p.1*p.2)) (height p)-1) ≤ J^2 := by
  have hsum : ∑ p ∈ square J, (cost p.1+cost p.2) =
      2*J*padicValNat 2 (J/2).factorial := by
    simp only [square,sum_product,sum_add_distrib,sum_const,Nat.card_Ioc,Nat.sub_zero,
      smul_eq_mul,← mul_sum,sum_cost]
    ring
  calc
    _ ≤ ∑ p ∈ primitive J, (cost p.1+cost p.2) := by
      apply sum_le_sum
      intro p hp
      obtain ⟨huv,hc⟩ := mem_filter.mp hp
      obtain ⟨hu,ha⟩ := mem_product.mp huv
      rw [← cost_coprime (mem_Ioc.mp hu).1 (mem_Ioc.mp ha).1 hc]
      exact Nat.sub_le_sub_right (min_le_left _ _) _
    _ ≤ ∑ p ∈ square J, (cost p.1+cost p.2) := sum_le_sum_of_subset (filter_subset _ _)
    _ ≤ J^2 := by
      rw [hsum]
      have hv := padicValNat_factorial_le (p := 2) (J/2)
      have hj : 2*padicValNat 2 (J/2).factorial ≤ J := by omega
      simpa only [pow_two,mul_assoc,mul_left_comm,mul_comm] using Nat.mul_le_mul_left J hj

/-- At least 51 percent of every square is primitive. The union bound
counts pairs divisible by p in both coordinates, then uses the bound on the
sum of inverse squares of primes. -/
theorem primitive_density (J : ℕ) : 51*J^2 ≤ 100*(primitive J).card := by
  let bad := (square J).filter fun p => ¬p.1.Coprime p.2
  let D (p : ℕ) := (Ioc 0 J).filter fun n => p∣n
  let P := Nat.primesBelow (J+1)
  have hsub : bad ⊆ P.biUnion (fun p => (D p) ×ˢ (D p)) := by
    intro b hb
    obtain ⟨hb,hc⟩ := mem_filter.mp hb
    obtain ⟨hu,ha⟩ := mem_product.mp hb
    obtain ⟨p,hp,hu',ha'⟩ := Nat.Prime.not_coprime_iff_dvd.mp hc
    have hle := (Nat.le_of_dvd (mem_Ioc.mp hu).1 hu').trans (mem_Ioc.mp hu).2
    exact mem_biUnion.mpr ⟨p,Nat.mem_primesBelow.mpr ⟨by omega,hp⟩,
      mem_product.mpr ⟨mem_filter.mpr ⟨hu,hu'⟩,mem_filter.mpr ⟨ha,ha'⟩⟩⟩
  have hcard : bad.card ≤ ∑ p ∈ P, (J/p)^2 := by
    refine (card_le_card hsub).trans (card_biUnion_le.trans ?_)
    apply sum_le_sum
    intro p _
    rw [card_product]
    simp only [D]
    rw [Nat.Ioc_filter_dvd_card_eq_div,pow_two]
  have hr : (bad.card : ℝ) ≤ (J : ℝ)^2*(49/100) := by
    calc
      _ ≤ ∑ p ∈ P, ((J/p : ℕ) : ℝ)^2 := by exact_mod_cast hcard
      _ ≤ ∑ p ∈ P, (J : ℝ)^2 * (1/(p : ℝ)^2) := by
        apply sum_le_sum
        intro p hp
        rw [mul_one_div,← div_pow]
        apply pow_le_pow_left₀ (Nat.cast_nonneg _)
        have hp' : 0<p := (Nat.mem_primesBelow.mp hp).2.pos
        apply (le_div_iff₀ (by exact_mod_cast hp' : (0 : ℝ)<p)).2
        exact_mod_cast Nat.div_mul_le_self J p
      _ ≤ _ := by
        rw [← mul_sum]
        exact mul_le_mul_of_nonneg_left (RHTower.sum_primesBelow_one_div_sq_le (J+1)) (sq_nonneg _)
  have h₀ : (primitive J).card+bad.card=J^2 := by
    rw [primitive]
    simp only [bad]
    rw [card_filter_add_card_filter_not,square,card_product,Nat.card_Ioc,Nat.sub_zero,pow_two]
  have hn : 100*bad.card ≤ 49*J^2 := by
    exact_mod_cast (show (100 : ℝ)*bad.card≤49*(J : ℝ)^2 by linarith only [hr])
  omega

/-- Restoring the correct ranks costs less than two extra bits per primitive
pair on average, uniformly in the side length and every competing exponent. -/
theorem mean_correction (J : ℕ) (height : ℕ × ℕ → ℕ) :
    51 * (∑ p ∈ primitive J, (min (padicValNat 2 (p.1*p.2)) (height p)-1)) ≤
      100*(primitive J).card :=
  (Nat.mul_le_mul_left 51 (box_cost J height)).trans (primitive_density J)

end GaloisForLFunctions.ArithmeticHarmonicAnalysis.DyadicRanks
