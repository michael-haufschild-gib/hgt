import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NthRewrite
import Mathlib.Tactic.Positivity

/-!
# Interval discrepancy from complete blocks

Two nonnegative measures of equal mass on each block differ only on the
two boundary blocks of an interval. This covers both empirical prime
averages and the normalized coprime indicator.
-/

noncomputable section
open Finset
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

private def blockMass (H k : ℕ) (f : ℕ → ℝ) : ℝ := ∑ i ∈ range H, f (k*H+i)

/-- Measures agreeing on whole blocks have interval discrepancy at most
twice the largest block mass. -/
theorem discrepancy_of_equal_blocks {H : ℕ} (hH : 0 < H) {f g : ℕ → ℝ} {M : ℝ}
    (hf : ∀ n, 0 ≤ f n) (hg : ∀ n, 0 ≤ g n)
    (he : ∀ k, (∑ i ∈ range H, f (k*H+i)) = ∑ i ∈ range H, g (k*H+i))
    (hm : ∀ k, (∑ i ∈ range H, f (k*H+i)) ≤ M) {L U : ℕ} (hl : L ≤ U) :
    |∑ m ∈ Ioc L U, (f m-g m)| ≤ 2*M := by
  let δ := fun m => f m-g m
  have whole (k : ℕ) : ∑ i ∈ range (k*H), δ i = 0 := by
    induction k with
    | zero => simp
    | succ k ih => rw [Nat.succ_mul,sum_range_add,ih,zero_add]; simp only [δ,sum_sub_distrib,he,sub_self]
  have hpre (n : ℕ) : |∑ i ∈ range n, δ i| ≤ M := by
    let k := n/H
    let r := n%H
    have hn : k*H+r = n := by simpa only [k,r,Nat.mul_comm,Nat.add_comm] using Nat.mod_add_div n H
    nth_rw 1 [←hn]
    rw [sum_range_add,whole,zero_add]
    change |∑ i ∈ range r, (f (k*H+i)-g (k*H+i))| ≤ M
    rw [sum_sub_distrib,abs_le]
    have sub := range_mono (Nat.mod_lt n hH).le
    have h₁ := (sum_le_sum_of_subset_of_nonneg (f := fun i => f (k*H+i)) sub (fun i _ _ => hf _)).trans (hm k)
    have h₂ := (sum_le_sum_of_subset_of_nonneg (f := fun i => g (k*H+i)) sub (fun i _ _ => hg _)).trans ((he k).symm.le.trans (hm k))
    have n₁ := sum_nonneg (s := range r) (fun i _ => hf (k*H+i))
    have n₂ := sum_nonneg (s := range r) (fun i _ => hg (k*H+i))
    constructor <;> linarith only [h₁,h₂,n₁,n₂]
  have hs : Ioc L U = Ico (L+1) (U+1) := by ext; simp only [mem_Ioc,mem_Ico]; omega
  change |∑ m ∈ Ioc L U, δ m| ≤ _
  rw [hs,sum_Ico_eq_sub _ (by omega : L+1 ≤ U+1)]
  exact (abs_sub _ _).trans (by linarith only [hpre (U+1),hpre (L+1)])

/-- The mean of the measure on the whole block containing n. -/
def blockMean (H : ℕ) (f : ℕ → ℝ) (n : ℕ) : ℝ := blockMass H (n/H) f / H

theorem discrepancy_block_mean {H : ℕ} (hH : 0 < H) {f : ℕ → ℝ} {D : ℝ}
    (hf : ∀ n, 0 ≤ f n) (hD : ∀ n, f n ≤ D) {L U : ℕ} (hl : L ≤ U) :
    |∑ m ∈ Ioc L U, (f m-blockMean H f m)| ≤ 2*((H : ℝ)*D) := by
  apply discrepancy_of_equal_blocks hH hf _ _ _ hl
  · intro n
    exact div_nonneg (sum_nonneg fun _ _ => hf _) (Nat.cast_nonneg _)
  · intro k
    have hid (i : ℕ) (hi : i ∈ range H) : (k*H+i)/H = k := by
      rw [Nat.mul_comm k H,Nat.mul_add_div hH,Nat.div_eq_of_lt (mem_range.mp hi),Nat.add_zero]
    calc _ = (H : ℝ)*(blockMass H k f/H) := by
              have hh : (H : ℝ) ≠ 0 := by exact_mod_cast hH.ne'
              change blockMass H k f = _
              field_simp
         _ = _ := by
              apply Eq.symm
              calc _ = ∑ _i ∈ range H, blockMass H k f/H := sum_congr rfl fun i hi => by rw [blockMean,hid i hi]
                   _ = _ := by simp
  · intro k
    exact (sum_le_sum (g := fun _ => D) (fun i _ => hD (k*H+i))).trans_eq (by simp)

/-- Normalized counting measure on the reduced residue classes. -/
def coprimeDensity (P n : ℕ) : ℝ := if P.Coprime n then (P : ℝ)/P.totient else 0

theorem coprime_density_discrepancy {P : ℕ} (hP : 0 < P) {L U : ℕ} (hl : L ≤ U) :
    |(∑ n ∈ Ioc L U, coprimeDensity P n)-((U : ℝ)-L)| ≤ 2*P := by
  have hper (n k : ℕ) : P.Coprime (k*P+n) ↔ P.Coprime n := by
    rw [Nat.add_comm,Nat.coprime_add_mul_right_right]
  have mass (k : ℕ) : (∑ i ∈ range P, coprimeDensity P (k*P+i)) = P := by
    simp only [coprimeDensity,hper,← sum_filter,sum_const,nsmul_eq_mul,← Nat.totient_eq_card_coprime]
    have ht : ((P.totient : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr hP).ne'
    change (P.totient : ℝ)*((P : ℝ)/P.totient) = P
    field_simp
  have hh := discrepancy_of_equal_blocks (H := P) (f := coprimeDensity P) (g := fun _ => (1 : ℝ))
    hP (fun n => by unfold coprimeDensity; split <;> positivity) (fun _ => zero_le_one)
    (fun k => by rw [mass]; simp) (fun k => (mass k).le) hl
  simpa only [sum_sub_distrib,sum_const,Nat.card_Ioc,nsmul_eq_mul,mul_one,Nat.cast_sub hl] using hh

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
