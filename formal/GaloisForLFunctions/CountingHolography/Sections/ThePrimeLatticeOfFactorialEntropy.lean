import GaloisForLFunctions.CountingHolography.Sections.EntropyAndValueOfBalancedFactorials
import Mathlib.Data.Nat.Factorization.Induction

/-! # The joint price and Stirling entropy of factorials at finite horizon

Below the top degree, a prime p contributes two independent integer
coordinates, log p to the price and p log p to the entropy. A prime at the
top contributes only their tied pair.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections
open Finset

/-- All pairs of logarithmic value and entropy at fixed maximum degree. -/
def factorialJointImage (L : ℕ) : AddSubgroup (ℝ×ℝ) where
  carrier := {x | ∃ c : ℕ →₀ ℤ, (∀ j, L < j → c j=0) ∧ factorialBalance c=0 ∧
    (factorialLogValue c,factorialEntropy c)=x}
  zero_mem' := ⟨0,fun _ _ => rfl,map_zero _,by rw [map_zero,map_zero]; rfl⟩
  add_mem' := by
    rintro x y ⟨c,hc,hb,rfl⟩ ⟨d,hd,hb',rfl⟩
    exact ⟨c+d,fun j hj => by simp [hc j hj,hd j hj],by rw [map_add,hb,hb',add_zero],
      by simp only [map_add]; rfl⟩
  neg_mem' := by
    rintro x ⟨c,hc,hb,rfl⟩
    exact ⟨-c,fun j hj => by simp [hc j hj],by rw [map_neg,hb,neg_zero],by simp only [map_neg]; rfl⟩

private def atom (k : ℕ) : ℝ×ℝ := (Real.log (k.factorial:ℝ),(k:ℝ)*Real.log k)

private theorem atom_mem {L k : ℕ} (hL : 1 ≤ L) (hk : k ≤ L) : atom k ∈ factorialJointImage L := by
  let c := Finsupp.single k (1:ℤ)-Finsupp.single 1 (k:ℤ)
  refine ⟨c,fun j hj => ?_,?_,?_⟩
  · simp [c,show k≠j by omega,show 1≠j by omega]
  · simp [c,factorialBalance,zsmul_eq_mul]
  · simp [c,factorialLogValue,factorialEntropy,atom]

private theorem price_mem {L : ℕ} {x : ℝ} (hx : x ∈ zeroEntropyPrices L) :
    (x,0) ∈ factorialJointImage L := by
  obtain ⟨c,hs,hb,he,hv⟩ := hx
  exact ⟨c,hs,hb,by rw [hv,he]⟩

private theorem fac_mem_of_logs {H : AddSubgroup (ℝ×ℝ)} {k : ℕ}
    (hl : ∀ j, 0 < j → j ≤ k → (Real.log (j:ℝ),0) ∈ H) :
    (Real.log (k.factorial:ℝ),0) ∈ H := by
  induction k with
  | zero =>
    simp only [Nat.factorial_zero,Nat.cast_one,Real.log_one]
    exact H.zero_mem
  | succ k ih =>
    have hm := H.add_mem (hl _ (Nat.succ_pos _) le_rfl) (ih fun j hj hjk => hl _ hj (Nat.le_succ_of_le hjk))
    rw [Nat.factorial_succ,Nat.cast_mul,Real.log_mul (by positivity) (by positivity)]
    simpa only [Prod.mk_add_mk,add_zero] using hm

/-- Independent prime axes below L and the tied top prime when L is prime. -/
def factorialPrimeReadings (L : ℕ) : Set (ℝ×ℝ) :=
  {z | (∃ p : ℕ, p.Prime ∧ p < L ∧ (z = (Real.log p,0) ∨ z = (0,(p:ℝ)*Real.log p))) ∨
    (L.Prime ∧ z=(Real.log L,(L:ℝ)*Real.log L))}

private theorem prime_mem_image {L : ℕ} (hL : 10 ≤ L) :
    factorialPrimeReadings L ⊆ factorialJointImage L := by
  let J := factorialJointImage L
  have hlog (k : ℕ) (hk : k < L) : (Real.log (k:ℝ),0) ∈ J :=
    price_mem (log_nat_mem_zeroEntropyPrices hL k hk)
  have hfac (k : ℕ) (hk : k < L) : (Real.log (k.factorial:ℝ),0) ∈ J :=
    fac_mem_of_logs fun j _ hj => hlog _ (hj.trans_lt hk)
  rintro z (⟨p,_,hp,he⟩ | ⟨_,rfl⟩)
  · rcases he with rfl | rfl
    · exact hlog p hp
    · have h := J.sub_mem (atom_mem (by omega) hp.le) (hfac p hp)
      simpa [atom] using h
  · obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : L≠0)
    have h := J.sub_mem (atom_mem (by omega) (le_refl (k+1))) (hfac k (Nat.lt_succ_self _))
    simpa [atom,Nat.factorial_succ,Real.log_mul (by positivity : (k:ℝ)+1≠0)
      (by positivity : (k.factorial:ℝ)≠0)] using h

private theorem mixed_logs {L : ℕ} {H : AddSubgroup (ℝ×ℝ)}
    (hc : factorialPrimeReadings L ⊆ H) (n : ℕ) :
    n < L ∨ n = L ∧ ¬ n.Prime →
      (Real.log (n:ℝ),0) ∈ H ∧ (0,(n:ℝ)*Real.log n) ∈ H := by
  induction n using Nat.recOnMul with
  | zero => intro _; simp; exact H.zero_mem
  | one => intro _; simp; exact H.zero_mem
  | prime p hp =>
    intro h
    have hlt : p < L := h.elim id (fun h => (h.2 hp).elim)
    exact ⟨hc (Or.inl ⟨p,hp,hlt,Or.inl rfl⟩),hc (Or.inl ⟨p,hp,hlt,Or.inr rfl⟩)⟩
  | mul a b ha hb =>
    intro h
    rcases eq_or_ne a 0 with rfl | ha₀
    · simp; exact H.zero_mem
    rcases eq_or_ne b 0 with rfl | hb₀
    · simp; exact H.zero_mem
    rcases eq_or_ne a 1 with rfl | ha₁
    · simpa only [one_mul] using hb (by simpa only [one_mul] using h)
    rcases eq_or_ne b 1 with rfl | hb₁
    · simpa only [mul_one] using ha (by simpa only [mul_one] using h)
    have hle : a*b ≤ L := h.elim (fun h => h.le) (fun h => h.1.le)
    have hal : a < L := (lt_mul_of_one_lt_right (Nat.pos_of_ne_zero ha₀) (by omega : 1<b)).trans_le hle
    have hbl : b < L := (lt_mul_of_one_lt_left (Nat.pos_of_ne_zero hb₀) (by omega : 1<a)).trans_le hle
    obtain ⟨ha',ha''⟩ := ha (Or.inl hal)
    obtain ⟨hb',hb''⟩ := hb (Or.inl hbl)
    rw [Nat.cast_mul,Real.log_mul (Nat.cast_ne_zero.mpr ha₀) (Nat.cast_ne_zero.mpr hb₀)]
    constructor
    · simpa only [Prod.mk_add_mk,add_zero] using H.add_mem ha' hb'
    · have hm := H.add_mem (H.nsmul_mem ha'' b) (H.nsmul_mem hb'' a)
      convert hm using 1
      ext <;> simp [nsmul_eq_mul] <;> ring

/-- Exact integral joint image of balance-zero factorials at every horizon
from ten onward. The closure here is algebraic subgroup generation. -/
theorem factorialJointImage_eq_prime_readings {L : ℕ} (hL : 10 ≤ L) :
    factorialJointImage L = AddSubgroup.closure (factorialPrimeReadings L) := by
  let H := AddSubgroup.closure (factorialPrimeReadings L)
  have hc : factorialPrimeReadings L ⊆ H := AddSubgroup.subset_closure
  have hlog {n : ℕ} (hn : n < L) := mixed_logs hc n (Or.inl hn)
  have hfac {n : ℕ} (hn : n < L) : (Real.log (n.factorial:ℝ),0) ∈ H :=
    fac_mem_of_logs fun j _ hj => (hlog (hj.trans_lt hn)).1
  have hA (k : ℕ) (hk : k ≤ L) : atom k ∈ H := by
    rcases lt_or_eq_of_le hk with h | rfl
    · simpa [atom] using H.add_mem (hfac h) (hlog h).2
    obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k≠0)
    have htop : (Real.log ((n+1:ℕ):ℝ),((n+1:ℕ):ℝ)*Real.log (n+1:ℕ)) ∈ H := by
      by_cases hpr : (n+1).Prime
      · exact hc (Or.inr ⟨hpr,rfl⟩)
      obtain ⟨h₁,h₂⟩ := mixed_logs hc (n+1) (Or.inr ⟨rfl,hpr⟩)
      simpa using H.add_mem h₁ h₂
    have h := H.add_mem htop (hfac (Nat.lt_succ_self n))
    simpa [atom,Nat.factorial_succ,Real.log_mul (by positivity : (n:ℝ)+1 ≠ 0)
      (by positivity : (n.factorial:ℝ) ≠ 0)] using h
  refine le_antisymm ?_ ((factorialJointImage L).closure_le.mpr (prime_mem_image hL))
  rintro z ⟨c,hs,_,rfl⟩
  have hsum := H.sum_mem (t := c.support) (f := fun k => c k • atom k)
    (fun k hk => H.zsmul_mem (hA k (le_of_not_gt fun h => (Finsupp.mem_support_iff.mp hk) (hs k h))) _)
  change (factorialLogValue c,factorialEntropy c) ∈ H
  convert hsum using 1
  ext <;> simp [factorialLogValue,factorialEntropy,Finsupp.linearCombination_apply,Finsupp.sum,atom,Prod.fst_sum,Prod.snd_sum,Prod.smul_mk,zsmul_eq_mul]

#print axioms factorialJointImage_eq_prime_readings

end GaloisForLFunctions.CountingHolography.Sections
