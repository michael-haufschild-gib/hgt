import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Mixed.Balance
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Sectors

/-! # Particle and vacancy sectors of the same bounded prime packet -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Mixed

open Finset _root_.HTGeometry
open FixedCount (State capacity count count_cap count_sum state_ext level integerLabel pairCount)

variable {S : Finset Nat.Primes} (c : S → ℕ) {m n : ℕ}

private def vacant (h : m+n=capacity c) (x : State c m) : State c n :=
  ⟨fun i => ⟨c i-count x i,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩,by
    change (∑ i, (c i-count x i))=n
    rw [sum_tsub_distrib _ (fun i _ => count_cap x i),count_sum,← capacity,← h]
    omega⟩

/-- Vacancies turn the entire particle sector into its complementary filling. -/
def holeEquiv (h : m+n=capacity c) : State c m ≃ State c n :=
  let h' : n+m=capacity c := by omega
  ⟨vacant c h,vacant c h',fun x => state_ext fun i => by
    change c i-(c i-count x i)=count x i
    have := count_cap x i
    omega,fun y => state_ext fun i => by
    change c i-(c i-count y i)=count y i
    have := count_cap y i
    omega⟩

def fullEnergy := energy (integerLabel S c)

theorem vacancy_energy (h : m+n=capacity c) (x : State c m) :
    sectorEnergy c m x+sectorEnergy c n (holeEquiv c h x)=fullEnergy c := by
  change energy (integerLabel S (count x))+energy (integerLabel S (count (holeEquiv c h x)))=_
  rw [← energy_mul,← FixedCount.integerLabel_add]
  apply congrArg (fun v => energy (integerLabel S v))
  funext i
  change count x i+(c i-count x i)=c i
  exact Nat.add_sub_of_le (count_cap x i)

def fillingEnergy (m n k l : ℕ) :=
  finiteTensorEnergy (copyEnergy (sectorEnergy c m) k) (copyEnergy (sectorEnergy c n) l)

theorem filling_matches (h : m+n=capacity c) (k l : ℕ) :
    Matches (mixedEnergy (sectorEnergy c m) (fullEnergy c) k l) (fillingEnergy c m n k l) := by
  let e := holeEquiv c h
  refine ⟨(Equiv.refl (Fin k → State c m)).prodCongr (Equiv.piCongrRight (fun _ : Fin l => e)),fun z => ?_⟩
  change _+(∑ i, (fullEnergy c-sectorEnergy c m (z.2 i))) =
    copyEnergy (sectorEnergy c m) k z.1 + ∑ i, sectorEnergy c n (e (z.2 i))
  refine congrArg (copyEnergy (sectorEnergy c m) k z.1 + ·) (sum_congr rfl fun i _ => ?_)
  linarith only [vacancy_energy c h (z.2 i)]

private theorem carry_pair {I J : Type*} {E : I → ℝ} {F : J → ℝ} (e : I ≃ J)
    (he : ∀ x, E x=F (e x)) {d : ℝ} (h : PairsAt F d) : PairsAt E d := by
  obtain ⟨R,hR⟩ := h
  refine ⟨(e.trans R).trans e.symm,fun x => ?_⟩
  change E x+E (e.symm (R (e x)))=d
  rw [he x,he _,e.apply_symm_apply,hR]

theorem pairs_congr {I J : Type*} {E : I → ℝ} {F : J → ℝ} (h : Matches E F) (d : ℝ) :
    PairsAt E d ↔ PairsAt F d := by
  obtain ⟨e,he⟩ := h
  refine ⟨carry_pair e.symm (fun y => ?_),carry_pair e he⟩
  rw [he,e.apply_symm_apply]

theorem filling_pairs_iff (h : m+n=capacity c) (k l : ℕ) (d : ℝ) :
    PairsAt (fillingEnergy c m n k l) (pairedSum (fullEnergy c) k l d) ↔
      k=l ∨ PairsAt (sectorEnergy c m) d := by
  rw [← pairs_congr (filling_matches c h k l),mixed_pairs_iff]

/-- Balancing particle copies and complementary vacancy copies restores reflection.
An unbalanced packet reflects precisely when its one-copy sector does. -/
theorem filling_reflection_iff (m k l : ℕ) :
    Reflects (fillingEnergy c m (capacity c-m) k l) ↔
      k=l ∨ capacity c < m ∨ (∑ i, pairCount c m i)=2*m := by
  by_cases hm : m ≤ capacity c
  · have h : m+(capacity c-m)=capacity c := Nat.add_sub_of_le hm
    have eq := filling_matches c h k l
    calc Reflects (fillingEnergy c m (capacity c-m) k l)
          ↔ Reflects (mixedEnergy (sectorEnergy c m) (fullEnergy c) k l) :=
             exists_congr fun d => (pairs_congr eq d).symm
         _ ↔ _ := by rw [mixed_reflects_iff,sector_reflection_iff]
  · have h := lt_of_not_ge hm
    refine ⟨fun _ => Or.inr (Or.inl h),fun _ => ?_⟩
    have left := (reflects_copies_iff (sectorEnergy c m) k).mpr
      (Or.inr ((sector_reflection_iff c m).mpr (Or.inl h)))
    have vac : Reflects (sectorEnergy c 0) := (sector_reflection_iff c 0).mpr
      (Or.inr (by simp [FixedCount.pairCount,FixedCount.lower,FixedCount.upper]))
    obtain ⟨a,ha⟩ := left
    obtain ⟨b,hb⟩ := (reflects_copies_iff (sectorEnergy c 0) l).mpr (Or.inr vac)
    rw [Nat.sub_eq_zero_of_le h.le]
    exact ⟨a+b,tensor_pair ha hb⟩

#print axioms vacancy_energy
#print axioms filling_matches
#print axioms filling_pairs_iff
#print axioms filling_reflection_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Mixed
