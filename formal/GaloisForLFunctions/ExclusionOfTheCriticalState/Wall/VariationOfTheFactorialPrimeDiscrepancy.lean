import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.OddQuotientsInTheFractionalPrimeTest
import GaloisForLFunctions.ExceptionalLayerTheory.TheAlternatingDivisorCountHasSquareRootError
import GaloisForLFunctions.RHTower.MertensFirst

/-!
# Variation and completion of the odd-quotient prime discrepancy

An odd quotient can change only when its denominator divides a crossed
integer. Summing absolute changes costs at most the logarithm of the
factorial ratio and the divisor count on that same interval. Completing
all denominators above the square root has only square-root discrepancy.
-/

noncomputable section
open scoped Classical
open Finset ArithmeticFunction
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ExceptionalLayerTheory

private theorem pos_inds (N : ℕ) : Finset.Icc 1 N=Finset.Ioc 0 N := by
  ext n; simp only [mem_Icc,mem_Ioc]; omega

private abbrev row (N : ℕ) (n : ℕ) := if N/n%2=1 then ordinaryPrimeExcessCoeff n else 0

private theorem mass_bound (n : ℕ) : |ordinaryPrimeExcessCoeff n| ≤ vonMangoldt n+1 := by
  by_cases hp : n.Prime
  · rw [ordinaryPrimeExcessCoeff,if_pos hp, vonMangoldt_apply_prime hp]
    exact (abs_sub _ _).trans_eq (by rw [abs_of_nonneg (Real.log_natCast_nonneg n),abs_one])
  · simp only [ordinaryPrimeExcessCoeff,if_neg hp,zero_sub,abs_neg,abs_one]
    linarith only [vonMangoldt_nonneg (n := n)]

private theorem complete_ordinary_row :
    ∃ C : ℝ, 0≤C ∧ ∀ H : ℕ, |oddQuotientPrimeExcess (Ioc 0 H) H| ≤ C*Real.sqrt H := by
  obtain ⟨A,hA⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  let C := 75+2*|Real.eulerMascheroniConstant|
  refine ⟨C+|A|,by dsimp only [C]; positivity,fun H => ?_⟩
  let Z := fun n : ℕ => ((vonMangoldt-(ArithmeticFunction.zeta : ArithmeticFunction ℝ)) n)*
    ((H/n%2:ℕ):ℝ)
  have hfull := abs_prefix_alternatingPrimeExcess H
  rw [alternatingPrimeExcess_eq_parity_count,pos_inds] at hfull
  have hdiff : |oddQuotientPrimeExcess (Ioc 0 H) H-∑ n ∈ Ioc 0 H, Z n| ≤
      Chebyshev.psi H-Chebyshev.theta H := by
    rw [oddQuotientPrimeExcess,← sum_sub_distrib,Chebyshev.psi_sub_theta_eq_sum_not_prime,
      Nat.floor_natCast,sum_filter]
    apply (abs_sum_le_sum_abs _ _).trans
    apply sum_le_sum
    intro n hn
    have hn0 := (mem_Ioc.mp hn).1.ne'
    have hz : (zeta n:ℝ)=1 := by simp [ArithmeticFunction.zeta_apply,hn0]
    have hval : (vonMangoldt-(zeta : ArithmeticFunction ℝ)) n = vonMangoldt n-1 := by
      change vonMangoldt n-(zeta n:ℝ)=_
      rw [hz]
    have hmod := Nat.mod_lt (H/n) (by decide : 0<2)
    by_cases h : H/n%2=1
    · have hz₁ : Z n=vonMangoldt n-1 := by simp only [Z,hval,h,Nat.cast_one,mul_one]
      rw [if_pos h,hz₁,ordinaryPrimeExcessCoeff]
      by_cases hp : n.Prime
      · simp [hp,vonMangoldt_apply_prime hp]
      · rw [if_neg hp,if_pos hp,show (0:ℝ)-1-(vonMangoldt n-1)= -vonMangoldt n by ring,
          abs_neg,abs_of_nonneg vonMangoldt_nonneg]
    · have hzero : H/n%2=0 := by omega
      have hz₀ : Z n=0 := by simp only [Z,hzero,Nat.cast_zero,mul_zero]
      rw [if_neg h,hz₀,sub_self,abs_zero]
      split_ifs <;> first | exact vonMangoldt_nonneg | exact le_rfl
  have h := abs_add_le (oddQuotientPrimeExcess (Ioc 0 H) H-∑ n ∈ Ioc 0 H, Z n) (∑ n ∈ Ioc 0 H, Z n)
  rw [sub_add_cancel] at h
  change |∑ n ∈ Ioc 0 H, Z n| ≤ C*Real.sqrt H at hfull
  linarith only [h,hdiff,hfull,hA H,mul_le_mul_of_nonneg_right (le_abs_self A) (Real.sqrt_nonneg (H:ℝ))]

/-- The complete ordinary-prime row beyond the square root has square-root
error at every numerator, with any upper cutoff at or above the numerator. -/
theorem oddQuotientPrimeExcess_complete_above_sqrt :
    ∃ C : ℝ, 0≤C ∧ ∀ H L : ℕ, H≤L →
      |oddQuotientPrimeExcess (Ioc ⌊Real.sqrt H⌋₊ L) H| ≤ C*Real.sqrt H := by
  obtain ⟨C,hC,h⟩ := complete_ordinary_row
  refine ⟨C+(1+Real.log 4),by positivity,fun H L hL => ?_⟩
  have htop : oddQuotientPrimeExcess (Ioc 0 L) H=oddQuotientPrimeExcess (Ioc 0 H) H := by
    symm
    apply sum_subset (fun n hn => mem_Ioc.mpr ⟨(mem_Ioc.mp hn).1,(mem_Ioc.mp hn).2.trans hL⟩)
    intro n hm hn
    have hlt : H<n := lt_of_not_ge (fun hj => hn (mem_Ioc.mpr ⟨(mem_Ioc.mp hm).1,hj⟩))
    simp only [Nat.div_eq_of_lt hlt,Nat.zero_mod,show ¬((0:ℕ)=1) by decide,if_false]
  have hre : ((Ioc 0 L).filter fun n : ℕ => Real.sqrt H<n)=Ioc ⌊Real.sqrt H⌋₊ L := by
    ext n
    rw [mem_filter,mem_Ioc,mem_Ioc,Nat.floor_lt (Real.sqrt_nonneg _)]
    constructor
    · rintro ⟨⟨_,hl⟩,hr⟩; exact ⟨hr,hl⟩
    · rintro ⟨hr,hl⟩; exact ⟨⟨Nat.cast_pos.mp ((Real.sqrt_nonneg _).trans_lt hr),hl⟩,hr⟩
  have hb := oddQuotientPrimeExcess_sqrt_cost (Ioc 0 L) (fun _ hn => (mem_Ioc.mp hn).1) H
  rw [hre,htop] at hb
  have hle := abs_sub (oddQuotientPrimeExcess (Ioc 0 H) H)
    (oddQuotientPrimeExcess (Ioc 0 H) H-oddQuotientPrimeExcess (Ioc ⌊Real.sqrt H⌋₊ L) H)
  rw [sub_sub_cancel] at hle
  linarith only [hle,h H,hb]

private def jumpPotential (N : ℕ) : ℝ :=
  ∑ n ∈ Ioc 0 N, (vonMangoldt n+1)*((N/n:ℕ):ℝ)

private theorem potential_on (S : Finset ℕ) (N : ℕ) (hS : Ioc 0 N ⊆ S) :
    jumpPotential N = ∑ n ∈ S, (vonMangoldt n+1)*((N/n:ℕ):ℝ) := by
  apply sum_subset hS
  intro n _ hn
  rcases Nat.eq_zero_or_pos n with rfl | hp
  · simp
  · have hlt : N<n := lt_of_not_ge (fun h => hn (mem_Ioc.mpr ⟨hp,h⟩))
    rw [Nat.div_eq_of_lt hlt,Nat.cast_zero,mul_zero]

private theorem gated_change (S : Finset ℕ) {M H : ℕ} (hm : M≤H) (f : ℕ → ℝ)
    (hgate : ∀ n, H/n=M/n → row H n=f n)
    (hval : ∀ n, f n=0 ∨ f n=ordinaryPrimeExcessCoeff n) :
    |oddQuotientPrimeExcess S H-∑ n ∈ S, f n| ≤ jumpPotential H-jumpPotential M := by
  let I := S ∪ Ioc 0 H
  let g := fun (k n : ℕ) => (vonMangoldt n+1)*((k/n:ℕ):ℝ)
  have hmono (n : ℕ) : (M/n:ℕ) ≤ H/n := Nat.div_le_div_right hm
  have hdiff (n : ℕ) : g H n-g M n=(vonMangoldt n+1)*(((H/n:ℕ):ℝ)-((M/n:ℕ):ℝ)) := (mul_sub ..).symm
  have hnn (n : ℕ) : 0≤g H n-g M n := by
    rw [hdiff]; exact mul_nonneg (by positivity) (sub_nonneg.mpr (Nat.cast_le.mpr (hmono n)))
  have hatom (n : ℕ) : |row H n-f n| ≤ g H n-g M n := by
    by_cases he : H/n=M/n
    · rw [hgate n he,sub_self,abs_zero]; exact hnn n
    have h₁ : (1:ℝ) ≤ ((H/n:ℕ):ℝ)-((M/n:ℕ):ℝ) := by
      have hi : M/n+1 ≤ H/n := by have := hmono n; omega
      have hc : ((M/n:ℕ):ℝ)+1 ≤ ((H/n:ℕ):ℝ) := by exact_mod_cast hi
      linarith only [hc]
    have hb : |ordinaryPrimeExcessCoeff n| ≤ g H n-g M n := by
      rw [hdiff]
      exact (mass_bound n).trans (le_mul_of_one_le_right (by positivity) h₁)
    by_cases h : H/n%2=1 <;> rcases hval n with m | m <;>
      simp only [row,h,m,if_true,if_false,sub_self,abs_zero,zero_sub,abs_neg,sub_zero] <;>
      first | exact hnn n | exact hb
  rw [oddQuotientPrimeExcess,← sum_sub_distrib]
  apply (abs_sum_le_sum_abs _ _).trans
  apply (sum_le_sum (fun n _ => hatom n)).trans
  have hI : Ioc 0 H ⊆ I := subset_union_right
  have hJ : Ioc 0 M ⊆ I := fun n hn => hI (mem_Ioc.mpr ⟨(mem_Ioc.mp hn).1,(mem_Ioc.mp hn).2.trans hm⟩)
  rw [potential_on I H hI,potential_on I M hJ,← sum_sub_distrib]
  exact sum_le_sum_of_subset_of_nonneg subset_union_left (fun n _ _ => hnn n)

private theorem row_change (S : Finset ℕ) {M H : ℕ} (hm : M≤H) :
    |oddQuotientPrimeExcess S H-oddQuotientPrimeExcess S M| ≤ jumpPotential H-jumpPotential M :=
  gated_change S hm (row M) (fun n h => by simp only [row,h])
    (fun n => by dsimp only [row]; split_ifs <;> simp)

/-- The ordinary-prime excess restricted to denominators whose quotients
are odd at every selected numerator. -/
def commonOddQuotientPrimeExcess (S E : Finset ℕ) : ℝ :=
  ∑ n ∈ S, if ∀ j ∈ E, j/n%2=1 then ordinaryPrimeExcessCoeff n else 0

private abbrev logs (N : ℕ) := ∑ n ∈ Ioc 0 N, Real.log n
private abbrev divs (N : ℕ) := ∑ n ∈ Icc 1 N, ((N/n:ℕ):ℝ)

private theorem potential_eq (N : ℕ) : jumpPotential N=logs N+divs N := by
  have he := _root_.RHTower.Mertens.log_summatory_eq N
  rw [pos_inds] at he
  simp only [jumpPotential,add_mul,one_mul,sum_add_distrib,logs,divs,pos_inds,he]

private theorem potential_change {M H : ℕ} (hm : 1≤M) (hMH : M≤H) :
    jumpPotential H-jumpPotential M ≤
      ((H:ℝ)-M)*(2*Real.log H+2+2*|Real.eulerMascheroniConstant|)+40*Real.sqrt H := by
  have hM : 0<(M:ℝ) := Nat.cast_pos.mpr hm
  have hH : 0<(H:ℝ) := Nat.cast_pos.mpr (hm.trans hMH)
  have hlog : logs H-logs M ≤ ((H:ℝ)-M)*Real.log H := by
    have he := sum_Ioc_consecutive (fun n : ℕ => Real.log n) (Nat.zero_le M) hMH
    change logs M+_ = logs H at he
    have hb := sum_le_sum (s := Ioc M H) (g := fun _ => Real.log (H:ℝ)) (fun n hn =>
      Real.log_le_log (Nat.cast_pos.mpr (Nat.zero_lt_of_lt (mem_Ioc.mp hn).1)) (Nat.cast_le.mpr (mem_Ioc.mp hn).2))
    rw [sum_const,Nat.card_Ioc,nsmul_eq_mul,Nat.cast_sub hMH] at hb
    linarith only [he,hb]
  have hder := Real.log_le_sub_one_of_pos (div_pos hH hM)
  rw [Real.log_div hH.ne' hM.ne'] at hder
  have hprod := mul_le_mul_of_nonneg_right hder hM.le
  simp only [sub_mul,div_mul_cancel₀ _ hM.ne',one_mul] at hprod
  have hU := (abs_le.mp (_root_.RHTower.abs_sum_div_sub_dirichlet_le H (hm.trans hMH))).2
  have hD := (abs_le.mp (_root_.RHTower.abs_sum_div_sub_dirichlet_le M hm)).1
  have hγ := mul_le_mul_of_nonneg_right (le_abs_self Real.eulerMascheroniConstant)
    (sub_nonneg.mpr (Nat.cast_le.mpr hMH : (M:ℝ)≤H))
  rw [potential_eq,potential_eq]
  dsimp only [divs]
  linarith only [hlog,hU,hD,hprod,hγ,Real.sqrt_le_sqrt (Nat.cast_le.mpr hMH : (M:ℝ)≤H),
    (show (M:ℝ)≤H from Nat.cast_le.mpr hMH)]

/-- Total variation in the numerator, uniform over all finite selections of
denominators. Every summand can jump only at a multiple of its denominator. -/
theorem oddQuotientPrimeExcess_numerator_variation (S : Finset ℕ) {M H : ℕ} (hm : 1≤M) (hMH : M≤H) :
    ∑ j ∈ Ico M H, |oddQuotientPrimeExcess S (j+1)-oddQuotientPrimeExcess S j| ≤
      ((H:ℝ)-M)*(2*Real.log H+2+2*|Real.eulerMascheroniConstant|)+40*Real.sqrt H := by
  apply (sum_le_sum (fun j _ => row_change S (Nat.le_succ j))).trans
  rw [sum_Ico_sub jumpPotential hMH]
  exact potential_change hm hMH

/-- Endpoint form of the variation bound. -/
theorem oddQuotientPrimeExcess_numerator_change (S : Finset ℕ) {M H : ℕ} (hm : 1≤M) (hMH : M≤H) :
    |oddQuotientPrimeExcess S H-oddQuotientPrimeExcess S M| ≤
      ((H:ℝ)-M)*(2*Real.log H+2+2*|Real.eulerMascheroniConstant|)+40*Real.sqrt H :=
  (row_change S hMH).trans (potential_change hm hMH)

/-- Intersecting the parity conditions over any nonempty family in the block
costs no more than crossing all its possible jumps. -/
theorem commonOddQuotientPrimeExcess_change (S E : Finset ℕ) {M H : ℕ} (hM : 1≤M) (hMH : M≤H)
    (hne : E.Nonempty) (hE : E ⊆ Icc M H) :
    |oddQuotientPrimeExcess S H-commonOddQuotientPrimeExcess S E| ≤
      ((H:ℝ)-M)*(2*Real.log H+2+2*|Real.eulerMascheroniConstant|)+40*Real.sqrt H := by
  apply le_trans _ (potential_change hM hMH)
  unfold commonOddQuotientPrimeExcess
  apply gated_change S hMH (fun n => if ∀ j ∈ E, j/n%2=1 then ordinaryPrimeExcessCoeff n else 0)
  · intro n h
    have hq (j : ℕ) (hj : j∈E) : j/n=H/n := le_antisymm (Nat.div_le_div_right (mem_Icc.mp (hE hj)).2)
      (h.trans_le (Nat.div_le_div_right (mem_Icc.mp (hE hj)).1))
    have he : (∀ j ∈ E, j/n%2=1) ↔ H/n%2=1 := by
      constructor
      · intro hall; obtain ⟨j,hj⟩ := hne; simpa only [hq j hj] using hall j hj
      · intro hh j hj; rwa [hq j hj]
    simp only [row,he]
  · intro n; split_ifs <;> simp

/-- A column survives every numerator of a consecutive block exactly when
one odd quotient covers the entire block. Its denominator then exceeds the
distance between the endpoints. -/
theorem odd_quotient_throughout_block {M H n : ℕ} (hMH : M≤H) (hn : 0<n) :
    (∀ j ∈ Icc M H, j/n%2=1) ↔ M/n=H/n ∧ H/n%2=1 ∧ H-M<n := by
  constructor
  · intro h
    have hleft := h M (mem_Icc.mpr ⟨le_rfl,hMH⟩)
    have hright := h H (mem_Icc.mpr ⟨hMH,le_rfl⟩)
    have hq : M/n=H/n := by
      by_contra he
      have hinc : M/n+1≤H/n := by have := Nat.div_le_div_right (c := n) hMH; omega
      have hlow := Nat.lt_mul_div_succ M hn
      have hhi := (Nat.le_div_iff_mul_le hn).mp hinc
      have hh := h ((M/n+1)*n) (mem_Icc.mpr ⟨by simpa only [mul_comm n] using hlow.le,hhi⟩)
      rw [Nat.mul_div_cancel _ hn] at hh
      omega
    have hu := Nat.lt_mul_div_succ H hn
    rw [← hq,Nat.mul_add,Nat.mul_one] at hu
    have hl := Nat.mul_div_le M n
    exact ⟨hq,hright,by omega⟩
  · rintro ⟨h,ho,_⟩ j hj
    obtain ⟨h₁,h₂⟩ := mem_Icc.mp hj
    have he := le_antisymm (Nat.div_le_div_right h₂ : j/n≤H/n) (h.symm.trans_le (Nat.div_le_div_right h₁))
    rwa [he]

#print axioms oddQuotientPrimeExcess_complete_above_sqrt
#print axioms oddQuotientPrimeExcess_numerator_variation
#print axioms odd_quotient_throughout_block
end GaloisForLFunctions.ExclusionOfTheCriticalState
