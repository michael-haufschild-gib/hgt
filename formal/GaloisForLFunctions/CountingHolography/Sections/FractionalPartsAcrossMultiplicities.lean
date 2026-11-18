import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

/-!
# Fractional parts of nearly quadratic negative readings

A quadratic reading with small first differences either stays near zero or
moves a definite fraction of one after a short integer shift. Both alternatives
give a lower bound for the sum of fractional parts on a multiplicity interval.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections

open Finset

private theorem separated_fractional_parts {x y : ℝ}
    (hl : 1/32 ≤ |x-y|) (hu : |x-y| ≤ 1/2) :
    1/32 ≤ Int.fract x + Int.fract y := by
  by_contra! hs
  have hx := Int.floor_add_fract x
  have hy := Int.floor_add_fract y
  have tx := Int.fract_nonneg x
  have ty := Int.fract_nonneg y
  obtain ⟨h₁,h₂⟩ := abs_le.mp hu
  have hlow : (-1:ℝ) < ((⌊x⌋-⌊y⌋ : ℤ):ℝ) := by
    rw [Int.cast_sub]; linarith only [hx,hy,tx,ty,h₁,hs]
  have hhigh : ((⌊x⌋-⌊y⌋ : ℤ):ℝ) < 1 := by
    rw [Int.cast_sub]; linarith only [hx,hy,tx,ty,h₂,hs]
  have hlow' : -1 < ⌊x⌋-⌊y⌋ := by exact_mod_cast hlow
  have hhigh' : ⌊x⌋-⌊y⌋ < 1 := by exact_mod_cast hhigh
  have he : ⌊x⌋ = ⌊y⌋ := by omega
  rw [he] at hx
  exact hl.not_gt (abs_lt.mpr ⟨by linarith only [hx,hy,tx,hs],
    by linarith only [hx,hy,ty,hs]⟩)

private theorem shift_fractional_parts {M : ℕ} (hM : 0 < M) {b : ℝ}
    (hstep : |b| *(M:ℝ) ≤ 1/64) (x : ℕ → ℝ)
    (hx : ∀ m ∈ Icc M (3*M), x m < 0 ∧ |x m-b*(m:ℝ)^2| ≤ 1/512) :
    ∃ h : ℕ, h ≤ M ∧ ∀ m ∈ Ico M (2*M),
      1/32 ≤ Int.fract (x m) + Int.fract (x (m+h)) := by
  have hM' : 0 < (M:ℝ) := Nat.cast_pos.mpr hM
  let s := |b| *(M:ℝ)
  by_cases hsmall : s*(M:ℝ) ≤ 1/8
  · refine ⟨0,Nat.zero_le _,fun m hm => ?_⟩
    obtain ⟨hl,hu⟩ := mem_Ico.mp hm
    obtain ⟨hn,ha⟩ := hx m (mem_Icc.mpr ⟨hl,by omega⟩)
    have hu' : (m:ℝ) ≤ 2*M := by exact_mod_cast hu.le
    have hpow := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hu' 2) (abs_nonneg b)
    have hb : |b*(m:ℝ)^2| ≤ 1/2 := by
      rw [abs_mul,abs_of_nonneg (sq_nonneg (m:ℝ))]
      dsimp only [s] at hsmall
      linarith only [hpow,hsmall]
    have hf : ⌊x m⌋ < 0 := by exact_mod_cast (Int.floor_le (x m)).trans_lt hn
    have hf' : ((⌊x m⌋ : ℤ):ℝ) ≤ -1 := by exact_mod_cast (show ⌊x m⌋ ≤ -1 by omega)
    rw [Nat.add_zero]
    linarith only [hf',Int.floor_add_fract (x m),(abs_le.mp ha).1,(abs_le.mp hb).1]
  have hs : 0 < s := pos_of_mul_pos_left (lt_trans (by norm_num) (lt_of_not_ge hsmall)) hM'.le
  let h := ⌈(1/32 : ℝ)/s⌉₊
  have hh : h ≤ M := Nat.ceil_le.mpr ((div_le_iff₀ hs).mpr (by linarith only [lt_of_not_ge hsmall, mul_comm s (M:ℝ)]))
  have hsl : 1/32 ≤ s*(h:ℝ) := by
    have := (div_le_iff₀ hs).mp (Nat.le_ceil ((1/32:ℝ)/s))
    linarith only [this]
  have hsu : s*(h:ℝ) ≤ 1/16 := by
    have ht := mul_le_mul_of_nonneg_right (Nat.ceil_lt_add_one (by positivity : 0 ≤ (1/32:ℝ)/s)).le hs.le
    rw [add_mul,div_mul_cancel₀ _ hs.ne',one_mul] at ht
    change s ≤ 1/64 at hstep
    linarith only [ht,hstep]
  refine ⟨h,hh,fun m hm => ?_⟩
  obtain ⟨hm₁,hm₂⟩ := mem_Ico.mp hm
  have hl : (M:ℝ) ≤ m := by exact_mod_cast hm₁
  have hu : (m:ℝ) ≤ 2*M := by exact_mod_cast hm₂.le
  have ht : (h:ℝ) ≤ M := by exact_mod_cast hh
  have ha := (hx m (mem_Icc.mpr ⟨hm₁,by omega⟩)).2
  have hb := (hx (m+h) (mem_Icc.mpr ⟨by omega,by omega⟩)).2
  rw [Nat.cast_add] at hb
  let d := b*((m:ℝ)+h)^2-b*(m:ℝ)^2
  have hd : |d| = (|b| *(h:ℝ))*(2*m+h) := by
    rw [show d = (b*(h:ℝ))*(2*m+h) by unfold d; ring,abs_mul,abs_mul,
      abs_of_nonneg (Nat.cast_nonneg (α := ℝ) h),abs_of_nonneg (by positivity : 0 ≤ 2*(m:ℝ)+h)]
  have hd₁ : 1/16 ≤ |d| := by
    rw [hd]
    have hp := mul_le_mul_of_nonneg_left (show 2*(M:ℝ) ≤ 2*m+h by linarith only [hl,Nat.cast_nonneg (α := ℝ) h])
      (mul_nonneg (abs_nonneg b) (Nat.cast_nonneg h))
    dsimp only [s] at hsl
    linarith only [hsl,hp]
  have hd₂ : |d| ≤ 5/16 := by
    rw [hd]
    have hp := mul_le_mul_of_nonneg_left (show 2*(m:ℝ)+h ≤ 5*M by linarith only [hu,ht])
      (mul_nonneg (abs_nonneg b) (Nat.cast_nonneg h))
    dsimp only [s] at hsu
    linarith only [hsu,hp]
  have herr : |(x m-x (m+h))-(-d)| ≤ 1/256 := by
    rw [abs_le]
    dsimp only [d]
    obtain ⟨l,u⟩ := abs_le.mp ha
    obtain ⟨l',u'⟩ := abs_le.mp hb
    constructor <;> linarith only [l,u,l',u']
  have hab := abs_sub_abs_le_abs_sub (x m-x (m+h)) (-d)
  have hba := abs_sub_abs_le_abs_sub (-d) (x m-x (m+h))
  rw [abs_neg] at hab hba
  rw [abs_sub_comm (-d)] at hba
  exact separated_fractional_parts (by linarith only [hba,herr,hd₁]) (by linarith only [hab,herr,hd₂])

/-- On the interval from M to 3M a negative quadratic reading with small
mesh errors loses a fixed fraction of M under integer flooring. -/
theorem negative_quadratic_floor_loss {M : ℕ} (hM : 0 < M) {b : ℝ}
    (hstep : |b| *(M:ℝ) ≤ 1/64) (x : ℕ → ℝ)
    (hx : ∀ m ∈ Icc M (3*M), x m < 0 ∧ |x m-b*(m:ℝ)^2| ≤ 1/512) :
    (M:ℝ)/64 ≤ ∑ m ∈ Icc M (3*M), Int.fract (x m) := by
  obtain ⟨h,hh,hpair⟩ := shift_fractional_parts hM hstep x hx
  let F := fun m => Int.fract (x m)
  let S := Ico M (2*M)
  let T := Icc M (3*M)
  have hshift (j : ℕ) (hj : j ≤ M) : ∑ m ∈ S, F (m+j) ≤ ∑ m ∈ T, F m := by
    rw [← sum_image (f := F) (g := fun m : ℕ => m+j) (by intro a _ b _ hab; exact Nat.add_right_cancel hab)]
    apply sum_le_sum_of_subset_of_nonneg _ fun i _ _ => Int.fract_nonneg (x i)
    intro i hi
    obtain ⟨m,hm,rfl⟩ := mem_image.mp hi
    obtain ⟨hl,hu⟩ := mem_Ico.mp hm
    exact mem_Icc.mpr ⟨by omega,by omega⟩
  have hsum := sum_le_sum hpair
  rw [sum_const,Nat.card_Ico,show 2*M-M=M by omega,nsmul_eq_mul,sum_add_distrib] at hsum
  have h0 := hshift 0 (Nat.zero_le _)
  simp only [Nat.add_zero] at h0
  linarith only [hsum,h0,hshift h hh]

#print axioms negative_quadratic_floor_loss

end GaloisForLFunctions.CountingHolography.Sections
