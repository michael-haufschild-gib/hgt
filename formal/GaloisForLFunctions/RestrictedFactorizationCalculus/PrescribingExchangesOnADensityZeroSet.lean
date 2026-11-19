import GaloisForLFunctions.RestrictedFactorizationCalculus.OneInvolutionForEverySharpPrefix

/-!
# Prescribing an infinite set of prime exchanges

A prescribed involution on a set of density zero displaces only that set
and its old partners. Injectivity counts the old partners through every
sharp cutoff. Thus all prescriptions coexist with density-one matching.
-/

noncomputable section

open Finset Filter
open ArithmeticFunction hiding id
open scoped Classical ArithmeticFunction.Moebius
open GaloisForLFunctions.QuantitativeFactorizationMatching

namespace GaloisForLFunctions.RestrictedFactorizationCalculus

/-- The number of prescribed integers through the given cutoff, including zero. -/
def prescribedCount (T : Set ℕ) (X : ℕ) := ((Icc 0 X).filter (· ∈ T)).card

/-- Retain each old pair unless it meets the prescribed set. -/
def prescribe (F G : ℕ → ℕ) (T : Set ℕ) (n : ℕ) :=
  if n ∈ T then G n else if F n ∈ T then n else F n

private theorem prescribe_law {F G : ℕ → ℕ} {T : Set ℕ}
    (hF : Function.Involutive F) (eF : ∀ n,F n=n ∨ GlobalDyadicOneTwoRel n (F n))
    (hG : ∀ n ∈ T,G n ∈ T ∧ G (G n)=n ∧ (G n=n ∨ GlobalDyadicOneTwoRel n (G n))) (n : ℕ) :
    let H := prescribe F G T
    H (H n)=n ∧ (H n=n ∨ GlobalDyadicOneTwoRel n (H n)) := by
  by_cases hn : n ∈ T
  · obtain ⟨inside,back,edge⟩ := hG n hn
    simp only [prescribe,if_pos hn,if_pos inside,back,true_and]
    exact edge
  by_cases hm : F n ∈ T
  · simp only [prescribe,if_neg hn,if_pos hm,true_or,and_self]
  · simp only [prescribe,if_neg hn,if_neg hm,hF n,true_and]
    exact eF n

/-- Finite price of arbitrary prescriptions. The upper cutoff for the
old partners only needs to cover the old image of the initial interval. -/
theorem unpaid_bound_after_prescriptions (F G : ℕ → ℕ) (T : Set ℕ) (hf : Function.Injective F)
    {X Y : ℕ} (hY : ∀ n ≤ X,F n ≤ Y) :
    (prefixUnpaid (prescribe F G T) X).card ≤
      (prefixUnpaid F X).card+prescribedCount T X+prescribedCount T Y := by
  let S := (Icc 0 X).filter (· ∈ T)
  let S' := (Icc 0 X).filter (fun n => F n ∈ T)
  have sub : prefixUnpaid (prescribe F G T) X ⊆ (prefixUnpaid F X ∪ S) ∪ S' := by
    intro n hn
    obtain ⟨hm,hu⟩ := mem_filter.mp hn
    have hx := (mem_Icc.mp (mem_filter.mp hm).1).2
    have hi : n ∈ Icc 0 X := mem_Icc.mpr ⟨Nat.zero_le _,hx⟩
    by_cases h : n ∈ T
    · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨hi,h⟩))
    by_cases h' : F n ∈ T
    · exact mem_union_right _ (mem_filter.mpr ⟨hi,h'⟩)
    · rw [prescribe,if_neg h,if_neg h'] at hu
      exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨hm,hu⟩))
  have hcard : S'.card ≤ prescribedCount T Y := by
    apply card_le_card_of_injOn F _ hf.injOn
    intro n hn
    obtain ⟨hi,h⟩ := mem_filter.mp hn
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.zero_le _,hY _ (mem_Icc.mp hi).2⟩,h⟩
  exact (card_le_card sub).trans ((card_union_le ..).trans
    (Nat.add_le_add (card_union_le ..) hcard))

/-- Every legal prescription on any density-zero set survives in one
global involution. Its actual unpaid population is sublinear at every
large cutoff. The displacement is sublinear if the prescribed moves are. -/
theorem density_one_with_prescribed_exchanges (T : Set ℕ) (G : ℕ → ℕ)
    (hT : ∀ ε : ℝ,0<ε → ∀ᶠ X : ℕ in atTop,(prescribedCount T X:ℝ) ≤ ε*X)
    (hG : ∀ n ∈ T,G n ∈ T ∧ G (G n)=n ∧ (G n=n ∨ GlobalDyadicOneTwoRel n (G n))) :
    ∃ H : ℕ → ℕ, (∀ n ∈ T,H n=G n) ∧ Function.Involutive H ∧
      (∀ n,H n=n ∨ GlobalDyadicOneTwoRel n (H n)) ∧
      (∀ X, ∑ n ∈ Icc 1 X, μ n=∑ n ∈ prefixUnpaid H X,μ n) ∧
      (∀ ε : ℝ,0<ε → ∀ᶠ X : ℕ in atTop,((prefixUnpaid H X).card:ℝ) ≤ ε*X) ∧
      ((∀ ε : ℝ,0<ε → ∀ᶠ n : ℕ in atTop,n ∈ T → |(G n:ℝ)-n| ≤ ε*n) →
        ∀ ε : ℝ,0<ε → ∀ᶠ n : ℕ in atTop,|(H n:ℝ)-n| ≤ ε*n) := by
  obtain ⟨hF,hedge,_,hsmall⟩ := one_involution_with_sublinear_unpaid_prefix
  let F := dyadicPrimeSwitch
  let H := prescribe F G T
  have law (n : ℕ) := prescribe_law hF hedge hG n
  -- A common cutoff eventually covers the whole old image below X.
  obtain ⟨K,hK⟩ := eventually_atTop.mp (hsmall 1 zero_lt_one)
  let A := ∑ n ∈ range K,F n
  have imageBound {X n : ℕ} (hX : A ≤ X) (hn : n ≤ X) : F n ≤ 2*X := by
    by_cases hk : K ≤ n
    · have h := (abs_le.mp (hK n hk).2).2
      have hh : (F n:ℝ) ≤ 2*(n:ℝ) := by dsimp only [F]; linarith only [h]
      exact (by exact_mod_cast hh : F n ≤ 2*n).trans (Nat.mul_le_mul_left _ hn)
    · have hh : F n ≤ A := single_le_sum (fun m _ => Nat.zero_le (F m)) (mem_range.mpr (Nat.lt_of_not_ge hk))
      omega
  refine ⟨H,fun n hn => if_pos hn,fun n => (law n).1,fun n => (law n).2,
    prefix_switch_balance H (fun n _ => law n),?_,?_⟩
  · intro ε hε
    have hδ : 0<ε/4 := by positivity
    obtain ⟨L,hL⟩ := eventually_atTop.mp (hT _ hδ)
    filter_upwards [eventually_ge_atTop (max A L),hsmall _ hδ] with X hX hs
    have hA := (le_max_left ..).trans hX
    have hLX := (le_max_right ..).trans hX
    have hm := unpaid_bound_after_prescriptions F G T hF.injective (imageBound hA)
    have hmr := (Nat.cast_le (α := ℝ)).mpr hm
    push_cast at hmr
    have h₂ := hL (2*X) (by omega)
    push_cast at h₂
    change ((prefixUnpaid H X).card:ℝ) ≤ _
    linarith only [hmr,hL X hLX,h₂,hs.1]
  · intro move ε hε
    filter_upwards [move ε hε,hsmall ε hε] with n h₁ h₂
    change |((if n ∈ T then G n else if F n ∈ T then n else F n : ℕ):ℝ)-n| ≤ _
    split_ifs with h h'
    · exact h₁ h
    · rw [sub_self,abs_zero]; positivity
    · exact h₂.2

end GaloisForLFunctions.RestrictedFactorizationCalculus
