import GaloisForLFunctions.RHTower.XiZeroCountRVMRemainder

/-!
# Integer blocks with the Riemann–von Mangoldt count

Rounding the smooth count gives a prescribed number of slots in each unit
interval. A fixed lower bound on the block sizes changes only a finite head.
The cumulative count therefore differs from the rounded main term by a constant.
-/

set_option autoImplicit false
noncomputable section
open Finset Filter Topology
namespace GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments
open _root_.RHTower

/-- Every unit block reserves at least six slots for a symmetric off-line divisor. -/
def rvmCompletionBlockSize (j : ℕ) : ℕ :=
  max 6 (⌊routeKSmoothRVMCount ((j:ℝ)+1)⌋₊-⌊routeKSmoothRVMCount (j:ℝ)⌋₊)

def rvmCompletionPrefix (J : ℕ) : ℕ :=
  ∑ j ∈ range J,rvmCompletionBlockSize (j+1)

lemma six_le_rvmCompletionBlockSize (j : ℕ) : 6≤rvmCompletionBlockSize j :=
  le_max_left _ _

lemma rvmCompletionPrefix_succ (J : ℕ) :
    rvmCompletionPrefix (J+1)=rvmCompletionPrefix J+rvmCompletionBlockSize (J+1) := by
  simp only [rvmCompletionPrefix,sum_range_succ]

/-- A lower increment bound complementary to the classical local upper bound. -/
lemma rvm_smooth_increment_lower {t H : ℝ} (ht : 0<t) (hH : 0≤H) :
    H*(Real.log t-Real.log routeKRVMBase)/(2*Real.pi) ≤
      routeKSmoothRVMCount (t+H)-routeKSmoothRVMCount t := by
  have htH : 0<t+H := add_pos_of_pos_of_nonneg ht hH
  have hl : Real.log t≤Real.log (t+H) :=
    Real.log_le_log ht (le_add_of_nonneg_right hH)
  have hm := mul_le_mul_of_nonneg_left hl htH.le
  rw [routeKSmoothRVMCount_sub_eq ht htH]
  apply div_le_div_of_nonneg_right ?_ (by positivity)
  nlinarith only [hm]

/-- Eventually the six-slot reserve is inactive, and each block has logarithmic size. -/
lemma eventually_rvmCompletionBlockSize_properties :
    ∀ᶠ j : ℕ in atTop,
      0≤routeKSmoothRVMCount (j:ℝ) ∧
      ⌊routeKSmoothRVMCount (j:ℝ)⌋₊≤⌊routeKSmoothRVMCount ((j:ℝ)+1)⌋₊ ∧
      rvmCompletionBlockSize j=
        ⌊routeKSmoothRVMCount ((j:ℝ)+1)⌋₊-⌊routeKSmoothRVMCount (j:ℝ)⌋₊ ∧
      (rvmCompletionBlockSize j:ℝ)≤Real.log (j:ℝ)+1 := by
  have hlog : Tendsto (fun j : ℕ => Real.log (j:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlog.eventually_ge_atTop (14*Real.pi+Real.log routeKRVMBase),
    (tendsto_natCast_atTop_atTop : Tendsto (fun j : ℕ => (j:ℝ)) atTop atTop).eventually_ge_atTop routeKRVMBase,
    eventually_ge_atTop 4] with j hjlog hjbase hj4
  have hj0 : (0:ℝ)<j := routeKRVMBase_pos.trans_le hjbase
  have hjF : 0≤routeKSmoothRVMCount (j:ℝ) := by
    have hr : 1≤(j:ℝ)/routeKRVMBase := (le_div_iff₀ routeKRVMBase_pos).mpr (by simpa using hjbase)
    have hl := Real.log_nonneg hr
    unfold routeKSmoothRVMCount
    positivity
  have hinc := rvm_smooth_increment_lower (t := (j:ℝ)) (H := 1) hj0 zero_le_one
  simp only [one_mul] at hinc
  have hseven : 7≤routeKSmoothRVMCount ((j:ℝ)+1)-routeKSmoothRVMCount (j:ℝ) := by
    apply le_trans ?_ hinc
    rw [le_div_iff₀ (by positivity : (0:ℝ)<2*Real.pi)]
    linarith only [hjlog]
  have hjF' : 0≤routeKSmoothRVMCount ((j:ℝ)+1) := by linarith only [hjF,hseven]
  have hf0 := Nat.floor_le hjF
  have hf1 := Nat.lt_floor_add_one (routeKSmoothRVMCount ((j:ℝ)+1))
  have hstep : ⌊routeKSmoothRVMCount (j:ℝ)⌋₊+6≤
      ⌊routeKSmoothRVMCount ((j:ℝ)+1)⌋₊ := by
    have hh : (⌊routeKSmoothRVMCount (j:ℝ)⌋₊:ℝ)+6≤
        (⌊routeKSmoothRVMCount ((j:ℝ)+1)⌋₊:ℝ) := by
      linarith only [hf0,hf1,hseven]
    exact_mod_cast hh
  have hmono : ⌊routeKSmoothRVMCount (j:ℝ)⌋₊≤
      ⌊routeKSmoothRVMCount ((j:ℝ)+1)⌋₊ := by omega
  have hsix : 6≤⌊routeKSmoothRVMCount ((j:ℝ)+1)⌋₊-
      ⌊routeKSmoothRVMCount (j:ℝ)⌋₊ := by omega
  have he : rvmCompletionBlockSize j=
      ⌊routeKSmoothRVMCount ((j:ℝ)+1)⌋₊-⌊routeKSmoothRVMCount (j:ℝ)⌋₊ :=
    max_eq_right hsix
  refine ⟨hjF,hmono,he,?_⟩
  rw [he,Nat.cast_sub hmono]
  have hfu := Nat.floor_le hjF'
  have hfl := Nat.lt_floor_add_one (routeKSmoothRVMCount (j:ℝ))
  have hu := routeKSmoothRVMCount_sub_le_log_of_mem_unitAbove
    (by exact_mod_cast hj4 : (4:ℝ)≤j) (by linarith : (j:ℝ)≤(j:ℝ)+1) le_rfl
  linarith only [hfu,hfl,hu]

/-- The cumulative number of slots equals the rounded main term plus one fixed offset. -/
theorem exists_rvmCompletionPrefix_floor_shift :
    ∃ J₀ : ℕ, ∃ c : ℝ, ∀ J : ℕ, J₀≤J →
      (rvmCompletionPrefix J:ℝ)=⌊routeKSmoothRVMCount ((J:ℝ)+1)⌋₊+c := by
  obtain ⟨J₀,hJ₀⟩ := eventually_atTop.mp eventually_rvmCompletionBlockSize_properties
  refine ⟨J₀,(rvmCompletionPrefix J₀:ℝ)-⌊routeKSmoothRVMCount ((J₀:ℝ)+1)⌋₊,?_⟩
  intro J hJ
  induction J,hJ using Nat.le_induction with
  | base => ring
  | succ J hJ ih =>
    have hb := hJ₀ (J+1) (by omega)
    have he : (rvmCompletionBlockSize (J+1):ℝ) =
        (⌊routeKSmoothRVMCount ((J:ℝ)+2)⌋₊:ℝ)-⌊routeKSmoothRVMCount ((J:ℝ)+1)⌋₊ := by
      rw [hb.2.2.1,Nat.cast_sub hb.2.1]
      push_cast
      rw [show (J:ℝ)+1+1=(J:ℝ)+2 by ring]
    rw [rvmCompletionPrefix_succ,Nat.cast_add,ih,he]
    push_cast
    have ha : (J:ℝ)+1+1=(J:ℝ)+2 := by ring
    rw [ha]
    ring

/-- The slot prefix has a uniformly bounded error at integer endpoints. -/
theorem exists_rvmCompletionPrefix_bounded_error :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ J : ℕ in atTop,
      |(rvmCompletionPrefix J:ℝ)-routeKSmoothRVMCount ((J:ℝ)+1)|≤C := by
  obtain ⟨J₀,c,hc⟩ := exists_rvmCompletionPrefix_floor_shift
  refine ⟨|c|+1,by positivity,?_⟩
  have hpos := eventually_rvmCompletionBlockSize_properties
  filter_upwards [eventually_ge_atTop J₀,hpos] with J hJ hj
  have hJ1 : 0≤routeKSmoothRVMCount ((J:ℝ)+1) := by
    by_contra h
    have hz : ⌊routeKSmoothRVMCount ((J:ℝ)+1)⌋₊=0 := Nat.floor_eq_zero.mpr (by linarith)
    have hs := six_le_rvmCompletionBlockSize J
    rw [hj.2.2.1,hz] at hs
    omega
  rw [hc J hJ]
  have hlo := Nat.floor_le hJ1
  have hhi := Nat.lt_floor_add_one (routeKSmoothRVMCount ((J:ℝ)+1))
  have hclo := neg_abs_le c
  have hchi := le_abs_self c
  exact abs_le.mpr ⟨by linarith only [hhi,hclo],by linarith only [hlo,hchi]⟩

/-- A coarse global bound controls the summability of coefficients placed in the slots. -/
theorem exists_rvmCompletionBlockSize_linear_bound :
    ∃ C : ℝ, 0<C ∧ ∀ j : ℕ, (rvmCompletionBlockSize j:ℝ)≤C*((j:ℝ)+1) := by
  obtain ⟨J,hJ⟩ := eventually_atTop.mp
    (eventually_rvmCompletionBlockSize_properties.and (eventually_ge_atTop 1))
  let S : ℝ := ∑ j ∈ range J,(rvmCompletionBlockSize j:ℝ)
  have hS : 0≤S := sum_nonneg fun _ _ => Nat.cast_nonneg _
  refine ⟨S+1,by positivity,?_⟩
  intro j
  by_cases hj : J≤j
  · have hb := (hJ j hj).1.2.2.2
    have hj1 := (hJ j hj).2
    have hj0 : (0:ℝ)<j := by exact_mod_cast (show 0<j by omega)
    have hl := Real.log_le_sub_one_of_pos hj0
    calc
      _ ≤ (j:ℝ)+1 := by linarith only [hb,hl]
      _ ≤ (S+1)*((j:ℝ)+1) := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right
          (show (1:ℝ)≤S+1 by linarith only [hS]) (show (0:ℝ)≤(j:ℝ)+1 by positivity)
  · have hterm : (rvmCompletionBlockSize j:ℝ)≤S :=
      single_le_sum (fun k _ => Nat.cast_nonneg (rvmCompletionBlockSize k))
        (mem_range.mpr (lt_of_not_ge hj))
    calc
      _ ≤ S+1 := by linarith only [hterm]
      _ ≤ (S+1)*((j:ℝ)+1) := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left
          (show (1:ℝ)≤(j:ℝ)+1 by have := Nat.cast_nonneg (α := ℝ) j;linarith)
          (show 0≤S+1 by positivity)

/-- Any count lying between the two adjacent slot prefixes has the classical
two-term asymptotic with a logarithmic remainder. -/
theorem exists_rvmCompletion_sandwich_log_error :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ T : ℝ in atTop, ∀ N : ℕ,
      rvmCompletionPrefix (⌊T⌋₊-1)≤N → N≤rvmCompletionPrefix ⌊T⌋₊ →
      |(N:ℝ)-routeKSmoothRVMCount T|≤C*Real.log T := by
  obtain ⟨C,hC,herr⟩ := exists_rvmCompletionPrefix_bounded_error
  obtain ⟨J₀,hJ₀⟩ := eventually_atTop.mp herr
  refine ⟨C+1,by positivity,?_⟩
  filter_upwards [eventually_ge_atTop ((J₀:ℝ)+2),eventually_ge_atTop (4:ℝ)] with T hTJ hT4
  intro N hNlo hNhi
  let J := ⌊T⌋₊
  have hJbig : J₀+2≤J := Nat.le_floor (by simpa using hTJ)
  have hJ1 : 1≤J := by omega
  have hT0 : 0<T := by linarith only [hT4]
  have hfloor : (J:ℝ)≤T := Nat.floor_le hT0.le
  have hceil : T<(J:ℝ)+1 := Nat.lt_floor_add_one T
  have hlow := hJ₀ (J-1) (by omega)
  have hupp := hJ₀ J (by omega)
  have heJ : ((J-1:ℕ):ℝ)+1=(J:ℝ) := by exact_mod_cast Nat.sub_add_cancel hJ1
  rw [heJ] at hlow
  have hvlo := routeKSmoothRVMCount_sub_le_log_of_mem_unitBelow hT4
    (by linarith only [hceil] : T-1≤(J:ℝ)) hfloor
  have hvhi := routeKSmoothRVMCount_sub_le_log_of_mem_unitAbove hT4 hceil.le
    (by linarith only [hfloor] : (J:ℝ)+1≤T+1)
  have hNlo' : (rvmCompletionPrefix (J-1):ℝ)≤N := by exact_mod_cast hNlo
  have hNhi' : (N:ℝ)≤rvmCompletionPrefix J := by exact_mod_cast hNhi
  have hlo := (abs_le.mp hlow).1
  have hup := (abs_le.mp hupp).2
  have habs : |(N:ℝ)-routeKSmoothRVMCount T|≤C+Real.log T :=
    abs_le.mpr ⟨by linarith only [hNlo',hlo,hvlo],by linarith only [hNhi',hup,hvhi]⟩
  have hlog : 1≤Real.log T := by
    rw [Real.le_log_iff_exp_le hT0]
    linarith only [Real.exp_one_lt_d9,hT4]
  exact habs.trans (by nlinarith only [mul_le_mul_of_nonneg_left hlog hC.le])

/-- Unit-height blocks give exact finite lower and upper counting brackets. -/
theorem finite_unit_block_count_sandwich {β : ℕ → Type*} [∀ j,Fintype (β j)]
    (γ : (j : ℕ) → β j → ℝ)
    (hγ : ∀ (j : ℕ) (b : β j),(j:ℝ)+1≤γ j b ∧ γ j b<(j:ℝ)+2)
    {T : ℝ} (hT : 1≤T) :
    Finite {a : (j : ℕ) × β j // γ a.1 a.2≤T} ∧
      (∑ j ∈ range (⌊T⌋₊-1),Fintype.card (β j))≤
        Nat.card {a : (j : ℕ) × β j // γ a.1 a.2≤T} ∧
      Nat.card {a : (j : ℕ) × β j // γ a.1 a.2≤T}≤
        ∑ j ∈ range ⌊T⌋₊,Fintype.card (β j) := by
  classical
  let J := ⌊T⌋₊
  let A := {a : (j : ℕ) × β j // γ a.1 a.2≤T}
  let U := (j : Fin J) × β j.val
  let L := (j : Fin (J-1)) × β j.val
  let f : A → U := fun a => ⟨⟨a.val.1,by
    have hj : a.val.1+1≤J := Nat.le_floor (by
      simpa only [Nat.cast_add,Nat.cast_one] using (hγ a.val.1 a.val.2).1.trans a.property)
    omega⟩,a.val.2⟩
  have hf : Function.Injective f := by
    intro a b he
    apply Subtype.ext
    exact congrArg (fun v : U => (⟨v.1.val,v.2⟩ : (j : ℕ) × β j)) he
  letI : Fintype A := Fintype.ofInjective f hf
  have hfloor : (J:ℝ)≤T := Nat.floor_le (zero_le_one.trans hT)
  let g : L → A := fun a => ⟨⟨a.1.val,a.2⟩,by
    have hj : a.1.val+2≤J := by have := a.1.isLt;omega
    have hjR : (a.1.val:ℝ)+2≤J := by exact_mod_cast hj
    exact ((hγ a.1.val a.2).2.trans_le (hjR.trans hfloor)).le⟩
  have hg : Function.Injective g := by
    rintro ⟨i,a⟩ ⟨j,b⟩ he
    have hij : i=j := Fin.ext (congrArg (fun v : A => v.val.1) he)
    subst j
    have hv : (⟨i.val,a⟩ : (j : ℕ) × β j)=⟨i.val,b⟩ := congrArg Subtype.val he
    have hab : a=b := by simpa only [Sigma.mk.inj_iff,heq_eq_eq,true_and] using hv
    subst b
    rfl
  have hU : Fintype.card U=∑ j ∈ range J,Fintype.card (β j) := by
    rw [Fintype.card_sigma]
    exact Fin.sum_univ_eq_sum_range (fun j => Fintype.card (β j)) _
  have hL : Fintype.card L=∑ j ∈ range (J-1),Fintype.card (β j) := by
    rw [Fintype.card_sigma]
    exact Fin.sum_univ_eq_sum_range (fun j => Fintype.card (β j)) _
  refine ⟨inferInstance,?_,?_⟩
  · change _≤Nat.card A
    rw [Nat.card_eq_fintype_card,← hL]
    exact Fintype.card_le_of_injective g hg
  · change Nat.card A≤_
    rw [Nat.card_eq_fintype_card,← hU]
    exact Fintype.card_le_of_injective f hf

/-- Prescribing these finite block sizes fixes the full real-height counting asymptotic. -/
theorem exists_unit_block_rvm_count {β : ℕ → Type*} [∀ j,Fintype (β j)]
    (γ : (j : ℕ) → β j → ℝ)
    (hγ : ∀ (j : ℕ) (b : β j),(j:ℝ)+1≤γ j b ∧ γ j b<(j:ℝ)+2)
    (hcard : ∀ j,Fintype.card (β j)=rvmCompletionBlockSize (j+1)) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ T : ℝ in atTop,
      |(Nat.card {a : (j : ℕ) × β j // γ a.1 a.2≤T}:ℝ)-routeKSmoothRVMCount T|≤C*Real.log T := by
  obtain ⟨C,hC,hbound⟩ := exists_rvmCompletion_sandwich_log_error
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound,eventually_ge_atTop (1:ℝ)] with T hboundT hT
  obtain ⟨_,hlo,hhi⟩ := finite_unit_block_count_sandwich γ hγ hT
  simp only [hcard] at hlo hhi
  exact hboundT _ hlo hhi

#print axioms finite_unit_block_count_sandwich
#print axioms exists_unit_block_rvm_count
#print axioms exists_rvmCompletionBlockSize_linear_bound
#print axioms exists_rvmCompletion_sandwich_log_error
#print axioms rvm_smooth_increment_lower
#print axioms eventually_rvmCompletionBlockSize_properties
#print axioms exists_rvmCompletionPrefix_floor_shift
#print axioms exists_rvmCompletionPrefix_bounded_error
end GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments
