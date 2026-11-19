import GaloisForLFunctions.RestrictedFactorizationCalculus.PrescribingTheSquarefreeFixedVertices
import GaloisForLFunctions.RestrictedFactorizationCalculus.ArbitrarilySlowSignedCrossingsOnOneDenseMatching

/-!
# Nonlinear allocation of the ordinary Mertens charge

Every nondecreasing unit-Lipschitz integer function h with h(0)=0
selects a subwalk of the fixed Möbius signs. Restoring the corresponding
edges after a separated completion allocates h(M) to fixed vertices and
M−h(M) to crossings with arbitrarily slowly diverging pointwise error.
-/

noncomputable section

open Filter Finset
open ArithmeticFunction hiding id
open scoped Classical ArithmeticFunction.Moebius
open GaloisForLFunctions.QuantitativeFactorizationMatching GaloisForLFunctions.BezoutValuationIncidence

namespace GaloisForLFunctions.RestrictedFactorizationCalculus

private abbrev fullWalk (X : ℕ) := ∑ n ∈ Icc 1 X,μ n
private def fixedStep (F : ℕ → ℕ) (n : ℕ) : ℤ := if Squarefree n ∧ F n=n then μ n else 0
private abbrev fixedWalk (F : ℕ → ℕ) (X : ℕ) := ∑ n ∈ Icc 1 X,fixedStep F n

private theorem real_full (X : ℕ) : (fullWalk X:ℝ)=coprimeMoebiusSum 1 X := by
  simp [fullWalk,coprimeMoebiusSum,coprimeMoebiusIndicator]

private theorem real_fixed (F : ℕ → ℕ) (X : ℕ) : (fixedWalk F X:ℝ)=fixedSignedPrefix F X := by
  simp only [fixedWalk,fixedSignedPrefix,squarefreeOf,filter_filter,sum_filter,fixedStep,Int.cast_sum]
  apply sum_congr rfl
  intro n _
  by_cases h : Squarefree n ∧ F n=n <;> simp [h]

private theorem bounded_increment_stretch (h : ℤ → ℤ) (inc : ∀ a,h (a+1)=h a ∨ h (a+1)=h a+1)
    (a b : ℤ) : |h a-h b| ≤ |a-b| := by
  have step (v : ℤ) (j : ℕ) : h v ≤ h (v+j) ∧ h (v+j) ≤ h v+j := by
    induction j with
    | zero => simp
    | succ j ih =>
      have hh := inc (v+j)
      rw [Nat.cast_succ,←add_assoc]
      omega
  have order {v u : ℤ} (le : v ≤ u) : h v ≤ h u ∧ h u-h v ≤ u-v := by
    have hh := step v (u-v).toNat
    rw [Int.toNat_of_nonneg (sub_nonneg.mpr le),show v+(u-v)=u by omega] at hh
    omega
  rcases le_total a b with le | le
  · have hh := order le
    rw [abs_of_nonpos (sub_nonpos.mpr hh.1),abs_of_nonpos (sub_nonpos.mpr le)]; omega
  · have hh := order le
    rw [abs_of_nonneg (sub_nonneg.mpr hh.1),abs_of_nonneg (sub_nonneg.mpr le)]; exact hh.2

private def chosenSteps (F : ℕ → ℕ) (h : ℤ → ℤ) : Set ℕ :=
  {n | h (fixedWalk F n) ≠ h (fixedWalk F (n-1))}

private theorem chosen_walk (F : ℕ → ℕ) (h : ℤ → ℤ) (zero : h 0=0)
    (inc : ∀ a,h (a+1)=h a ∨ h (a+1)=h a+1) (X : ℕ) :
    (∑ n ∈ Icc 1 X,if n ∈ chosenSteps F h then fixedStep F n else 0)=h (fixedWalk F X) := by
  induction X with
  | zero => simp [fixedWalk,zero]
  | succ n ih =>
    let s := fixedWalk F n
    let v := fixedStep F (n+1)
    have step : fixedWalk F (n+1)=s+v := sum_Icc_succ_top (by omega : 1 ≤ n+1) _
    have select : n+1 ∈ chosenSteps F h ↔ h (s+v) ≠ h s := by
      simp only [chosenSteps,Set.mem_setOf_eq,step,Nat.add_sub_cancel]
      rfl
    rw [sum_Icc_succ_top (by omega),ih,step]
    change h s+(if n+1 ∈ chosenSteps F h then v else 0)=h (s+v)
    simp only [select]
    have sign : v=0 ∨ v=1 ∨ v= -1 := by
      unfold v fixedStep
      split
      · rcases moebius_eq_or (n+1) with hv | hv | hv <;> omega
      · exact Or.inl rfl
    rcases sign with hv | hv | hv
    · simp [hv]
    · have hh := inc s
      rw [hv]; split <;> omega
    · have hh := inc (s-1)
      rw [sub_add_cancel] at hh
      have eq : s+v=s-1 := by omega
      rw [eq]
      by_cases same : h (s-1)=h s
      · simp [same]
      · rw [if_pos same]
        omega

private theorem compare_requested (F G : ℕ → ℕ) (S : Set ℕ) (X : ℕ) :
    |fixedSignedPrefix G X-(∑ n ∈ requestedFixed F S X,(μ n:ℝ))| ≤ (fixedErrors F G S X).card := by
  simpa only [requestedFixed,fixedErrors,supportErrors,Set.mem_setOf_eq] using
    fixed_charge_error_le_support_errors G {n | n ∈ S ∧ F n=n} X

private theorem requested_charge_of_subwalk (F : ℕ → ℕ) (h : ℤ → ℤ) (zero : h 0=0)
    (inc : ∀ a,h (a+1)=h a ∨ h (a+1)=h a+1) (X : ℕ) :
    |(∑ n ∈ requestedFixed F (chosenSteps F h) X,(μ n:ℝ))-(h (fixedWalk F X):ℝ)| ≤ 1 := by
  let S := chosenSteps F h
  have compare := chosen_walk F h zero inc X
  rw [←compare,Int.cast_sum,requestedFixed,squarefreeOf,filter_filter,sum_filter,←sum_sub_distrib]
  apply (abs_sum_le_sum_abs ..).trans
  have minor (n : ℕ) (hn : n ∈ Icc 1 X) :
      |(if Squarefree n ∧ (n=1 ∨ n ∈ S ∧ F n=n) then (μ n:ℝ) else 0)-
       ((if n ∈ S then fixedStep F n else 0 : ℤ):ℝ)| ≤ (if n=1 then 1 else 0) := by
    by_cases one : n=1
    · subst n
      by_cases sel : 1 ∈ S <;> by_cases fixed : F 1=1 <;> simp [fixedStep,sel,fixed]
    · by_cases sel : n ∈ S <;> by_cases fixed : F n=n <;> by_cases sf : Squarefree n <;>
        simp [one,sel,fixed,sf,fixedStep]
  apply (sum_le_sum minor).trans
  by_cases haveOne : 1 ∈ Icc 1 X <;> simp [haveOne]

/-- One legal matching divides the actual Mertens prefix according to
any integer rule whose successive increments are zero or one. At every
cutoff the two allocation errors are opposite, with absolute value at
most one plus half of the prescribed diverging envelope. -/
theorem nonlinear_allocation_of_the_mertens_prefix (h : ℤ → ℤ) (zero : h 0=0)
    (inc : ∀ a,h (a+1)=h a ∨ h (a+1)=h a+1) (w : ℕ → ℝ)
    (pos : ∀ n,0 ≤ w n) (top : Tendsto w atTop atTop) :
    ∃ G : ℕ → ℕ,(∀ n,G (G n)=n ∧ (G n=n ∨ GlobalDyadicOneTwoRel n (G n))) ∧
      (∀ ε : ℝ,0<ε → ∀ᶠ X : ℕ in atTop,((prefixUnpaid G X).card:ℝ) ≤ ε*X) ∧
      ∀ X,let M := ∑ n ∈ Icc 1 X,μ n
        |fixedSignedPrefix G X-(h M:ℝ)| ≤ 1+w X/2 ∧
        crossingSignedPrefix G X-((M:ℝ)-(h M:ℝ))= -(fixedSignedPrefix G X-(h M:ℝ)) := by
  let v := fun X => w X/4
  have vtop : Tendsto v atTop atTop := tendsto_atTop.mpr (fun c =>
    (top.eventually_ge_atTop (4*c)).mono (fun X h => by dsimp only [v]; linarith only [h]))
  obtain ⟨F,hF,pop,track⟩ := arbitrarily_slow_signed_crossings v (fun n => div_nonneg (pos n) (by norm_num)) vtop
  obtain ⟨B,price⟩ := separation_threshold_within_envelope w pos top
  let S := chosenSteps F h
  obtain ⟨G,back,law,card⟩ := prescribe_fixed_vertices_at_all_cutoffs F (fun n => (hF n).1)
    (fun n => (hF n).2) S B
  let D := fun X => ((range (X+1)).filter (fun n => B n<X)).card
  refine ⟨G,fun n => ⟨back n,law n⟩,?_,?_⟩
  · intro ε hε
    have quarter : 0<ε/4 := div_pos hε (by norm_num)
    filter_upwards [pop (ε/2) (half_pos hε),square_root_repair_cost_is_sublinear quarter] with X hX small
    have extra := (Nat.cast_le (α := ℝ)).mpr (price X).2
    have all := (Nat.cast_le (α := ℝ)).mpr (card X).2
    push_cast only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] at all
    linarith only [hX.1,extra,all,small]
  intro X
  let m := fullWalk X
  let f := fixedWalk F X
  let A := ∑ n ∈ requestedFixed F S X,(μ n:ℝ)
  have a1 := (compare_requested F G S X).trans ((Nat.cast_le.mpr (card X).1).trans (price X).1)
  have a2 := requested_charge_of_subwalk F h zero inc X
  have a3 : |(h f:ℝ)-(h m:ℝ)| ≤ |(f:ℝ)-(m:ℝ)| := by
    exact_mod_cast bounded_increment_stretch h inc f m
  have a4 : |(f:ℝ)-(m:ℝ)| ≤ w X/4 := by
    rw [abs_sub_comm,real_fixed,real_full]; exact (track X).2
  have h1 := abs_sub_le (fixedSignedPrefix G X) A (h f:ℝ)
  have h2 := abs_sub_le (fixedSignedPrefix G X) (h f:ℝ) (h m:ℝ)
  have charge := fixed_add_crossing G (fun n _ => ⟨back n,law n⟩) X
  rw [←real_full] at charge
  change |fixedSignedPrefix G X-(h m:ℝ)| ≤ _ ∧ _=_
  constructor
  · linarith only [a1,a2,a3,a4,h1,h2]
  · change crossingSignedPrefix G X-((m:ℝ)-(h m:ℝ))= -(fixedSignedPrefix G X-(h m:ℝ))
    linarith only [charge]

/-- Fixed vertices can carry the positive part of M and crossings the
negative part, simultaneously in the same sparse matching. -/
theorem separate_the_positive_and_negative_mertens_excursions (w : ℕ → ℝ) (pos : ∀ n,0 ≤ w n)
    (top : Tendsto w atTop atTop) :
    ∃ G : ℕ → ℕ,(∀ n,G (G n)=n ∧ (G n=n ∨ GlobalDyadicOneTwoRel n (G n))) ∧
      (∀ ε : ℝ,0<ε → ∀ᶠ X : ℕ in atTop,((prefixUnpaid G X).card:ℝ) ≤ ε*X) ∧
      ∀ᶠ X : ℕ in atTop,|fixedSignedPrefix G X-max (coprimeMoebiusSum 1 X) 0| ≤ w X ∧
        |crossingSignedPrefix G X-min (coprimeMoebiusSum 1 X) 0| ≤ w X := by
  let h := fun a : ℤ => max a 0
  have incr (a : ℤ) : h (a+1)=h a ∨ h (a+1)=h a+1 := by dsimp only [h]; omega
  obtain ⟨G,law,count,split⟩ := nonlinear_allocation_of_the_mertens_prefix h (by rfl) incr w pos top
  refine ⟨G,law,count,?_⟩
  filter_upwards [top.eventually_ge_atTop 2] with X hx
  have hm : (h (fullWalk X):ℝ)=max (coprimeMoebiusSum 1 X) 0 := by
    simp only [h,Int.cast_max,Int.cast_zero,real_full]
  have eq : (fullWalk X:ℝ)-(h (fullWalk X):ℝ)=min (coprimeMoebiusSum 1 X) 0 := by
    rw [real_full,hm]; rcases le_total (coprimeMoebiusSum 1 X) 0 with le | le <;> simp [le]
  have ca := (split X).1
  have cb := congrArg abs (split X).2
  change |fixedSignedPrefix G X-(h (fullWalk X):ℝ)| ≤ _ at ca
  change |crossingSignedPrefix G X-((fullWalk X:ℝ)-(h (fullWalk X):ℝ))|=_ at cb
  rw [eq,abs_neg,hm] at cb
  rw [hm] at ca
  rw [cb]
  exact ⟨by linarith only [hx,ca],by linarith only [hx,ca]⟩

/-- Every fixed proportion of the ordinary signed prefix can be carried
by the fixed vertices, uniformly over all sufficiently large cutoffs. -/
theorem fractional_allocation_of_the_mertens_prefix (α : ℝ) (hα : 0 ≤ α) (h1 : α ≤ 1)
    (w : ℕ → ℝ) (pos : ∀ n,0 ≤ w n) (top : Tendsto w atTop atTop) :
    ∃ G : ℕ → ℕ,(∀ n,G (G n)=n ∧ (G n=n ∨ GlobalDyadicOneTwoRel n (G n))) ∧
      (∀ ε : ℝ,0<ε → ∀ᶠ X : ℕ in atTop,((prefixUnpaid G X).card:ℝ) ≤ ε*X) ∧
      ∀ᶠ X : ℕ in atTop,|fixedSignedPrefix G X-α*coprimeMoebiusSum 1 X| ≤ w X ∧
        |crossingSignedPrefix G X-(1-α)*coprimeMoebiusSum 1 X| ≤ w X := by
  let h := fun a : ℤ => ⌊α*(a:ℝ)⌋
  have incr (a : ℤ) : h (a+1)=h a ∨ h (a+1)=h a+1 := by
    have eq : α*((a+1:ℤ):ℝ)=α*(a:ℝ)+α := by push_cast; ring
    have lo := Int.floor_mono (le_add_of_nonneg_right hα : α*(a:ℝ) ≤ α*(a:ℝ)+α)
    have hi := Int.floor_mono (show α*(a:ℝ)+α ≤ α*(a:ℝ)+1 by linarith only [h1])
    rw [Int.floor_add_one] at hi
    simp only [h,eq]
    omega
  obtain ⟨G,law,count,split⟩ := nonlinear_allocation_of_the_mertens_prefix h (by simp [h]) incr w pos top
  refine ⟨G,law,count,?_⟩
  filter_upwards [top.eventually_ge_atTop 4] with X hx
  let u := α*coprimeMoebiusSum 1 X
  have eq : h (fullWalk X)=⌊u⌋ := by simp only [h,u,real_full]
  have first := (split X).1
  change |fixedSignedPrefix G X-(h (fullWalk X):ℝ)| ≤ _ at first
  rw [eq] at first
  have round : |(⌊u⌋:ℝ)-u| ≤ 1 := by
    rw [abs_of_nonpos (sub_nonpos.mpr (Int.floor_le u))]
    linarith only [Int.lt_floor_add_one u]
  have paid := (abs_sub_le (fixedSignedPrefix G X) (⌊u⌋:ℝ) u).trans (add_le_add first round)
  have bound : |fixedSignedPrefix G X-u| ≤ w X := paid.trans (by linarith only [hx])
  have charge := fixed_add_crossing G (fun n _ => law n) X
  have opp : crossingSignedPrefix G X-(1-α)*coprimeMoebiusSum 1 X= -(fixedSignedPrefix G X-u) := by
    dsimp only [u]
    linarith only [charge]
  rw [opp,abs_neg]
  exact ⟨bound,bound⟩

#print axioms fractional_allocation_of_the_mertens_prefix
#print axioms nonlinear_allocation_of_the_mertens_prefix
#print axioms separate_the_positive_and_negative_mertens_excursions

end GaloisForLFunctions.RestrictedFactorizationCalculus
