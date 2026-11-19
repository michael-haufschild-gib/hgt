import GaloisForLFunctions.RestrictedFactorizationCalculus.EqualMobiusSignsInConsecutiveWindows
import GaloisForLFunctions.RestrictedFactorizationCalculus.ArbitrarilySlowSignedCrossingsOnOneDenseMatching

/-!
# The bounded endpoint of signed cancellation

A long enough window of equal nonzero signs either contains a selected
vertex of that sign or forces the complementary primitive beyond its
cap at one endpoint. Positive lower density of both orientations gives
a uniform tradeoff at every sufficiently large cutoff.
-/

noncomputable section

open Filter Finset
open ArithmeticFunction hiding id
open scoped Classical ArithmeticFunction.Moebius
open GaloisForLFunctions.QuantitativeFactorizationMatching GaloisForLFunctions.BezoutValuationIncidence

namespace GaloisForLFunctions.RestrictedFactorizationCalculus

/-- Signed ordinary prefix of the complement of S. -/
def complementaryCharge (S : Set ℕ) (X : ℕ) : ℤ :=
  ∑ n ∈ Icc 1 X,if n ∈ S then 0 else μ n

/-- Selected occurrences of a specified Möbius sign through X. -/
def selectedMobiusSigns (S : Set ℕ) (σ : ℤ) (X : ℕ) := (Icc 1 X).filter (fun n => n ∈ S ∧ μ n=σ)
/-- Cutoffs through X at which the complementary charge exceeds K in modulus. -/
def complementaryExcursions (S : Set ℕ) (K X : ℕ) := (Icc 1 X).filter (fun n => (K:ℤ) < |complementaryCharge S n|)

private theorem window_change (S : Set ℕ) (H x : ℕ) :
    complementaryCharge S (x+H)-complementaryCharge S x=
      ∑ r ∈ Icc 1 H,if x+r ∈ S then 0 else μ (x+r) := by
  induction H with
  | zero => simp
  | succ H ih =>
    rw [Nat.add_succ,sum_Icc_succ_top (by omega : 1 ≤ H+1)]
    unfold complementaryCharge at ih ⊢
    rw [sum_Icc_succ_top (by omega : 1 ≤ x+H+1)]
    rw [←ih]
    let step : ℤ := if (x+H+1) ∈ S then 0 else μ (x+H+1)
    change (_+step)-_=(_-_)+step
    abel

private theorem detect_equal_window (S : Set ℕ) {σ : ℤ} (hσ : σ=1 ∨ σ= -1)
    {k K H x : ℕ} (large : 2*K<k) (h : equalSignWindow H k σ x) :
    (∃ r ∈ Icc 1 H,x+r ∈ S ∧ μ (x+r)=σ) ∨ (K:ℤ) < |complementaryCharge S x| ∨
      (K:ℤ) < |complementaryCharge S (x+H)| := by
  by_contra! no
  obtain ⟨miss,lo,hi⟩ := no
  have same (r : ℕ) (hr : r ∈ Icc 1 H) : (if x+r ∈ S then (0:ℤ) else μ (x+r))=μ (x+r) := by
    by_cases chosen : x+r ∈ S
    · rw [if_pos chosen]; exact ((h.2 r hr).resolve_right (miss r hr chosen)).symm
    · rw [if_neg chosen]
  let I := (Icc 1 H).filter (fun r => μ (x+r) ≠ 0)
  have eq : (∑ r ∈ Icc 1 H,μ (x+r))=k*σ := by
    have supp : (∑ r ∈ I,μ (x+r))=∑ r ∈ Icc 1 H,μ (x+r) := by
      apply sum_subset (filter_subset ..)
      intro r hr absent
      exact of_not_not (fun hn => absent (mem_filter.mpr ⟨hr,hn⟩))
    rw [←supp]
    change _=(k:ℤ)*σ
    have flat : (∑ r ∈ I,μ (x+r))=∑ _ ∈ I,σ := sum_congr rfl
      (fun r hr => (h.2 r (mem_filter.mp hr).1).resolve_left (mem_filter.mp hr).2)
    rw [flat,sum_const,nsmul_eq_mul,show I.card=k from h.1]
  have dif := window_change S H x
  rw [sum_congr rfl same,eq] at dif
  have l := abs_le.mp lo
  have u := abs_le.mp hi
  have big : (2:ℤ)*K<k := by exact_mod_cast large
  rcases hσ with rfl | rfl <;> simp only [mul_one,mul_neg_one] at dif <;> omega

/-- Uniform over all selections and both signs. Through each sufficiently
large cutoff, the number of selected vertices of that sign plus the
number of excursions of the complementary charge occupies a positive
fraction. The fraction depends only on the prescribed cap. -/
theorem bounded_charge_requires_both_signs_or_frequent_excursions (K : ℕ) :
    ∃ C : ℕ,0<C ∧ ∀ᶠ X : ℕ in atTop,∀ S : Set ℕ,∀ σ : ℤ,σ=1 ∨ σ= -1 →
      X ≤ C*((selectedMobiusSigns S σ X).card+(complementaryExcursions S K X).card) := by
  let k := 2*K+1
  obtain ⟨H,A,hH,hA,hits⟩ := positive_lower_density_of_equal_sign_windows k
  obtain ⟨Np,Hp⟩ := eventually_atTop.mp (hits 1 (Or.inl rfl))
  obtain ⟨Nm,Hm⟩ := eventually_atTop.mp (hits (-1) (Or.inr rfl))
  refine ⟨2*A*(H+2),by positivity,?_⟩
  filter_upwards [eventually_ge_atTop (Np+Nm+2*H+1)] with X hx
  intro S σ hσ
  let Y := X-H
  let W := (Icc 1 Y).filter (equalSignWindow H k σ)
  let B := selectedMobiusSigns S σ X
  let E := complementaryExcursions S K X
  have hit : Y ≤ A*W.card := by
    rcases hσ with rfl | rfl
    · exact Hp _ (by dsimp only [Y]; omega)
    · exact Hm _ (by dsimp only [Y]; omega)
  let withAt := fun r : ℕ => W.filter (fun x => x+r ∈ B)
  let after := W.filter (fun x => x+H ∈ E)
  have cover : W ⊆ (Icc 1 H).biUnion withAt ∪ (E ∪ after) := by
    intro x hw
    obtain ⟨hi,win⟩ := mem_filter.mp hw
    obtain ⟨x0,xy⟩ := mem_Icc.mp hi
    have end_ : x+H ≤ X := by dsimp only [Y] at xy; omega
    rcases detect_equal_window S hσ (by dsimp only [k]; omega : 2*K<k) win with hh | left | right
    · obtain ⟨r,hr,chosen,sign⟩ := hh
      have mr := mem_Icc.mp hr
      exact mem_union_left _ (mem_biUnion.mpr ⟨r,hr,mem_filter.mpr ⟨hw,mem_filter.mpr
        ⟨mem_Icc.mpr ⟨by omega,by omega⟩,chosen,sign⟩⟩⟩)
    · exact mem_union_right _ (mem_union_left _ (mem_filter.mpr ⟨mem_Icc.mpr ⟨x0,by omega⟩,left⟩))
    · exact mem_union_right _ (mem_union_right _ (mem_filter.mpr ⟨hw,mem_filter.mpr
        ⟨mem_Icc.mpr ⟨by omega,end_⟩,right⟩⟩))
  have shifted_count (r : ℕ) (U : Finset ℕ) : (W.filter (fun x => x+r ∈ U)).card ≤ U.card :=
    card_le_card_of_injOn (fun x => x+r) (fun x hx => (mem_filter.mp hx).2)
      (fun a _ b _ h => Nat.add_right_cancel h)
  have size := (card_le_card cover).trans ((card_union_le ..).trans (Nat.add_le_add
    ((card_biUnion_le ..).trans (sum_le_sum (fun r (_ : r ∈ Icc 1 H) => shifted_count r B)))
    ((card_union_le ..).trans (Nat.add_le_add_left (shifted_count H E) E.card))))
  simp only [sum_const,nsmul_eq_mul,Nat.card_Icc,Nat.add_sub_cancel] at size
  have lim : W.card ≤ (H+2)*(B.card+E.card) := size.trans (by
    nlinarith only [Nat.zero_le (H*E.card),Nat.zero_le B.card])
  have xy : X ≤ 2*Y := by dsimp only [Y]; omega
  change X ≤ 2*A*(H+2)*(B.card+E.card)
  exact xy.trans ((Nat.mul_le_mul_left 2 (hit.trans (Nat.mul_le_mul_left A lim))).trans_eq (by ring))

private theorem complement_of_fixed {F : ℕ → ℕ}
    (law : ∀ n,F (F n)=n ∧ (F n=n ∨ GlobalDyadicOneTwoRel n (F n))) (X : ℕ) :
    (complementaryCharge {n | Squarefree n ∧ F n=n} X:ℝ)=crossingSignedPrefix F X := by
  have charges := fixed_add_crossing F (fun n _ => law n) X
  have split : fixedSignedPrefix F X+(complementaryCharge {n | Squarefree n ∧ F n=n} X:ℝ)=
      coprimeMoebiusSum 1 X := by
    simp only [fixedSignedPrefix,squarefreeOf,filter_filter,sum_filter,complementaryCharge,Int.cast_sum,
      Set.mem_setOf_eq,coprimeMoebiusSum,coprimeMoebiusIndicator]
    rw [←sum_add_distrib]
    apply sum_congr rfl
    intro n _
    by_cases h : Squarefree n ∧ F n=n <;> simp [h]
  linarith only [charges,split]

/-- A nondecreasing integer cap bounds every signed crossing of some
density-one restricted matching with sublinear displacement exactly when
the cap tends to infinity. -/
theorem attainable_monotone_crossing_caps (B : ℕ → ℕ) (mono : Monotone B) :
    (∃ F : ℕ → ℕ,(∀ n,F (F n)=n ∧ (F n=n ∨ GlobalDyadicOneTwoRel n (F n))) ∧
      (∀ ε : ℝ,0<ε → ∀ᶠ X : ℕ in atTop,((prefixUnpaid F X).card:ℝ) ≤ ε*X ∧
        |(F X:ℝ)-X| ≤ ε*X) ∧ ∀ X,|crossingSignedPrefix F X| ≤ B X) ↔ Tendsto B atTop atTop := by
  constructor
  · rintro ⟨F,law,count,cap⟩
    apply tendsto_atTop.mpr
    intro K
    suffices h : ∃ n,K ≤ B n by
      obtain ⟨n,hn⟩ := h
      exact (eventually_ge_atTop n).mono (fun m hm => hn.trans (mono hm))
    by_contra! bounded
    let S : Set ℕ := {n | Squarefree n ∧ F n=n}
    have paid (X : ℕ) : |complementaryCharge S X| ≤ (K:ℤ) := by
      have h := (cap X).trans (Nat.cast_le.mpr (bounded X).le)
      rw [←complement_of_fixed law] at h
      exact_mod_cast h
    obtain ⟨C,hC,must⟩ := bounded_charge_requires_both_signs_or_frequent_excursions K
    let ε : ℝ := 1/(2*(C:ℝ))
    have hCr : (0:ℝ)<C := Nat.cast_pos.mpr hC
    have pos : 0<ε := by dsimp only [ε]; positivity
    obtain ⟨X,req,hcnt,xpos⟩ := (must.and ((count ε pos).and (eventually_ge_atTop 1))).exists
    have nec := req S 1 (Or.inl rfl)
    have none : complementaryExcursions S K X=∅ :=
      filter_eq_empty_iff.mpr (fun n _ => (paid n).not_gt)
    rw [none,card_empty,add_zero] at nec
    have sub : selectedMobiusSigns S 1 X ⊆ prefixUnpaid F X := by
      intro n hn
      simp only [selectedMobiusSigns,mem_filter] at hn
      obtain ⟨hi,sel,_⟩ := hn
      exact mem_filter.mpr ⟨mem_filter.mpr ⟨hi,sel.1⟩,Or.inl sel.2⟩
    have need : (X:ℝ) ≤ C*((prefixUnpaid F X).card:ℝ) := by
      exact_mod_cast nec.trans (Nat.mul_le_mul_left C (card_le_card sub))
    have upper := mul_le_mul_of_nonneg_left hcnt.1 hCr.le
    have cancel : (C:ℝ)*(ε*X)=(X:ℝ)/2 := by dsimp only [ε]; field_simp
    rw [cancel] at upper
    have xp : (0:ℝ)<X := Nat.cast_pos.mpr xpos
    linarith only [need,upper,xp]
  · intro top
    obtain ⟨F,law,count,cap⟩ := arbitrarily_slow_signed_crossings (fun n => (B n:ℝ))
      (fun n => Nat.cast_nonneg _) (tendsto_natCast_atTop_atTop.comp top)
    exact ⟨F,law,count,fun X => (cap X).1⟩

#print axioms attainable_monotone_crossing_caps

#print axioms bounded_charge_requires_both_signs_or_frequent_excursions

end GaloisForLFunctions.RestrictedFactorizationCalculus
