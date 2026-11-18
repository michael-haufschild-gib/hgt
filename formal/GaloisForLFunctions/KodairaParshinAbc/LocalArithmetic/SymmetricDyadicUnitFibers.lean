import GaloisForLFunctions.KodairaParshinAbc.LocalArithmetic.DyadicLargeTargetUniqueness

/-!
# Exact fibers of the symmetric dyadic unit equation

For an odd positive target, unequal dyadic orders force one summand to be
a signed unit of absolute value one. Equal orders allow only the diagonal
solution at target one. Above three, at most one neighbor of the target
is a power of two, since two multiples of four cannot differ by two.
-/

noncomputable section
open scoped Classical
namespace GaloisForLFunctions.KodairaParshinAbc
open GaloisForLFunctions.RHTower
local notation "U" => fieldOneSUnitSubgroup dyadicUnitPlaces

/-- Positive integral powers of two with exponent at least one. -/
def dyadicNeighborPower (t : ℚ) : Prop := ∃ k : ℕ, t = 2^(k+1)

/-- Candidate first summands, including both orders of each off-diagonal pair. -/
def dyadicOddTargetSummands (C : ℕ) : Finset ℚ := by
  classical
  exact ((if C=1 then {1/2} else ∅) ∪
    (if dyadicNeighborPower (C-1 : ℚ) then {1,(C:ℚ)-1} else ∅)) ∪
    (if dyadicNeighborPower ((C:ℚ)+1) then {-1,(C:ℚ)+1} else ∅)

private theorem mem_optional {α : Type*} (P : Prop) [Decidable P] (s : Finset α) (x : α) :
    x ∈ (if P then s else ∅) ↔ P ∧ x ∈ s := by
  by_cases h : P <;> simp [h]

private theorem mem_summands (C : ℕ) (t : ℚ) : t ∈ dyadicOddTargetSummands C ↔
    ((C=1 ∧ t=1/2) ∨ (dyadicNeighborPower ((C:ℚ)-1) ∧ (t=1 ∨ t=(C:ℚ)-1))) ∨
    (dyadicNeighborPower ((C:ℚ)+1) ∧ (t= -1 ∨ t=(C:ℚ)+1)) := by
  classical
  simp only [dyadicOddTargetSummands,Finset.mem_union,mem_optional,Finset.mem_insert,Finset.mem_singleton]

private theorem dyadic_odd_pair (C : ℕ) (hc : Odd C) (x y : U)
    (he : (x.val:ℚ)+(y.val:ℚ)=C) :
    (C=1 ∧ (x.val:ℚ)=1/2) ∨ ((x.val:ℚ)=1 ∨ (x.val:ℚ)= -1) ∨
      ((y.val:ℚ)=1 ∨ (y.val:ℚ)= -1) := by
  have hpos : 0<C := by obtain ⟨n,hn⟩ := hc; omega
  have hpos' : (0:ℚ)<C := by exact_mod_cast hpos
  have hc' : Odd (C:ℤ) := by exact_mod_cast hc
  have hv : padicValRat 2 (C:ℚ)=0 := by
    simpa only [Int.cast_natCast] using dyadicOdd_integer_valuation _ hc'
  by_cases h : padicValRat 2 (x.val:ℚ) = padicValRat 2 (y.val:ℚ)
  · have ha := (dyadicUnit_abs_val x).trans ((congrArg ((2:ℚ)^·) h).trans (dyadicUnit_abs_val y).symm)
    have hxy : (x.val:ℚ)=(y.val:ℚ) := by
      rcases le_or_gt 0 (x.val:ℚ) with hx|hx <;> rcases le_or_gt 0 (y.val:ℚ) with hy|hy
      · simpa only [abs_of_nonneg hx,abs_of_nonneg hy] using ha
      · rw [abs_of_nonneg hx,abs_of_neg hy] at ha; linarith only [ha,he,hpos']
      · rw [abs_of_neg hx,abs_of_nonneg hy] at ha; linarith only [ha,he,hpos']
      · simpa only [abs_of_neg hx,abs_of_neg hy,neg_inj] using ha
    have hdouble : (2:ℚ)*(x.val:ℚ)=C := by linarith only [he,hxy]
    have hh := congrArg (padicValRat 2) hdouble
    have htwo : padicValRat 2 (2:ℚ) = 1 := by
      simpa only [Nat.cast_ofNat] using padicValRat.self (p := 2) Nat.one_lt_two
    rw [padicValRat.mul (by norm_num : (2:ℚ) ≠ 0) x.val.ne_zero,htwo,hv] at hh
    have hx := dyadicUnit_abs_val x
    rw [show padicValRat 2 (x.val:ℚ) = -1 by omega,zpow_neg_one,
      abs_of_pos (by linarith only [hdouble,hpos'] : (0:ℚ)<(x.val:ℚ))] at hx
    have hx' : (x.val:ℚ)=1/2 := by simpa only [one_div] using hx
    exact Or.inl ⟨by exact_mod_cast (show (C:ℚ)=1 by linarith only [hdouble,hx']),hx'⟩
  · have hh := padicValRat.add_eq_min (p := 2) (he.trans_ne hpos'.ne') x.val.ne_zero y.val.ne_zero h
    rw [he,hv] at hh
    have hunit (w : U) (hw : padicValRat 2 (w.val:ℚ)=0) :
        (w.val:ℚ)=1 ∨ (w.val:ℚ)= -1 := by
      have ha := dyadicUnit_abs_val w
      rw [hw,zpow_zero] at ha
      rcases le_or_gt 0 (w.val:ℚ) with h|h
      · exact Or.inl ((abs_of_nonneg h).symm.trans ha)
      · right; rw [abs_of_neg h] at ha; exact neg_eq_iff_eq_neg.mp ha
    rcases le_total (padicValRat 2 (x.val:ℚ)) (padicValRat 2 (y.val:ℚ)) with ht|ht
    · exact Or.inr (Or.inl (hunit x (hh.trans (min_eq_left ht)).symm))
    · exact Or.inr (Or.inr (hunit y (hh.trans (min_eq_right ht)).symm))

private theorem neighbor_of_unit (C : ℕ) (hc : Odd C) (e : ℚ) (he : e=1 ∨ e= -1)
    (u : U) (hu : (u.val:ℚ)=(C:ℚ)-e) : dyadicNeighborPower ((C:ℚ)-e) := by
  have hc' : C=1 ∨ 3 ≤ C := by obtain ⟨n,hn⟩ := hc; omega
  have h : 1<(u.val:ℚ) := by
    rcases hc' with rfl|h
    · rcases he with rfl|rfl
      · exact (u.val.ne_zero (hu.trans (by norm_num))).elim
      · norm_num at hu; linarith only [hu]
    · have hl : (3:ℚ) ≤ C := by exact_mod_cast h
      rcases he with rfl|rfl <;> linarith only [hu,hl]
  rw [← hu]
  exact dyadicUnit_positive_power_of_one_lt u h

/-- Every odd target has exactly the listed rational first coordinates. -/
theorem dyadicOddTarget_first_summands (C : ℕ) (hc : Odd C) (t : ℚ) :
    (∃ z : RationalUnitSolutions dyadicUnitPlaces 1 1 C, (z.val.1.val:ℚ)=t) ↔
      t ∈ dyadicOddTargetSummands C := by
  rw [mem_summands]
  constructor
  · rintro ⟨⟨⟨x,y⟩,hz⟩,rfl⟩
    have he : (x.val:ℚ)+(y.val:ℚ)=C := by simpa only [one_mul] using hz
    rcases dyadic_odd_pair C hc x y he with hd|(hx|hx)|(hy|hy)
    · exact Or.inl (Or.inl hd)
    · exact Or.inl (Or.inr ⟨neighbor_of_unit C hc 1 (Or.inl rfl) y (by linarith only [he,hx]),Or.inl hx⟩)
    · have h := neighbor_of_unit C hc (-1) (Or.inr rfl) y (by linarith only [he,hx])
      exact Or.inr ⟨by simpa only [sub_neg_eq_add] using h,Or.inl hx⟩
    · have hh : (x.val:ℚ)=(C:ℚ)-1 := by linarith only [he,hy]
      exact Or.inl (Or.inr ⟨neighbor_of_unit C hc 1 (Or.inl rfl) x hh,Or.inr hh⟩)
    · have hh : (x.val:ℚ)=(C:ℚ)-(-1) := by linarith only [he,hy]
      exact Or.inr ⟨by simpa only [sub_neg_eq_add] using neighbor_of_unit C hc (-1) (Or.inr rfl) x hh,
        Or.inr (by simpa only [sub_neg_eq_add] using hh)⟩
  · have pair (x y : U) (h : (x.val:ℚ)+(y.val:ℚ)=C) (ht : t=(x.val:ℚ) ∨ t=(y.val:ℚ)) :
        ∃ z : RationalUnitSolutions dyadicUnitPlaces 1 1 C, (z.val.1.val:ℚ)=t := by
      rcases ht with h'|h'
      · exact ⟨⟨(x,y),by simpa only [one_mul] using h⟩,h'.symm⟩
      · exact ⟨⟨(y,x),by simpa only [one_mul] using (add_comm _ _).trans h⟩,h'.symm⟩
    rintro ((⟨rfl,rfl⟩|⟨⟨k,hk⟩,ht⟩)|⟨⟨k,hk⟩,ht⟩)
    · obtain ⟨u,hu⟩ := dyadicUnit_positive_power_exists 1
      have hi : ((u⁻¹).val:ℚ)=1/2 := by
        rw [Subgroup.coe_inv,Units.val_inv_eq_inv_val,hu,pow_one,one_div]
      exact pair u⁻¹ u⁻¹ (by rw [hi]; norm_num) (Or.inl hi.symm)
    · obtain ⟨u,hu⟩ := dyadicUnit_positive_power_exists (k+1)
      have hu' := hu.trans hk.symm
      apply pair 1 u
      · change 1+(u.val:ℚ)=C; linarith only [hu']
      · change t=1 ∨ t=(u.val:ℚ); rwa [hu']
    · obtain ⟨u,hu⟩ := dyadicUnit_positive_power_exists (k+1)
      let sign : U := ⟨-1,fieldOne_negOne_mem_sUnitSubgroup _⟩
      have hu' := hu.trans hk.symm
      apply pair sign u
      · change -1+(u.val:ℚ)=C; linarith only [hu']
      · change t= -1 ∨ t=(u.val:ℚ); rwa [hu']

/-- Projection onto the first coordinate enumerates the entire ordered solution fiber without multiplicity. -/
def dyadicOddTargetFiberEquiv (C : ℕ) (hc : Odd C) :
    RationalUnitSolutions dyadicUnitPlaces 1 1 C ≃ ↥(dyadicOddTargetSummands C) := by
  let f (z : RationalUnitSolutions dyadicUnitPlaces 1 1 C) : ↥(dyadicOddTargetSummands C) :=
    ⟨(z.val.1.val:ℚ),(dyadicOddTarget_first_summands C hc _).1 ⟨z,rfl⟩⟩
  apply Equiv.ofBijective f
  constructor
  · intro z w h
    have hx : (z.val.1.val:ℚ)=(w.val.1.val:ℚ) := congrArg Subtype.val h
    have he := z.property.trans w.property.symm
    simp only [one_mul,hx,add_right_inj] at he
    exact Subtype.ext (Prod.ext (Subtype.ext (Units.ext hx)) (Subtype.ext (Units.ext he)))
  · rintro ⟨t,ht⟩
    obtain ⟨z,hz⟩ := (dyadicOddTarget_first_summands C hc t).2 ht
    exact ⟨z,Subtype.ext hz⟩

/-- For every signed dyadic dilate, the exceptional fibers at one and three have sizes three and four. -/
theorem dyadicSymmetric_exceptional_cards (w : U) :
    Nat.card (RationalUnitSolutions dyadicUnitPlaces 1 1 (w.val:ℚ)) = 3 ∧
    Nat.card (RationalUnitSolutions dyadicUnitPlaces 1 1 (3*(w.val:ℚ))) = 4 := by
  classical
  have h₀ : ¬dyadicNeighborPower 0 := by
    rintro ⟨k,hk⟩; exact (pow_ne_zero _ (by norm_num : (2:ℚ) ≠ 0)) hk.symm
  have h₂ : dyadicNeighborPower 2 := ⟨0,by norm_num⟩
  have h₄ : dyadicNeighborPower 4 := ⟨1,by norm_num⟩
  have h (C : ℕ) (hc : Odd C) : Nat.card (RationalUnitSolutions dyadicUnitPlaces 1 1 (C*(w.val:ℚ))) =
      (dyadicOddTargetSummands C).card := by
    let e := rationalUnitSolutionsRescale dyadicUnitPlaces 1 1 C 1 1 w
    simpa using (Nat.card_congr e).symm.trans ((Nat.card_congr (dyadicOddTargetFiberEquiv C hc)).trans
      (by simp only [Nat.card_eq_fintype_card,Fintype.card_coe]))
  constructor
  · have he := h 1 ⟨0,rfl⟩
    norm_num [dyadicOddTargetSummands,h₀,h₂,Finset.card_insert_of_notMem] at he ⊢
    exact he
  · have he := h 3 ⟨1,rfl⟩
    norm_num [dyadicOddTargetSummands,h₂,h₄,Finset.card_insert_of_notMem] at he ⊢
    exact he

private theorem four_dvd_power {n : ℕ} (hn : 2 < n) (h : dyadicNeighborPower (n:ℚ)) : 4 ∣ n := by
  obtain ⟨k,hk⟩ := h
  have he : n = 2^(k+1) := by exact_mod_cast hk
  cases k with
  | zero => rw [he] at hn; norm_num at hn
  | succ j => exact ⟨2^j,by rw [he,pow_succ,pow_succ]; ring⟩

/-- Beyond three the ordered fiber is a transposed pair precisely when a neighbor is a power of two. -/
theorem dyadicSymmetric_large_card (C : ℕ) (hc : Odd C) (hl : 3<C) :
    Nat.card (RationalUnitSolutions dyadicUnitPlaces 1 1 C) =
      (if dyadicNeighborPower ((C:ℚ)-1) ∨ dyadicNeighborPower ((C:ℚ)+1) then 2 else 0) := by
  classical
  have hC : (3:ℚ)<C := by exact_mod_cast hl
  have hminus : (C:ℚ)-1 ≠ 1 := by linarith only [hC]
  have hplus : (C:ℚ)+1 ≠ -1 := by linarith only [hC]
  have hex (hm : dyadicNeighborPower ((C:ℚ)-1)) (hp : dyadicNeighborPower ((C:ℚ)+1)) : False := by
    have hm' : dyadicNeighborPower ((C-1:ℕ):ℚ) := by rwa [Nat.cast_sub (by omega),Nat.cast_one]
    have hp' : dyadicNeighborPower ((C+1:ℕ):ℚ) := by simpa only [Nat.cast_add,Nat.cast_one] using hp
    obtain ⟨i,hi⟩ := four_dvd_power (by omega : 2<C-1) hm'
    obtain ⟨j,hj⟩ := four_dvd_power (by omega : 2<C+1) hp'
    omega
  rw [Nat.card_congr (dyadicOddTargetFiberEquiv C hc),Nat.card_eq_fintype_card,Fintype.card_coe]
  by_cases hm : dyadicNeighborPower ((C:ℚ)-1) <;> by_cases hp : dyadicNeighborPower ((C:ℚ)+1)
  · exact (hex hm hp).elim
  all_goals simp [dyadicOddTargetSummands,show C ≠ 1 by omega,hm,hp,hminus.symm,hplus.symm]

#print axioms dyadicOddTarget_first_summands
#print axioms dyadicOddTargetFiberEquiv
#print axioms dyadicSymmetric_exceptional_cards
#print axioms dyadicSymmetric_large_card
end GaloisForLFunctions.KodairaParshinAbc
