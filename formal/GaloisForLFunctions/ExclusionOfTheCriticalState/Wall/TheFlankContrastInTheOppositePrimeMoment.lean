import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.OppositePrimeExcursionsOnOneFixedBand

/-!
# The flank contrast in the opposite-prime moment

At a fixed numerator, maximize over the two orientations and the two
flanks. Twice this price is the positive part of the middle square plus
the absolute middle discrepancy times the absolute difference of the
flanks, less the signed middle discrepancy times the complete row.
-/

open Finset Filter
noncomputable section
namespace GaloisForLFunctions.ExclusionOfTheCriticalState

/-- Largest of the four original prices at the same numerator. -/
def largestOppositePrimePrice (k L H : ℕ) : ℝ :=
  max (max (oppositePrimeProduct true 1 k L H) (oppositePrimeProduct true (-1) k L H))
    (max (oppositePrimeProduct false 1 k L H) (oppositePrimeProduct false (-1) k L H))

/-- Unsigned middle square plus the middle discrepancy times the
absolute left-right flank contrast. -/
def middleFlankContrastPrice (k L H : ℕ) : ℝ :=
  let u := oddQuotientPrimeExcess (Ioc k L) H
  let v := oddQuotientPrimeExcess (middleTestFlank true k L H) H
  let w := oddQuotientPrimeExcess (middleTestFlank false k L H) H
  (u^2+|u| * |v-w|)/(H:ℝ)^2

private theorem contrast_nonneg (k L H : ℕ) : 0 ≤ middleFlankContrastPrice k L H :=
  div_nonneg (add_nonneg (sq_nonneg _) (mul_nonneg (abs_nonneg _) (abs_nonneg _))) (sq_nonneg _)

private theorem two_signs (u v : ℝ) :
    max (max 0 u*max 0 (-v)) (max 0 (-u)*max 0 v) = max 0 (-(u*v)) := by
  rcases le_total 0 u with hu|hu <;> rcases le_total 0 v with hv|hv
  · simp [max_eq_right hu,max_eq_right hv,max_eq_left (neg_nonpos.mpr hu),
      max_eq_left (neg_nonpos.mpr hv),max_eq_left (neg_nonpos.mpr (mul_nonneg hu hv))]
  · have h : 0≤ -(u*v) := neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos hu hv)
    simp [max_eq_right hu,max_eq_left hv,max_eq_left (neg_nonpos.mpr hu),
      max_eq_right (neg_nonneg.mpr hv),max_eq_right h,max_eq_left h]
  · have h : 0≤ -(u*v) := neg_nonneg.mpr (mul_nonpos_of_nonpos_of_nonneg hu hv)
    simp [max_eq_left hu,max_eq_right hv,max_eq_right (neg_nonneg.mpr hu),
      max_eq_left (neg_nonpos.mpr hv),max_eq_right h]
  · simp [max_eq_left hu,max_eq_left hv,max_eq_right (neg_nonneg.mpr hu),
      max_eq_right (neg_nonneg.mpr hv),max_eq_left (neg_nonpos.mpr (mul_nonneg_of_nonpos_of_nonpos hu hv))]

private theorem max_div_same (x y q : ℝ) (hq : 0≤q) : max (x/q) (y/q)=max x y/q := by
  rcases le_total x y with h|h
  · rw [max_eq_right h,max_eq_right (div_le_div_of_nonneg_right h hq)]
  · rw [max_eq_left h,max_eq_left (div_le_div_of_nonneg_right h hq)]

private theorem twice_peak (u v w : ℝ) :
    2*max (max 0 (-(u*v))) (max 0 (-(u*w))) =
    max 0 (u^2+|u| * |v-w|-u*(u+v+w)) := by
  have two (a b : ℝ) : 2*max a b=a+b+|a-b| := by
    rcases le_total a b with h|h
    · rw [max_eq_right h,abs_of_nonpos (sub_nonpos.mpr h)]
      ring
    · rw [max_eq_left h,abs_of_nonneg (sub_nonneg.mpr h)]
      ring
  have eq : 2*max (-(u*v)) (-(u*w))=u^2+|u| * |v-w|-u*(u+v+w) := by
    rw [two,show -(u*v)- -(u*w)= -(u*(v-w)) by ring,abs_neg,abs_mul]
    ring
  rw [←eq,show max (max 0 (-(u*v))) (max 0 (-(u*w))) = max 0 (max (-(u*v)) (-(u*w))) by
    simp only [max_assoc,max_left_comm,max_comm,max_self]]
  rcases le_total 0 (max (-(u*v)) (-(u*w))) with h|h
  · rw [max_eq_right h,max_eq_right (mul_nonneg (by norm_num) h)]
  · rw [max_eq_left h,mul_zero,max_eq_left (mul_nonpos_of_nonneg_of_nonpos (by norm_num) h)]

/-- Exact sign-free formula at every numerator, with no restriction on
the endpoints. All four possible prices refer to the original flanks. -/
theorem largest_opposite_prime_price_exact (k L H : ℕ) :
    let u := oddQuotientPrimeExcess (Ioc k L) H
    let v := oddQuotientPrimeExcess (middleTestFlank true k L H) H
    let w := oddQuotientPrimeExcess (middleTestFlank false k L H) H
    2*largestOppositePrimePrice k L H =
      max 0 (u^2+|u| * |v-w|-u*(u+v+w))/(H:ℝ)^2 := by
  intro u v w
  unfold largestOppositePrimePrice oppositePrimeProduct
  simp only [one_mul,neg_one_mul,neg_neg]
  rw [max_div_same _ _ _ (sq_nonneg _),max_div_same _ _ _ (sq_nonneg _),
    max_div_same _ _ _ (sq_nonneg _),two_signs,two_signs,←mul_div_assoc,twice_peak]

private theorem combined_row (k L H : ℕ) (hk : k≤L) (hr : ⌊Real.sqrt H⌋₊≤k) :
    oddQuotientPrimeExcess (Ioc k L) H +
    oddQuotientPrimeExcess (middleTestFlank true k L H) H +
    oddQuotientPrimeExcess (middleTestFlank false k L H) H =
    oddQuotientPrimeExcess (Ioc ⌊Real.sqrt H⌋₊ (max L H)) H := by
  have clip : Ioc L H=Ioc L (max L H) := by
    rcases le_total L H with hl|hl
    · rw [max_eq_right hl]
    · rw [max_eq_left hl,Ioc_eq_empty_of_le hl,Ioc_self]
  change _+_+oddQuotientPrimeExcess (Ioc L H) H=_
  rw [clip,add_comm (oddQuotientPrimeExcess (Ioc k L) H),
    show oddQuotientPrimeExcess (middleTestFlank true k L H) H + oddQuotientPrimeExcess (Ioc k L) H =
      oddQuotientPrimeExcess (Ioc ⌊Real.sqrt H⌋₊ L) H from sum_Ioc_consecutive _ hr hk]
  exact sum_Ioc_consecutive _ (hr.trans hk) (le_max_left ..)

/-- Replacing twice the maximal mixed price by the middle square and
flank contrast costs at most the square-root error of the complete row
times the middle discrepancy, at every numerator. -/
theorem prime_price_contrast_error :
    ∃ C : ℝ, 0≤C ∧ ∀ k L H : ℕ, k≤L → ⌊Real.sqrt H⌋₊≤k →
      |2*largestOppositePrimePrice k L H-middleFlankContrastPrice k L H| ≤
        C*Real.sqrt H*|oddQuotientPrimeExcess (Ioc k L) H|/(H:ℝ)^2 := by
  obtain ⟨C,hC,row⟩ := oddQuotientPrimeExcess_complete_above_sqrt
  refine ⟨C,hC,fun k L H hk hr => ?_⟩
  let u := oddQuotientPrimeExcess (Ioc k L) H
  let v := oddQuotientPrimeExcess (middleTestFlank true k L H) H
  let w := oddQuotientPrimeExcess (middleTestFlank false k L H) H
  let A := u^2+|u| * |v-w|
  have hA : 0≤A := add_nonneg (sq_nonneg _) (mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have bound : |u+v+w|≤C*Real.sqrt H := by
    rw [show u+v+w=_ from combined_row k L H hk hr]
    exact row H (max L H) (le_max_right ..)
  have close := abs_max_sub_max_le_abs (A-u*(u+v+w)) A 0
  rw [max_eq_left hA,show A-u*(u+v+w)-A= -(u*(u+v+w)) by ring,abs_neg,abs_mul] at close
  rw [largest_opposite_prime_price_exact]
  change |max 0 (A-u*(u+v+w))/(H:ℝ)^2-A/(H:ℝ)^2| ≤ _
  rw [←sub_div,abs_div,abs_of_nonneg (sq_nonneg _),max_comm 0]
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  exact close.trans ((mul_le_mul_of_nonneg_left bound (abs_nonneg u)).trans_eq (mul_comm ..))

/-- On any family exceeding B square roots in the middle, the relative
error in the contrast price is at most C/B. This also covers numerators
above the middle endpoint, where both flanks can contribute. -/
theorem middle_tail_contrast_comparison :
    ∃ C : ℝ, 0≤C ∧ ∀ (k L : ℕ) (D : Finset ℕ) (B : ℝ), k≤L → 0<B →
      (∀ H ∈ D, ⌊Real.sqrt H⌋₊≤k ∧ B*Real.sqrt H≤|oddQuotientPrimeExcess (Ioc k L) H|) →
      |2*(∑ H ∈ D, largestOppositePrimePrice k L H)-(∑ H ∈ D, middleFlankContrastPrice k L H)| ≤
        (C/B)*(∑ H ∈ D, middleFlankContrastPrice k L H) := by
  obtain ⟨C,hC,error⟩ := prime_price_contrast_error
  refine ⟨C,hC,fun k L D B hk hB hD => ?_⟩
  rw [mul_sum,←sum_sub_distrib,mul_sum]
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro H hi
  obtain ⟨hr,big⟩ := hD H hi
  let u := oddQuotientPrimeExcess (Ioc k L) H
  let v := oddQuotientPrimeExcess (middleTestFlank true k L H) H
  let w := oddQuotientPrimeExcess (middleTestFlank false k L H) H
  apply (error k L H hk hr).trans
  have cost : Real.sqrt H≤|u|/B := (le_div_iff₀ hB).mpr (by simpa only [mul_comm B] using big)
  have sq : |u| * |u|=u^2 := by rw [←pow_two,sq_abs]
  have pay : C*Real.sqrt H*|u| ≤ (C/B)*(u^2+|u| * |v-w|) := by
    calc _ = (C*|u|)*Real.sqrt H := by ring
         _ ≤ (C*|u|)*(|u|/B) := mul_le_mul_of_nonneg_left cost (mul_nonneg hC (abs_nonneg _))
         _ = (C/B)*(|u| * |u|) := by ring
         _ ≤ _ := by
           rw [sq]
           exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right
             (mul_nonneg (abs_nonneg _) (abs_nonneg _))) (div_nonneg hC hB.le)
  change _ ≤ (C/B)*((u^2+|u| * |v-w|)/(H:ℝ)^2)
  rw [←mul_div_assoc]
  exact div_le_div_of_nonneg_right pay (sq_nonneg _)

/-- Eligible numerators selected by the absolute middle discrepancy
alone, with the same geometric restrictions as the signed test. -/
def middleContrastNumerators (a g d T : ℝ) (k L : ℕ) : Finset ℕ :=
  (middleTestNumerators T d k L).filter fun H =>
    a*Real.exp (g*T)*Real.sqrt H < |oddQuotientPrimeExcess (Ioc k L) H|

private theorem middle_conditions {a g d T : ℝ} {k L H : ℕ}
    (hi : H∈middleContrastNumerators a g d T k L) :
    ⌊Real.sqrt H⌋₊≤k ∧ a*Real.exp (g*T)*Real.sqrt H≤|oddQuotientPrimeExcess (Ioc k L) H| :=
  ⟨Nat.floor_le_of_le (mem_filter.mp (mem_filter.mp hi).1).2.2.2.le,(mem_filter.mp hi).2.le⟩

private theorem price_le_peak (left : Bool) {s : ℝ} (hs : s=1 ∨ s= -1) (k L H : ℕ) :
    oppositePrimeProduct left s k L H ≤ largestOppositePrimePrice k L H := by
  rcases hs with rfl|rfl <;> cases left <;> unfold largestOppositePrimePrice
  · exact (le_max_left ..).trans (le_max_right ..)
  · exact (le_max_left ..).trans (le_max_left ..)
  · exact (le_max_right ..).trans (le_max_right ..)
  · exact (le_max_right ..).trans (le_max_left ..)

private theorem peak_attained (k L H : ℕ) : ∃ (l : Bool) (s : ℝ), (s=1 ∨ s= -1) ∧
    largestOppositePrimePrice k L H=oppositePrimeProduct l s k L H := by
  let p l s := oppositePrimeProduct l s k L H
  let m l := max (p l 1) (p l (-1))
  have side l : m l=p l 1 ∨ m l=p l (-1) := by
    rcases le_total (p l 1) (p l (-1)) with h|h
    · exact Or.inr (max_eq_right h)
    · exact Or.inl (max_eq_left h)
  obtain ⟨l,hl⟩ : ∃ l, largestOppositePrimePrice k L H=m l := by
    rcases le_total (m true) (m false) with h|h
    · exact ⟨false,max_eq_right h⟩
    · exact ⟨true,max_eq_left h⟩
  rcases side l with h|h
  · exact ⟨l,1,Or.inl rfl,hl.trans h⟩
  · exact ⟨l,-1,Or.inr rfl,hl.trans h⟩

private theorem winning_pair {τ u v s : ℝ} (ht : 0≤τ) (hu : τ < |u|) (hs : |s|=1)
    (h : τ*|u| < max 0 (s*u)*max 0 ((-s)*v)) : τ<s*u ∧ τ<(-s)*v := by
  have posU : 0<s*u := by
    by_contra! hn
    rw [max_eq_left hn,zero_mul] at h
    exact h.not_ge (mul_nonneg ht (abs_nonneg _))
  have id : s*u=|u| := by rw [←abs_of_pos posU,abs_mul,hs,one_mul]
  rw [max_eq_right posU.le,id,mul_comm τ] at h
  have strict : τ < max 0 ((-s)*v) := lt_of_not_ge (fun he =>
    h.not_ge (mul_le_mul_of_nonneg_left he (abs_nonneg u)))
  exact ⟨hu.trans_eq id.symm,(lt_max_iff.mp strict).resolve_left ht.not_gt⟩

/-- After paying the complete-row error, half the remaining middle
floor can be imposed on the opposite flank. A winning fixed test
captures the full maximal price at that numerator. -/
theorem winning_opposite_test_after_row_error :
    ∃ C : ℝ, 0≤C ∧ ∀ (a a' g d T : ℝ) (k L H : ℕ), 0≤a' → k≤L →
      2*(a'*Real.exp (g*T))+C≤a*Real.exp (g*T) →
      H∈middleContrastNumerators a g d T k L →
      ∃ (l : Bool) (s : ℝ), (s=1 ∨ s= -1) ∧ H∈largeOppositePrimeNumerators l s a' g d T k L ∧
        largestOppositePrimePrice k L H=oppositePrimeProduct l s k L H := by
  obtain ⟨C,hC,row⟩ := oddQuotientPrimeExcess_complete_above_sqrt
  refine ⟨C,hC,fun a a' g d T k L H ha' hk high hH => ?_⟩
  obtain ⟨hn,big⟩ := mem_filter.mp hH
  obtain ⟨_,xH,_,root⟩ := mem_filter.mp hn
  let u := oddQuotientPrimeExcess (Ioc k L) H
  let v := oddQuotientPrimeExcess (middleTestFlank true k L H) H
  let w := oddQuotientPrimeExcess (middleTestFlank false k L H) H
  let τ := a'*Real.exp (g*T)*Real.sqrt H
  change a*Real.exp (g*T)*Real.sqrt H < |u| at big
  have ht : 0≤τ := by dsimp only [τ]; positivity
  have cr := mul_nonneg hC (Real.sqrt_nonneg (H:ℝ))
  have room : 2*τ+C*Real.sqrt H < |u| := by
    have cap := mul_le_mul_of_nonneg_right high (Real.sqrt_nonneg (H:ℝ))
    dsimp only [τ]
    linarith only [cap,big]
  have exceeds : τ < |u| := by linarith only [room,cr,ht]
  have hU := ht.trans_lt exceeds
  have sum : |u+v+w| ≤ C*Real.sqrt H := by
    rw [show u+v+w=_ from combined_row k L H hk (Nat.floor_le_of_le root.le)]
    exact row H (max L H) (le_max_right ..)
  have loss : u*(u+v+w) ≤ |u| * (C*Real.sqrt H) := (le_abs_self _).trans
    ((abs_mul _ _).le.trans (mul_le_mul_of_nonneg_left sum hU.le))
  have square : |u| * |u|=u^2 := by rw [←pow_two,sq_abs]
  have size := mul_lt_mul_of_pos_right room hU
  rw [square] at size
  have strong : 2*(τ*|u|) < max 0 (u^2+|u| * |v-w|-u*(u+v+w)) := by
    apply lt_of_lt_of_le _ (le_max_right ..)
    linarith only [loss,size,mul_nonneg hU.le (abs_nonneg (v-w))]
  have hh : 0<(H:ℝ) := (Real.exp_pos T).trans_le xH
  have exactPrice := largest_opposite_prime_price_exact k L H
  change 2*largestOppositePrimePrice k L H=max 0 (u^2+|u| * |v-w|-u*(u+v+w))/(H:ℝ)^2 at exactPrice
  have exposure : τ*|u|/(H:ℝ)^2 < largestOppositePrimePrice k L H := by
    have q := div_lt_div_of_pos_right strong (sq_pos_of_pos hh)
    rw [←exactPrice,mul_div_assoc] at q
    linarith only [q]
  obtain ⟨l,s,hs,hit⟩ := peak_attained k L H
  rw [hit] at exposure
  let y := oddQuotientPrimeExcess (middleTestFlank l k L H) H
  change τ*|u|/(H:ℝ)^2 < (max 0 (s*u)*max 0 ((-s)*y))/(H:ℝ)^2 at exposure
  have sign : |s|=1 := by rcases hs with rfl|rfl <;> norm_num
  obtain ⟨hm,hy⟩ := winning_pair ht exceeds sign
    ((div_lt_div_iff_of_pos_right (sq_pos_of_pos hh)).mp exposure)
  exact ⟨l,s,hs,mem_filter.mpr ⟨hn,hm,hy⟩,hit⟩

/-- At a sufficiently high common floor, any original signed and
flank-selected tail sum is bounded by the unsigned middle-only
contrast sum, with coefficient one. -/
theorem signed_prime_moment_le_middle_contrast :
    ∃ C : ℝ, 0≤C ∧ ∀ (a g d T : ℝ) (k L : ℕ) (left : Bool) (s : ℝ),
      0<a → C≤a*Real.exp (g*T) → k≤L → (s=1 ∨ s= -1) →
      (∑ H ∈ largeOppositePrimeNumerators left s a g d T k L, oppositePrimeProduct left s k L H) ≤
      ∑ H ∈ middleContrastNumerators a g d T k L, middleFlankContrastPrice k L H := by
  obtain ⟨C,hC,comp⟩ := middle_tail_contrast_comparison
  refine ⟨C,hC,fun a g d T k L left s ha high hk hs => ?_⟩
  let B := a*Real.exp (g*T)
  let D := middleContrastNumerators a g d T k L
  let S := largeOppositePrimeNumerators left s a g d T k L
  have hB : 0<B := mul_pos ha (Real.exp_pos _)
  have cover : S⊆D := by
    intro H hH
    obtain ⟨hn,hm,_⟩ := mem_filter.mp hH
    apply mem_filter.mpr ⟨hn,hm.trans_le ?_⟩
    rcases hs with rfl|rfl
    · simpa only [one_mul] using le_abs_self (oddQuotientPrimeExcess (Ioc k L) H)
    · simpa only [neg_one_mul] using neg_le_abs (oddQuotientPrimeExcess (Ioc k L) H)
  have budget := comp k L D B hk hB (fun _ hi => middle_conditions hi)
  let Q := ∑ H ∈ D, middleFlankContrastPrice k L H
  have hQ : 0≤Q := sum_nonneg (fun H _ => contrast_nonneg k L H)
  have paid : C/B*Q≤Q := mul_le_of_le_one_left hQ ((div_le_one hB).mpr high)
  have net := (le_abs_self _).trans budget
  change 2*(∑ H ∈ D, largestOppositePrimePrice k L H)-Q≤C/B*Q at net
  calc (∑ H ∈ S, oppositePrimeProduct left s k L H) ≤
        ∑ H ∈ S, largestOppositePrimePrice k L H := sum_le_sum (fun H _ => price_le_peak left hs k L H)
       _ ≤ ∑ H ∈ D, largestOppositePrimePrice k L H := sum_le_sum_of_subset_of_nonneg cover
          (fun H _ _ => (div_nonneg (mul_nonneg (le_max_left ..) (le_max_left ..)) (sq_nonneg _)).trans
            (price_le_peak true (Or.inl rfl : (1:ℝ)=1 ∨ (1:ℝ)= -1) k L H))
       _ ≤ Q := by linarith only [net,paid]

/-- Conversely, the four original tails at a quarter of the floor pay
for the entire middle-only contrast moment. Together with the forward
bound this gives the same growth exponent in both formulations. -/
theorem middle_contrast_le_four_opposite_tails :
    ∃ C : ℝ, 0≤C ∧ ∀ (a g d T : ℝ) (k L : ℕ), 0<a → k≤L → C≤a*Real.exp (g*T)/4 →
      let m := fun l s => ∑ H ∈ largeOppositePrimeNumerators l s (a/4) g d T k L, oppositePrimeProduct l s k L H
      3*(∑ H ∈ middleContrastNumerators a g d T k L, middleFlankContrastPrice k L H) ≤
        8*(m true 1+m true (-1)+m false 1+m false (-1)) := by
  obtain ⟨C₁,h₁,win⟩ := winning_opposite_test_after_row_error
  obtain ⟨C₂,_,cmp⟩ := middle_tail_contrast_comparison
  refine ⟨max C₁ C₂,h₁.trans (le_max_left ..),fun a g d T k L ha hk high => ?_⟩
  intro m
  let B := a*Real.exp (g*T)
  let D := middleContrastNumerators a g d T k L
  let S l s := largeOppositePrimeNumerators l s (a/4) g d T k L
  let f l s (H : ℕ) := if H∈S l s then oppositePrimeProduct l s k L H else 0
  have nonneg (l : Bool) (s : ℝ) (H : ℕ) : 0≤oppositePrimeProduct l s k L H :=
    div_nonneg (mul_nonneg (le_max_left ..) (le_max_left ..)) (sq_nonneg _)
  have hf (l : Bool) (s : ℝ) (H : ℕ) : 0≤f l s H := by
    dsimp only [f]
    split <;> first | exact nonneg .. | exact le_rfl
  have Bpos : 0<B := mul_pos ha (Real.exp_pos _)
  have enough : C₁≤B/4 := (le_max_left ..).trans high
  have floorRoom : 2*((a/4)*Real.exp (g*T))+C₁≤a*Real.exp (g*T) := by
    change C₁≤a*Real.exp (g*T)/4 at enough
    linarith only [enough,mul_nonneg ha.le (Real.exp_pos (g*T)).le]
  have pay (H : ℕ) (hi : H∈D) : largestOppositePrimePrice k L H ≤
      f true 1 H+f true (-1) H+f false 1 H+f false (-1) H := by
    obtain ⟨l,s,hs,mem,hit⟩ := win a (a/4) g d T k L H (by positivity) hk floorRoom hi
    have eq : largestOppositePrimePrice k L H=f l s H := hit.trans (if_pos mem).symm
    rw [eq]
    rcases hs with rfl|rfl <;> cases l <;>
      linarith only [hf true 1 H,hf true (-1) H,hf false 1 H,hf false (-1) H]
  have group (l : Bool) (s : ℝ) : (∑ H ∈ D, f l s H) ≤ m l s := by
    change (∑ H ∈ D, if H∈S l s then oppositePrimeProduct l s k L H else 0) ≤ _
    rw [←sum_filter]
    exact sum_le_sum_of_subset_of_nonneg (fun H hH => (mem_filter.mp hH).2) (fun H _ _ => nonneg l s H)
  have collected := sum_le_sum pay
  simp only [sum_add_distrib] at collected
  have all : (∑ H ∈ D, largestOppositePrimePrice k L H) ≤ m true 1+m true (-1)+m false 1+m false (-1) := by
    linarith only [collected,group true 1,group true (-1),group false 1,group false (-1)]
  have close := cmp k L D B hk Bpos (fun _ hi => middle_conditions hi)
  let Q := ∑ H ∈ D, middleFlankContrastPrice k L H
  have hQ : 0≤Q := sum_nonneg (fun H _ => contrast_nonneg k L H)
  have rate : C₂/B≤1/4 := (div_le_iff₀ Bpos).mpr (by
    have h : C₂≤B/4 := (le_max_right ..).trans high
    linarith only [h])
  have lower := (neg_le_abs _).trans close
  change -(2*(∑ H ∈ D, largestOppositePrimePrice k L H)-Q)≤C₂/B*Q at lower
  change 3*Q≤_
  linarith only [lower,mul_le_mul_of_nonneg_right rate hQ,all]

/-- Failure of RH forces a large unsigned contrast sum on numerators
selected only by their middle interval. No sign or flank appears in
the resulting test. -/
theorem rh_or_large_middle_contrast : RiemannHypothesis ∨
    ∃ a c g d w : ℝ, 0<a ∧ 0<c ∧ 0<g ∧ 0<d ∧ d≤1/4 ∧ 0<w ∧
      ∀ η : ℝ, 0<η → η≤w → ∃ (T : ℕ → ℝ) (k : ℕ → ℕ), Tendsto T atTop atTop ∧
        (∀ i, T i/(1+η)≤Real.log (k i) ∧ Real.log (k i)≤T i) ∧
        ∀ᶠ i in atTop, let L := ⌈Real.exp ((1+η)*T i)⌉₊
          c*a^2*Real.exp ((1/2+3*g)*T i) <
            (L:ℝ)*∑ H ∈ middleContrastNumerators a g d (T i) (k i) L, middleFlankContrastPrice (k i) L H := by
  rcases riemannHypothesis_or_fixed_band_opposite_prime_moment with rh |
    ⟨_,_,_,a,c,g,d,w,_,_,_,_,_,ha,hc,hg,hd,hd',hw,seq⟩
  · exact Or.inl rh
  obtain ⟨C,_,payment⟩ := signed_prime_moment_le_middle_contrast
  refine Or.inr ⟨a,c,g,d,w,ha,hc,hg,hd,hd',hw,fun η hη hηw => ?_⟩
  obtain ⟨T,k,ht,hk,_,ev⟩ := seq η hη hηw
  refine ⟨T,k,ht,hk,?_⟩
  have floorHigh := ((Real.tendsto_exp_atTop.comp (ht.const_mul_atTop hg)).const_mul_atTop ha).eventually_ge_atTop C
  filter_upwards [ev,ht.eventually_ge_atTop 0,floorHigh] with i hi hT high
  let L := ⌈Real.exp ((1+η)*T i)⌉₊
  have small : k i≤L := by
    rcases Nat.eq_zero_or_pos (k i) with z|p
    · rw [z]; exact Nat.zero_le _
    have cast : (k i:ℝ)≤(L:ℝ) := calc
      (k i:ℝ) = Real.exp (Real.log (k i)) := (Real.exp_log (Nat.cast_pos.mpr p)).symm
      _ ≤ Real.exp ((1+η)*T i) := Real.exp_le_exp.mpr
        ((hk i).2.trans (by linarith only [mul_nonneg hη.le hT]))
      _ ≤ (L:ℝ) := Nat.le_ceil _
    exact_mod_cast cast
  obtain ⟨_,_,s,left,_,_,hs,_,_,_,_,_,big⟩ := hi
  exact big.trans_le (mul_le_mul_of_nonneg_left (payment a g d (T i) (k i) L left s ha high small hs)
    (Nat.cast_nonneg L))

end GaloisForLFunctions.ExclusionOfTheCriticalState
