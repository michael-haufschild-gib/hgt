import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.TheOccupiedLevelsOfTheOppositePrimeMoment
import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.ThePowerSavingOnEveryOddQuotientDenominatorInterval

/-!
# A diagonal cutoff for the two signed prime excursions

Dividing each discrepancy by its numerator's square root changes the
moment weight to 1/H. One factor is limited by Chebyshev's prime mass and
the other by the count of observable denominators. Their product rules
out all dyadic levels above a single diagonal.
-/

open Finset Filter
noncomputable section
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHarmonicAnalysis

private theorem triangular_layer_mass (K : ℕ) :
    (∑ r ∈ range (K+1), dyadicRelativeJump r*(1+((K-r:ℕ):ℝ)/2)) =
      1+(K:ℝ)+(K:ℝ)*((K:ℝ)-1)/8 := by
  induction K with
  | zero => norm_num [dyadicRelativeJump]
  | succ K ih =>
    rw [sum_range_succ]
    have step r (hr : r ∈ range (K+1)) :
        dyadicRelativeJump r*(1+((K+1-r:ℕ):ℝ)/2) =
          dyadicRelativeJump r*(1+((K-r:ℕ):ℝ)/2)+dyadicRelativeJump r*(1/2) := by
      have rr : K+1-r=(K-r)+1 := by have := mem_range.mp hr; omega
      rw [rr,Nat.cast_add,Nat.cast_one]
      ring
    rw [sum_congr rfl step,sum_add_distrib,←sum_mul,dyadic_relative_mass,ih]
    simp only [dyadicRelativeJump,Nat.succ_ne_zero,if_false,Nat.sub_self,Nat.cast_zero,Nat.cast_succ]
    ring

/-- Occupation below r+t≤K has total relative area at most
1+K+K(K−1)/8. Axial layers cost one half and interior layers one quarter. -/
theorem occupied_area_of_diagonal_cutoff {ι : Type*} (S : Finset ι) (F G : ι → ℝ) (K : ℕ)
    (diagonal : ∀ i ∈ S, ∀ r t : ℕ, (2:ℝ)^r ≤ F i → (2:ℝ)^t ≤ G i → r+t ≤ K) :
    occupiedDyadicArea S F G K K ≤ 1+(K:ℝ)+(K:ℝ)*((K:ℝ)-1)/8 := by
  classical
  let a := dyadicRelativeJump
  have nonneg (n : ℕ) : 0 ≤ a n := by dsimp only [a,dyadicRelativeJump]; split <;> norm_num
  rw [←triangular_layer_mass]
  apply sum_le_sum
  intro r hr
  have hK : r ≤ K := Nat.le_of_lt_succ (mem_range.mp hr)
  have inc (t : ℕ) (_ : t ∈ range (K+1)) :
      (if ∃ i ∈ S, (2:ℝ)^r ≤ F i ∧ (2:ℝ)^t ≤ G i then a r*a t else 0) ≤
        (if t ≤ K-r then a r*a t else 0) := by
    by_cases ho : ∃ i ∈ S, (2:ℝ)^r ≤ F i ∧ (2:ℝ)^t ≤ G i
    · obtain ⟨i,hi,hf,hg⟩ := ho
      have hd := diagonal i hi r t hf hg
      rw [if_pos ⟨i,hi,hf,hg⟩,if_pos (by omega)]
    · rw [if_neg ho]
      split <;> first | exact mul_nonneg (nonneg _) (nonneg _) | exact le_rfl
  apply (sum_le_sum inc).trans_eq
  have filt : (range (K+1)).filter (fun t => t ≤ K-r) = range (K-r+1) := by
    ext t
    simp only [mem_filter,mem_range]
    omega
  rw [←sum_filter,filt,←mul_sum,dyadic_relative_mass]

private theorem height_le_abs (D : Finset ℕ) (t : ℝ) (H : ℕ) (ht : |t|=1) :
    numeratorExcursionHeight D t H ≤ |oddQuotientPrimeExcess D H| := by
  apply max_le (abs_nonneg _)
  exact (le_abs_self _).trans_eq (by rw [abs_mul,ht,one_mul])

private theorem middle_height_le (k L H : ℕ) (s : ℝ) (hs : |s|=1) :
    numeratorExcursionHeight (Ioc k L) s H ≤ 4*(L:ℝ) := by
  apply (height_le_abs _ s H hs).trans
  apply (oddQuotientPrimeExcess_le _ L H (fun n hn => mem_Ioc.mpr
    ⟨(Nat.zero_le _).trans_lt (mem_Ioc.mp hn).1,(mem_Ioc.mp hn).2⟩)).trans
  apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
  linarith only [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4)]

/-- At large numerators the product cutoff improves from L log 4 to
o(L), uniformly over both endpoints, signs, and flank choices. -/
theorem eventually_prime_product_below_every_linear_cap {ε : ℝ} (he : 0<ε) :
    ∀ᶠ H : ℕ in atTop, ∀ (k L : ℕ) (left : Bool) (s : ℝ), |s|=1 →
      (numeratorExcursionHeight (Ioc k L) s H / Real.sqrt H) *
      (numeratorExcursionHeight (middleTestFlank left k L H) (-s) H / Real.sqrt H) ≤ ε*L := by
  filter_upwards [eventually_all_odd_quotient_intervals (show 0<ε/4 by linarith only [he]),
    eventually_ge_atTop 1] with H h hH
  intro k L left s hs
  have mid := middle_height_le k L H s hs
  have side : numeratorExcursionHeight (middleTestFlank left k L H) (-s) H ≤ ε/4*H := by
    apply (height_le_abs _ _ H ((abs_neg s).trans hs)).trans
    cases left <;> exact h _ _
  rw [div_mul_div_comm,←sq,Real.sq_sqrt (Nat.cast_nonneg _)]
  apply (div_le_iff₀ (Nat.cast_pos.mpr hH : 0 < (H:ℝ))).mpr
  have prod := mul_le_mul mid side (le_max_left ..) (by positivity)
  linarith only [prod]

private theorem joint_envelope {D c : ℝ} (hD : 0<D)
    (all : ∀ H : ℕ, 1≤H → ∀ x y : ℕ, |oddQuotientPrimeExcess (Ioc x y) H| ≤ D*(H:ℝ)^c)
    (H k L : ℕ) (left : Bool) (s : ℝ) (hH : 1≤H) (hs : |s|=1) :
      (numeratorExcursionHeight (Ioc k L) s H / Real.sqrt H) *
      (numeratorExcursionHeight (middleTestFlank left k L H) (-s) H / Real.sqrt H) ≤
      min (4*D*L*(H:ℝ)^(c-1)) (D^2*(H:ℝ)^(2*c-1)) := by
  have hpos : 0 < (H:ℝ) := Nat.cast_pos.mpr hH
  have side : numeratorExcursionHeight (middleTestFlank left k L H) (-s) H ≤ D*(H:ℝ)^c := by
    apply (height_le_abs _ _ H ((abs_neg s).trans hs)).trans
    cases left <;> exact all H hH _ _
  have mid := (height_le_abs (Ioc k L) s H hs).trans (all H hH k L)
  have length := middle_height_le k L H s hs
  rw [div_mul_div_comm,←sq,Real.sq_sqrt hpos.le]
  apply le_min
  · apply (div_le_iff₀ hpos).mpr
    have fac : (H:ℝ)^(c-1)*H=(H:ℝ)^c := by
      simpa only [Real.rpow_one,sub_add_cancel] using (Real.rpow_add hpos (c-1) 1).symm
    have bound := mul_le_mul length side (le_max_left ..) (by positivity)
    calc _ ≤ _ := bound
         _ = 4*D*L*((H:ℝ)^(c-1)*H) := by rw [fac]; ring
         _ = _ := by ring
  · apply (div_le_iff₀ hpos).mpr
    have fac : (H:ℝ)^c*(H:ℝ)^c=(H:ℝ)^(2*c-1)*H := by
      calc _ = (H:ℝ)^(c+c) := (Real.rpow_add hpos c c).symm
           _ = (H:ℝ)^((2*c-1)+1) := by rw [sub_add_cancel,two_mul]
           _ = _ := by rw [Real.rpow_add hpos,Real.rpow_one]
    have bound := mul_le_mul mid side (le_max_left ..) (mul_nonneg hD.le (Real.rpow_nonneg hpos.le _))
    calc _ ≤ _ := bound
         _ = D^2*((H:ℝ)^c*(H:ℝ)^c) := by ring
         _ = _ := by rw [fac]; ring

/-- At exponent 8/9 the decreasing branch costs L H^(-1/9) and the
increasing branch costs H^(7/9). Both hold for both orientations. -/
theorem root_scaled_prime_product_power_saving :
    ∃ D : ℝ, 0 < D ∧ ∀ (H k L : ℕ) (left : Bool) (s : ℝ), 1 ≤ H → |s|=1 →
      (numeratorExcursionHeight (Ioc k L) s H / Real.sqrt H) *
      (numeratorExcursionHeight (middleTestFlank left k L H) (-s) H / Real.sqrt H) ≤
      min (4*D*L*(H:ℝ)^(-1/9:ℝ)) (D^2*(H:ℝ)^(7/9:ℝ)) := by
  obtain ⟨D,hD,all⟩ := all_odd_quotient_intervals_eight_ninths
  refine ⟨D,hD,fun H k L left s hH hs => ?_⟩
  simpa only [show (8/9:ℝ)-1= -1/9 by norm_num,show 2*(8/9:ℝ)-1=7/9 by norm_num] using
    joint_envelope hD all H k L left s hH hs

/-- Every exponent above the zero abscissa and below one bounds the
joint price in terms of the middle endpoint alone. The two numerator
envelopes meet at scale L^(2−b). -/
theorem middle_endpoint_power_above_abscissa {b : ℝ} (hw : _root_.RHTower.zeroReSup<b) (hb1 : b<1) :
    ∃ C : ℝ, 0<C ∧ ∀ (k L H : ℕ) (left : Bool) (s : ℝ), |s|=1 →
      (numeratorExcursionHeight (Ioc k L) s H / Real.sqrt H) *
      (numeratorExcursionHeight (middleTestFlank left k L H) (-s) H / Real.sqrt H) ≤ C*(L:ℝ)^b := by
  obtain ⟨D,hD,all⟩ := odd_quotient_interval_above_abscissa hw hb1
  have hb : 0<b := lt_trans (by norm_num : (0:ℝ)<1/2) (_root_.RHTower.half_le_zeroReSup.trans_lt hw)
  have denom : 0<2-b := by linarith only [hb1]
  let c := 1/(2-b)
  have idc : (2-b)*c=1 := by dsimp only [c]; field_simp [denom.ne']
  have rise : 0≤2*c-1 := by
    by_contra! he
    linarith only [mul_neg_of_pos_of_neg denom he,idc,hb.le]
  have decay : c-1≤0 := by
    by_contra! he
    linarith only [mul_pos denom he,idc,hb1.le]
  let C := max (4*D) (D^2)
  have hc : 0<C := (sq_pos_of_pos hD).trans_le (le_max_right ..)
  refine ⟨C,hc,?_⟩
  intro k L H left s hs
  rcases Nat.eq_zero_or_pos H with rfl | hH
  · simp only [Nat.cast_zero,Real.sqrt_zero,div_zero,mul_zero]
    positivity
  rcases Nat.eq_zero_or_pos L with rfl | hL
  · simp [numeratorExcursionHeight,oddQuotientPrimeExcess,Ioc_eq_empty_of_le (Nat.zero_le k),
      Real.zero_rpow hb.ne']
  have price := joint_envelope hD all H k L left s hH hs
  have lp : 0<(L:ℝ) := Nat.cast_pos.mpr hL
  let X := (L:ℝ)^(2-b)
  have xp : 0<X := Real.rpow_pos_of_pos lp _
  by_cases cut : (H:ℝ) ≤ X
  · have growth := Real.rpow_le_rpow (Nat.cast_nonneg H) cut rise
    have id : X^(2*c-1)=(L:ℝ)^b := by
      dsimp only [X]
      rw [←Real.rpow_mul lp.le,show (2-b)*(2*c-1)=b by linarith only [idc]]
    rw [id] at growth
    exact (price.trans (min_le_right ..)).trans (mul_le_mul (le_max_right ..) growth
      (Real.rpow_nonneg (Nat.cast_nonneg H) _) hc.le)
  · have fall := Real.rpow_le_rpow_of_nonpos xp (le_of_not_ge cut) decay
    have id : (L:ℝ)*X^(c-1)=(L:ℝ)^b := by
      dsimp only [X]
      rw [←Real.rpow_mul lp.le]
      calc _ = (L:ℝ)^(1:ℝ)*(L:ℝ)^((2-b)*(c-1)) := by rw [Real.rpow_one]
           _ = _ := by rw [←Real.rpow_add lp,show 1+(2-b)*(c-1)=b by linarith only [idc]]
    have cap := mul_le_mul_of_nonneg_left fall (mul_nonneg (mul_nonneg (by norm_num) hD.le) lp.le)
    calc _ ≤ _ := price.trans (min_le_left ..)
         _ ≤ _ := cap
         _ = (4*D)*(L:ℝ)^b := by rw [mul_assoc,id]
         _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left ..) (Real.rpow_nonneg lp.le _)

/-- The corpus zero-width bound gives the fixed endpoint exponent 7/8. -/
theorem uniform_middle_endpoint_power_cap :
    ∃ C : ℝ, 0<C ∧ ∀ (k L H : ℕ) (left : Bool) (s : ℝ), |s|=1 →
      (numeratorExcursionHeight (Ioc k L) s H / Real.sqrt H) *
      (numeratorExcursionHeight (middleTestFlank left k L H) (-s) H / Real.sqrt H) ≤ C*(L:ℝ)^(7/8:ℝ) :=
  middle_endpoint_power_above_abscissa (ExceptionalLayerTheory.zeroReSup_le_sub_seven_eighths.trans_lt
    (by norm_num)) (by norm_num)

/-- Joint product ceiling using both the elementary Chebyshev cap and
the denominator-interval power saving. -/
def primeDiagonalCeiling (L : ℕ) : ℝ :=
  min ((L:ℝ)*Real.log 4) (uniform_middle_endpoint_power_cap.choose*(L:ℝ)^(7/8:ℝ))

/-- Largest possible sum of the two dyadic level indices. -/
def primeDiagonalDepth (L : ℕ) (A : ℝ) := Nat.log 2 ⌊primeDiagonalCeiling L/A^2⌋₊

/-- Largest admissible rectangle in the square-root normalization. Its
weight is reciprocal numerator mass. The moment is bounded with the
closed triangular cost and the maximizing pair lies below the diagonal. -/
theorem opposite_prime_moment_at_one_diagonal_rectangle (left : Bool) {s a g d T : ℝ}
    (k L : ℕ) (hs : s=1 ∨ s= -1) (ha : 0<a) :
    let A := a*Real.exp (g*T)
    let S := largeOppositePrimeNumerators left s a g d T k L
    let F := fun H => (numeratorExcursionHeight (Ioc k L) s H / Real.sqrt H)/A
    let G := fun H => (numeratorExcursionHeight (middleTestFlank left k L H) (-s) H / Real.sqrt H)/A
    let K := primeDiagonalDepth L A
    ∃ r t : ℕ, r+t ≤ K ∧ (∑ H ∈ S, oppositePrimeProduct left s k L H) ≤
      (4+4*(K:ℝ)+(K:ℝ)*((K:ℝ)-1)/2)*
        (A^2*upperRectangle S F G (fun H => 1/(H:ℝ)) (2^r) (2^t)) := by
  classical
  intro A S F G K
  let w (H : ℕ) := 1/(H:ℝ)
  let P (j : ℕ × ℕ) := upperRectangle S F G w (2^j.1) (2^j.2)
  have hA : 0<A := mul_pos ha (Real.exp_pos _)
  have sign : |s|=1 := by rcases hs with rfl|rfl <;> norm_num
  have top : primeDiagonalCeiling L/A^2 < (2:ℝ)^(K+1) := by
    apply (Nat.lt_floor_add_one _).trans_le
    exact_mod_cast Nat.succ_le_of_lt
      (Nat.lt_pow_succ_log_self (by decide : 1<2) ⌊primeDiagonalCeiling L/A^2⌋₊)
  have posH (H : ℕ) (hi : H ∈ S) : 0 < (H:ℝ) :=
    (Real.exp_pos _).trans_le (mem_filter.mp (mem_filter.mp hi).1).2.1
  have lower (H : ℕ) (hi : H ∈ S) : 1 ≤ F H ∧ 1 ≤ G H := by
    obtain ⟨_,hf,hg⟩ := mem_filter.mp hi
    have hroot := Real.sqrt_pos.mpr (posH H hi)
    exact ⟨(one_le_div hA).mpr ((le_div_iff₀ hroot).mpr (hf.le.trans (le_max_right ..))),
      (one_le_div hA).mpr ((le_div_iff₀ hroot).mpr (hg.le.trans (le_max_right ..)))⟩
  have prod (H : ℕ) : F H*G H < (2:ℝ)^(K+1) := by
    apply lt_of_le_of_lt _ top
    dsimp only [F,G]
    rw [div_mul_div_comm,←sq A]
    exact div_le_div_of_nonneg_right (le_min (opposite_prime_root_scaled_product left sign k L H)
      (uniform_middle_endpoint_power_cap.choose_spec.2 k L H left s sign)) (sq_nonneg A)
  have diag (H : ℕ) (_ : H ∈ S) (r t : ℕ) (hf : (2:ℝ)^r ≤ F H) (hg : (2:ℝ)^t ≤ G H) : r+t ≤ K := by
    by_contra! h
    have high := pow_le_pow_right₀ (by norm_num : 1 ≤ (2:ℝ)) (show K+1 ≤ r+t by omega)
    have low := mul_le_mul hf hg (by positivity) ((by positivity : 0 ≤ (2:ℝ)^r).trans hf)
    rw [pow_add] at high
    exact (prod H).not_ge (high.trans low)
  let J := ((range (K+1)) ×ˢ (range (K+1))).filter (fun j : ℕ × ℕ => j.1+j.2 ≤ K)
  have ne : J.Nonempty := ⟨(0,0),mem_filter.mpr ⟨mem_product.mpr
    ⟨mem_range.mpr (Nat.zero_lt_succ _),mem_range.mpr (Nat.zero_lt_succ _)⟩,Nat.zero_le _⟩⟩
  obtain ⟨j,hj,hm⟩ := J.exists_max_image P ne
  have ppos : 0 ≤ P j := mul_nonneg (by positivity) (sum_nonneg fun H _ => by dsimp only [w]; positivity)
  have cap r (hr : r ≤ K) t (ht : t ≤ K) : upperRectangle S F G w (2^r) (2^t) ≤ P j := by
    by_cases h : r+t ≤ K
    · exact hm (r,t) (mem_filter.mpr ⟨mem_product.mpr
        ⟨mem_range.mpr (Nat.lt_succ_of_le hr),mem_range.mpr (Nat.lt_succ_of_le ht)⟩,h⟩)
    · have emp : S.filter (fun H => (2:ℝ)^r ≤ F H ∧ (2:ℝ)^t ≤ G H)=∅ :=
        eq_empty_iff_forall_notMem.mpr (fun H hH => h (diag H (mem_filter.mp hH).1 r t
          (mem_filter.mp hH).2.1 (mem_filter.mp hH).2.2))
      simpa only [upperRectangle,emp,sum_empty,mul_zero] using ppos
  have bounds (H : ℕ) (hi : H ∈ S) : 1 ≤ F H ∧ F H < (2:ℝ)^(K+1) ∧
      1 ≤ G H ∧ G H < (2:ℝ)^(K+1) ∧ 0 ≤ w H := by
    obtain ⟨hf,hg⟩ := lower H hi
    have fm := mul_le_mul_of_nonneg_left hg (zero_le_one.trans hf)
    have gm := mul_le_mul_of_nonneg_right hf (zero_le_one.trans hg)
    rw [mul_one] at fm
    rw [one_mul] at gm
    exact ⟨hf,fm.trans_lt (prod H),hg,gm.trans_lt (prod H),by dsimp only [w]; positivity⟩
  have grid := dyadic_rectangle_occupied_bound S F G w K K (P j) bounds cap
  have area := occupied_area_of_diagonal_cutoff S F G K diag
  have bound := grid.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left area (by norm_num : (0:ℝ) ≤ 4)) ppos)
  have raw (H : ℕ) (hi : H ∈ S) : oppositePrimeProduct left s k L H=A^2*(F H*G H*w H) := by
    let f := numeratorExcursionHeight (Ioc k L) s H
    let g := numeratorExcursionHeight (middleTestFlank left k L H) (-s) H
    change f*g/(H:ℝ)^2 = A^2*((f/Real.sqrt H/A)*(g/Real.sqrt H/A)*(1/(H:ℝ)))
    rw [div_mul_div_comm,div_mul_div_comm f (Real.sqrt H) g (Real.sqrt H),←sq (Real.sqrt H),Real.sq_sqrt (Nat.cast_nonneg H)]
    field_simp [hA.ne',(posH H hi).ne'] <;> ring
  refine ⟨j.1,j.2,(mem_filter.mp hj).2,?_⟩
  rw [sum_congr rfl raw,←mul_sum]
  change A^2*_ ≤ _*(A^2*P j)
  linarith only [mul_le_mul_of_nonneg_left bound (sq_nonneg A)]

/-- An off-line zero forces a sequence of large reciprocal-mass rectangles
below the explicit diagonal, for each sufficiently narrow fixed band. -/
theorem rh_or_large_diagonal_prime_rectangle : RiemannHypothesis ∨
    ∃ a c g d w : ℝ, 0 < a ∧ 0 < c ∧ 0 < g ∧ 0 < d ∧ d ≤ 1/4 ∧ 0 < w ∧
      ∀ η : ℝ, 0 < η → η ≤ w → ∃ (T : ℕ → ℝ) (k : ℕ → ℕ), Tendsto T atTop atTop ∧
        (∀ i, T i/(1+η) ≤ Real.log (k i) ∧ Real.log (k i) ≤ T i) ∧
        ∀ᶠ i in atTop,
          let L := ⌈Real.exp ((1+η)*T i)⌉₊
          let A := a*Real.exp (g*T i)
          let K := primeDiagonalDepth L A
          ∃ (s : ℝ) (left : Bool), (s=1 ∨ s= -1) ∧
            let S := largeOppositePrimeNumerators left s a g d (T i) (k i) L
            let F := fun H => (numeratorExcursionHeight (Ioc (k i) L) s H / Real.sqrt H)/A
            let G := fun H => (numeratorExcursionHeight (middleTestFlank left (k i) L H) (-s) H / Real.sqrt H)/A
            ∃ r t : ℕ, r+t ≤ K ∧ c*a^2*Real.exp ((1/2+3*g)*T i) <
              (L:ℝ)*((4+4*(K:ℝ)+(K:ℝ)*((K:ℝ)-1)/2)*
                (A^2*upperRectangle S F G (fun H => 1/(H:ℝ)) (2^r) (2^t))) := by
  rcases riemannHypothesis_or_fixed_band_opposite_prime_moment with rh |
    ⟨_,_,_,a,c,g,d,w,_,_,_,_,_,ha,hc,hg,hd,hd',hw,seq⟩
  · exact Or.inl rh
  refine Or.inr ⟨a,c,g,d,w,ha,hc,hg,hd,hd',hw,fun η hη hηw => ?_⟩
  obtain ⟨T,k,ht,hk,_,ev⟩ := seq η hη hηw
  refine ⟨T,k,ht,hk,?_⟩
  filter_upwards [ev] with i hi
  let L := ⌈Real.exp ((1+η)*T i)⌉₊
  obtain ⟨_,_,s,left,_,_,hs,_,_,_,_,_,big⟩ := hi
  obtain ⟨r,t,hdg,small⟩ := opposite_prime_moment_at_one_diagonal_rectangle left
    (g:=g) (d:=d) (T:=T i) (k i) L hs ha
  exact ⟨s,left,hs,r,t,hdg,big.trans_le (mul_le_mul_of_nonneg_left small (Nat.cast_nonneg L))⟩

end GaloisForLFunctions.ExclusionOfTheCriticalState
