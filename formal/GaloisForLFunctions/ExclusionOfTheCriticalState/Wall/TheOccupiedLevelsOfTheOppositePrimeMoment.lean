import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.TwoThresholdsForOppositePrimeExcursions
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.WeightedUpperRectanglesOnFiniteGrids

/-!
# Occupied levels of the opposite-prime moment

Every eligible numerator already exceeds a common positive floor in both
coordinates. Measuring from this floor shortens the two threshold grids.
Only levels occupied by the same numerator enter the loss, with different
caps for the fixed middle interval and the chosen flank.
-/

open Finset Filter
noncomputable section
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHarmonicAnalysis

/-- Raw height of a signed odd-quotient prime discrepancy. -/
def numeratorExcursionHeight (D : Finset ℕ) (s : ℝ) (H : ℕ) : ℝ :=
  max 0 (s*oddQuotientPrimeExcess D H)

/-- Common height guaranteed by eligibility of a numerator. -/
def primeExcursionFloor (a g T : ℝ) : ℝ := a*Real.exp (g*T)*Real.sqrt (Real.exp T)

/-- An integer square-root error bound for the complete odd-quotient row. -/
def primeRowFlankAllowance : ℕ := ⌈oddQuotientPrimeExcess_complete_above_sqrt.choose⌉₊

/-- The right flank can use the numerator bound or completion to the
full row. Completion gives a linear cap in the middle endpoint. -/
def primeFlankCap (left : Bool) (k L : ℕ) : ℕ :=
  if left then 4*k else min (4*L^2) ((4+primeRowFlankAllowance)*L)

def primeLevelCount (cap : ℕ) (B : ℝ) : ℕ := Nat.log 2 ⌈(cap:ℝ)/B⌉₊

private theorem cap_height (D : Finset ℕ) {V H : ℕ} (hD : D⊆Ioc 0 V)
    {s : ℝ} (hs : |s|=1) : numeratorExcursionHeight D s H≤4*(V:ℝ) := by
  apply max_le (by positivity)
  calc _ ≤ |s*oddQuotientPrimeExcess D H| := le_abs_self _
       _ = |oddQuotientPrimeExcess D H| := by rw [abs_mul,hs,one_mul]
       _ ≤ (1+Real.log 4)*V := oddQuotientPrimeExcess_le D V H hD
       _ ≤ _ := by
         apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
         linarith only [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4)]

private theorem cap_height_numerator (D : Finset ℕ) (H : ℕ) {s : ℝ} (hs : |s|=1) :
    numeratorExcursionHeight D s H ≤ 4*(H:ℝ) := by
  apply max_le (by positivity)
  calc _ ≤ |s*oddQuotientPrimeExcess D H| := le_abs_self _
       _ = |oddQuotientPrimeExcess D H| := by rw [abs_mul,hs,one_mul]
       _ ≤ _ := odd_prime_excess_bound_by_numerator D H

/-- Above the middle endpoint the right flank is the complement of a
row of length at most L inside a complete square-root-error row. -/
theorem completed_right_flank_cap (L H : ℕ) (hr : Real.sqrt H ≤ L) :
    |oddQuotientPrimeExcess (Ioc L H) H| ≤ ((4+primeRowFlankAllowance:ℕ):ℝ)*L := by
  by_cases h : H ≤ L
  · rw [Ioc_eq_empty_of_le h]
    simp only [oddQuotientPrimeExcess,sum_empty,abs_zero]
    positivity
  let C := oddQuotientPrimeExcess_complete_above_sqrt.choose
  obtain ⟨_,row⟩ := oddQuotientPrimeExcess_complete_above_sqrt.choose_spec
  have comp := row H H le_rfl
  have hC : C ≤ (primeRowFlankAllowance:ℝ) := Nat.le_ceil _
  let I := oddQuotientPrimeExcess (Ioc ⌊Real.sqrt H⌋₊ L) H
  let J := oddQuotientPrimeExcess (Ioc L H) H
  have add : I+J=oddQuotientPrimeExcess (Ioc ⌊Real.sqrt H⌋₊ H) H :=
    sum_Ioc_consecutive _ (Nat.floor_le_of_le hr) (le_of_not_ge h)
  have si : |I| ≤ (1+Real.log 4)*L := oddQuotientPrimeExcess_le _ L H
    (fun n hn => mem_Ioc.mpr ⟨(Nat.zero_le _).trans_lt (mem_Ioc.mp hn).1,(mem_Ioc.mp hn).2⟩)
  have si' : |I| ≤ 4*(L:ℝ) := si.trans (mul_le_mul_of_nonneg_right
    (by linarith only [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4)]) (Nat.cast_nonneg L))
  rw [←add] at comp
  have full : |I+J| ≤ (primeRowFlankAllowance:ℝ)*L :=
    comp.trans (mul_le_mul hC hr (Real.sqrt_nonneg _) (Nat.cast_nonneg _))
  have tri := abs_sub (I+J) I
  rw [add_sub_cancel_left] at tri
  change |J| ≤ _
  push_cast
  linarith only [tri,full,si']

/-- The positive excursion is paid from the available prime mass. The
negative excursion is paid from the number of odd-quotient sites. -/
theorem one_sided_odd_quotient_heights (D : Finset ℕ) (H V : ℕ)
    (hv : D.filter (fun n => H/n%2=1) ⊆ Ioc 0 V) :
    numeratorExcursionHeight D 1 H ≤ (V:ℝ)*Real.log 4 ∧
    numeratorExcursionHeight D (-1) H ≤ (D.filter (fun n => H/n%2=1)).card := by
  let Q := D.filter fun n => H/n%2=1
  let P := Q.filter Nat.Prime
  let W := ∑ n ∈ P, Real.log (n:ℝ)
  have id : oddQuotientPrimeExcess D H = W-(Q.card:ℝ) := by
    rw [oddQuotientPrimeExcess,← sum_filter]
    change (∑ n ∈ Q, ((if n.Prime then Real.log (n:ℝ) else 0)-1))=_
    rw [sum_sub_distrib,← sum_filter,sum_const,nsmul_eq_mul,mul_one]
  have hP : P ⊆ Nat.primesLE V := fun n hn => Nat.mem_primesLE.mpr
    ⟨(mem_Ioc.mp (hv (mem_filter.mp hn).1)).2,(mem_filter.mp hn).2⟩
  have upper : W ≤ (V:ℝ)*Real.log 4 := (sum_le_sum_of_subset_of_nonneg hP
    (fun n _ _ => Real.log_natCast_nonneg n)).trans (_root_.RHTower.Sieve.sum_log_primesLE_le V)
  have low : 0 ≤ W := sum_nonneg fun n _ => Real.log_natCast_nonneg n
  simp only [numeratorExcursionHeight,id,one_mul,neg_one_mul]
  exact ⟨max_le (by positivity) ((sub_le_self _ (Nat.cast_nonneg _)).trans upper),
    max_le (Nat.cast_nonneg _) (by linarith only [low])⟩

/-- After measuring heights in units of √H, the middle interval and
either flank have product at most L log 4. Opposite orientations charge
only one Chebyshev bound, and the flank's numerator cap cancels both
square-root factors. -/
theorem opposite_prime_root_scaled_product (left : Bool) {s : ℝ} (hs : |s|=1)
    (k L H : ℕ) :
    (numeratorExcursionHeight (Ioc k L) s H / Real.sqrt H) *
      (numeratorExcursionHeight (middleTestFlank left k L H) (-s) H / Real.sqrt H) ≤ (L:ℝ)*Real.log 4 := by
  rcases Nat.eq_zero_or_pos H with rfl | hp
  · simp only [Nat.cast_zero,Real.sqrt_zero,div_zero,mul_zero]
    positivity
  let f := numeratorExcursionHeight (Ioc k L) s H
  let g := numeratorExcursionHeight (middleTestFlank left k L H) (-s) H
  let D := middleTestFlank left k L H
  have mid : (Ioc k L).filter (fun n => H/n%2=1) ⊆ Ioc 0 L := by
    intro n hn
    obtain ⟨lo,hi⟩ := mem_Ioc.mp (mem_filter.mp hn).1
    exact mem_Ioc.mpr ⟨(Nat.zero_le _).trans_lt lo,hi⟩
  have side : D.filter (fun n => H/n%2=1) ⊆ Ioc 0 H := by
    intro n hn
    have odd := (mem_filter.mp hn).2
    apply mem_Ioc.mpr
    constructor
    · by_contra! he
      have hz : n = 0 := by omega
      simp [hz] at odd
    · by_contra! he
      simp [Nat.div_eq_of_lt he] at odd
  have cardBound {Q : Finset ℕ} {V : ℕ} (hQ : Q ⊆ Ioc 0 V) : (Q.card:ℝ) ≤ V := by
    exact_mod_cast (show Q.card ≤ V by simpa only [Nat.card_Ioc,Nat.sub_zero] using card_le_card hQ)
  obtain ⟨mpos,mneg⟩ := one_sided_odd_quotient_heights (Ioc k L) H L mid
  obtain ⟨gpos,gneg⟩ := one_sided_odd_quotient_heights D H H side
  have sign : s=1 ∨ s= -1 := by
    by_cases h : 0 ≤ s
    · exact Or.inl ((abs_of_nonneg h).symm.trans hs)
    · rw [abs_of_neg (lt_of_not_ge h)] at hs
      exact Or.inr (by linarith only [hs])
  have prod : f*g ≤ (L:ℝ)*Real.log 4*H := by
    change numeratorExcursionHeight _ s H * numeratorExcursionHeight D (-s) H ≤ _
    rcases sign with rfl | rfl
    · exact mul_le_mul mpos (gneg.trans (cardBound side)) (le_max_left ..) (by positivity)
    · rw [neg_neg]
      have p := mul_le_mul (mneg.trans (cardBound mid)) gpos (le_max_left 0 _) (Nat.cast_nonneg L)
      linarith only [p]
  rw [div_mul_div_comm,← sq,Real.sq_sqrt (Nat.cast_nonneg H)]
  apply (div_le_iff₀ (Nat.cast_pos.mpr hp : 0 < (H:ℝ))).mpr
  exact prod

/-- Every nonempty pair of square-root-normalized dyadic superlevels lies
below a single diagonal, independently of the band endpoints and the
choice of flank. -/
theorem root_scaled_prime_levels_diagonal (left : Bool) {s A : ℝ} (hs : |s|=1)
    (hA : 0 ≤ A) (k L H r t : ℕ)
    (hf : A*2^r ≤ numeratorExcursionHeight (Ioc k L) s H / Real.sqrt H)
    (hg : A*2^t ≤ numeratorExcursionHeight (middleTestFlank left k L H) (-s) H / Real.sqrt H) :
    A^2 * 2^(r+t) ≤ (L:ℝ)*Real.log 4 := by
  have h := mul_le_mul hf hg (by positivity) (hf.trans' (by positivity))
  calc A^2 * 2^(r+t) = (A*2^r)*(A*2^t) := by rw [pow_add]; ring
       _ ≤ _ := h.trans (opposite_prime_root_scaled_product left hs k L H)

private theorem top_height {x B : ℝ} (hB : 0<B) {cap : ℕ} (hx : x≤cap) :
    x/B < (2:ℝ)^(primeLevelCount cap B+1) := by
  have he := Nat.le_ceil ((cap:ℝ)/B)
  apply ((div_le_div_of_nonneg_right hx hB.le).trans he).trans_lt
  exact_mod_cast Nat.lt_pow_succ_log_self (by decide : 1<2) ⌈(cap:ℝ)/B⌉₊

/-- The simultaneous occupied levels and the two raw cutoffs refer to one
maximizing rectangle. The cost can be read either from the actual joint
support or from separate upper bounds for the two coordinates. -/
theorem opposite_prime_occupied_levels (left : Bool) {s a g d T : ℝ} (k L : ℕ)
    (hs : s=1 ∨ s= -1) (ha : 0<a) :
    let S := largeOppositePrimeNumerators left s a g d T k L
    let B := primeExcursionFloor a g T
    let f := numeratorExcursionHeight (Ioc k L) s
    let h := fun H => numeratorExcursionHeight (middleTestFlank left k L H) (-s) H
    let M := primeLevelCount (4*L) B
    let N := primeLevelCount (primeFlankCap left k L) B
    ∃ r≤M, ∃ t≤N,
      let R := upperRectangle S f h (fun H => 1/(H:ℝ)^2) (B*2^r) (B*2^t)
      (∑ H ∈ S, oppositePrimeProduct left s k L H) ≤
        4*occupiedDyadicArea S (fun H => f H/B) (fun H => h H/B) M N*R ∧
      (∑ H ∈ S, oppositePrimeProduct left s k L H) ≤ ((M:ℝ)+2)*((N:ℝ)+2)*R := by
  classical
  intro S B f h M N
  have hB : 0<B := mul_pos (mul_pos ha (Real.exp_pos _)) (Real.sqrt_pos.mpr (Real.exp_pos _))
  have hsg : |s|=1 := by rcases hs with rfl|rfl <;> norm_num
  let F i := f i/B
  let G i := h i/B
  let w (i : ℕ) := 1/(i:ℝ)^2
  have bounds (i : ℕ) (hi : i∈S) :
      1≤F i ∧ F i<(2:ℝ)^(M+1) ∧ 1≤G i ∧ G i<(2:ℝ)^(N+1) ∧ 0≤w i := by
    obtain ⟨hnum,hi₁,hi₂⟩ := mem_filter.mp hi
    obtain ⟨hrange,hT,_⟩ := mem_filter.mp hnum
    have hfloor : B≤a*Real.exp (g*T)*Real.sqrt i :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hT) (mul_pos ha (Real.exp_pos _)).le
    have lower₁ := (hfloor.trans hi₁.le).trans (le_max_right 0 _)
    have lower₂ := (hfloor.trans hi₂.le).trans (le_max_right 0 _)
    have max₁ : f i≤((4*L:ℕ):ℝ) := by
      push_cast
      exact cap_height _ (fun n hn => mem_Ioc.mpr ⟨(Nat.zero_le _).trans_lt (mem_Ioc.mp hn).1,(mem_Ioc.mp hn).2⟩) hsg
    have max₂ : h i≤((primeFlankCap left k L:ℕ):ℝ) := by
      cases left with
      | true =>
        change numeratorExcursionHeight (Ioc ⌊Real.sqrt (i:ℝ)⌋₊ k) (-s) i≤((4*k:ℕ):ℝ)
        push_cast
        exact cap_height _ (fun n hn => mem_Ioc.mpr ⟨(Nat.zero_le _).trans_lt (mem_Ioc.mp hn).1,(mem_Ioc.mp hn).2⟩)
          ((abs_neg s).trans hsg)
      | false =>
        change numeratorExcursionHeight (Ioc L i) (-s) i ≤ ((min _ _:ℕ):ℝ)
        rw [Nat.cast_min]
        apply le_min
        · apply (cap_height_numerator _ i ((abs_neg s).trans hsg)).trans
          exact_mod_cast Nat.mul_le_mul_left 4 (mem_range.mp hrange).le
        · have hr : Real.sqrt (i:ℝ) ≤ L := Real.sqrt_le_iff.mpr
            ⟨Nat.cast_nonneg _,by exact_mod_cast (mem_range.mp hrange).le⟩
          apply max_le (Nat.cast_nonneg _)
          calc _ ≤ |(-s)*oddQuotientPrimeExcess (Ioc L i) i| := le_abs_self _
               _ = |oddQuotientPrimeExcess (Ioc L i) i| := by rw [abs_mul,abs_neg,hsg,one_mul]
               _ ≤ _ := by simpa only [Nat.cast_mul] using completed_right_flank_cap L i hr
    exact ⟨(one_le_div hB).mpr lower₁,top_height hB max₁,(one_le_div hB).mpr lower₂,
      top_height hB max₂,by dsimp only [w]; positivity⟩
  let J := range (M+1) ×ˢ range (N+1)
  let P (z : ℕ × ℕ) := upperRectangle S F G w (2^z.1) (2^z.2)
  have hJ : J.Nonempty := ⟨(0,0),mem_product.mpr ⟨mem_range.mpr (by omega),mem_range.mpr (by omega)⟩⟩
  obtain ⟨j,hj,hmax⟩ := J.exists_max_image P hJ
  obtain ⟨hr,ht⟩ := mem_product.mp hj
  refine ⟨j.1,Nat.le_of_lt_succ (mem_range.mp hr),j.2,Nat.le_of_lt_succ (mem_range.mp ht),?_⟩
  intro R
  let area := occupiedDyadicArea S F G M N
  have budget := dyadic_rectangle_occupied_bound S F G w M N (P j) bounds
    (fun r hr t ht => hmax (r,t) (mem_product.mpr ⟨mem_range.mpr (by omega),mem_range.mpr (by omega)⟩))
  have raw H (hi : H ∈ S) : oppositePrimeProduct left s k L H = B^2*(F H*G H*w H) := by
    have hp : 0 < (H:ℝ) := (Real.exp_pos T).trans_le (mem_filter.mp (mem_filter.mp hi).1).2.1
    change (f H*h H)/(H:ℝ)^2=B^2*((f H/B)*(h H/B)*(1/(H:ℝ)^2))
    field_simp [hB.ne',hp.ne']
  have rect : B^2*P j = R := by
    have thr (y t : ℝ) : t≤y/B ↔ B*t≤y := by rw [le_div_iff₀ hB,mul_comm t]
    change B^2*((2:ℝ)^j.1*2^j.2*∑ H ∈ S.filter (fun H => _), w H)=
      (B*2^j.1)*(B*2^j.2)*∑ H ∈ S.filter (fun H => _), w H
    simp only [F,G,thr]
    ring
  have positive : 0≤P j := mul_nonneg (by positivity) (sum_nonneg (fun H _ => by dsimp only [w]; positivity))
  have hR : 0≤R := rect ▸ mul_nonneg (sq_nonneg B) positive
  have first : (∑ H ∈ S, oppositePrimeProduct left s k L H)≤4*area*R := by
    rw [sum_congr rfl raw,←mul_sum,←rect]
    have hb := mul_le_mul_of_nonneg_left budget (sq_nonneg B)
    change B^2*_≤B^2*(4*area*P j) at hb
    linarith only [hb]
  refine ⟨first,first.trans ?_⟩
  apply mul_le_mul_of_nonneg_right _ hR
  have hh := occupiedDyadicArea_le S F G M N
  change area≤_ at hh
  linarith only [hh]

/-- An off-line zero forces, at arbitrarily late cutoffs on one fixed
band, a single joint rectangle priced above the critical scale after
multiplication by its observed occupied area. -/
theorem rh_or_occupied_prime_rectangle : RiemannHypothesis ∨
    ∃ a c g d w : ℝ, 0 < a ∧ 0 < c ∧ 0 < g ∧ 0 < d ∧ d ≤ 1/4 ∧ 0 < w ∧
      ∀ η : ℝ, 0 < η → η ≤ w → ∃ (T : ℕ → ℝ) (k : ℕ → ℕ), Tendsto T atTop atTop ∧
        (∀ i, T i/(1+η) ≤ Real.log (k i) ∧ Real.log (k i) ≤ T i) ∧
        ∀ᶠ i in atTop,
          let L := ⌈Real.exp ((1+η)*T i)⌉₊
          let B := primeExcursionFloor a g (T i)
          ∃ (s : ℝ) (left : Bool), (s=1 ∨ s= -1) ∧
            let S := largeOppositePrimeNumerators left s a g d (T i) (k i) L
            let f := numeratorExcursionHeight (Ioc (k i) L) s
            let h := fun H => numeratorExcursionHeight (middleTestFlank left (k i) L H) (-s) H
            let M := primeLevelCount (4*L) B
            let N := primeLevelCount (primeFlankCap left (k i) L) B
            ∃ r ≤ M, ∃ t ≤ N,
              let R := upperRectangle S f h (fun H => 1/(H:ℝ)^2) (B*2^r) (B*2^t)
              let Z := c*a^2*Real.exp ((1/2+3*g)*T i)
              Z < (L:ℝ)*(4*occupiedDyadicArea S (fun H => f H/B) (fun H => h H/B) M N*R) ∧
                Z < (L:ℝ)*(((M:ℝ)+2)*((N:ℝ)+2)*R) := by
  rcases riemannHypothesis_or_fixed_band_opposite_prime_moment with rh |
    ⟨_,_,_,a,c,g,d,w,_,_,_,_,_,ha,hc,hg,hd,hd',hw,seq⟩
  · exact Or.inl rh
  refine Or.inr ⟨a,c,g,d,w,ha,hc,hg,hd,hd',hw,fun η hη hηw => ?_⟩
  obtain ⟨T,k,ht,hk,_,ev⟩ := seq η hη hηw
  refine ⟨T,k,ht,hk,?_⟩
  filter_upwards [ev] with i hi
  let L := ⌈Real.exp ((1+η)*T i)⌉₊
  obtain ⟨_,_,s,left,_,_,hs,_,_,_,_,_,big⟩ := hi
  obtain ⟨r,hr,t,ht,small,full⟩ := opposite_prime_occupied_levels left (g:=g) (d:=d) (T:=T i) (k i) L hs ha
  exact ⟨s,left,hs,r,hr,t,ht,big.trans_le (mul_le_mul_of_nonneg_left small (Nat.cast_nonneg L)),
    big.trans_le (mul_le_mul_of_nonneg_left full (Nat.cast_nonneg L))⟩

#print axioms rh_or_occupied_prime_rectangle
#print axioms opposite_prime_occupied_levels
#print axioms opposite_prime_root_scaled_product
#print axioms completed_right_flank_cap
#print axioms one_sided_odd_quotient_heights
#print axioms root_scaled_prime_levels_diagonal
end GaloisForLFunctions.ExclusionOfTheCriticalState
