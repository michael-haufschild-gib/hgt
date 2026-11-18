import GaloisForLFunctions.ExceptionalLayerTheory.FactorialWeightsOnReciprocalProductWindows
import GaloisForLFunctions.ExceptionalLayerTheory.ShortComplementsInTheSquareRootProductWindow
import GaloisForLFunctions.ExceptionalLayerTheory.RemovingSmallOrdinaryPrimesAtBothWidths

/-!
# Cancellation across the square-root product interval

For short complementary factors, the complete prime interval lies in the
reciprocal prime band. For two long factors the bilinear fractional-part
bound applies simultaneously to all divisors of the centered weight.
-/

noncomputable section
open Finset RHTower ArithmeticFunction
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- Upper endpoint of the square-root product interval. -/
def squareRootProductUpper (X : ℕ) := ⌊(X : ℝ)^(500000001/1000000000 : ℝ)⌋₊

/-- Ordinary-prime coefficient, extended to all first factors. -/
private def primeLog (p : ℕ) : ℝ := if p.Prime then Real.log p else 0

/-- Ordinary prime products over a prescribed interval of complementary factors. -/
def ordinaryProductWindow (D R X F L U c d : ℕ) : ℝ :=
  ∑ q ∈ (Ico (F+1) (X+1) ×ˢ Ico c d) with L<q.1*q.2 ∧ q.1*q.2≤U,
    (primeLog q.1*innerJump D q.2)*centeredPrimeWeight R (X/(q.1*q.2))

/-- Transposing the sharp window keeps the integer quotient endpoints exactly. -/
theorem ordinary_window_by_complement {D R X F L U c d : ℕ} (hc : 1 ≤ c) (hu : U ≤ X) :
    ordinaryProductWindow D R X F L U c d =
      ∑ v ∈ Ico c d, innerJump D v*∑ p ∈ squareRootWindowPrimes F L U v,
        Real.log p*centeredPrimeWeight R (X/v/p) := by
  unfold ordinaryProductWindow
  rw [sum_filter,sum_product,sum_comm]
  apply sum_congr rfl
  intro v hv
  have hv₁ := hc.trans (mem_Ico.mp hv).1
  let test (p : ℕ) := p.Prime ∧ L<p*v ∧ p*v≤U
  have hidx : squareRootWindowPrimes F L U v=((Ico (F+1) (X+1)).filter test) := by
    ext p
    have hlo : L/v<p ↔ L<p*v := Nat.div_lt_iff_lt_mul hv₁
    have hhi : p≤U/v ↔ p*v≤U := Nat.le_div_iff_mul_le hv₁
    have hpx : U/v ≤ X := (Nat.div_le_self U v).trans hu
    simp only [squareRootWindowPrimes,mem_filter,mem_Ico,max_le_iff,test]
    omega
  rw [hidx,sum_filter,mul_sum]
  apply sum_congr rfl
  intro p _
  by_cases hp : p.Prime <;> by_cases hh : L<p*v ∧ p*v≤U <;>
    simp [primeLog,test,hp,hh,Nat.div_div_eq_div_mul,Nat.mul_comm v p,mul_left_comm,mul_assoc]

/-- Cutting the complementary factor is an exact partition at every fixed
pair of product endpoints. -/
theorem ordinary_window_split {D R X F L U q : ℕ} (hu : U ≤ X) (hq : q ≤ X) :
    ordinaryProductWindow D R X F L U 1 (X+1) =
      ordinaryProductWindow D R X F L U 1 (q+1)+ordinaryProductWindow D R X F L U (q+1) (X+1) := by
  rw [ordinary_window_by_complement (by decide) hu,ordinary_window_by_complement (by decide) hu,
    ordinary_window_by_complement (Nat.succ_pos _) hu]
  exact (sum_Ico_consecutive _ (Nat.succ_le_succ (Nat.zero_le q)) (Nat.succ_le_succ hq)).symm

/-- At logarithmic factorial cutoff the prime product window costs at most
square-root error with five logarithms, uniformly in the first-prime
threshold above the short complementary-factor scale. -/
theorem ordinary_square_root_window_bound :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ X : ℕ, 1 ≤ X → ∀ F L : ℕ,
      ⌊(X : ℝ)^(1/1000000 : ℝ)⌋₊ ≤ F →
      Real.sqrt X ≤ (L : ℝ)+1 →
      let D := ⌊1+Real.log X⌋₊
      |ordinaryProductWindow D D X F L (squareRootProductUpper X) 1 (X+1)| ≤
        K*(1+Real.log X)^5*Real.sqrt X := by
  obtain ⟨C,hC,hshort⟩ := short_complement_window_bound
  obtain ⟨K,hK,hlong⟩ := square_root_window_power_bound
  obtain ⟨B,hB,hmass⟩ := mass_uniform
  obtain ⟨Z,hZ⟩ := Filter.eventually_atTop.mp (Sieve.eventually_const_mul_one_add_log_pow_le_rpow
    (by norm_num : (0 : ℝ) < 1/25000000) (by norm_num : (0 : ℝ) < 17000) 2)
  let E := ∑ i ∈ Icc 1 ⌈Z⌉₊, ∑ p ∈ Icc 1 i, ∑ v ∈ Icc 1 i,
    |(primeLog p*innerJump ⌊1+Real.log i⌋₊ v)*centeredPrimeWeight ⌊1+Real.log i⌋₊ (i/(p*v))|
  have hE : 0 ≤ E := sum_nonneg fun _ _ => sum_nonneg fun _ _ => sum_nonneg fun _ _ => abs_nonneg _
  let T := 16*K*(1+B)^2+2*C+E
  have hT : 0 ≤ T := by dsimp [T]; positivity
  refine ⟨T,hT,?_⟩
  intro X hx F L hF hL D
  let J := 1+Real.log X
  let U := squareRootProductUpper X
  let q := ⌊(X : ℝ)^(1/1000000 : ℝ)⌋₊
  have hx₁ : (1 : ℝ) ≤ X := by exact_mod_cast hx
  have hJ : 1 ≤ J := le_add_of_nonneg_right (Real.log_natCast_nonneg X)
  have hJ₀ := zero_le_one.trans hJ
  have hD : 1 ≤ D := (Nat.one_le_floor_iff _).mpr hJ
  have hd : (D : ℝ) ≤ J := Nat.floor_le hJ₀
  have hd₁ : ((D+1 : ℕ) : ℝ) ≤ 2*J := by push_cast; linarith only [hd,hJ]
  have hU : (U : ℝ) ≤ (X : ℝ)^(500000001/1000000000 : ℝ) := Nat.floor_le (by positivity)
  have hu : U ≤ X := by exact_mod_cast hU.trans ((Real.rpow_le_rpow_of_exponent_le hx₁
    (by norm_num : (500000001/1000000000 : ℝ) ≤ 1)).trans_eq (Real.rpow_one _))
  have hq : q ≤ X := Nat.floor_le_of_le ((Real.rpow_le_rpow_of_exponent_le hx₁
    (by norm_num : (1/1000000 : ℝ) ≤ 1)).trans_eq (Real.rpow_one _))
  have hroot : 1 ≤ Real.sqrt X := Real.one_le_sqrt.mpr hx₁
  by_cases hZX : Z ≤ X
  swap
  · let w (p v : ℕ) := (primeLog p*innerJump D v)*centeredPrimeWeight D (X/(p*v))
    have hsub : ((Ico (F+1) (X+1) ×ˢ Ico 1 (X+1)).filter
        (fun t : ℕ×ℕ => L<t.1*t.2 ∧ t.1*t.2≤U)) ⊆ Icc 1 X ×ˢ Icc 1 X := by
      intro t ht
      obtain ⟨hp,hv⟩ := mem_product.mp (mem_filter.mp ht).1
      obtain ⟨hl,hu⟩ := mem_Ico.mp hp
      obtain ⟨hv₁,hv₂⟩ := mem_Ico.mp hv
      exact mem_product.mpr ⟨mem_Icc.mpr ⟨by omega,by omega⟩,mem_Icc.mpr ⟨hv₁,by omega⟩⟩
    have hrow : |ordinaryProductWindow D D X F L U 1 (X+1)| ≤ E := by
      unfold ordinaryProductWindow
      apply (abs_sum_le_sum_abs _ _).trans
      apply (sum_le_sum_of_subset_of_nonneg hsub (fun t _ _ => abs_nonneg (w t.1 t.2))).trans
      rw [sum_product]
      exact single_le_sum (f := fun i => ∑ p ∈ Icc 1 i, ∑ v ∈ Icc 1 i,
        |(primeLog p*innerJump ⌊1+Real.log i⌋₊ v)*centeredPrimeWeight ⌊1+Real.log i⌋₊ (i/(p*v))|)
        (fun _ _ => sum_nonneg fun _ _ => sum_nonneg fun _ _ => abs_nonneg _) (mem_Icc.mpr ⟨hx,
          by exact_mod_cast (le_of_not_ge hZX).trans (Nat.le_ceil Z)⟩)
    have het : E ≤ T := by dsimp [T]; linarith only [hC,mul_nonneg hK (sq_nonneg (1+B))]
    exact hrow.trans (het.trans ((le_mul_of_one_le_right hT (one_le_pow₀ hJ)).trans
      (le_mul_of_one_le_right (by positivity) hroot)))
  have hz : 17000*J^2 ≤ (X : ℝ)^(1/25000000 : ℝ) := hZ _ hZX
  have hj₂ := one_le_pow₀ hJ (n := 2)
  have hlarge : 64 ≤ (X : ℝ)^(1/25000000 : ℝ) := by linarith only [hz,hj₂]
  have hbig : J ≤ (X : ℝ)^(1/25000000 : ℝ) := by
    have hh := le_mul_of_one_le_right hJ₀ hJ
    linarith only [hh,hz,hj₂]
  have hm : ((128*(128*D^2+1) : ℕ) : ℝ) ≤ (X : ℝ)^(1/25000000 : ℝ) := by
    push_cast; linarith only [pow_le_pow_left₀ (Nat.cast_nonneg D) hd 2,hz,hj₂]
  have hright {s : ℝ} (hs : 1/25000000 ≤ s) : (X : ℝ)^(1/25000000 : ℝ) ≤ (X : ℝ)^s :=
    Real.rpow_le_rpow_of_exponent_le hx₁ hs
  have hsmall := hshort (D := D) (F := F) hx hD
    ((show (2 : ℝ) ≤ 64 by norm_num).trans (hlarge.trans (hright (by norm_num))))
    (hd.trans (hbig.trans (hright (by norm_num)))) hL hU
  have hs : |ordinaryProductWindow D D X F L U 1 (q+1)| ≤ 2*C*J*Real.sqrt X := by
    rw [ordinary_window_by_complement (by decide) hu,show Ico 1 (q+1)=Icc 1 q by ext n; simp; omega]
    apply hsmall.trans
    have hp : (X : ℝ)^(499701/1000000 : ℝ) ≤ Real.sqrt X := by
      rw [Real.sqrt_eq_rpow]; exact Real.rpow_le_rpow_of_exponent_le hx₁ (by norm_num)
    exact (mul_le_mul (mul_le_mul_of_nonneg_left hd₁ hC) hp (by positivity)
      (by positivity)).trans_eq (by ring)
  have weight : 1+mass D ≤ (1+B)*J := by
    linarith only [hmass D hD,mul_le_mul_of_nonneg_left hd hB,hJ]
  have inner : ∀ m, |innerJump D m| ≤ 4*(1+B)*J := by
    intro m
    apply (innerJump_pointwise_bound D m).trans
    linarith only [hmass (D+1) (Nat.succ_pos D),mul_le_mul_of_nonneg_left hd₁ hB,hJ,mul_nonneg hB hJ₀]
  have hlog : 1+Real.log (X+1 : ℕ) ≤ 2*J := by
    have hh : ((X+1 : ℕ) : ℝ) ≤ 2*X := by push_cast; linarith only [hx₁]
    have hl := Real.log_le_log (by positivity : (0 : ℝ) < (X+1 : ℕ)) hh
    rw [Real.log_mul (by norm_num) (zero_lt_one.trans_le hx₁).ne'] at hl
    dsimp [J]; linarith only [hl,Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<2),Real.log_natCast_nonneg X]
  have hlong' : |ordinaryProductWindow D D X F L U (q+1) (X+1)| ≤
      16*K*(1+B)^2*J^5*Real.sqrt X := by
    by_cases hfx : F ≤ X
    swap
    · simp only [ordinaryProductWindow,Ico_eq_empty (show X+1 ≤ F+1 by omega),empty_product,filter_empty,sum_empty,abs_zero]
      positivity
    have a : (X : ℝ)^(1/1000000 : ℝ) ≤ (q+1 : ℕ) := by
      push_cast; exact (Nat.lt_floor_add_one _).le
    have hh := hlong hD hx hlarge hm (a.trans (by exact_mod_cast Nat.succ_le_succ hF)) a
      (Nat.succ_le_succ hfx) (Nat.succ_le_succ hq) hL hU primeLog (innerJump D)
      hJ₀ (by positivity : 0 ≤ 4*(1+B)*J) (fun p hp => by
        by_cases hpp : p.Prime
        · have hpx : p ≤ X := Nat.le_of_lt_succ (mem_Ico.mp hp).2
          simp only [primeLog,if_pos hpp,abs_of_nonneg (Real.log_natCast_nonneg _)]
          exact (Real.log_le_log (by exact_mod_cast hpp.pos) (by exact_mod_cast hpx)).trans
            (by dsimp [J]; linarith)
        · simpa only [primeLog,if_neg hpp,abs_zero] using hJ₀) (fun m _ => inner m)
    apply hh.trans
    have hl₀ := le_add_of_nonneg_right (Real.log_natCast_nonneg (X+1))
    have hcost := mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left weight hK) hlog
      (zero_le_one.trans hl₀) (by positivity)) hlog (zero_le_one.trans hl₀) (by positivity)
    exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcost
      (by positivity : 0 ≤ J*(4*(1+B)*J))) (Real.sqrt_nonneg _)).trans_eq (by ring)
  rw [ordinary_window_split hu hq]
  apply (abs_add_le _ _).trans ((add_le_add hs hlong').trans _)
  have hpow := (by simpa only [pow_one] using pow_le_pow_right₀ hJ (by norm_num : 1 ≤ 5) : J ≤ J^5)
  have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow
    (by positivity : 0 ≤ 2*C)) (Real.sqrt_nonneg (X : ℝ))
  change _ ≤ T*J^5*Real.sqrt X
  dsimp [T]; linarith only [hh,mul_nonneg (mul_nonneg hE (pow_nonneg hJ₀ 5)) (Real.sqrt_nonneg (X : ℝ))]


/-- Logarithmic prime pairing above the first-factor threshold. -/
def ordinaryFactorTail (F X : ℕ) (f : ℕ → ℝ) : ℝ :=
  ∑ p ∈ (Ioc F X).filter Nat.Prime, vonMangoldt p*f p

/-- Raising the lower product endpoint removes precisely the corresponding
ordinary prime window, including its boundary products. -/
theorem ordinary_window_tail_difference {D R X F L U : ℕ} (hU : U ≤ X) :
    ordinaryProductWindow D R X F L U 1 (X+1) =
      ordinaryFactorTail F X (factorSlice D R X L) -
      ordinaryFactorTail F X (factorSlice D R X (max L U)) := by
  let f (p v : ℕ) := innerJump D v*centeredPrimeWeight R (X/p/v)
  let Δ (p : ℕ) := factorSlice D R X L p-factorSlice D R X (max L U) p
  have diff (p : ℕ) : Δ p = ∑ v ∈ Ioc (L/p) (U/p), f p v := by
    dsimp only [Δ,factorSlice]
    by_cases h : L ≤ U
    · rw [max_eq_right h,←sum_Ioc_consecutive (f p) (Nat.div_le_div_right h) (Nat.div_le_div_right hU)]
      ring
    · rw [max_eq_left (le_of_not_ge h),sub_self,Ioc_eq_empty (Nat.div_le_div_right (le_of_not_ge h)),sum_empty]
  have tail : ordinaryFactorTail F X (factorSlice D R X L) -
      ordinaryFactorTail F X (factorSlice D R X (max L U)) = ordinaryFactorTail F X Δ := by
    unfold ordinaryFactorTail
    rw [←sum_sub_distrib]
    exact sum_congr rfl fun p _ => (mul_sub _ _ _).symm
  rw [tail]
  unfold ordinaryProductWindow ordinaryFactorTail
  rw [sum_filter,sum_product,sum_filter,show Ico (F+1) (X+1)=Ioc F X by ext p; simp only [mem_Ico,mem_Ioc]; omega]
  apply sum_congr rfl
  intro p hp
  have hp₁ : 0 < p := (Nat.zero_le F).trans_lt (mem_Ioc.mp hp).1
  by_cases prime : p.Prime
  · have idx : (Ico 1 (X+1)).filter (fun v => L<p*v ∧ p*v≤U)=Ioc (L/p) (U/p) := by
      ext v
      have hlo : L/p<v ↔ L<p*v := by rw [Nat.div_lt_iff_lt_mul hp₁,Nat.mul_comm v p]
      have hhi : v≤U/p ↔ p*v≤U := by rw [Nat.le_div_iff_mul_le hp₁,Nat.mul_comm v p]
      have hx := (Nat.div_le_self U p).trans hU
      simp only [mem_filter,mem_Ico,mem_Ioc]
      omega
    rw [if_pos prime,vonMangoldt_apply_prime prime,diff,←idx,sum_filter,mul_sum]
    apply sum_congr rfl
    intro v _
    by_cases hh : L<p*v ∧ p*v≤U <;> simp [primeLog,prime,hh,f,Nat.div_div_eq_div_mul,mul_assoc]
  · rw [if_neg prime]
    apply sum_eq_zero
    intro v _
    simp [primeLog,prime]

/-- The shared-prime correction above any larger first-prime cutoff has
square-root cost uniformly in the lower product endpoint. -/
theorem ordinary_tail_coprime_difference :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {D R X F : ℕ}, 1 ≤ D → 1 ≤ R → 1 ≤ X → 2*(D+1) ≤ F → ∀ Y : ℕ,
      |ordinaryFactorTail F X (factorSlice D R X Y)-ordinaryFactorTail F X (coprimeSlice D R X Y)| ≤
        K*((D+1 : ℕ) : ℝ)*R*Real.sqrt X*(1+Real.log X) := by
  obtain ⟨C,hC,h⟩ := factor_slice_bounds
  let M := Real.log 4+4
  have hM : 1 ≤ M := by dsimp [M]; linarith only [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)]
  refine ⟨C*M,by positivity,?_⟩
  intro D R X F hD hR hX hF Y
  let A := C*((D+1 : ℕ) : ℝ)*R*Real.sqrt X
  have hA : 0 ≤ A := by dsimp [A]; positivity
  let S := (Ioc F X).filter Nat.Prime
  have hs : S ⊆ Icc 1 X := by
    intro p hp
    obtain ⟨hi,prime⟩ := mem_filter.mp hp
    exact mem_Icc.mpr ⟨prime.pos,(mem_Ioc.mp hi).2⟩
  have hm : ∑ p ∈ S, vonMangoldt p/p ≤ M*(1+Real.log X) := by
    apply (sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ => div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg _))).trans
    have hh := (abs_le.mp (Mertens.mertens_first X hX)).2
    have hm := mul_le_mul_of_nonneg_right hM (Real.log_natCast_nonneg X)
    dsimp only [M] at hm ⊢; linarith only [hh,hm]
  unfold ordinaryFactorTail
  rw [←sum_sub_distrib]
  apply (abs_sum_le_sum_abs _ _).trans
  calc _ ≤ ∑ p ∈ S, A*(vonMangoldt p/p) := by
            apply sum_le_sum
            intro p hp
            obtain ⟨hi,prime⟩ := mem_filter.mp hp
            rw [←mul_sub,abs_mul,abs_of_nonneg vonMangoldt_nonneg]
            have hh := (h hD hR X Y).2 p prime (hF.trans_lt (mem_Ioc.mp hi).1)
            exact (mul_le_mul_of_nonneg_left hh vonMangoldt_nonneg).trans_eq (by dsimp [A]; ring)
       _ ≤ _ := by
            rw [←mul_sum]
            exact (mul_le_mul_of_nonneg_left hm hA).trans_eq (by dsimp [A]; ring)

/-- Separate the small first primes before moving the product endpoint. -/
theorem ordinary_first_prime_partition (D R X Y : ℕ) :
    coprimePrimeRow D R X Y = shortFirstRow D R X Y+
      ordinaryFactorTail (max (2*(D+1)) ⌊(X : ℝ)^(1/200 : ℝ)⌋₊) X (coprimeSlice D R X Y) := by
  let S := (Ioc (2*(D+1)) X).filter Nat.Prime
  let Q := ⌊(X : ℝ)^(1/200 : ℝ)⌋₊
  have h₁ : S.filter (fun p => p≤Q) = shortFirstPrimes D X := by
    ext p
    simp only [S,shortFirstPrimes,mem_filter,mem_Ioc,le_min_iff,Q]; tauto
  have h₂ : S.filter (fun p => ¬p≤Q) = (Ioc (max (2*(D+1)) Q) X).filter Nat.Prime := by
    ext p
    simp only [S,mem_filter,mem_Ioc,max_lt_iff,not_le]; tauto
  exact (sum_filter_add_sum_filter_not S (fun p => p≤Q) (fun p => vonMangoldt p*coprimeSlice D R X Y p)).symm.trans
    (by rw [h₁,h₂]; rfl)

#print axioms ordinary_square_root_window_bound

/-- The logarithmic coprime row supported strictly above the square-root
product window and the small first-prime range. -/
def aboveSquareRootProductRow (X : ℕ) : ℝ :=
  let D := ⌊1+Real.log X⌋₊
  let F := max (2*(D+1)) ⌊(X : ℝ)^(1/200 : ℝ)⌋₊
  ordinaryFactorTail F X (coprimeSlice D D X (max (productLower D X) (squareRootProductUpper X)))

/-- Moving the entire lower product boundary to a fixed power strictly
above one half costs square-root error up to logarithms at both widths. -/
theorem above_square_root_product_cofactors :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ V W N : ℕ,
      |cofactorCountError V W N-∑ d ∈ Icc 1 (min N W), Sieve.typeIIShort V d*aboveSquareRootProductRow (N/d)| ≤
        (∑ d ∈ Icc 1 W, |Sieve.typeIIShort V d|)*(K*(1+Real.log N)^6*Real.sqrt N) := by
  obtain ⟨C,hC,hcop⟩ := coprime_prime_row_bound
  obtain ⟨B,hB,hsmall⟩ := logarithmic_short_first_bound
  obtain ⟨A,hA,hslab⟩ := ordinary_square_root_window_bound
  obtain ⟨E,hE,hrep⟩ := ordinary_tail_coprime_difference
  let K := C+B+A+4*E
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨K,hK,cofactor_transfer_majorant _ (fun x => K*(1+Real.log x)^6*Real.sqrt x)
    (fun x => by have := Real.log_natCast_nonneg x; positivity) ?_ ?_⟩
  · intro x n hx hxn
    have hlog := Real.log_le_log (by exact_mod_cast hx : (0 : ℝ)<x) (by exact_mod_cast hxn : (x : ℝ) ≤ n)
    have hz := Real.log_natCast_nonneg x
    exact mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity)
      (add_le_add (le_refl (1 : ℝ)) hlog) 6) hK) (Real.sqrt_le_sqrt (by exact_mod_cast hxn))
      (Real.sqrt_nonneg _) (by have := Real.log_natCast_nonneg n; positivity)
  · intro X hx
    let H := 1+Real.log X
    let D := ⌊H⌋₊
    let F := max (2*(D+1)) ⌊(X : ℝ)^(1/200 : ℝ)⌋₊
    let Y := productLower D X
    let U := squareRootProductUpper X
    let Y' := max Y U
    let G := H^6*Real.sqrt X
    let c (L : ℕ) := ordinaryFactorTail F X (coprimeSlice D D X L)
    let r (L : ℕ) := ordinaryFactorTail F X (factorSlice D D X L)
    have hx' : (1 : ℝ) ≤ X := by exact_mod_cast hx
    have hH : 1 ≤ H := le_add_of_nonneg_right (Real.log_natCast_nonneg X)
    have hH₀ := zero_le_one.trans hH
    have hD := (Nat.one_le_floor_iff _).mpr hH
    have hd : (D : ℝ) ≤ H := Nat.floor_le hH₀
    have hd' : ((D+1 : ℕ) : ℝ) ≤ 2*H := by push_cast; linarith only [hd,hH]
    have hY : ⌊Real.sqrt X⌋₊ ≤ Y := by
      exact le_min (Nat.floor_le_of_le (by rw [Real.sqrt_eq_rpow]; exact (Real.rpow_le_rpow_of_exponent_le
        hx' (by norm_num : (1/2 : ℝ) ≤ 1)).trans_eq (Real.rpow_one _)))
        (Nat.le_mul_of_pos_left _ (Nat.succ_pos D))
    have hfloor : Real.sqrt X ≤ (Y : ℝ)+1 := (Nat.lt_floor_add_one _).le.trans
      (add_le_add_right (by exact_mod_cast hY) 1)
    have hU : U ≤ X := Nat.floor_le_of_le ((Real.rpow_le_rpow_of_exponent_le hx'
      (by norm_num : (500000001/1000000000 : ℝ) ≤ 1)).trans_eq (Real.rpow_one _))
    have hF : ⌊(X : ℝ)^(1/1000000 : ℝ)⌋₊ ≤ F := (Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le
      hx' (by norm_num : (1/1000000 : ℝ) ≤ 1/200))).trans (le_max_right ..)
    have log5 : H^5*Real.sqrt X ≤ G := mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ hH (by norm_num : 5 ≤ 6)) (Real.sqrt_nonneg _)
    have first := hcop hx hD hD hH hd hd (show Real.log X ≤ H by dsimp [H]; linarith)
    have hc : |(Chebyshev.psi X-X)-coprimePrimeRow D D X Y| ≤ C*G :=
      first.trans ((by ring : C*H^5*Real.sqrt X=C*(H^5*Real.sqrt X)).le.trans (mul_le_mul_of_nonneg_left log5 hC))
    have hs : |shortFirstRow D D X Y| ≤ B*G := (hsmall X hx).trans_eq (by dsimp [G,H]; ring)
    have hw : |r Y-r Y'| ≤ A*G := by
      change |ordinaryFactorTail F X (factorSlice D D X Y)-ordinaryFactorTail F X (factorSlice D D X (max Y U))| ≤ _
      rw [←ordinary_window_tail_difference hU]
      exact (hslab X hx F Y hF hfloor).trans ((by ring : A*H^5*Real.sqrt X=A*(H^5*Real.sqrt X)).le.trans
        (mul_le_mul_of_nonneg_left log5 hA))
    have hr (L : ℕ) : |r L-c L| ≤ (2*E)*G := by
      have hp := hrep hD hD hx (le_max_left (2*(D+1)) ⌊(X : ℝ)^(1/200 : ℝ)⌋₊) L
      have hh := mul_le_mul hd' hd (Nat.cast_nonneg D) (by positivity)
      have hpoly := (by simpa only [pow_one] using pow_le_pow_right₀ hH (by norm_num : 3 ≤ 6) : H^3 ≤ H^6)
      have hz := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hh hH₀) (Real.sqrt_nonneg (X : ℝ))
      have ht := mul_le_mul_of_nonneg_right hpoly (Real.sqrt_nonneg (X : ℝ))
      apply hp.trans
      have s₁ := mul_le_mul_of_nonneg_left hz hE
      have s₂ := mul_le_mul_of_nonneg_left ht (by positivity : 0 ≤ 2*E)
      change E*((D+1 : ℕ) : ℝ)*D*Real.sqrt X*H ≤ (2*E)*G
      dsimp only [G]; linarith only [s₁,s₂]
    have split : coprimePrimeRow D D X Y=shortFirstRow D D X Y+c Y := ordinary_first_prime_partition ..
    have eq : (Chebyshev.psi X-X)-aboveSquareRootProductRow X =
        ((Chebyshev.psi X-X)-coprimePrimeRow D D X Y)+shortFirstRow D D X Y+
        (c Y-r Y)+(r Y-r Y')+(r Y'-c Y') := by
      change (Chebyshev.psi X-X)-c Y' = _
      rw [split]; ring
    rw [eq]
    have h₁ := (abs_add_le _ _).trans (add_le_add hc hs)
    have h₂ := (abs_add_le _ _).trans (add_le_add h₁ ((abs_sub_comm _ _).le.trans (hr Y)))
    have h₃ := (abs_add_le _ _).trans (add_le_add h₂ hw)
    exact (abs_add_le _ _).trans ((add_le_add h₃ (hr Y')).trans_eq (by dsimp [K,G,H]; ring))

#print axioms above_square_root_product_cofactors

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
