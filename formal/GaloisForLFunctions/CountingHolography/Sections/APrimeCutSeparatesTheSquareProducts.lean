import GaloisForLFunctions.CountingHolography.Sections.PrimeFactorMultiplicityOfTheSquareGenerator

/-! # One prime cutoff for the two reduced square products

Smoothing by a box preserves a single change from positive to negative.
The two shifted spline terms therefore have a common separator at every
scale. All prime factors on the wrong side cost only the total row error.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections

open ArithmeticCastelnuovoSeveri Set MeasureTheory Filter Topology ArithmeticWeightTheory BiScaleUncertainty.ChebyshevGauge
open _root_.RHTower.WeilDeletion _root_.RHTower ArithmeticFunction
open scoped Convolution

private def separatedAt (f : ℝ → ℝ) (c : ℝ) :=
  (∀ x ≤ c, 0 ≤ f x) ∧ ∀ x, c < x → f x ≤ 0

private theorem box_integral {f : ℝ → ℝ} (hf : Integrable f) (x : ℝ) :
    (unif 1 ⋆ f) x = (1/2:ℝ)*(∫ t in x-1..x+1, f t) := by
  rw [unif_convolution_eq one_pos hf,intervalIntegral.integral_interval_sub_left hf.intervalIntegrable hf.intervalIntegrable,
    mul_one]

/-- In the straddling window, motion to the right deletes positive mass
at the left edge and adds negative mass at the right edge. -/
private theorem box_separates {f : ℝ → ℝ} (hf : Integrable f) {c : ℝ} (hs : separatedAt f c) :
    ∃ d, separatedAt (unif 1 ⋆ f) d := by
  let F := fun x : ℝ => ∫ t in (0:ℝ)..x, f t
  let g := unif 1 ⋆ f
  have primitive (x y : ℝ) : F y-F x=∫ t in x..y, f t :=
    intervalIntegral.integral_interval_sub_left hf.intervalIntegrable hf.intervalIntegrable
  have inc {x y : ℝ} (hxy : x ≤ y) (hy : y ≤ c) : F x ≤ F y := by
    apply sub_nonneg.mp
    rw [primitive,intervalIntegral.integral_of_le hxy]
    exact setIntegral_nonneg measurableSet_Ioc fun t ht => hs.1 t (ht.2.trans hy)
  have dec {x y : ℝ} (hxy : x ≤ y) (hx : c ≤ x) : F y ≤ F x := by
    apply sub_nonpos.mp
    rw [primitive,intervalIntegral.integral_of_le hxy]
    exact setIntegral_nonpos measurableSet_Ioc fun t ht => hs.2 t (hx.trans_lt ht.1)
  have hg (x : ℝ) : g x=(1/2:ℝ)*(F (x+1)-F (x-1)) := by
    rw [primitive]; exact box_integral hf x
  have hleft {x : ℝ} (hx : x ≤ c-1) : 0 ≤ g x := by
    rw [hg]; exact mul_nonneg (by norm_num) (sub_nonneg.mpr (inc (by linarith) (by linarith)))
  have hright {x : ℝ} (hx : c+1 ≤ x) : g x ≤ 0 := by
    rw [hg]; exact mul_nonpos_of_nonneg_of_nonpos (by norm_num) (sub_nonpos.mpr (dec (by linarith) (by linarith)))
  have hant : AntitoneOn g (Icc (c-1) (c+1)) := by
    intro x hx y hy hxy
    rw [hg,hg]
    exact mul_le_mul_of_nonneg_left (sub_le_sub (dec (by linarith) (by linarith only [hx.1]))
      (inc (by linarith) (by linarith only [hy.2]))) (by norm_num)
  have hcont : Continuous g := continuous_unif_convolution one_pos hf
  obtain ⟨d,hd,hzero⟩ := intermediate_value_Icc' (show c-1 ≤ c+1 by linarith) hcont.continuousOn
    (show (0:ℝ) ∈ Icc (g (c+1)) (g (c-1)) from ⟨hright le_rfl,hleft le_rfl⟩)
  refine ⟨d,fun x hx => ?_,fun x hx => ?_⟩
  · by_cases h : x ≤ c-1
    · exact hleft h
    exact hzero ▸ hant ⟨le_of_not_ge h,hx.trans hd.2⟩ hd hx
  · by_cases h : c+1 ≤ x
    · exact hright h
    exact hzero ▸ hant hd ⟨hd.1.trans hx.le,le_of_not_ge h⟩ hx.le

private def boxDifference (b : ℝ) (j : ℕ) (x : ℝ) := 2*upow 1 j x-upow 1 j (x-b)

private theorem boxDifference_step (b : ℝ) (j : ℕ) :
    boxDifference b (j+1) = unif 1 ⋆ boxDifference b j := by
  let f := upow 1 j
  have hf : Integrable f := integrable_upow 1 j
  have hd : Integrable (boxDifference b j) := (hf.const_mul 2).sub (hf.comp_sub_right b)
  funext x
  change 2*(unif 1 ⋆ f) x-(unif 1 ⋆ f) (x-b)=(unif 1 ⋆ boxDifference b j) x
  rw [box_integral hf,box_integral hf,box_integral hd]
  unfold boxDifference
  rw [intervalIntegral.integral_sub (hf.const_mul 2).intervalIntegrable (hf.comp_sub_right b).intervalIntegrable,
    intervalIntegral.integral_const_mul,intervalIntegral.integral_comp_sub_right]
  rw [show x-1-b=x-b-1 by ring,show x+1-b=x-b+1 by ring]
  dsimp only [f]
  ring

private theorem boxDifference_separates {b : ℝ} (hb : 0 ≤ b) (j : ℕ) : ∃ c, separatedAt (boxDifference b j) c := by
  induction j with
  | zero =>
    refine ⟨1,fun x hx => ?_,fun x hx => ?_⟩
    · change 0 ≤ 2*unif 1 x-unif 1 (x-b)
      by_cases hm : x ∈ Icc (-1:ℝ) 1
      · unfold unif
        rw [indicator_of_mem hm]
        by_cases he : x-b ∈ Icc (-1:ℝ) 1 <;> (simp [he]; norm_num)
      have hn : x < -1 := lt_of_not_ge fun h => hm ⟨h,hx⟩
      have he : x-b ∉ Icc (-1:ℝ) 1 := fun h => by linarith only [hn,hb,h.1]
      simp [unif,hm,he]
    · have hm : x ∉ Icc (-1:ℝ) 1 := fun h => hx.not_ge h.2
      change 2*unif 1 x-unif 1 (x-b) ≤ 0
      rw [show unif 1 x=0 from indicator_of_notMem hm _]
      linarith only [unif_nonneg one_pos (x-b)]
  | succ j ih =>
    obtain ⟨c,hc⟩ := ih
    rw [boxDifference_step]
    exact box_separates (((integrable_upow 1 j).const_mul 2).sub ((integrable_upow 1 j).comp_sub_right b)) hc

/-- The two translated eight-box splines change sign in a single direction. -/
theorem squareLogProfile_has_prime_cut : ∃ c : ℝ,
    (∀ t ≤ c, 0 ≤ squareLogProfile t) ∧ ∀ t, c < t → squareLogProfile t ≤ 0 := by
  obtain ⟨c,h⟩ := boxDifference_separates (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 4)) 7
  refine ⟨c,?_⟩
  simpa only [separatedAt,boxDifference,squareLogProfile,splineAutoCorr_eq_eight_boxes] using h

private abbrev lags (n : ℕ) := ordinaryPrimeLags (3*windowEnd ((2*n+1)^2+1))
private abbrev price (n : ℕ) := ordinaryPrimeGenerator (n • successorSquareTriple n)

/-- All misplaced numerator and denominator factors together cost at most
quadratic log size at one fixed prime cutoff times the conductor square. -/
theorem square_prime_cut_misplaced_mass : ∃ c C : ℝ, 0 ≤ C ∧ ∀ {n : ℕ}, 0 < n →
    (∑ p ∈ lags n, (if (p:ℝ) ≤ Real.exp c*(n:ℝ)^2 then max (-(deningerRatExp (price n) p:ℝ)) 0
      else max (deningerRatExp (price n) p:ℝ) 0)*vonMangoldt p) ≤ C*(n:ℝ)^2 := by
  obtain ⟨c,hpos,hneg⟩ := squareLogProfile_has_prime_cut
  obtain ⟨C,hC,hrow⟩ := diagonal_prime_exponent_profile_error
  refine ⟨c,C,hC,fun {n} hn => ?_⟩
  apply le_trans _ (hrow hn)
  refine Finset.sum_le_sum fun p hp => mul_le_mul_of_nonneg_right ?_ vonMangoldt_nonneg
  have hp' := (Finset.mem_filter.mp hp).2.pos
  have hn' : 0 < (n:ℝ) := Nat.cast_pos.mpr hn
  let y := (p:ℝ)/(n:ℝ)^2
  have hy : 0 < y := div_pos (Nat.cast_pos.mpr hp') (sq_pos_of_pos hn')
  have hs := Real.sqrt_pos.mpr hy
  let e : ℝ := deningerRatExp (price n) p
  let f := diagonalPrimeProfile n p
  have he : f=2*(n:ℝ)*(squareLogProfile (Real.log y)/Real.sqrt y) := diagonalPrimeProfile_eq_dilate hn hp'
  by_cases h : (p:ℝ) ≤ Real.exp c*(n:ℝ)^2
  · rw [if_pos h]
    have hl := (Real.log_le_iff_le_exp hy).mpr ((div_le_iff₀ (sq_pos_of_pos hn')).mpr h)
    have hf : 0 ≤ f := by
      rw [he]
      exact mul_nonneg (mul_nonneg two_pos.le hn'.le) (div_nonneg (hpos _ hl) hs.le)
    change max (-e) 0 ≤ |e-f|
    exact max_le (by linarith only [neg_abs_le (e-f),hf]) (abs_nonneg _)
  · rw [if_neg h]
    have hl := (Real.lt_log_iff_exp_lt hy).mpr ((lt_div_iff₀ (sq_pos_of_pos hn')).mpr (lt_of_not_ge h))
    have hf : f ≤ 0 := by
      rw [he]
      exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg two_pos.le hn'.le)
        (div_nonpos_of_nonpos_of_nonneg (hneg _ hl) hs.le)
    change max e 0 ≤ |e-f|
    exact max_le (by linarith only [le_abs_self (e-f),hf]) (abs_nonneg _)

private def positiveProfile (x : ℝ) := max (squareLogProfile x) 0

private theorem numerator_log_sum (n : ℕ) :
    Real.log (price n).num.natAbs = ∑ p ∈ lags n, max (deningerRatExp (price n) p:ℝ) 0*vonMangoldt p := by
  rw [ordinaryPrimeGenerator_num,log_ordinaryPrimeModulus]
  apply Finset.sum_congr rfl
  intro p hp
  rw [ordinaryPrimeGenerator_exponent,if_pos hp,← Int.floor_toNat]
  generalize ⌊contactMultiplicity _ _ _ p⌋ = z
  rcases le_or_gt 0 z with h | h
  · rw [max_eq_left (by exact_mod_cast h),← Int.cast_natCast,Int.toNat_of_nonneg h]
  · rw [max_eq_right (by exact_mod_cast h.le),Int.toNat_of_nonpos h.le]
    simp

/-- Splitting the signed logarithmic prime sum at any cutoff undercounts
both reduced logarithms by exactly the same misplaced mass. -/
theorem square_prime_cut_log_errors (n : ℕ) (T : ℝ) :
    let e := fun p => (deningerRatExp (price n) p:ℝ)
    let E := ∑ p ∈ lags n, (if (p:ℝ) ≤ T then max (-e p) 0 else max (e p) 0)*vonMangoldt p
    Real.log (price n).num.natAbs - (∑ p ∈ lags n, if (p:ℝ) ≤ T then e p*vonMangoldt p else 0) = E ∧
    Real.log (price n).den + (∑ p ∈ lags n, if (p:ℝ) ≤ T then 0 else e p*vonMangoldt p) = E := by
  dsimp only
  have hprice : Real.log (price n:ℝ) =
      ∑ p ∈ lags n, (deningerRatExp (price n) p:ℝ)*vonMangoldt p := by
    rw [log_ordinaryPrimeGenerator]
    refine Finset.sum_congr rfl fun p hp => ?_
    have he := ordinaryPrimeGenerator_exponent (n • successorSquareTriple n) p
    change deningerRatExp (price n) p = if p ∈ lags n then _ else 0 at he
    rw [if_pos hp] at he
    rw [he]
  have hnum := numerator_log_sum n
  have hden := log_ordinaryPrimeGenerator_den (n • successorSquareTriple n)
  rw [← ordinaryPrimeGenerator_num] at hden
  change Real.log (price n).den = Real.log (price n).num.natAbs-Real.log (price n:ℝ) at hden
  rw [hprice,hnum] at hden
  have hp (x : ℝ) : max x 0 - x = max (-x) 0 := by
    rcases le_total 0 x with h | h
    · simp [max_eq_left h,max_eq_right (neg_nonpos.mpr h)]
    · simp [max_eq_right h,max_eq_left (neg_nonneg.mpr h)]
  constructor
  · rw [hnum,← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    split_ifs <;> simp only [← sub_mul,hp,sub_zero]
  · rw [hden,← Finset.sum_sub_distrib,← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    split_ifs
    · rw [add_zero,← sub_mul,hp]
    · exact sub_add_cancel _ _

private theorem positive_profile_limit :
    Tendsto (fun n : ℕ => (∑ p ∈ lags n, max (diagonalPrimeProfile n p) 0*vonMangoldt p)/(n:ℝ)^3)
      atTop (𝓝 (2*∫ u : ℝ, positiveProfile u*Real.exp (u/2))) := by
  have hH : HasCompactSupport splineAutoCorr := by
    rw [show splineAutoCorr=upow 1 7 from funext splineAutoCorr_eq_eight_boxes]
    exact hasCompactSupport_upow 1 7
  have hF : HasCompactSupport squareLogProfile := hH.mul_left.sub (hH.comp_homeomorph (Homeomorph.subRight (Real.log 4)))
  have hc : Continuous squareLogProfile := (continuous_const.mul continuous_splineAutoCorr).sub
    (continuous_splineAutoCorr.comp (continuous_id.sub continuous_const))
  let g := fun u : ℝ => if 0 ≤ squareLogProfile u then (1:ℝ) else 0
  have hg (u : ℝ) : g u*squareLogProfile u=positiveProfile u := by
    dsimp only [g,positiveProfile]
    split_ifs with h
    · rw [one_mul,max_eq_left h]
    · rw [zero_mul,max_eq_right (le_of_not_ge h)]
  have hpos : HasCompactSupport positiveProfile := by
    rw [show positiveProfile=(fun u => g u*squareLogProfile u) from (funext hg).symm]
    exact hF.mul_left
  have hpnt := tendsto_ordinary_prime_log_test (show Continuous positiveProfile from hc.max continuous_const) hpos
  have ht := (tendsto_pow_atTop (α := ℝ) two_ne_zero).comp tendsto_natCast_atTop_atTop
  refine ((hpnt.comp ht).const_mul 2).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn' : 0 < (n:ℝ) := Nat.cast_pos.mpr hn
  let F := fun p : ℕ => Real.log p*(positiveProfile (Real.log ((p:ℝ)/(n:ℝ)^2))/Real.sqrt ((p:ℝ)/(n:ℝ)^2))
  have hw : (∑' p : Nat.Primes, F p.val)=∑ p ∈ lags n, F p := by
    simpa only [F,hg] using diagonal_prime_test_window hn g
  change 2*((∑' p : Nat.Primes, F p.val)/(n:ℝ)^2)=_
  have he : (∑ p ∈ lags n, max (diagonalPrimeProfile n p) 0*vonMangoldt p)=
      (2*(n:ℝ))*(∑ p ∈ lags n, F p) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p h => ?_
    have hp := (Finset.mem_filter.mp h).2
    rw [vonMangoldt_apply_prime hp,diagonalPrimeProfile_eq_dilate hn hp.pos]
    let y := (p:ℝ)/(n:ℝ)^2
    have hy : 0 < y := div_pos (Nat.cast_pos.mpr hp.pos) (sq_pos_of_pos hn')
    dsimp only [F,positiveProfile]
    change max (2*(n:ℝ)*(squareLogProfile (Real.log y)/Real.sqrt y)) 0*Real.log p=
      2*(n:ℝ)*(Real.log p*(max (squareLogProfile (Real.log y)) 0/Real.sqrt y))
    by_cases hz : 0 ≤ squareLogProfile (Real.log y)
    · rw [max_eq_left hz,max_eq_left (mul_nonneg (by positivity) (div_nonneg hz (Real.sqrt_nonneg y)))]
      ring
    · rw [max_eq_right (le_of_not_ge hz),max_eq_right (mul_nonpos_of_nonneg_of_nonpos (by positivity)
        (div_nonpos_of_nonpos_of_nonneg (le_of_not_ge hz) (Real.sqrt_nonneg y)))]
      simp
  rw [hw,he]; field_simp

private theorem cut_integral {c : ℝ} (hc : separatedAt squareLogProfile c) :
    (∫ u : ℝ, positiveProfile u*Real.exp (u/2))=
      2*∫ u in c-Real.log 4..c, splineAutoCorr u*Real.exp (u/2) := by
  let b := Real.log 4
  let D := fun u : ℝ => splineAutoCorr u*Real.exp (u/2)
  have kH : HasCompactSupport splineAutoCorr := by
    rw [show splineAutoCorr=upow 1 7 from funext splineAutoCorr_eq_eight_boxes]
    exact hasCompactSupport_upow 1 7
  have hD : Integrable D := (continuous_splineAutoCorr.mul (by fun_prop)).integrable_of_hasCompactSupport kH.mul_right
  have hb : Real.exp (b/2)=2 := by
    dsimp only [b]
    rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow]
    convert Real.exp_log (by norm_num : (0:ℝ) < 2) using 2 <;> ring
  have hin : (fun u : ℝ => positiveProfile u*Real.exp (u/2))=
      fun u => 2*((Iic c).indicator D u-(Iic (c-b)).indicator D (u-b)) := by
    funext u
    by_cases hu : u ≤ c
    · rw [indicator_of_mem (show u∈Iic c from hu),indicator_of_mem (show u-b∈Iic (c-b) from sub_le_sub_right hu b)]
      have hs : Real.exp (u/2)=Real.exp ((u-b)/2)*2 := by
        calc _ = Real.exp ((u-b)/2+b/2) := congrArg Real.exp (by ring)
          _ = _ := by rw [Real.exp_add,hb]
      dsimp only [positiveProfile]
      rw [max_eq_left (hc.1 u hu)]
      change (2*splineAutoCorr u-splineAutoCorr (u-b))*Real.exp (u/2)=
        2*(splineAutoCorr u*Real.exp (u/2)-splineAutoCorr (u-b)*Real.exp ((u-b)/2))
      rw [hs]; ring
    · have hx : u-b∉Iic (c-b) := fun h => hu ((sub_le_sub_iff_right b).mp h)
      rw [indicator_of_notMem (show u∉Iic c from hu),indicator_of_notMem hx]
      simp only [positiveProfile,max_eq_right (hc.2 u (lt_of_not_ge hu)),zero_mul,sub_self,mul_zero]
  rw [hin,integral_const_mul,integral_sub (hD.indicator measurableSet_Iic) ((hD.indicator measurableSet_Iic).comp_sub_right b),
    integral_sub_right_eq_self,integral_indicator measurableSet_Iic,integral_indicator measurableSet_Iic,
    intervalIntegral.integral_Iic_sub_Iic hD.integrableOn hD.integrableOn]

/-- Both reduced logarithms have the same cubic leading constant, equal
to four times the positive autocorrelation mass in one translating interval. -/
theorem square_products_at_prime_cut : ∃ c : ℝ,
    ((∀ t ≤ c, 0 ≤ squareLogProfile t) ∧ ∀ t, c < t → squareLogProfile t ≤ 0) ∧
    let K := 4*∫ t in c-Real.log 4..c, splineAutoCorr t*Real.exp (t/2)
    Tendsto (fun n : ℕ => Real.log (price n).num.natAbs/(n:ℝ)^3) atTop (𝓝 K) ∧
    Tendsto (fun n : ℕ => Real.log (price n).den/(n:ℝ)^3) atTop (𝓝 K) := by
  obtain ⟨c,hc⟩ := squareLogProfile_has_prime_cut
  obtain ⟨C,_,hrow⟩ := diagonal_prime_exponent_profile_error
  let P := fun n : ℕ => ∑ p ∈ lags n, max (diagonalPrimeProfile n p) 0*vonMangoldt p
  have herr : Tendsto (fun n : ℕ => (Real.log (price n).num.natAbs-P n)/(n:ℝ)^3) atTop (𝓝 0) := by
    have h : Tendsto (fun n : ℕ => C/(n:ℝ)) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    apply squeeze_zero_norm' _ h
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : 0 < (n:ℝ) := Nat.cast_pos.mpr hn
    have he : |Real.log (price n).num.natAbs-P n| ≤ C*(n:ℝ)^2 := by
      rw [numerator_log_sum]
      dsimp only [P]
      rw [← Finset.sum_sub_distrib]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun p _ => ?_).trans (hrow hn))
      rw [← sub_mul,abs_mul,abs_of_nonneg vonMangoldt_nonneg]
      exact mul_le_mul_of_nonneg_right (abs_max_sub_max_le_abs _ _ _) vonMangoldt_nonneg
    rw [Real.norm_eq_abs,abs_div,abs_of_pos (pow_pos hn' 3)]
    exact (div_le_div_of_nonneg_right he (pow_nonneg hn'.le _)).trans_eq (by field_simp)
  have hU := positive_profile_limit.add herr
  rw [add_zero,cut_integral hc,show ∀ a : ℝ, 2*(2*a)=4*a from fun a => by ring] at hU
  have hU' : Tendsto (fun n : ℕ => Real.log (price n).num.natAbs/(n:ℝ)^3) atTop
      (𝓝 (4*∫ t in c-Real.log 4..c, splineAutoCorr t*Real.exp (t/2))) := hU.congr fun n => by
    change P n/(n:ℝ)^3+(Real.log (price n).num.natAbs-P n)/(n:ℝ)^3=_
    rw [← add_div]
    ring
  have hz : Tendsto (fun n : ℕ => Real.log (price n:ℝ)/(n:ℝ)^3) atTop (𝓝 0) := by
    simpa only [pow_zero,one_mul] using diagonal_log_negligible_at_every_logarithmic_order 0
  refine ⟨c,hc,hU',?_⟩
  have hV := hU'.sub hz
  rw [sub_zero] at hV
  exact hV.congr fun n => by
    rw [← sub_div,log_ordinaryPrimeGenerator_den,← ordinaryPrimeGenerator_num]

end GaloisForLFunctions.CountingHolography.Sections
