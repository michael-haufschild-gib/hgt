import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheCubicCorrectionOfTheCompositeMidpoint
import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.ThePrimeMidpointInTwoAdjacentGcdHorizons

/-!
# Half the zero abscissa in the composite midpoint remainder

Subtract the prime midpoint and the explicit square and cube biases from
the centered composite price. Its one-sided power threshold is half the
zeta zero abscissa. Midpoint inversion bounds the real prefix. Testing
at squares then bounds the ordinary prime surplus after absorbing the
smaller cube error. At the exact quarter power this would contradict
Littlewood's positive excursions.
-/

noncomputable section
open Finset Filter
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

private theorem corrected_profile_abs {t : ℝ} (ht : 1/4<t) {M : ℝ} (hM : 0≤M)
    (hθ : ∀ y : ℝ, 1≤y → |Chebyshev.theta y-y|≤M*y^(2*t)) :
    ∃ K : ℝ, 0≤K ∧ ∀ x : ℝ, 1≤x → |correctedProperPrefix x|≤K*x^t := by
  obtain ⟨C,hC,he⟩ := corrected_prefix_prime_errors ht.le
  have ht₀ := (by norm_num : (0:ℝ)<1/4).trans ht
  refine ⟨C+5*M,by positivity,fun x hx => ?_⟩
  have hx₀ := zero_le_one.trans hx
  have hrow (a : ℝ) (ha : 0≤a) (ha' : a≤1/2) :
      |Chebyshev.theta (x^a)-x^a|≤M*x^t := by
    have hh := hθ (x^a) (Real.one_le_rpow hx ha)
    rw [←Real.rpow_mul hx₀] at hh
    have hab := mul_le_mul_of_nonneg_right ha' (mul_nonneg (by norm_num : (0:ℝ)≤2) ht₀.le)
    exact hh.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx
      (by linarith only [hab] : a*(2*t)≤t)) hM)
  have hs := abs_le.mp (hrow (1/2) (by norm_num) le_rfl)
  have hc := abs_le.mp (hrow (1/3) (by norm_num) (by norm_num))
  have hp := abs_le.mp (he x hx)
  rw [abs_le]
  constructor <;> linarith only [hs.1,hs.2,hc.1,hc.2,hp.1,hp.2]

private theorem initial_corrected_profile :
    ∃ C : ℝ, ∀ x : ℝ, 0<x → correctedProperPrefix x≤C*x^(1/2:ℝ) := by
  have hl := Real.log_nonneg (by norm_num : (1:ℝ)≤4)
  have hθ (y : ℝ) (hy : 1≤y) : |Chebyshev.theta y-y|≤(Real.log 4+1)*y^(2*(1/2:ℝ)) := by
    rw [show 2*(1/2:ℝ)=1 by norm_num,Real.rpow_one,abs_le]
    have hpos := zero_le_one.trans hy
    have hh := Chebyshev.theta_le_log4_mul_x hpos
    have hp := Chebyshev.theta_nonneg y
    have hm := mul_nonneg hl hpos
    constructor <;> linarith only [hh,hp,hm,hpos]
  obtain ⟨C,hC,hu⟩ := corrected_profile_abs (by norm_num : (1/4:ℝ)<1/2) (by positivity) hθ
  refine ⟨C,fun x hx => ?_⟩
  by_cases h : 1≤x
  · exact (le_abs_self _).trans (hu x h)
  · have he : fullLogProperPrefix 1 x=0 := by simp [fullLogProperPrefix,Nat.floor_eq_zero.mpr (lt_of_not_ge h)]
    rw [correctedProperPrefix,he]
    have h₂ := Real.rpow_nonneg hx.le (1/2:ℝ)
    have h₃ := Real.rpow_nonneg hx.le (1/3:ℝ)
    linarith only [h₂,h₃,mul_nonneg hC h₂]

/-- One-sided integer control on the corrected composite price bounds
the entire real corrected prefix at the same exponent. -/
theorem corrected_prefix_from_integer_composites {t : ℝ} (ht : 1/4≤t) (ht₁ : t<1)
    (h : ∃ A : ℝ, ∀ n : ℕ, 1≤n → correctedBalancedCompositePrice n≤A*(n:ℝ)^t) :
    ∃ K : ℝ, ∀ x : ℝ, 0<x → correctedProperPrefix x≤K*x^t := by
  obtain ⟨A,hA⟩ := h
  obtain ⟨C,hC,he⟩ := corrected_composite_price_reads_the_prefix ht
  have ht₀ := (by norm_num : (0:ℝ)<1/4).trans_le ht
  apply upper_power_from_dilation_midpoint (a:=1/2) ⟨by norm_num,by norm_num⟩ ⟨ht₀,ht₁⟩ initial_corrected_profile
  refine ⟨|A|+C+4*(3:ℝ)^t/t,fun x hx => ?_⟩
  let n := ⌊x⌋₊
  have hsrc : realMidpointObservation correctedProperPrefix n ≤ (|A|+C)*(n:ℝ)^t := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · rw [hn,Nat.cast_zero,Real.zero_rpow ht₀.ne',mul_zero]
      simp only [realMidpointObservation,mul_zero]
      linarith
    · have hd := (abs_le.mp (he n hn)).1
      have hp := (hA n hn).trans (mul_le_mul_of_nonneg_right (le_abs_self A) (Real.rpow_nonneg (Nat.cast_nonneg n) _))
      linarith only [hd,hp]
  have hc := corrected_prefix_midpoint_rounding ht₀ hx
  have hm := hsrc.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg n)
    (Nat.floor_le hx.le) ht₀.le) (add_nonneg (abs_nonneg _) hC))
  change realMidpointObservation correctedProperPrefix x ≤ _
  linarith only [hc,hm]

private theorem read_from_profile_bound {t : ℝ} (ht : 1/4<t)
    (h : ∃ K : ℝ, 0≤K ∧ ∀ x : ℝ, 1≤x → |correctedProperPrefix x|≤K*x^t) :
    ∃ A : ℝ, 0≤A ∧ ∀ n : ℕ, 1≤n → |correctedBalancedCompositePrice n|≤A*(n:ℝ)^t := by
  obtain ⟨K,hK,h⟩ := h
  obtain ⟨C,hC,he⟩ := corrected_composite_price_reads_the_prefix ht.le
  have ht₀ := (by norm_num : (0:ℝ)<1/4).trans ht
  refine ⟨C+4*K*(4:ℝ)^t,by positivity,fun n hn => ?_⟩
  have hx := (Nat.one_le_cast (α:=ℝ)).mpr hn
  have hcut (k : ℝ) (hk : 1≤k) (h4 : k≤4) :
      |correctedProperPrefix (k*n)|≤K*((4:ℝ)^t*(n:ℝ)^t) := by
    have hh := h (k*n) (one_le_mul_of_one_le_of_one_le hk hx)
    rw [Real.mul_rpow (zero_le_one.trans hk) (Nat.cast_nonneg _)] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow (zero_le_one.trans hk) h4 ht₀.le) (Real.rpow_nonneg (Nat.cast_nonneg n) t)) hK)
  have h₂ := abs_le.mp (hcut 2 (by norm_num) (by norm_num))
  have h₃ := abs_le.mp (hcut 3 (by norm_num) (by norm_num))
  have h₄ := abs_le.mp (hcut 4 (by norm_num) le_rfl)
  have hv := abs_le.mp (he n hn)
  simp only [realMidpointObservation] at hv
  rw [abs_le]
  constructor <;> linarith only [hv.1,hv.2,h₂.1,h₂.2,h₃.1,h₃.2,h₄.1,h₄.2]

private theorem zero_sup_le_abscissa :
    _root_.RHTower.zeroReSup ≤ _root_.RHTower.zetaZeroAbscissa :=
  _root_.RHTower.zeroReSup_le_of_forall_re_le fun q =>
    _root_.RHTower.re_le_zetaZeroAbscissa (_root_.RHTower.riemannZeta_eq_zero_of_xiZeroCopy q)

/-- Above half the zero abscissa the ordinary-prime envelope bounds
both root rows and hence both signs of the corrected observation. -/
theorem absolute_composite_bound_above_half_abscissa {t : ℝ} (h : _root_.RHTower.zetaZeroAbscissa<2*t) :
    ∃ A : ℝ, 0≤A ∧ ∀ n : ℕ, 1≤n → |correctedBalancedCompositePrice n|≤A*(n:ℝ)^t := by
  have ht : 1/4<t := by linarith only [h,_root_.RHTower.half_le_zetaZeroAbscissa]
  obtain ⟨M,hM,hθ⟩ := theta_power_envelope_of_zero_sup (zero_sup_le_abscissa.trans_lt h) (by linarith only [ht])
  exact read_from_profile_bound ht (corrected_profile_abs ht hM hθ)

/-- At square arguments the cube row costs the same power as the
assumed upper bound whenever its ordinary error exponent is below 3t. -/
private theorem ordinary_upper_from_composite {t : ℝ} (ht : 1/4≤t) (ht₁ : t<1)
    (hW : _root_.RHTower.zeroReSup<3*t)
    (h : ∃ A : ℝ, ∀ n : ℕ, 1≤n → correctedBalancedCompositePrice n≤A*(n:ℝ)^t) :
    ∃ B : ℝ, ∀ y : ℝ, 1≤y → Chebyshev.theta y-y≤B*y^(2*t) := by
  obtain ⟨M,_,hθ⟩ := theta_power_envelope_of_zero_sup hW (by linarith only [ht])
  obtain ⟨K,hK⟩ := corrected_prefix_from_integer_composites ht ht₁ h
  obtain ⟨C,_,hP⟩ := corrected_prefix_prime_errors ht
  refine ⟨(K+C+3*M)/2,fun y hy => ?_⟩
  have hy₀ := zero_lt_one.trans_le hy
  let x := y^(2:ℝ)
  have hx : 1≤x := Real.one_le_rpow hy (by norm_num)
  have hpow (a : ℝ) : x^a=y^(2*a) := (Real.rpow_mul hy₀.le _ _).symm
  have hs : x^(1/2:ℝ)=y := by rw [hpow]; norm_num
  have hc : (x^(1/3:ℝ))^(3*t)=y^(2*t) := by
    rw [←Real.rpow_mul (zero_le_one.trans hx),hpow]
    congr 1
    ring
  have he := (abs_le.mp (hθ (x^(1/3:ℝ)) (Real.one_le_rpow hx (by norm_num)))).1
  rw [hc] at he
  have hp := (abs_le.mp (hP x hx)).1
  have hu := hK x (zero_lt_one.trans_le hx)
  rw [hs,hpow t] at hp
  rw [hpow t] at hu
  linarith only [he,hp,hu]

/-- The square root exposes the zero abscissa at half its ordinary
exponent. The cube row is smaller at every separating exponent chosen
strictly above one third of the abscissa. -/
theorem corrected_composite_upper_spectrum_iff {b : ℝ} (hb : 1/4≤b) :
    (∀ t : ℝ, b<t → t<1/2 → ∃ A : ℝ, ∀ n : ℕ, 1≤n → correctedBalancedCompositePrice n≤A*(n:ℝ)^t) ↔
      _root_.RHTower.zetaZeroAbscissa≤2*b := by
  constructor
  · intro h
    by_contra! bad
    let W := _root_.RHTower.zetaZeroAbscissa
    have hW : 0<W := by dsimp only [W]; linarith only [hb,bad]
    have hg : max b (W/3)<W/2 := max_lt (by dsimp only [W]; linarith only [bad]) (by linarith only [hW])
    obtain ⟨t,ht,htW⟩ := exists_between hg
    have hbt := (le_max_left _ _).trans_lt ht
    have h3t := (le_max_right _ _).trans_lt ht
    have ht₁ : t<1/2 := htW.trans_le (div_le_div_of_nonneg_right _root_.RHTower.zetaZeroAbscissa_le_one (by norm_num))
    have ht₀ := hb.trans_lt hbt
    have hθsup : _root_.RHTower.zeroReSup<3*t := zero_sup_le_abscissa.trans_lt (by change W<3*t; linarith only [h3t])
    have hw := zero_abscissa_of_ordinary_prime_surplus (b:=2*t) (by linarith only [ht₀])
      (ordinary_upper_from_composite ht₀.le (ht₁.trans (by norm_num)) hθsup (h t hbt ht₁))
    exact htW.not_ge (by change W≤2*t at hw; linarith only [hw])
  · intro hs t hbt _
    obtain ⟨A,_,hA⟩ := absolute_composite_bound_above_half_abscissa (t:=t) (hs.trans_lt (by linarith only [hbt]))
    exact ⟨A,fun n hn => (le_abs_self _).trans (hA n hn)⟩

/-- Quarter-power upper control on the corrected balanced-composite
remainder characterizes the Riemann hypothesis. -/
theorem riemannHypothesis_iff_quarter_power_composite_remainder :
    RiemannHypothesis ↔ ∀ t : ℝ, 1/4<t → t<1/2 →
      ∃ A : ℝ, ∀ n : ℕ, 1≤n → correctedBalancedCompositePrice n≤A*(n:ℝ)^t := by
  rw [corrected_composite_upper_spectrum_iff le_rfl,show 2*(1/4:ℝ)=1/2 by norm_num]
  exact riemannHypothesis_iff_prime_midpoint.trans (prime_midpoint_upper_spectrum_iff le_rfl)

/-- Every constant multiple of the exact quarter power is exceeded
infinitely often. Such an upper bound would first force RH, then bound
the ordinary prime surplus by a constant times the square root, contrary
to the positive Littlewood excursions. -/
theorem unbounded_quarter_power_composite_surplus (A : ℝ) :
    ∃ᶠ n : ℕ in Filter.atTop, A*(n:ℝ)^(1/4:ℝ)<correctedBalancedCompositePrice n := by
  have impossible : ¬∃ U : ℝ, ∀ n : ℕ, 1≤n → correctedBalancedCompositePrice n≤U*(n:ℝ)^(1/4:ℝ) := by
    rintro ⟨U,hU⟩
    have hW := (corrected_composite_upper_spectrum_iff (b:=1/4) le_rfl).mp (by
      intro t ht _
      refine ⟨|U|,fun n hn => (hU n hn).trans ?_⟩
      exact mul_le_mul (le_abs_self U) (Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.mpr hn) ht.le)
        (Real.rpow_nonneg (Nat.cast_nonneg n) _) (abs_nonneg U))
    have he : _root_.RHTower.zeroReSup<3*(1/4:ℝ) :=
      zero_sup_le_abscissa.trans_lt (hW.trans_lt (by norm_num))
    obtain ⟨B,hB⟩ := ordinary_upper_from_composite (t:=1/4) le_rfl (by norm_num) he ⟨U,hU⟩
    let c := _root_.RHTower.littlewoodConst/28
    have hc : 0<c := div_pos _root_.RHTower.littlewoodConst_pos (by norm_num)
    have hl := _root_.RHTower.tendsto_logLogLog_atTop.eventually_gt_atTop (B/c)
    obtain ⟨y,hp,hy,hlog⟩ := (_root_.RHTower.chebyshevTheta_sub_omega_pm_littlewood.2.and_eventually
      ((Filter.eventually_ge_atTop (1:ℝ)).and hl)).exists
    have hu := hB y hy
    rw [show 2*(1/4:ℝ)=1/2 by norm_num,←Real.sqrt_eq_rpow] at hu
    have hpaid := mul_lt_mul_of_pos_right ((div_lt_iff₀ hc).mp hlog)
      (Real.sqrt_pos.mpr (zero_lt_one.trans_le hy))
    change c*Real.sqrt y*Real.log (Real.log (Real.log y))<Chebyshev.theta y-y at hp
    linarith only [hp,hu,hpaid]
  rw [Filter.frequently_atTop]
  intro N
  by_contra! h
  let M := ∑ j ∈ range N, |correctedBalancedCompositePrice j|
  have hM : 0≤M := sum_nonneg fun j _ => abs_nonneg _
  apply impossible
  refine ⟨M+|A|,fun n hn => ?_⟩
  have hx := (Nat.one_le_cast (α:=ℝ)).mpr hn
  by_cases hnN : n<N
  · have hh := single_le_sum (fun j (_ : j∈range N) => abs_nonneg (correctedBalancedCompositePrice j))
      (mem_range.mpr hnN)
    exact ((le_abs_self _).trans hh).trans ((le_add_of_nonneg_right (abs_nonneg A) : M≤M+|A|).trans
      (le_mul_of_one_le_right (add_nonneg hM (abs_nonneg _)) (Real.one_le_rpow hx (by norm_num))))
  · exact (h n (le_of_not_gt hnN)).trans (mul_le_mul_of_nonneg_right
      ((le_abs_self A).trans (le_add_of_nonneg_left hM)) (Real.rpow_nonneg (Nat.cast_nonneg _) _))

/-- The one-sided power threshold is exactly half the zero abscissa
for every real cutoff, including those below one quarter. -/
theorem corrected_composite_all_power_cutoffs (b : ℝ) :
    (∀ t : ℝ, b<t → t<1/2 → ∃ A : ℝ, ∀ n : ℕ, 1≤n → correctedBalancedCompositePrice n≤A*(n:ℝ)^t) ↔
      _root_.RHTower.zetaZeroAbscissa≤2*b := by
  by_cases hb : 1/4≤b
  · exact corrected_composite_upper_spectrum_iff hb
  have hlow := lt_of_not_ge hb
  constructor
  · intro h
    obtain ⟨A,hA⟩ := h (1/4) hlow (by norm_num)
    obtain ⟨n,hn,he⟩ := Filter.frequently_atTop.mp (unbounded_quarter_power_composite_surplus A) 1
    exact (he.not_ge (hA n hn)).elim
  · intro h
    exfalso
    linarith only [h,hlow,_root_.RHTower.half_le_zetaZeroAbscissa]

/-- The absolute error has exactly the same threshold as its upper side.
Any zero-free strip above the tested exponent controls both signs. -/
theorem corrected_composite_absolute_power_cutoffs (b : ℝ) :
    (∀ t : ℝ, b<t → t<1/2 → ∃ A : ℝ, ∀ n : ℕ, 1≤n → |correctedBalancedCompositePrice n|≤A*(n:ℝ)^t) ↔
      _root_.RHTower.zetaZeroAbscissa≤2*b := by
  constructor
  · intro h
    apply (corrected_composite_all_power_cutoffs b).mp
    intro t hbt ht
    obtain ⟨A,hA⟩ := h t hbt ht
    exact ⟨A,fun n hn => (le_abs_self _).trans (hA n hn)⟩
  · intro h t hbt _
    obtain ⟨A,_,hA⟩ := absolute_composite_bound_above_half_abscissa (t:=t) (h.trans_lt (by linarith only [hbt]))
    exact ⟨A,hA⟩

/-- At and above the cube-root scale only the square bias needs to be
removed. In particular the exponent 5/12 tests the 5/6 zero-free strip. -/
theorem square_corrected_composite_upper_spectrum_iff {b : ℝ} (hb : 1/3≤b) :
    (∀ t : ℝ, b<t → t<1/2 → ∃ A : ℝ, ∀ n : ℕ, 1≤n → squareCenteredCompositePrice n≤A*(n:ℝ)^t) ↔
      _root_.RHTower.zetaZeroAbscissa≤2*b := by
  rw [←corrected_composite_upper_spectrum_iff ((by norm_num : (1/4:ℝ)≤1/3).trans hb)]
  let g := 3*midpointPowerGap (1/3)
  have hg : 0≤g := mul_nonneg (by norm_num) (midpointPowerGap_pos ⟨by norm_num,by norm_num⟩).le
  constructor
  · intro h t hbt hhalf
    obtain ⟨A,hA⟩ := h t hbt hhalf
    refine ⟨A,fun n hn => ?_⟩
    exact (sub_le_self _ (mul_nonneg hg (Real.rpow_nonneg (Nat.cast_nonneg n) _))).trans (hA n hn)
  · intro h t hbt hhalf
    obtain ⟨A,hA⟩ := h t hbt hhalf
    refine ⟨A+g,fun n hn => ?_⟩
    have he := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.mpr hn)
      (hb.trans hbt.le)) hg
    have hp := hA n hn
    change squareCenteredCompositePrice n-g*(n:ℝ)^(1/3:ℝ)≤A*(n:ℝ)^t at hp
    linarith only [hp,he]

/-- If only the square bias is removed, the upper threshold is the larger
of one third and half the zero abscissa. Positive excursions of the
twice-corrected remainder prevent cancellation of the retained cube. -/
theorem square_corrected_composite_all_power_cutoffs (b : ℝ) :
    (∀ t : ℝ, b<t → t<1/2 → ∃ A : ℝ, ∀ n : ℕ, 1≤n → squareCenteredCompositePrice n≤A*(n:ℝ)^t) ↔
      1/3≤b ∧ _root_.RHTower.zetaZeroAbscissa≤2*b := by
  constructor
  · intro h
    have hb : 1/3≤b := by
      by_contra! hlow
      obtain ⟨t,hbt,ht⟩ := exists_between hlow
      obtain ⟨A,hA⟩ := h t hbt (ht.trans (by norm_num))
      let g := 3*midpointPowerGap (1/3)
      have hg : 0<g := mul_pos (by norm_num) (midpointPowerGap_pos ⟨by norm_num,by norm_num⟩)
      have hlim := ((tendsto_rpow_neg_atTop (sub_pos.mpr ht)).comp
        (tendsto_natCast_atTop_atTop (R:=ℝ))).const_mul A
      rw [mul_zero] at hlim
      obtain ⟨n,hp,hn,hs⟩ := ((unbounded_quarter_power_composite_surplus 0).and_eventually
        ((eventually_ge_atTop 1).and (hlim.eventually_lt_const hg))).exists
      have hn₀ := (Nat.cast_pos (α:=ℝ)).mpr hn
      have hsmall := mul_lt_mul_of_pos_right hs (Real.rpow_pos_of_pos hn₀ (1/3:ℝ))
      change A*(n:ℝ)^(-(1/3-t))*(n:ℝ)^(1/3:ℝ)<g*(n:ℝ)^(1/3:ℝ) at hsmall
      rw [mul_assoc,←Real.rpow_add hn₀,show -(1/3-t)+1/3=t by ring] at hsmall
      rw [zero_mul] at hp
      change 0<squareCenteredCompositePrice n-g*(n:ℝ)^(1/3:ℝ) at hp
      linarith only [hp,hsmall,hA n hn]
    exact ⟨hb,(square_corrected_composite_upper_spectrum_iff hb).mp h⟩
  · rintro ⟨hb,hW⟩
    exact (square_corrected_composite_upper_spectrum_iff hb).mpr hW

/-- The 11/3 conductor-prefix condition is equivalent to a one-sided
5/12 power threshold for the square-corrected composite remainder. -/
theorem square_corrected_composite_iff_eleven_thirds :
    (∀ t : ℝ, 5/12<t → t<1/2 → ∃ A : ℝ, ∀ n : ℕ, 1≤n → squareCenteredCompositePrice n≤A*(n:ℝ)^t) ↔
      ∃ C : ℝ, 0≤C ∧ ∀ N : ℕ, |seventeenNinthsConductorPrefix N|≤C*(N:ℝ)^(11/3:ℝ) := by
  rw [square_corrected_composite_upper_spectrum_iff (by norm_num : (1/3:ℝ)≤5/12),
    show 2*(5/12:ℝ)=5/6 by norm_num]
  exact five_sixths_iff_seventeenNinthsConductorPrefix

#print axioms corrected_prefix_from_integer_composites
#print axioms absolute_composite_bound_above_half_abscissa
#print axioms corrected_composite_upper_spectrum_iff
#print axioms riemannHypothesis_iff_quarter_power_composite_remainder
#print axioms unbounded_quarter_power_composite_surplus
#print axioms corrected_composite_all_power_cutoffs
#print axioms corrected_composite_absolute_power_cutoffs
#print axioms square_corrected_composite_all_power_cutoffs
#print axioms square_corrected_composite_iff_eleven_thirds

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
