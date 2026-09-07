import GaloisForLFunctions.RHTower.ArithmeticFiniteCutoffZeroBudget
import GaloisForLFunctions.RHTower.EulerDeletionQuarticRemainder

/-!
# A phase cone for the complete centered arithmetic tail

The nonnegative quartic primitive has positive mean and a bounded periodic fifth primitive.
Exact integration by parts gives an all-height mean error; the fourth-Bernoulli Fourier series
improves it at a linear height cutoff, retaining every signed frequency. The normalized complete
tail then has real part at least three fifths. At zeta zeros this is exactly a normalization of
the finite arithmetic residual. Together with the actual simple-critical zero budget, this
excludes exhaustive exact matching by every finite cutoff at sufficiently large heights.
The result retains controlled approximation and supplies no off-line zero exclusion.
-/

noncomputable section
open Complex MeasureTheory Set Filter Topology
namespace RHTower.DeletionMixedRefinement

/-- The zero-mean quartic's periodic primitive, with every integer endpoint fixed to zero. -/
def bernoulliFifthPrimitive (x : ℝ) : ℝ :=
  Int.fract x^5/120-Int.fract x^4/48+Int.fract x^3/72-Int.fract x/720

/-- The primitive retains a factored expression useful for uniform bounds. -/
theorem bernoulliFifthPrimitive_factor (x : ℝ) :
    bernoulliFifthPrimitive x=Int.fract x*(Int.fract x-1)*(2*Int.fract x-1)*
      (3*Int.fract x^2-3*Int.fract x-1)/720 := by
  unfold bernoulliFifthPrimitive
  ring

/-- A uniform bound for the complete periodic primitive. -/
theorem abs_bernoulliFifthPrimitive_le (x : ℝ) : |bernoulliFifthPrimitive x|≤1/720 := by
  have h0 := Int.fract_nonneg x
  have h1 := Int.fract_lt_one x
  have ha : |Int.fract x*(Int.fract x-1)|≤1/4 := by
    rw [abs_of_nonpos (mul_nonpos_of_nonneg_of_nonpos h0 (by linarith))]
    nlinarith [sq_nonneg (Int.fract x-1/2)]
  have hb : |2*Int.fract x-1|≤1 := by rw [abs_le]; constructor <;> linarith
  have hc : |3*Int.fract x^2-3*Int.fract x-1|≤7/4 := by
    rw [abs_le]
    constructor
    · nlinarith [sq_nonneg (Int.fract x-1/2)]
    · nlinarith [mul_nonneg h0 (show 0≤1-Int.fract x by linarith)]
  rw [bernoulliFifthPrimitive_factor,abs_div,abs_mul,abs_mul]
  norm_num only [abs_of_nonneg (by norm_num : (0:ℝ)≤720)]
  calc
    _ ≤ ((1/4:ℝ)*1*(7/4))/720 := by gcongr
    _ ≤ 1/720 := by norm_num

/-- Integer endpoints vanish exactly. -/
@[simp] theorem bernoulliFifthPrimitive_nat (N : ℕ) : bernoulliFifthPrimitive N=0 := by
  simp [bernoulliFifthPrimitive]

/-- The periodic primitive is continuous through every integer join. -/
theorem continuous_bernoulliFifthPrimitive : Continuous bernoulliFifthPrimitive := by
  have hc : Continuous (fun x : ℝ => x^5/120-x^4/48+x^3/72-x/720) := by fun_prop
  exact hc.continuousOn.comp_fract'' (by norm_num)

/-- The right derivative keeps the zero-mean quartic density at every join. -/
theorem bernoulliFifthPrimitive_right (x : ℝ) :
    HasDerivWithinAt bernoulliFifthPrimitive (bernoulliQuarticPrimitive x-1/720) (Ioi x) x := by
  have hf := tendsto_pure.mp (tendsto_floor_right_pure_floor x)
  have he : bernoulliFifthPrimitive =ᶠ[𝓝[≥] x]
      (fun y : ℝ => (y-(Int.floor x:ℝ))^5/120-(y-(Int.floor x:ℝ))^4/48+
        (y-(Int.floor x:ℝ))^3/72-(y-(Int.floor x:ℝ))/720) := by
    filter_upwards [hf] with y hy
    simp only [bernoulliFifthPrimitive,Int.fract,hy]
  have hi := (hasDerivAt_id x).sub_const (Int.floor x:ℝ)
  have hd : HasDerivAt
      (fun y : ℝ => (y-(Int.floor x:ℝ))^5/120-(y-(Int.floor x:ℝ))^4/48+
        (y-(Int.floor x:ℝ))^3/72-(y-(Int.floor x:ℝ))/720)
      (bernoulliQuarticPrimitive x-1/720) x := by
    convert! ((((hi.pow 5).div_const 120).sub ((hi.pow 4).div_const 48)).add
      ((hi.pow 3).div_const 72)).sub (hi.div_const 720) using 1
    simp only [bernoulliQuarticPrimitive,Int.fract]
    norm_num
    ring
  exact (hd.hasDerivWithinAt.congr_of_eventuallyEq he rfl).mono Ioi_subset_Ici_self

/-- The exact derivative is valid on both sides of every integer. -/
theorem hasDerivAt_bernoulliFifthPrimitive (x : ℝ) :
    HasDerivAt bernoulliFifthPrimitive (bernoulliQuarticPrimitive x-1/720) x := by
  have hQ : Continuous bernoulliQuarticPrimitive :=
    continuous_iff_continuousAt.mpr (fun y => (hasDerivAt_bernoulliQuarticPrimitive y).continuousAt)
  have hc : Continuous (fun y : ℝ => bernoulliQuarticPrimitive y-1/720) := hQ.sub continuous_const
  have he (y : ℝ) : (∫ z in (0:ℝ)..y, bernoulliQuarticPrimitive z-1/720)=
      bernoulliFifthPrimitive y := by
    have h := intervalIntegral.integral_eq_sub_of_hasDeriv_right
      (a := 0) (b := y) continuous_bernoulliFifthPrimitive.continuousOn
      (fun z _ => bernoulliFifthPrimitive_right z) (hc.intervalIntegrable 0 y)
    simpa [bernoulliFifthPrimitive] using h
  have hfun : bernoulliFifthPrimitive=(fun y => ∫ z in (0:ℝ)..y,
      bernoulliQuarticPrimitive z-1/720) := funext (fun y => (he y).symm)
  rw [hfun]
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 x)
    (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt

/-- The literal next arithmetic tail. -/
def fifthPrimitiveTail (N : ℕ) (s : ℂ) : ℂ :=
  ∫ x in Ioi (N:ℝ), (bernoulliFifthPrimitive x:ℂ)*(x:ℂ)^(-s-5)

/-- Absolute convergence of the retained periodic correction. -/
theorem integrable_fifthPrimitiveTail {s : ℂ} (hs : -1<s.re) {N : ℕ} (hN : 1≤N) :
    IntegrableOn (fun x : ℝ => (bernoulliFifthPrimitive x:ℂ)*(x:ℂ)^(-s-5)) (Ioi (N:ℝ)) := by
  have hNp : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hre : -s.re-5 < -1 := by linarith
  have hi := (integrableOn_Ioi_rpow_of_lt hre hNp).const_mul (1/720:ℝ)
  apply Integrable.mono hi
  · apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
    intro x hx
    apply ContinuousWithinAt.mul
    · exact (Complex.continuous_ofReal.comp continuous_bernoulliFifthPrimitive).continuousAt.continuousWithinAt
    · exact (hasDerivAt_ofReal_cpow_const (hNp.trans hx).ne' (by
        intro h; have hr := congrArg Complex.re h; norm_num at hr; linarith : -s-5≠0)).continuousAt.continuousWithinAt
  · rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with x hx
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_cpow_eq_rpow_re_of_pos (hNp.trans hx)]
    have he : (-s-5).re=-s.re-5 := by simp
    rw [he]
    simpa only [Real.norm_eq_abs,abs_mul,
      abs_of_nonneg (by norm_num : (0:ℝ)≤1/720),
      abs_of_nonneg (Real.rpow_nonneg (hNp.trans hx).le _)] using
      mul_le_mul_of_nonneg_right (abs_bernoulliFifthPrimitive_le x)
        (Real.rpow_nonneg (hNp.trans hx).le (-s.re-5))

/-- The complete correction has an explicit height-uniform absolute bound. -/
theorem norm_fifthPrimitiveTail_le {s : ℂ} (hs : -1<s.re) {N : ℕ} (hN : 1≤N) :
    ‖fifthPrimitiveTail N s‖≤(N:ℝ)^(-s.re-4)/(720*(s.re+4)) := by
  have hNp : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hre : -s.re-5 < -1 := by linarith
  have hi := (integrableOn_Ioi_rpow_of_lt hre hNp).const_mul (1/720:ℝ)
  have hb : ‖fifthPrimitiveTail N s‖≤∫ x in Ioi (N:ℝ), (1/720:ℝ)*x^(-s.re-5) := by
    apply norm_integral_le_of_norm_le hi
    rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with x hx
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_cpow_eq_rpow_re_of_pos (hNp.trans hx)]
    have he : (-s-5).re=-s.re-5 := by simp
    rw [he]
    exact mul_le_mul_of_nonneg_right (abs_bernoulliFifthPrimitive_le x)
      (Real.rpow_nonneg (hNp.trans hx).le _)
  refine hb.trans_eq ?_
  rw [integral_const_mul,integral_Ioi_rpow_of_lt hre hNp,
    show -s.re-5+1=-(s.re+4) by ring,neg_div_neg_eq]
  rw [show -(s.re+4)=-s.re-4 by ring]
  field_simp

/-- The positive quartic mean is separated with the complete next tail retained. -/
theorem quarticPrimitiveTail_eq_mean_add_fifth {s : ℂ} (hs : -1<s.re) {N : ℕ} (hN : 1≤N) :
    quarticPrimitiveTail N s=(N:ℂ)^(-s-3)/(720*(s+3))+(s+4)*fifthPrimitiveTail N s := by
  have hNp : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hre : (-s-4).re < -1 := by simp; linarith
  have hrne : -s-4≠0 := by intro h; rw [h] at hre; norm_num at hre
  have hd (x : ℝ) (hx : 0<x) : HasDerivAt (fun y : ℝ => (y:ℂ)^(-s-4))
      ((-s-4)*(x:ℂ)^(-s-5)) x := by
    simpa only [show -s-4-1=-s-5 by ring] using hasDerivAt_ofReal_cpow_const hx.ne' hrne
  have hiC := (integrableOn_Ioi_cpow_of_lt hre hNp).const_mul (1/720:ℂ)
  have hiQ := integrable_quarticPrimitiveTail hs hN
  have hi : IntegrableOn (fun x : ℝ => ((bernoulliQuarticPrimitive x-1/720:ℝ):ℂ)*
      (x:ℂ)^(-s-4)) (Ioi (N:ℝ)) := by
    have he : (fun x : ℝ => ((bernoulliQuarticPrimitive x-1/720:ℝ):ℂ)*(x:ℂ)^(-s-4))=
        (fun x : ℝ => (bernoulliQuarticPrimitive x:ℂ)*(x:ℂ)^(-s-4)-(1/720:ℂ)*(x:ℂ)^(-s-4)) := by
      funext x; push_cast; ring
    rw [he]
    exact hiQ.sub hiC
  have hip := (integrable_fifthPrimitiveTail hs hN).const_mul (-s-4)
  have hprod0 : Tendsto (fun x : ℝ => (bernoulliFifthPrimitive x:ℂ)*(x:ℂ)^(-s-4))
      (𝓝[>] (N:ℝ)) (𝓝 0) := by
    have hc := ((hasDerivAt_bernoulliFifthPrimitive (N:ℝ)).ofReal_comp.mul (hd N hNp)).continuousAt
    simpa [bernoulliFifthPrimitive_nat,Pi.mul_def] using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hprodt : Tendsto (fun x : ℝ => (bernoulliFifthPrimitive x:ℂ)*(x:ℂ)^(-s-4)) atTop (𝓝 0) := by
    have ht := tendsto_rpow_neg_atTop (by linarith : 0<s.re+4)
    rw [show -(s.re+4)=-s.re-4 by ring] at ht
    apply squeeze_zero_norm' ?_ ht
    filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_cpow_eq_rpow_re_of_pos hx]
    have he : (-s-4).re=-s.re-4 := by simp
    rw [he]
    exact mul_le_of_le_one_left (Real.rpow_nonneg hx.le _)
      ((abs_bernoulliFifthPrimitive_le x).trans (by norm_num))
  have hb := MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul
    (u := fun x : ℝ => (x:ℂ)^(-s-4))
    (u' := fun x : ℝ => (-s-4)*(x:ℂ)^(-s-5))
    (v := fun x : ℝ => (bernoulliFifthPrimitive x:ℂ))
    (v' := fun x : ℝ => ((bernoulliQuarticPrimitive x-1/720:ℝ):ℂ))
    (a := (N:ℝ)) (a' := (0:ℂ)) (b' := (0:ℂ))
    (fun x hx => hd x (hNp.trans hx))
    (fun x _ => (hasDerivAt_bernoulliFifthPrimitive x).ofReal_comp)
    (by simpa [Pi.mul_def,mul_comm] using hi)
    (by simpa [IntegrableOn,Pi.mul_def,mul_assoc,mul_left_comm,mul_comm] using hip)
    (by simpa [Pi.mul_def,mul_comm] using hprod0)
    (by simpa [Pi.mul_def,mul_comm] using hprodt)
  have hleft : (∫ x in Ioi (N:ℝ), (x:ℂ)^(-s-4)*((bernoulliQuarticPrimitive x-1/720:ℝ):ℂ))=
      quarticPrimitiveTail N s-(N:ℂ)^(-s-3)/(720*(s+3)) := by
    have he : (fun x : ℝ => (x:ℂ)^(-s-4)*((bernoulliQuarticPrimitive x-1/720:ℝ):ℂ))=
        (fun x : ℝ => (bernoulliQuarticPrimitive x:ℂ)*(x:ℂ)^(-s-4)-(1/720:ℂ)*(x:ℂ)^(-s-4)) := by
      funext x; push_cast; ring
    rw [he,integral_sub hiQ hiC,integral_const_mul,integral_Ioi_cpow_of_lt hre hNp]
    unfold quarticPrimitiveTail
    congr 1
    rw [show -s-4+1=-(s+3) by ring,neg_div_neg_eq]
    rw [show -(s+3)=-s-3 by ring]
    push_cast
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  have hright : (∫ x in Ioi (N:ℝ), ((-s-4)*(x:ℂ)^(-s-5))*(bernoulliFifthPrimitive x:ℂ))=
      (-s-4)*fifthPrimitiveTail N s := by
    rw [show (fun x : ℝ => ((-s-4)*(x:ℂ)^(-s-5))*(bernoulliFifthPrimitive x:ℂ))=
      (fun x : ℝ => (-s-4)*((bernoulliFifthPrimitive x:ℂ)*(x:ℂ)^(-s-5))) by funext x; ring,
      integral_const_mul]
    rfl
  rw [hleft,hright] at hb
  linear_combination hb

/-- The fourth Bernoulli function in explicit polynomial form. -/
theorem bernoulliFun_four_explicit (x : ℝ) : bernoulliFun 4 x=x^4-2*x^3+x^2-1/30 := by
  have h4 : bernoulli 4=(-1/30:ℚ) := by
    rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num : (4:ℕ)≠1),bernoulli'_four]
  have h3 : bernoulli 3=0 := by
    rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num : (3:ℕ)≠1),bernoulli'_three]
  simp [bernoulliFun,Polynomial.bernoulli_def,Finset.sum_range_succ,h4,h3]
  rw [Nat.choose_two_right]
  norm_num
  ring

/-- Positive coefficient mass of the fourth Bernoulli Fourier series. -/
def quarticModeWeight (k : ℤ) : ℝ := 1/(16*Real.pi^4*(k:ℝ)^4)

/-- The positive quartic's mean-minus-source expansion preserves every signed frequency. -/
theorem hasSum_quarticModeWeight_fourier (x : ℝ) :
    HasSum (fun k : ℤ => (quarticModeWeight k:ℂ)*fourier k (x : AddCircle (1:ℝ)))
      (((1/720:ℝ)-bernoulliQuarticPrimitive x:ℝ):ℂ) := by
  have hx : Int.fract x∈Icc (0:ℝ) 1 := ⟨Int.fract_nonneg x,(Int.fract_lt_one x).le⟩
  have h := (hasSum_one_div_pow_mul_fourier_mul_bernoulliFun (k := 4) (by norm_num) hx).mul_left
    (1/(16*(Real.pi:ℂ)^4))
  have hi4 : (2*(Real.pi:ℂ)*I)^4=16*(Real.pi:ℂ)^4 := by
    calc
      _ = (2*(Real.pi:ℂ))^4*(Complex.I^2)^2 := by ring
      _ = _ := by rw [Complex.I_sq]; ring
  rw [hi4] at h
  simp only [AddCircle.coe_fract,bernoulliFun_four_explicit] at h
  convert! h using 1
  · ext k
    dsimp only [quarticModeWeight]
    push_cast
    ring
  · dsimp [bernoulliQuarticPrimitive]
    push_cast
    norm_num
    field_simp
    ring

/-- The complete fourth-order coefficient mass is exactly the positive mean. -/
theorem hasSum_quarticModeWeight : HasSum quarticModeWeight (1/720) := by
  apply Complex.hasSum_ofReal.mp
  simpa [bernoulliQuarticPrimitive,fourier_coe_apply] using hasSum_quarticModeWeight_fourier 0

/-- Complete quartic Fourier term with the literal complex power. -/
def quarticFourierTerm (k : ℤ) (s : ℂ) (x : ℝ) : ℂ :=
  (quarticModeWeight k:ℂ)*(fourier k (x : AddCircle (1:ℝ))*(x:ℂ)^(-s-4))

/-- Every coefficient is nonnegative. -/
theorem quarticModeWeight_nonneg (k : ℤ) : 0≤quarticModeWeight k := by
  unfold quarticModeWeight
  positivity

/-- Exact power majorant for every quartic Fourier mode. -/
theorem norm_quarticFourierTerm (k : ℤ) (s : ℂ) {x : ℝ} (hx : 0<x) :
    ‖quarticFourierTerm k s x‖=quarticModeWeight k*x^(-s.re-4) := by
  rw [quarticFourierTerm,norm_mul,norm_mul,norm_fourier_real,
    Complex.norm_cpow_eq_rpow_re_of_pos hx,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (quarticModeWeight_nonneg k)]
  simp

/-- Each full signed mode is absolutely integrable. -/
theorem integrable_quarticFourierTerm {a : ℝ} (ha : 0<a) {s : ℂ} (hs : -1<s.re) (k : ℤ) :
    IntegrableOn (quarticFourierTerm k s) (Ioi a) := by
  have hi := (integrable_logarithmicFourierMode ha (by linarith : 1<s.re+4)
    (-s.im) (2*Real.pi*k)).const_mul (quarticModeWeight k:ℂ)
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have he := fourier_mul_cpow_eq_mode k (s+2) (ha.trans hx)
  rw [show -(s+2)-2=-s-4 by ring,
    show (s+2).re+2=s.re+4 by simp; ring,
    show (s+2).im=s.im by simp] at he
  exact congrArg (fun z : ℂ => (quarticModeWeight k:ℂ)*z) he.symm

/-- The full sum and integral commute, with the mean kept separate. -/
theorem hasSum_integral_quarticFourierTerm {a : ℝ} (ha : 0<a) {s : ℂ} (hs : -1<s.re) :
    HasSum (fun k : ℤ => ∫ x in Ioi a, quarticFourierTerm k s x)
      (∫ x in Ioi a, (((1/720:ℝ)-bernoulliQuarticPrimitive x:ℝ):ℂ)*(x:ℂ)^(-s-4)) := by
  have hsum : Summable (fun k : ℤ => ∫ x in Ioi a, ‖quarticFourierTerm k s x‖) := by
    have he (k : ℤ) : (∫ x in Ioi a, ‖quarticFourierTerm k s x‖)=
        quarticModeWeight k*(∫ x in Ioi a, x^(-s.re-4)) := by
      rw [←integral_const_mul]
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact norm_quarticFourierTerm k s (ha.trans hx)
    simp_rw [he]
    exact hasSum_quarticModeWeight.summable.mul_right _
  have h := hasSum_integral_of_summable_integral_norm (integrable_quarticFourierTerm ha hs) hsum
  convert! h using 1
  apply integral_congr_ae
  filter_upwards with x
  have hx := (hasSum_quarticModeWeight_fourier x).mul_right ((x:ℂ)^(-s-4))
  simpa only [quarticFourierTerm,mul_assoc] using hx.tsum_eq.symm

/-- The complete signed Fourier bound is uniform jointly in height and cutoff. -/
theorem norm_integral_quarticFourierTerm_le {a : ℝ} (ha : 0<a) {s : ℂ}
    (hs : -1<s.re) (ht : |s.im|≤a) (k : ℤ) :
    ‖∫ x in Ioi a, quarticFourierTerm k s x‖≤quarticModeWeight k*(4*a^(-s.re-4)/5) := by
  by_cases hk : k=0
  · simp [hk,quarticFourierTerm,quarticModeWeight]
  have he : (∫ x in Ioi a, quarticFourierTerm k s x)=
      (quarticModeWeight k:ℂ)*∫ x in Ioi a, logarithmicFourierMode (s.re+4) (-s.im) (2*Real.pi*k) x := by
    rw [←integral_const_mul]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have he := fourier_mul_cpow_eq_mode k (s+2) (ha.trans hx)
    rw [show -(s+2)-2=-s-4 by ring,
      show (s+2).re+2=s.re+4 by simp; ring,
      show (s+2).im=s.im by simp] at he
    exact congrArg (fun z : ℂ => (quarticModeWeight k:ℂ)*z) he
  have hk1 : (1:ℝ)≤|(k:ℝ)| := by exact_mod_cast Int.one_le_abs hk
  have hω : 6≤|2*Real.pi*(k:ℝ)| := by
    rw [abs_mul,abs_of_pos (by positivity : (0:ℝ)<2*Real.pi)]
    nlinarith [Real.pi_gt_three]
  have hb := norm_integral_Ioi_logarithmicFourierMode_le_abs (t := -s.im) ha
    (by linarith : 1<s.re+4) hω (by simpa using ht)
  rw [he,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (quarticModeWeight_nonneg k)]
  simpa only [neg_add_rev,sub_eq_add_neg,add_comm] using
    mul_le_mul_of_nonneg_left hb (quarticModeWeight_nonneg k)

/-- Signed Fourier cancellation improves the full quartic mean error at a linear height cutoff. -/
theorem norm_quarticPrimitiveTail_sub_mean_le_linear {s : ℂ} (hs : -1<s.re)
    {N : ℕ} (hN : 1≤N) (ht : |s.im|≤N) :
    ‖quarticPrimitiveTail N s-(N:ℂ)^(-s-3)/(720*(s+3))‖≤(N:ℝ)^(-s.re-4)/900 := by
  have hNp : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hsbound := (hasSum_integral_quarticFourierTerm hNp hs).norm_le_of_bounded
    (hasSum_quarticModeWeight.mul_right (4*(N:ℝ)^(-s.re-4)/5))
    (norm_integral_quarticFourierTerm_le hNp hs ht)
  have hre : (-s-4).re < -1 := by simp; linarith
  have hiC := (integrableOn_Ioi_cpow_of_lt hre hNp).const_mul (1/720:ℂ)
  have hiQ := integrable_quarticPrimitiveTail hs hN
  have he : (∫ x in Ioi (N:ℝ), (((1/720:ℝ)-bernoulliQuarticPrimitive x:ℝ):ℂ)*(x:ℂ)^(-s-4))=
      (N:ℂ)^(-s-3)/(720*(s+3))-quarticPrimitiveTail N s := by
    have hf : (fun x : ℝ => (((1/720:ℝ)-bernoulliQuarticPrimitive x:ℝ):ℂ)*(x:ℂ)^(-s-4))=
        (fun x : ℝ => (1/720:ℂ)*(x:ℂ)^(-s-4)-(bernoulliQuarticPrimitive x:ℂ)*(x:ℂ)^(-s-4)) := by
      funext x; push_cast; ring
    rw [hf,integral_sub hiC hiQ,integral_const_mul,integral_Ioi_cpow_of_lt hre hNp]
    unfold quarticPrimitiveTail
    congr 1
    rw [show -s-4+1=-(s+3) by ring,neg_div_neg_eq,show -(s+3)=-s-3 by ring]
    push_cast
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  rw [he,norm_sub_rev] at hsbound
  convert! hsbound using 1
  ring

/-- The full centered tail normalized by its actual positive quartic mean. -/
def centeredTailPhase (N : ℕ) (s : ℂ) : ℂ :=
  720*(s+3)*(N:ℂ)^(s+3)*quarticPrimitiveTail N s

/-- Its distance from one is exactly the normalized complete mean error. -/
theorem centeredTailPhase_sub_one {s : ℂ} (hs : -1<s.re) {N : ℕ} (hN : 1≤N) :
    centeredTailPhase N s-1=720*(s+3)*(N:ℂ)^(s+3)*
      (quarticPrimitiveTail N s-(N:ℂ)^(-s-3)/(720*(s+3))) := by
  have hn : (N:ℂ)≠0 := by exact_mod_cast (show N≠0 by omega)
  have hd : s+3≠0 := by intro h; have := congrArg Complex.re h; norm_num at this; linarith
  have he : (N:ℂ)^(s+3)*(N:ℂ)^(-s-3)=1 := by
    rw [←Complex.cpow_add _ _ hn,show s+3+(-s-3)=0 by ring,Complex.cpow_zero]
  have hb : 720*(s+3)*(N:ℂ)^(s+3)*((N:ℂ)^(-s-3)/(720*(s+3)))=1 := by
    calc
      _ = (N:ℂ)^(s+3)*(N:ℂ)^(-s-3) := by field_simp
      _ = 1 := he
  unfold centeredTailPhase
  rw [mul_sub,hb]

/-- All-height mean control retains the full complex-parameter cost. -/
theorem norm_centeredTailPhase_sub_one_le {s : ℂ} (hs : -1<s.re) {N : ℕ} (hN : 1≤N) :
    ‖centeredTailPhase N s-1‖≤‖s+3‖*‖s+4‖/((s.re+4)*(N:ℝ)) := by
  have hNp : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hmean : quarticPrimitiveTail N s-(N:ℂ)^(-s-3)/(720*(s+3))=
      (s+4)*fifthPrimitiveTail N s := by rw [quarticPrimitiveTail_eq_mean_add_fifth hs hN]; ring
  rw [centeredTailPhase_sub_one hs hN,hmean,norm_mul,norm_mul,norm_mul,norm_mul,
    Complex.norm_natCast_cpow_of_pos (show 0<N by omega)]
  rw [show (s+3).re=s.re+3 by simp]
  norm_num only [Complex.norm_ofNat]
  have he : (N:ℝ)^(s.re+3)*(N:ℝ)^(-s.re-4)=(N:ℝ)⁻¹ := by
    rw [←Real.rpow_add hNp,show s.re+3+(-s.re-4)=(-1:ℝ) by ring,Real.rpow_neg_one]
  calc
    _ ≤ 720*‖s+3‖*(N:ℝ)^(s.re+3)*(‖s+4‖*((N:ℝ)^(-s.re-4)/(720*(s.re+4)))) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (norm_fifthPrimitiveTail_le hs hN) (norm_nonneg _)) (by positivity)
    _ = _ := by
      have hprod : 720*‖s+3‖*(N:ℝ)^(s.re+3)*(‖s+4‖*((N:ℝ)^(-s.re-4)/(720*(s.re+4))))=
          ‖s+3‖*‖s+4‖*((N:ℝ)^(s.re+3)*(N:ℝ)^(-s.re-4))/(s.re+4) := by field_simp
      rw [hprod,he]
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring

/-- Complete signed-frequency cancellation gives a linear-height phase bound. -/
theorem norm_centeredTailPhase_sub_one_le_linear {s : ℂ} (hs : -1<s.re)
    {N : ℕ} (hN : 1≤N) (ht : |s.im|≤N) :
    ‖centeredTailPhase N s-1‖≤4*‖s+3‖/(5*(N:ℝ)) := by
  have hNp : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  rw [centeredTailPhase_sub_one hs hN,norm_mul,norm_mul,norm_mul,
    Complex.norm_natCast_cpow_of_pos (show 0<N by omega)]
  rw [show (s+3).re=s.re+3 by simp]
  norm_num only [Complex.norm_ofNat]
  have he : (N:ℝ)^(s.re+3)*(N:ℝ)^(-s.re-4)=(N:ℝ)⁻¹ := by
    rw [←Real.rpow_add hNp,show s.re+3+(-s.re-4)=(-1:ℝ) by ring,Real.rpow_neg_one]
  calc
    _ ≤ 720*‖s+3‖*(N:ℝ)^(s.re+3)*((N:ℝ)^(-s.re-4)/900) := by
      exact mul_le_mul_of_nonneg_left (norm_quarticPrimitiveTail_sub_mean_le_linear hs hN ht) (by positivity)
    _ = _ := by
      have hprod : 720*‖s+3‖*(N:ℝ)^(s.re+3)*((N:ℝ)^(-s.re-4)/900)=
          4*‖s+3‖*((N:ℝ)^(s.re+3)*(N:ℝ)^(-s.re-4))/5 := by ring
      rw [hprod,he]
      ring

/-- A linear spectral cutoff puts the actual tail in a fixed strict right-half-plane cone. -/
theorem centeredTailPhase_re_ge_three_fifths {s : ℂ} (hs : -1<s.re)
    {N : ℕ} (hN : 1≤N) (hcut : 2*‖s+3‖≤N) :
    3/5≤(centeredTailPhase N s).re := by
  have hNp : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have ht : |s.im|≤N := by
    have h := Complex.abs_im_le_norm (s+3)
    norm_num at h
    linarith [norm_nonneg (s+3)]
  have hb := norm_centeredTailPhase_sub_one_le_linear hs hN ht
  have hrad : 4*‖s+3‖/(5*(N:ℝ))≤2/5 := by
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  have hre := (neg_le_abs ((centeredTailPhase N s-1).re)).trans
    (Complex.abs_re_le_norm (centeredTailPhase N s-1))
  simp only [Complex.sub_re,Complex.one_re] at hre
  linarith

/-- The phase normalization is exactly the original centered arithmetic tail. -/
theorem centeredTailPhase_mul_eq_centered_tail {s : ℂ} (hs : -1<s.re) {N : ℕ} (hN : 1≤N) :
    (s+2)*centeredTailPhase N s=720*(N:ℂ)^(s+3)*
      (∫ x in Ioi (N:ℝ), ((bernoulliPeriodic x+1/12:ℝ):ℂ)*(x:ℂ)^(-s-2)) := by
  rw [centeredBernoulliTail_eq_sub_mean hs hN,bernoulliTail_eq_mean_add_quartic hs hN]
  unfold centeredTailPhase
  ring

/-- The complete centered tail is nonzero beyond the linear cutoff. -/
theorem centered_tail_ne_zero_of_linear_cutoff {s : ℂ} (hs : -1<s.re) {N : ℕ}
    (hN : 1≤N) (hcut : 2*‖s+3‖≤N) :
    (∫ x in Ioi (N:ℝ), ((bernoulliPeriodic x+1/12:ℝ):ℂ)*(x:ℂ)^(-s-2))≠0 := by
  intro hzero
  have hb := centeredTailPhase_re_ge_three_fifths hs hN hcut
  have he := centeredTailPhase_mul_eq_centered_tail hs hN
  rw [hzero,mul_zero] at he
  have hd : s+2≠0 := by intro h; have := congrArg Complex.re h; norm_num at this; linarith
  have hC := (mul_eq_zero.mp he).resolve_left hd
  rw [hC] at hb
  norm_num at hb

/-- At an actual zeta zero the phase cone is the exactly normalized finite head. -/
theorem centeredTailPhase_eq_finiteResidual_at_zero {s : ℂ} (hs : 0<s.re) (hs1 : s≠1)
    (hz : riemannZeta s=0) {N : ℕ} (hN : 1≤N) :
    centeredTailPhase N s=720*(N:ℂ)^(s+3)*finiteCutoffResidual N s/
      (s*(s-1)*(s+1)*(s+2)) := by
  have hs0 : s≠0 := by intro h; rw [h] at hs; norm_num at hs
  have hsp : s+1≠0 := by intro h; have := congrArg Complex.re h; norm_num at this; linarith
  have hsp2 : s+2≠0 := by intro h; have := congrArg Complex.re h; norm_num at this; linarith
  rw [finiteCutoffResidual_at_zero hN hs hs1 hz]
  have he := centeredTailPhase_mul_eq_centered_tail (by linarith : -1<s.re) hN
  apply (eq_div_iff (mul_ne_zero (mul_ne_zero (mul_ne_zero hs0 (sub_ne_zero.mpr hs1)) hsp) hsp2)).mpr
  calc
    _ = (s*(s-1)*(s+1))*((s+2)*centeredTailPhase N s) := by ring
    _ = _ := by rw [he]; ring

/-- Every actual zeta zero has nonzero finite residual at every sufficiently long linear cutoff. -/
theorem finiteCutoffResidual_ne_zero_at_zero_of_linear_cutoff {s : ℂ}
    (hs : 0<s.re) (hs1 : s≠1) (hz : riemannZeta s=0)
    {N : ℕ} (hN : 1≤N) (hcut : 2*‖s+3‖≤N) : finiteCutoffResidual N s≠0 := by
  intro hzero
  have hb := centeredTailPhase_re_ge_three_fifths (by linarith : -1<s.re) hN hcut
  rw [centeredTailPhase_eq_finiteResidual_at_zero hs hs1 hz hN,hzero,mul_zero,zero_div] at hb
  norm_num at hb

/-- Beyond one height, no finite cutoff can match the whole actual simple-critical census,
even when the cutoff is allowed to vary with height. -/
theorem eventually_no_finiteCutoff_exact_critical_matching :
    ∀ᶠ T : ℝ in atTop, ∀ N : ℕ, 1≤N →
      ∃ s∈xiSimpleCriticalZeroFinset T, finiteCutoffResidual N s≠0 := by
  obtain ⟨rho,hrho,hrhomem,hrhone⟩ := exists_high_finiteCutoff_missed (N := 1) (by omega) 0
  obtain ⟨hr0,hr1,hi0,-,hxi,hr,ho⟩ := mem_xiSimpleCriticalZeroFinset.mp hrhomem
  have hz := (xi_zero_iff_zeta_zero_of_mem_strip hr0 hr1).mp hxi
  have hc : 0<Real.log 2/(864*Real.pi) := by positivity
  have hpow := (tendsto_rpow_atTop hc).eventually_ge_atTop (2*‖rho+3‖)
  filter_upwards [eventually_finiteCutoff_matching_power_lower,hpow,
    eventually_ge_atTop rho.im] with T hcost hlarge hheight
  intro N hN
  by_contra! hmatch
  have hNr := hcost N hN hmatch
  have hm : rho∈xiSimpleCriticalZeroFinset T :=
    mem_xiSimpleCriticalZeroFinset.mpr ⟨hr0,hr1,hi0,hheight,hxi,hr,ho⟩
  have hs1 : rho≠1 := by intro h; rw [h] at hr1; norm_num at hr1
  exact finiteCutoffResidual_ne_zero_at_zero_of_linear_cutoff hr0 hs1 hz hN
    (hlarge.trans hNr) (hmatch rho hm)

end RHTower.DeletionMixedRefinement
