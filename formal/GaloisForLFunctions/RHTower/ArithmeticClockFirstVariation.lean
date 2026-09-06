import GaloisForLFunctions.RHTower.ArithmeticClockResonanceMoments
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# First variation of the actual arithmetic exponential clock

The periodic quadratic is globally Lipschitz and has a right derivative at every point,
including its integer slope jumps. The exponential clock approaches each point from the
right as its parameter decreases to zero. These facts supply a dominated difference
quotient on every fixed finite interval without discarding any arithmetic boundary.

At an integer endpoint completing an integer number of phase turns, the leading prefix
vanishes. Its exact first-order coefficient is the strictly negative moment combination
proved in `ArithmeticClockResonanceMoments`. At reciprocal integer clock parameters this
is the first-order asymptotic of the actual logarithmic remainder segment.

Together with the existing noninteger-endpoint theorem, this proves eventual negativity
for each fixed complete prefix at `0 < lam < 2*pi` and `sigma >= -1`. The cutoff may depend
on that prefix. No uniform-in-prefix inequality or constraint at a zeta zero is asserted.
-/

noncomputable section
open MeasureTheory Set Filter Topology
namespace RHTower.DeletionMixedRefinement

private theorem bernoulli_abs_eq (x : ℝ) :
    |RHTower.bernoulliPeriodic x|=Int.fract x*(1-Int.fract x)/2 := by
  have h0 := Int.fract_nonneg x
  have h1 := Int.fract_lt_one x
  rw [RHTower.bernoulliPeriodic,abs_of_nonpos (by nlinarith : (Int.fract x^2-Int.fract x)/2≤0)]
  ring

/-- The periodic quadratic has Lipschitz constant one half, including across integer joins. -/
theorem bernoulliPeriodic_lipschitz_bound (x y : ℝ) :
    |RHTower.bernoulliPeriodic x-RHTower.bernoulliPeriodic y|≤|x-y|/2 := by
  wlog hxy : x≤y generalizing x y
  · simpa [abs_sub_comm] using this y x (le_of_not_ge hxy)
  have hx0 := Int.fract_nonneg x
  have hx1 := Int.fract_lt_one x
  have hy0 := Int.fract_nonneg y
  have hy1 := Int.fract_lt_one y
  by_cases hf : Int.floor x=Int.floor y
  · have he : RHTower.bernoulliPeriodic x-RHTower.bernoulliPeriodic y =
        (x-y)*(Int.fract x+Int.fract y-1)/2 := by
      simp only [RHTower.bernoulliPeriodic,Int.fract,hf]
      ring
    rw [he,abs_div,abs_mul]
    norm_num
    have hb : |Int.fract x+Int.fract y-1|≤1 := abs_le.mpr (by constructor <;> linarith)
    nlinarith [mul_le_mul_of_nonneg_left hb (abs_nonneg (x-y))]
  · have hfm : Int.floor x≤Int.floor y := Int.floor_mono hxy
    have hf' : Int.floor x+1≤Int.floor y := by omega
    have hfr : (Int.floor x:ℝ)+1≤(Int.floor y:ℝ) := by exact_mod_cast hf'
    have hx : |RHTower.bernoulliPeriodic x|≤(1-Int.fract x)/2 := by
      rw [bernoulli_abs_eq]
      nlinarith [mul_nonneg (sub_nonneg.mpr hx1.le) (sub_nonneg.mpr hx1.le)]
    have hy : |RHTower.bernoulliPeriodic y|≤Int.fract y/2 := by
      rw [bernoulli_abs_eq]
      nlinarith [sq_nonneg (Int.fract y)]
    have h := abs_sub (RHTower.bernoulliPeriodic x) (RHTower.bernoulliPeriodic y)
    rw [abs_of_nonpos (sub_nonpos.mpr hxy)]
    dsimp only [Int.fract] at hx hy
    linarith

/-- The right derivative retains the correct slope at every integer join. -/
theorem bernoulliPeriodic_hasDerivWithinAt_right (x : ℝ) :
    HasDerivWithinAt RHTower.bernoulliPeriodic (Int.fract x-1/2) (Ici x) x := by
  have hf := tendsto_pure.mp (tendsto_floor_right_pure_floor x)
  have he : RHTower.bernoulliPeriodic =ᶠ[𝓝[≥] x]
      (fun y : ℝ => ((y-(Int.floor x:ℝ))^2-(y-(Int.floor x:ℝ)))/2) := by
    filter_upwards [hf] with y hy
    simp only [RHTower.bernoulliPeriodic,Int.fract,hy]
  have hi := (hasDerivAt_id x).sub_const (Int.floor x:ℝ)
  have hd : HasDerivAt
      (fun y : ℝ => ((y-(Int.floor x:ℝ))^2-(y-(Int.floor x:ℝ)))/2)
      (Int.fract x-1/2) x := by
    convert! ((hi.pow 2).sub hi).div_const 2 using 1
    simp only [Int.fract]
    norm_num
    ring
  exact hd.hasDerivWithinAt.congr_of_eventuallyEq he rfl

/-- The exponential arithmetic clock with its continuous value at zero acceleration. -/
def expArithmeticClock (h v : ℝ) : ℝ :=
  if h=0 then v else (Real.exp (h*v)-1)/h

/-- At zero acceleration the arithmetic clock is the identity. -/
theorem expArithmeticClock_zero (v : ℝ) : expArithmeticClock 0 v=v := by
  simp [expArithmeticClock]

/-- The exact clock derivative at zero acceleration is the quadratic displacement. -/
theorem expArithmeticClock_hasDerivAt_zero (v : ℝ) :
    HasDerivAt (fun h => expArithmeticClock h v) (v^2/2) 0 := by
  by_cases hv : v=0
  · subst v
    simpa [expArithmeticClock] using hasDerivAt_const (0:ℝ) (0:ℝ)
  have ho := (Real.exp_sub_sum_range_succ_isLittleO_pow 2).tendsto_div_nhds_zero
  have ho' : Tendsto (fun z : ℝ => (Real.exp z-(1+z+z^2/2))/z^2) (𝓝 0) (𝓝 0) := by
    simpa [Finset.sum_range_succ,Nat.factorial] using ho
  have hm : Tendsto (fun h : ℝ => h*v) (𝓝 0) (𝓝 0) := by
    simpa using (show Tendsto (fun h : ℝ => h) (𝓝 0) (𝓝 0) from tendsto_id).mul_const v
  have ht := ((ho'.comp hm).mono_left (show 𝓝[≠] (0:ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)).const_mul (v^2)
  have ht' : Tendsto (fun h : ℝ => v^2/2+v^2*((Real.exp (h*v)-(1+h*v+(h*v)^2/2))/(h*v)^2))
      (𝓝[≠] 0) (𝓝 (v^2/2)) := by
    simpa using tendsto_const_nhds.add ht
  apply hasDerivAt_iff_tendsto_slope.mpr
  apply ht'.congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hh0 : h≠0 := by simpa using hh
  simp [slope_def_field,expArithmeticClock,hh0]
  field_simp [hh0,hv]
  ring


/-- Positive acceleration moves the clock to the right of its linear value. -/
theorem expArithmeticClock_ge {h : ℝ} (hh : 0 < h) (v : ℝ) :
    v ≤ expArithmeticClock h v := by
  rw [expArithmeticClock,if_neg hh.ne']
  apply (le_div_iff₀ hh).mpr
  linarith [Real.add_one_le_exp (h*v)]

/-- A symbolic local displacement bound for the exponential clock. -/
theorem expArithmeticClock_displacement_le {h v : ℝ} (hh : 0 < h)
    (hv : 0 ≤ v) (hsmall : h*v ≤ 1) :
    |expArithmeticClock h v-v| ≤ h*v^2 := by
  have he : expArithmeticClock h v-v=(Real.exp (h*v)-1-h*v)/h := by
    rw [expArithmeticClock,if_neg hh.ne']
    field_simp
  have hb := Real.abs_exp_sub_one_sub_id_le
    (show |h*v| ≤ 1 by rwa [abs_of_nonneg (mul_nonneg hh.le hv)])
  rw [he,abs_div,abs_of_pos hh]
  apply (div_le_iff₀ hh).mpr
  nlinarith [hb]

/-- The actual periodic quadratic, transported weight, and unchanged phase in clock coordinates. -/
def clockVariationIntegrand (sigma lam h v : ℝ) : ℝ :=
  RHTower.bernoulliPeriodic (expArithmeticClock h v)*
    Real.exp (-(sigma+1)*v*h)*Real.sin (lam*v)

/-- The exact right derivative of the clock integrand at zero acceleration. -/
def clockVariationDensity (sigma lam v : ℝ) : ℝ :=
  ((v^2/2)*(Int.fract v-1/2)-(sigma+1)*v*RHTower.bernoulliPeriodic v)*Real.sin (lam*v)

/-- The right derivative of the literal integrand exists even at arithmetic slope jumps. -/
theorem clockVariationIntegrand_hasDerivWithinAt_zero (sigma lam v : ℝ) :
    HasDerivWithinAt (fun h => clockVariationIntegrand sigma lam h v)
      (clockVariationDensity sigma lam v) (Ioi 0) 0 := by
  have hq := (expArithmeticClock_hasDerivAt_zero v).hasDerivWithinAt (s:=Ioi 0)
  have hb := (bernoulliPeriodic_hasDerivWithinAt_right v).comp_of_eq 0 hq
    (show MapsTo (fun h => expArithmeticClock h v) (Ioi 0) (Ici v) from
      fun h hh => expArithmeticClock_ge hh v) (expArithmeticClock_zero v).symm
  have hw : HasDerivAt (fun h : ℝ => Real.exp (-(sigma+1)*v*h)) (-(sigma+1)*v) 0 := by
    convert! ((hasDerivAt_id (0:ℝ)).const_mul (-(sigma+1)*v)).exp using 1
    simp
  convert! (hb.mul hw.hasDerivWithinAt).mul_const (Real.sin (lam*v)) using 1
  dsimp only [clockVariationIntegrand,clockVariationDensity,Function.comp_apply]
  rw [expArithmeticClock_zero]
  norm_num
  ring_nf
  simp

/-- The pointwise right difference quotient has the exact variation density as its limit. -/
theorem tendsto_clockVariationIntegrand_quotient (sigma lam v : ℝ) :
    Tendsto (fun h => (clockVariationIntegrand sigma lam h v-
      RHTower.bernoulliPeriodic v*Real.sin (lam*v))/h) (𝓝[>] 0)
      (𝓝 (clockVariationDensity sigma lam v)) := by
  have h := (hasDerivWithinAt_iff_tendsto_slope' (by simp : (0:ℝ)∉Ioi (0:ℝ))).mp
    (clockVariationIntegrand_hasDerivWithinAt_zero sigma lam v)
  have h' : Tendsto (fun h => (clockVariationIntegrand sigma lam h v-
      clockVariationIntegrand sigma lam 0 v)/(h-0)) (𝓝[>] 0)
      (𝓝 (clockVariationDensity sigma lam v)) :=
    h.congr' (Eventually.of_forall (fun h => slope_def_field _ _ h))
  simpa only [clockVariationIntegrand,expArithmeticClock_zero,mul_zero,Real.exp_zero,mul_one,sub_zero] using h'


/-- A polynomial bound dominates every sufficiently small positive clock difference quotient. -/
theorem clockVariation_quotient_bound {sigma h v : ℝ} (hsigma : -1 ≤ sigma)
    (hh : 0 < h) (hv : 0 ≤ v) (hsmall : h*v ≤ 1) (lam : ℝ) :
    |(clockVariationIntegrand sigma lam h v-
      RHTower.bernoulliPeriodic v*Real.sin (lam*v))/h| ≤ v^2/2+(sigma+1)*v := by
  have ha : 0 ≤ sigma+1 := by linarith
  have hw : Real.exp (-(sigma+1)*v*h) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    nlinarith [mul_nonneg (mul_nonneg ha hv) hh.le]
  have hw' : |Real.exp (-(sigma+1)*v*h)-1| ≤ (sigma+1)*v*h := by
    rw [abs_of_nonpos (sub_nonpos.mpr hw)]
    linarith [Real.add_one_le_exp (-(sigma+1)*v*h)]
  have hb : |RHTower.bernoulliPeriodic (expArithmeticClock h v)-
      RHTower.bernoulliPeriodic v| ≤ h*v^2/2 := by
    have hl := bernoulliPeriodic_lipschitz_bound (expArithmeticClock h v) v
    have hq := expArithmeticClock_displacement_le hh hv hsmall
    linarith
  have he : clockVariationIntegrand sigma lam h v-
      RHTower.bernoulliPeriodic v*Real.sin (lam*v) =
      ((RHTower.bernoulliPeriodic (expArithmeticClock h v)-RHTower.bernoulliPeriodic v)*
        Real.exp (-(sigma+1)*v*h)+RHTower.bernoulliPeriodic v*(Real.exp (-(sigma+1)*v*h)-1))*
        Real.sin (lam*v) := by
    unfold clockVariationIntegrand
    ring
  rw [he,abs_div,abs_of_pos hh,abs_mul]
  apply (div_le_iff₀ hh).mpr
  have habs : |(RHTower.bernoulliPeriodic (expArithmeticClock h v)-RHTower.bernoulliPeriodic v)*
        Real.exp (-(sigma+1)*v*h)+RHTower.bernoulliPeriodic v*(Real.exp (-(sigma+1)*v*h)-1)| ≤
      |RHTower.bernoulliPeriodic (expArithmeticClock h v)-RHTower.bernoulliPeriodic v| *
        Real.exp (-(sigma+1)*v*h)+|RHTower.bernoulliPeriodic v| * |Real.exp (-(sigma+1)*v*h)-1| := by
    simpa only [sub_neg_eq_add,abs_neg,abs_mul,abs_of_pos (Real.exp_pos _)] using
      abs_sub ((RHTower.bernoulliPeriodic (expArithmeticClock h v)-RHTower.bernoulliPeriodic v)*
        Real.exp (-(sigma+1)*v*h)) (-(RHTower.bernoulliPeriodic v*(Real.exp (-(sigma+1)*v*h)-1)))
  calc _ ≤ (|RHTower.bernoulliPeriodic (expArithmeticClock h v)-RHTower.bernoulliPeriodic v| *
      Real.exp (-(sigma+1)*v*h)+|RHTower.bernoulliPeriodic v| * |Real.exp (-(sigma+1)*v*h)-1|)*1 :=
        mul_le_mul habs (Real.abs_sin_le_one _) (abs_nonneg _) (by positivity)
    _ ≤ (h*v^2/2)*1+1*((sigma+1)*v*h) := by
      rw [mul_one]
      gcongr
      exact RHTower.abs_bernoulliPeriodic_le_one v
    _ = (v^2/2+(sigma+1)*v)*h := by ring


private theorem deformation_bernoulli_continuous : Continuous RHTower.bernoulliPeriodic :=
  (show Continuous (fun x : ℝ => (x^2-x)/2) by fun_prop).continuousOn.comp_fract'' (by norm_num)

private theorem clockVariationIntegrand_continuous (sigma lam h : ℝ) :
    Continuous (clockVariationIntegrand sigma lam h) := by
  have hq : Continuous (expArithmeticClock h) := by
    change Continuous (fun v : ℝ => expArithmeticClock h v)
    by_cases hh : h=0
    · simp only [expArithmeticClock,if_pos hh]
      exact continuous_id
    · simp only [expArithmeticClock,if_neg hh]
      fun_prop
  unfold clockVariationIntegrand
  exact ((deformation_bernoulli_continuous.comp hq).mul (by fun_prop)).mul (by fun_prop)

/-- The finite arithmetic prefix at an exponential clock parameter. -/
def clockVariationPrefix (sigma lam h A : ℝ) : ℝ :=
  ∫ v in (0:ℝ)..A, clockVariationIntegrand sigma lam h v

/-- At zero acceleration the clock prefix is the exact constant-speed arithmetic prefix. -/
theorem clockVariationPrefix_zero (sigma lam A : ℝ) :
    clockVariationPrefix sigma lam 0 A=linearPhasePrefix lam A := by
  simp only [clockVariationPrefix,clockVariationIntegrand,expArithmeticClock_zero,
    mul_zero,Real.exp_zero,mul_one,linearPhasePrefix]

/-- Dominated convergence gives the first variation on every fixed nonnegative finite interval. -/
theorem tendsto_clockVariationPrefix_quotient {sigma A : ℝ} (hsigma : -1 ≤ sigma)
    (hA : 0 ≤ A) (lam : ℝ) :
    Tendsto (fun h => (clockVariationPrefix sigma lam h A-linearPhasePrefix lam A)/h)
      (𝓝[>] 0) (𝓝 (∫ v in (0:ℝ)..A, clockVariationDensity sigma lam v)) := by
  have h := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (a:=0) (b:=A) (μ:=volume) (l:=𝓝[>] (0:ℝ))
    (F:=fun h v => (clockVariationIntegrand sigma lam h v-
      RHTower.bernoulliPeriodic v*Real.sin (lam*v))/h)
    (f:=clockVariationDensity sigma lam) (bound:=fun v => v^2/2+(sigma+1)*v)
  have hc0 : Continuous (fun v : ℝ => RHTower.bernoulliPeriodic v*Real.sin (lam*v)) :=
    deformation_bernoulli_continuous.mul (by fun_prop)
  have hm : ∀ᶠ h in 𝓝[>] (0:ℝ), AEStronglyMeasurable
      (fun v => (clockVariationIntegrand sigma lam h v-
        RHTower.bernoulliPeriodic v*Real.sin (lam*v))/h) (volume.restrict (uIoc 0 A)) := by
    filter_upwards with h
    exact (((clockVariationIntegrand_continuous sigma lam h).sub hc0).div_const h).aestronglyMeasurable.restrict
  have hsmall : ∀ᶠ h in 𝓝[>] (0:ℝ), h*A ≤ 1 := by
    have ht : Tendsto (fun h : ℝ => h*A) (𝓝[>] 0) (𝓝 0) := by
      simpa using (show Tendsto (fun h : ℝ => h) (𝓝[>] 0) (𝓝 0) from
        tendsto_id.mono_left nhdsWithin_le_nhds).mul_const A
    exact (ht.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1))).mono (fun _ hh => hh.le)
  have hb : ∀ᶠ h in 𝓝[>] (0:ℝ), ∀ᵐ v : ℝ ∂volume, v ∈ uIoc 0 A →
      ‖(clockVariationIntegrand sigma lam h v-
        RHTower.bernoulliPeriodic v*Real.sin (lam*v))/h‖ ≤ v^2/2+(sigma+1)*v := by
    filter_upwards [self_mem_nhdsWithin,hsmall] with h hh hsmall'
    filter_upwards with v hv
    rw [uIoc_of_le hA] at hv
    rw [Real.norm_eq_abs]
    exact clockVariation_quotient_bound hsigma hh hv.1.le
      ((mul_le_mul_of_nonneg_left hv.2 hh.le).trans hsmall') lam
  have hl : ∀ᵐ v : ℝ ∂volume, v ∈ uIoc 0 A →
      Tendsto (fun h => (clockVariationIntegrand sigma lam h v-
        RHTower.bernoulliPeriodic v*Real.sin (lam*v))/h) (𝓝[>] 0)
        (𝓝 (clockVariationDensity sigma lam v)) := by
    filter_upwards with v _
    exact tendsto_clockVariationIntegrand_quotient sigma lam v
  have hlim := h hm hb ((show Continuous (fun v : ℝ => v^2/2+(sigma+1)*v) by fun_prop).intervalIntegrable 0 A) hl
  apply hlim.congr'
  filter_upwards with h
  rw [intervalIntegral.integral_div,intervalIntegral.integral_sub
    ((clockVariationIntegrand_continuous sigma lam h).intervalIntegrable 0 A) (hc0.intervalIntegrable 0 A)]
  rfl


private theorem slope_intervalIntegrable (a b : ℝ) :
    IntervalIntegrable (fun v : ℝ => Int.fract v-1/2) volume a b := by
  apply (intervalIntegrable_const (c:=(1:ℝ)) (a:=a) (b:=b)).mono_fun'
    (measurable_fract.sub_const (1/2)).aestronglyMeasurable.restrict
  filter_upwards with v
  rw [Real.norm_eq_abs]
  apply abs_le.mpr
  constructor <;> linarith [Int.fract_nonneg v,Int.fract_lt_one v]

/-- Right-derivative integration retains all integer slope jumps and evaluates the variation density. -/
theorem integral_clockVariationDensity (sigma lam : ℝ) (m : ℕ) :
    (∫ v in (0:ℝ)..(m:ℝ), clockVariationDensity sigma lam v)=
      resonantClockMomentCoefficient sigma lam m := by
  let T : ℝ → ℝ := fun v => (v^2/2)*(Int.fract v-1/2)*Real.sin (lam*v)
  let U : ℝ → ℝ := fun v => v*RHTower.bernoulliPeriodic v*Real.sin (lam*v)
  let V : ℝ → ℝ := fun v => v^2*RHTower.bernoulliPeriodic v*Real.cos (lam*v)
  have hT : IntervalIntegrable T volume 0 (m:ℝ) :=
    ((slope_intervalIntegrable 0 m).continuousOn_mul (by fun_prop)).mul_continuousOn (by fun_prop)
  have hU : IntervalIntegrable U volume 0 (m:ℝ) :=
    ((continuous_id.mul deformation_bernoulli_continuous).mul (by fun_prop)).intervalIntegrable 0 m
  have hV : IntervalIntegrable V volume 0 (m:ℝ) :=
    (((continuous_id.pow 2).mul deformation_bernoulli_continuous).mul (by fun_prop)).intervalIntegrable 0 m
  let g : ℝ → ℝ := fun v => (v^2/2)*RHTower.bernoulliPeriodic v*Real.sin (lam*v)
  have hgcont : Continuous g :=
    (((continuous_id.pow 2).div_const 2).mul deformation_bernoulli_continuous).mul (by fun_prop)
  have hgd (v : ℝ) : HasDerivWithinAt g (T v+U v+(lam/2)*V v) (Ioi v) v := by
    have hb := (bernoulliPeriodic_hasDerivWithinAt_right v).mono Ioi_subset_Ici_self
    have hp := ((hasDerivAt_id v).pow 2).div_const 2
    have hs := (Real.hasDerivAt_sin (lam*v)).comp v ((hasDerivAt_id v).const_mul lam)
    convert! (hp.hasDerivWithinAt.mul hb).mul hs.hasDerivWithinAt using 1
    dsimp [g,T,U,V]
    norm_num
    ring
  have hftc := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le
    (show (0:ℝ)≤ m by positivity) hgcont.continuousOn (fun v _ => hgd v)
    ((hT.add hU).add (hV.const_mul (lam/2)))
  have hends : g (m:ℝ)-g 0=0 := by simp [g,RHTower.bernoulliPeriodic]
  rw [hends,intervalIntegral.integral_add (hT.add hU) (hV.const_mul (lam/2)),
    intervalIntegral.integral_add hT hU,intervalIntegral.integral_const_mul] at hftc
  have he : (∫ v in (0:ℝ)..(m:ℝ),clockVariationDensity sigma lam v)=
      (∫ v in (0:ℝ)..(m:ℝ),T v)-(sigma+1)*linearSineMoment lam m := by
    have hi : (∫ v in (0:ℝ)..(m:ℝ),clockVariationDensity sigma lam v)=
        ∫ v in (0:ℝ)..(m:ℝ),T v-(sigma+1)*U v := by
      apply intervalIntegral.integral_congr
      intro v _
      dsimp [clockVariationDensity,T,U]
      ring
    rw [hi,intervalIntegral.integral_sub hT (hU.const_mul (sigma+1)),
      intervalIntegral.integral_const_mul]
    rfl
  rw [he,resonantClockMomentCoefficient]
  change (∫ v in (0:ℝ)..(m:ℝ),T v)+linearSineMoment lam m+
    (lam/2)*linearSecondCosineMoment lam m=0 at hftc
  linear_combination hftc

/-- At an integer endpoint completing whole turns, the full clock prefix divided by acceleration tends to its exact moment coefficient. -/
theorem tendsto_clockVariationPrefix_div_at_resonance {sigma lam : ℝ}
    (hsigma : -1 ≤ sigma) (hlam : 0 < lam) (hlam' : lam < 2*Real.pi)
    (m K : ℕ) (hturn : lam*(m:ℝ)=2*Real.pi*K) :
    Tendsto (fun h => clockVariationPrefix sigma lam h m/h) (𝓝[>] 0)
      (𝓝 (resonantClockMomentCoefficient sigma lam m)) := by
  have hz : linearPhasePrefix lam (m:ℝ)=0 := by
    have he := linearPhasePrefix_eq_complete_turn (r:=0) hlam hlam' m K
      (by norm_num) (by norm_num) (by simpa using hturn)
    simpa using he
  have h := tendsto_clockVariationPrefix_quotient hsigma (show (0:ℝ)≤ m by positivity) lam
  simpa only [hz,sub_zero,integral_clockVariationDensity] using h

/-- Each fixed positive integer endpoint completing whole turns has negative prefix at sufficiently small positive acceleration. -/
theorem eventually_clockVariationPrefix_neg {sigma lam : ℝ}
    (hsigma : -1 ≤ sigma) (hlam : 0 < lam) (hlam' : lam < 2*Real.pi)
    {m : ℕ} (hm : 0 < m) (K : ℕ) (hturn : lam*(m:ℝ)=2*Real.pi*K) :
    ∀ᶠ h in 𝓝[>] (0:ℝ), clockVariationPrefix sigma lam h m < 0 := by
  have hlim := tendsto_clockVariationPrefix_div_at_resonance hsigma hlam hlam' m K hturn
  have hn := hlim.eventually (eventually_lt_nhds
    (resonantClockMomentCoefficient_neg hsigma hlam hlam' hm K hturn))
  filter_upwards [self_mem_nhdsWithin,hn] with h hh hn'
  simpa using (div_lt_iff₀ hh).mp hn'


/-- Reciprocal integer clock parameters recover the literal scaled logarithmic source integral. -/
theorem clockVariationPrefix_reciprocal_integer (sigma lam A : ℝ) {N : ℕ} (hN : 0 < N) :
    clockVariationPrefix sigma lam (1/(N:ℝ)) A=scaledLogarithmicSegment sigma lam N 0 A := by
  have hNp : (0:ℝ) < N := by exact_mod_cast hN
  have hh : (1:ℝ)/(N:ℝ) ≠ 0 := (div_pos (by norm_num) hNp).ne'
  rw [clockVariationPrefix,scaledLogarithmicSegment_eq_clock sigma lam 0 A hN]
  apply intervalIntegral.integral_congr
  intro v _
  have hq : expArithmeticClock (1/(N:ℝ)) v+(N:ℝ)=(N:ℝ)*Real.exp (v/N) := by
    rw [expArithmeticClock,if_neg hh]
    simp only [one_div,inv_mul_eq_div,div_inv_eq_mul]
    ring
  have hb : RHTower.bernoulliPeriodic (expArithmeticClock (1/(N:ℝ)) v)=
      RHTower.bernoulliPeriodic ((N:ℝ)*Real.exp (v/N)) := by
    rw [← hq]
    simp only [RHTower.bernoulliPeriodic,Int.fract_add_natCast]
  unfold clockVariationIntegrand arithmeticClockIntegrand
  rw [hb]
  rw [show -(sigma+1)*v*(1/(N:ℝ))=-(sigma+1)*v/(N:ℝ) by ring]

private theorem reciprocal_nat_clock_tendsto :
    Tendsto (fun n : ℕ => (1:ℝ)/(n+1:ℕ)) atTop (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · simpa only [Nat.cast_add,Nat.cast_one] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ))
  · exact Eventually.of_forall (fun n => by change (0:ℝ)<1/(n+1:ℕ); positivity)

/-- At integer endpoint coincidences, the actual source prefix has the exact first-order coefficient. -/
theorem tendsto_scaledLogarithmic_integer_prefix_first_order {sigma lam : ℝ}
    (hsigma : -1 ≤ sigma) (hlam : 0 < lam) (hlam' : lam < 2*Real.pi)
    (m K : ℕ) (hturn : lam*(m:ℝ)=2*Real.pi*K) :
    Tendsto (fun n : ℕ => (n+1:ℕ)*scaledLogarithmicSegment sigma lam (n+1) 0 m) atTop
      (𝓝 (resonantClockMomentCoefficient sigma lam m)) := by
  have h := (tendsto_clockVariationPrefix_div_at_resonance hsigma hlam hlam' m K hturn).comp
    reciprocal_nat_clock_tendsto
  apply h.congr'
  filter_upwards with n
  dsimp only [Function.comp_apply]
  rw [clockVariationPrefix_reciprocal_integer sigma lam m (show 0 < n+1 by omega)]
  simp [div_eq_mul_inv,mul_comm]

/-- Every fixed positive integer endpoint coincidence has an eventually negative actual source prefix. -/
theorem eventually_scaledLogarithmic_integer_prefix_neg {sigma lam : ℝ}
    (hsigma : -1 ≤ sigma) (hlam : 0 < lam) (hlam' : lam < 2*Real.pi)
    {m : ℕ} (hm : 0 < m) (K : ℕ) (hturn : lam*(m:ℝ)=2*Real.pi*K) :
    ∀ᶠ n : ℕ in atTop, scaledLogarithmicSegment sigma lam (n+1) 0 m < 0 := by
  have h := (tendsto_scaledLogarithmic_integer_prefix_first_order hsigma hlam hlam' m K hturn).eventually
    (eventually_lt_nhds (resonantClockMomentCoefficient_neg hsigma hlam hlam' hm K hturn))
  filter_upwards [h] with n hn
  have hp : (0:ℝ) < (n+1:ℕ) := by positivity
  apply (mul_lt_mul_iff_of_pos_left hp).mp
  simpa using hn

/-- All positive complete endpoints are covered, including both integer and noninteger arithmetic endpoints. -/
theorem eventually_scaledLogarithmic_complete_prefix_neg {sigma lam A : ℝ}
    (hsigma : -1 ≤ sigma) (hlam : 0 < lam) (hlam' : lam < 2*Real.pi)
    (hA : 0 < A) (K : ℕ) (hturn : lam*A=2*Real.pi*K) :
    ∀ᶠ n : ℕ in atTop, scaledLogarithmicSegment sigma lam (n+1) 0 A < 0 := by
  have he : (⌊A⌋₊:ℝ)+Int.fract A=A := by
    rw [natCast_floor_eq_intCast_floor hA.le,Int.floor_add_fract]
  by_cases hf : Int.fract A=0
  · have hmA : (⌊A⌋₊:ℝ)=A := by simpa only [hf,add_zero] using he
    have hm : 0 < ⌊A⌋₊ := by
      have hp : (0:ℝ) < (⌊A⌋₊:ℝ) := by rwa [hmA]
      exact_mod_cast hp
    have h := eventually_scaledLogarithmic_integer_prefix_neg hsigma hlam hlam' hm K
      (show lam*(⌊A⌋₊:ℝ)=2*Real.pi*K by rwa [hmA])
    simpa only [hmA] using h
  · have hr : 0 < Int.fract A := lt_of_le_of_ne (Int.fract_nonneg A) (Ne.symm hf)
    have h := eventually_scaledLogarithmic_prefix_neg hsigma hlam hlam' ⌊A⌋₊ K
      hr (Int.fract_lt_one A) (show lam*((⌊A⌋₊:ℝ)+Int.fract A)=2*Real.pi*K by rwa [he])
    simpa only [he] using h

/-- For each fixed positive number of turns the source prefix is eventually negative; the cutoff is not asserted to be uniform in the turn count. -/
theorem eventually_scaledLogarithmic_turn_prefix_neg {sigma lam : ℝ}
    (hsigma : -1 ≤ sigma) (hlam : 0 < lam) (hlam' : lam < 2*Real.pi)
    {K : ℕ} (hK : 0 < K) :
    ∀ᶠ n : ℕ in atTop,
      scaledLogarithmicSegment sigma lam (n+1) 0 (2*Real.pi*K/lam) < 0 := by
  apply eventually_scaledLogarithmic_complete_prefix_neg hsigma hlam hlam' (by positivity) K
  field_simp

end RHTower.DeletionMixedRefinement
