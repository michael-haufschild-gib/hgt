import GaloisForLFunctions.RHTower.ArithmeticLogarithmicPhaseScaling
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

/-!
# Exact arithmetic moments at integer phase coincidences

The Bernoulli cosine prefix at an integer endpoint is an exact sine times a rational
trigonometric coefficient. Differentiating its literal finite integral before imposing
an integer phase coincidence gives the first sine and second cosine moments.

Their clock-variation combination is strictly negative whenever `sigma >= -1`,
`0 < lam < 2*pi`, the integer endpoint is positive, and `lam*m = 2*pi*K`.
The proof retains all arithmetic endpoint terms and uses no numerical input.

These are source moment identities. Identifying the combination with the first-order
change of the exponential-clock integral requires a separate limiting theorem.
No uniform finite-cutoff sign law or constraint at a zeta zero is asserted here.
-/

noncomputable section
open MeasureTheory Set Filter Topology
open scoped BigOperators
namespace RHTower.DeletionMixedRefinement

/-- The cosine transform of the actual periodic quadratic on a finite prefix. -/
def linearCosinePrefix (lam A : ℝ) : ℝ :=
  ∫ x in (0:ℝ)..A, RHTower.bernoulliPeriodic x*Real.cos (lam*x)

/-- The coefficient in the exact integer-endpoint cosine transform. -/
def phaseCosineCoefficient (lam : ℝ) : ℝ :=
  Real.cos (lam/2)/(2*lam^2*Real.sin (lam/2))-1/lam^3

/-- The derivative of the cosine coefficient away from its displayed denominators. -/
def phaseCosineCoefficientDeriv (lam : ℝ) : ℝ :=
  -1/(4*lam^2*Real.sin (lam/2)^2)-Real.cos (lam/2)/(lam^3*Real.sin (lam/2))+3/lam^4

private def cosinePhasePrimitive (lam m x : ℝ) : ℝ :=
  ((x-m)^2-(x-m))/2 * Real.sin (lam*x)/lam +
    (x-m-1/2)*Real.cos (lam*x)/lam^2 - Real.sin (lam*x)/lam^3

private theorem cosinePhasePrimitive_deriv {lam : ℝ} (hlam : lam ≠ 0) (m x : ℝ) :
    HasDerivAt (cosinePhasePrimitive lam m)
      (((x-m)^2-(x-m))/2*Real.cos (lam*x)) x := by
  have hy := (hasDerivAt_id x).sub_const m
  have hb := ((hy.pow 2).sub hy).div_const 2
  have hc := (Real.hasDerivAt_cos (lam*x)).comp x ((hasDerivAt_id x).const_mul lam)
  have hs := (Real.hasDerivAt_sin (lam*x)).comp x ((hasDerivAt_id x).const_mul lam)
  have h := (((hb.mul hs).div_const lam).add
    (((hy.sub_const (1/2)).mul hc).div_const (lam^2))).sub (hs.div_const (lam^3))
  convert! h using 1
  dsimp [cosinePhasePrimitive]
  norm_num
  field_simp [hlam]
  ring

private theorem variation_bernoulli_continuous : Continuous RHTower.bernoulliPeriodic :=
  (show Continuous (fun x : ℝ => (x^2-x)/2) by fun_prop).continuousOn.comp_fract'' (by norm_num)

private theorem cosinePhase_integrable (lam a b : ℝ) :
    IntervalIntegrable (fun x : ℝ => RHTower.bernoulliPeriodic x*Real.cos (lam*x))
      volume a b :=
  (variation_bernoulli_continuous.mul (by fun_prop)).intervalIntegrable a b

private theorem cosinePhase_cell_eq {lam : ℝ} (hlam : lam ≠ 0) (m : ℕ) :
    (∫ x in (m:ℝ)..((m:ℝ)+1), RHTower.bernoulliPeriodic x*Real.cos (lam*x)) =
      cosinePhasePrimitive lam m ((m:ℝ)+1)-cosinePhasePrimitive lam m m := by
  have he : (∫ x in (m:ℝ)..((m:ℝ)+1),
      RHTower.bernoulliPeriodic x*Real.cos (lam*x)) =
      ∫ x in (m:ℝ)..((m:ℝ)+1),
        (((x-(m:ℝ))^2-(x-(m:ℝ)))/2)*Real.cos (lam*x) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le (by linarith)] at hx
    by_cases hxe : x=(m:ℝ)+1
    · subst x
      simp [RHTower.bernoulliPeriodic]
    · have hxl : x<(m:ℝ)+1 := lt_of_le_of_ne hx.2 hxe
      have hf : Int.floor x=(m:ℤ) := Int.floor_eq_iff.mpr (by simpa using And.intro hx.1 hxl)
      simp [RHTower.bernoulliPeriodic,Int.fract,hf]
  rw [he]
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => cosinePhasePrimitive_deriv hlam m x) (by
      apply Continuous.intervalIntegrable
      fun_prop)

private theorem cosinePhase_prefix_nat {lam : ℝ} (hlam : lam ≠ 0) (m : ℕ) :
    linearCosinePrefix lam m =
      (1/2)*(1-Real.cos (lam*(m:ℝ)))/lam^2-Real.sin (lam*(m:ℝ))/lam^3+
        (∑ j ∈ Finset.range m, Real.cos (lam*((j:ℝ)+1)))/lam^2 := by
  induction m with
  | zero => simp [linearCosinePrefix]
  | succ m ih =>
    have h := intervalIntegral.integral_add_adjacent_intervals
      (cosinePhase_integrable lam 0 m) (cosinePhase_integrable lam m ((m:ℝ)+1))
    change linearCosinePrefix lam m+_=linearCosinePrefix lam ((m:ℝ)+1) at h
    rw [cosinePhase_cell_eq hlam m,ih] at h
    simp only [Nat.cast_succ,Finset.sum_range_succ]
    rw [← h]
    simp only [cosinePhasePrimitive]
    ring

private theorem phase_cosine_sum (lam : ℝ) (m : ℕ) :
    (2*Real.sin (lam/2))*(∑ j ∈ Finset.range m, Real.cos (lam*((j:ℝ)+1))) =
      Real.sin (lam*((m:ℝ)+1/2))-Real.sin (lam/2) := by
  induction m with
  | zero => simp [div_eq_mul_inv]
  | succ m ih =>
    rw [Finset.sum_range_succ,mul_add,ih]
    have he : 2*Real.sin (lam/2)*Real.cos (lam*((m:ℝ)+1)) =
        Real.sin (lam*((m:ℝ)+3/2))-Real.sin (lam*((m:ℝ)+1/2)) := by
      have h := Real.sin_sub (lam*((m:ℝ)+1)) (lam/2)
      have h' := Real.sin_add (lam*((m:ℝ)+1)) (lam/2)
      rw [show lam*((m:ℝ)+1)-lam/2=lam*((m:ℝ)+1/2) by ring] at h
      rw [show lam*((m:ℝ)+1)+lam/2=lam*((m:ℝ)+3/2) by ring] at h'
      nlinarith [h,h']
    rw [he]
    push_cast
    rw [show (m:ℝ)+1+1/2=(m:ℝ)+3/2 by ring]
    ring

/-- Exact integer-cell integration, retaining every endpoint and slope jump. -/
theorem linearCosinePrefix_nat_eq {lam : ℝ} (hlam : lam ≠ 0)
    (hsin : Real.sin (lam/2)≠0) (m : ℕ) :
    linearCosinePrefix lam m = Real.sin (lam*(m:ℝ))*phaseCosineCoefficient lam := by
  have hsum := phase_cosine_sum lam m
  rw [show lam*((m:ℝ)+1/2)=lam*(m:ℝ)+lam/2 by ring,Real.sin_add] at hsum
  have he : (∑ j ∈ Finset.range m,Real.cos (lam*((j:ℝ)+1))) =
      (Real.sin (lam*(m:ℝ))*Real.cos (lam/2)+
        Real.cos (lam*(m:ℝ))*Real.sin (lam/2)-Real.sin (lam/2))/(2*Real.sin (lam/2)) := by
    apply (eq_div_iff (mul_ne_zero (by norm_num) hsin)).mpr
    nlinarith [hsum]
  rw [cosinePhase_prefix_nat hlam m,he,phaseCosineCoefficient]
  field_simp
  ring


/-- The first spatial moment against the sine phase. -/
def linearSineMoment (lam : ℝ) (m : ℕ) : ℝ :=
  ∫ x in (0:ℝ)..(m:ℝ), x*RHTower.bernoulliPeriodic x*Real.sin (lam*x)

/-- The second spatial moment against the cosine phase. -/
def linearSecondCosineMoment (lam : ℝ) (m : ℕ) : ℝ :=
  ∫ x in (0:ℝ)..(m:ℝ), x^2*RHTower.bernoulliPeriodic x*Real.cos (lam*x)

/-- Frequency differentiation of the literal cosine integral produces its first sine moment. -/
theorem hasDerivAt_linearCosinePrefix (lam : ℝ) (m : ℕ) :
    HasDerivAt (fun l => linearCosinePrefix l m) (-linearSineMoment lam m) lam := by
  have h := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (a:=0) (b:=(m:ℝ)) (μ:=volume)
    (F:=fun l x : ℝ => RHTower.bernoulliPeriodic x*Real.cos (l*x))
    (F':=fun l x : ℝ => -(x*RHTower.bernoulliPeriodic x*Real.sin (l*x)))
    (bound:=fun _ => (m:ℝ)+1) (Metric.ball_mem_nhds lam (by norm_num : (0:ℝ)<1))
  have hm : ∀ᶠ l in 𝓝 lam, AEStronglyMeasurable
      (fun x : ℝ => RHTower.bernoulliPeriodic x*Real.cos (l*x))
      (volume.restrict (uIoc 0 (m:ℝ))) := by
    filter_upwards with l
    exact (variation_bernoulli_continuous.mul (by fun_prop)).aestronglyMeasurable.restrict
  have hm' : AEStronglyMeasurable
      (fun x : ℝ => -(x*RHTower.bernoulliPeriodic x*Real.sin (lam*x)))
      (volume.restrict (uIoc 0 (m:ℝ))) := by
    exact (((continuous_id.mul variation_bernoulli_continuous).mul (by fun_prop)).neg).aestronglyMeasurable.restrict
  have hb : ∀ᵐ x : ℝ ∂volume, x ∈ uIoc 0 (m:ℝ) →
      ∀ l ∈ Metric.ball lam 1, ‖-(x*RHTower.bernoulliPeriodic x*Real.sin (l*x))‖ ≤ (m:ℝ)+1 := by
    filter_upwards with x hx l _
    rw [uIoc_of_le (by positivity)] at hx
    rw [norm_neg,norm_mul,norm_mul,Real.norm_eq_abs,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_pos hx.1]
    calc x*|RHTower.bernoulliPeriodic x| * |Real.sin (l*x)| ≤ (m:ℝ)*1*1 := by
          gcongr
          · exact hx.2
          · exact RHTower.abs_bernoulliPeriodic_le_one x
          · exact Real.abs_sin_le_one _
      _ ≤ (m:ℝ)+1 := by linarith
  have hd : ∀ᵐ x : ℝ ∂volume, x ∈ uIoc 0 (m:ℝ) →
      ∀ l ∈ Metric.ball lam 1,
        HasDerivAt (fun l => RHTower.bernoulliPeriodic x*Real.cos (l*x))
          (-(x*RHTower.bernoulliPeriodic x*Real.sin (l*x))) l := by
    filter_upwards with x _ l _
    convert! (((Real.hasDerivAt_cos (l*x)).comp l ((hasDerivAt_id l).mul_const x)).const_mul
      (RHTower.bernoulliPeriodic x)) using 1
    simp only [one_mul]
    ring
  have hd' := (h hm (cosinePhase_integrable lam 0 m) hm' hb intervalIntegrable_const hd).2
  simpa only [linearCosinePrefix,linearSineMoment,intervalIntegral.integral_neg] using hd'

/-- A second frequency differentiation produces the second cosine moment. -/
theorem hasDerivAt_linearSineMoment (lam : ℝ) (m : ℕ) :
    HasDerivAt (fun l => linearSineMoment l m) (linearSecondCosineMoment lam m) lam := by
  have h := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (a:=0) (b:=(m:ℝ)) (μ:=volume)
    (F:=fun l x : ℝ => x*RHTower.bernoulliPeriodic x*Real.sin (l*x))
    (F':=fun l x : ℝ => x^2*RHTower.bernoulliPeriodic x*Real.cos (l*x))
    (bound:=fun _ => ((m:ℝ)+1)^2) (Metric.ball_mem_nhds lam (by norm_num : (0:ℝ)<1))
  have hm : ∀ᶠ l in 𝓝 lam, AEStronglyMeasurable
      (fun x : ℝ => x*RHTower.bernoulliPeriodic x*Real.sin (l*x))
      (volume.restrict (uIoc 0 (m:ℝ))) := by
    filter_upwards with l
    exact ((continuous_id.mul variation_bernoulli_continuous).mul (by fun_prop)).aestronglyMeasurable.restrict
  have hm' : AEStronglyMeasurable
      (fun x : ℝ => x^2*RHTower.bernoulliPeriodic x*Real.cos (lam*x))
      (volume.restrict (uIoc 0 (m:ℝ))) := by
    exact (((continuous_id.pow 2).mul variation_bernoulli_continuous).mul (by fun_prop)).aestronglyMeasurable.restrict
  have hb : ∀ᵐ x : ℝ ∂volume, x ∈ uIoc 0 (m:ℝ) →
      ∀ l ∈ Metric.ball lam 1, ‖x^2*RHTower.bernoulliPeriodic x*Real.cos (l*x)‖ ≤ ((m:ℝ)+1)^2 := by
    filter_upwards with x hx l _
    rw [uIoc_of_le (by positivity)] at hx
    rw [norm_mul,norm_mul,Real.norm_eq_abs,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg x)]
    calc x^2*|RHTower.bernoulliPeriodic x| * |Real.cos (l*x)| ≤ ((m:ℝ)+1)^2*1*1 := by
          gcongr
          · exact hx.1.le
          · linarith [hx.2]
          · exact RHTower.abs_bernoulliPeriodic_le_one x
          · exact Real.abs_cos_le_one _
      _ = ((m:ℝ)+1)^2 := by ring
  have hd : ∀ᵐ x : ℝ ∂volume, x ∈ uIoc 0 (m:ℝ) →
      ∀ l ∈ Metric.ball lam 1,
        HasDerivAt (fun l => x*RHTower.bernoulliPeriodic x*Real.sin (l*x))
          (x^2*RHTower.bernoulliPeriodic x*Real.cos (l*x)) l := by
    filter_upwards with x _ l _
    convert! (((Real.hasDerivAt_sin (l*x)).comp l ((hasDerivAt_id l).mul_const x)).const_mul
      (x*RHTower.bernoulliPeriodic x)) using 1
    simp only [one_mul]
    ring
  exact (h hm (((continuous_id.mul variation_bernoulli_continuous).mul (by fun_prop)).intervalIntegrable 0 m)
    hm' hb intervalIntegrable_const hd).2

private theorem coefficient_hasDerivAt {lam : ℝ} (hlam : lam ≠ 0)
    (hsin : Real.sin (lam/2)≠0) :
    HasDerivAt phaseCosineCoefficient (phaseCosineCoefficientDeriv lam) lam := by
  have hc := (Real.hasDerivAt_cos (lam/2)).comp lam ((hasDerivAt_id lam).div_const 2)
  have hs := (Real.hasDerivAt_sin (lam/2)).comp lam ((hasDerivAt_id lam).div_const 2)
  have hden := (((hasDerivAt_id lam).pow 2).const_mul 2).mul hs
  have h := (hc.div hden (by positivity : 2*lam^2*Real.sin (lam/2)≠0)).sub
    ((hasDerivAt_const lam (1:ℝ)).div ((hasDerivAt_id lam).pow 3) (pow_ne_zero _ hlam))
  convert! h using 1
  dsimp [phaseCosineCoefficient,phaseCosineCoefficientDeriv]
  norm_num
  field_simp
  linear_combination (4*lam^2)*(Real.sin_sq_add_cos_sq (lam/2))


private theorem coefficient_near {lam : ℝ} (hlam : lam ≠ 0)
    (hsin : Real.sin (lam/2)≠0) :
    ∀ᶠ l in 𝓝 lam, l≠0 ∧ Real.sin (l/2)≠0 := by
  exact (eventually_ne_nhds hlam).and
    ((show ContinuousAt (fun l : ℝ => Real.sin (l/2)) lam by fun_prop).eventually_ne hsin)

private theorem linearSineMoment_eq {lam : ℝ} (hlam : lam ≠ 0)
    (hsin : Real.sin (lam/2)≠0) (m : ℕ) :
    linearSineMoment lam m = -(m:ℝ)*Real.cos (lam*(m:ℝ))*phaseCosineCoefficient lam -
      Real.sin (lam*(m:ℝ))*phaseCosineCoefficientDeriv lam := by
  have hd := coefficient_hasDerivAt hlam hsin
  have hs := (Real.hasDerivAt_sin (lam*(m:ℝ))).comp lam ((hasDerivAt_id lam).mul_const (m:ℝ))
  have he : (fun l : ℝ => linearCosinePrefix l m) =ᶠ[𝓝 lam]
      (fun l => Real.sin (l*(m:ℝ))*phaseCosineCoefficient l) := by
    filter_upwards [coefficient_near hlam hsin] with l hl
    exact linearCosinePrefix_nat_eq hl.1 hl.2 m
  have h := (hs.mul hd).congr_of_eventuallyEq he
  have heq := (hasDerivAt_linearCosinePrefix lam m).deriv.symm.trans h.deriv
  simp only [one_mul,Function.comp_apply,id_eq] at heq
  linear_combination -heq

private theorem resonance_sin_cos {lam : ℝ} (m K : ℕ)
    (hturn : lam*(m:ℝ)=2*Real.pi*K) :
    Real.sin (lam*(m:ℝ))=0 ∧ Real.cos (lam*(m:ℝ))=1 := by
  rw [hturn]
  constructor
  · simpa [mul_comm,mul_left_comm,mul_assoc] using Real.sin_add_nat_mul_two_pi 0 K
  · simpa [mul_comm,mul_left_comm,mul_assoc] using Real.cos_add_nat_mul_two_pi 0 K

/-- Exact first moment when the integer endpoint is a complete phase turn. -/
theorem linearSineMoment_at_resonance {lam : ℝ} (hlam : lam ≠ 0)
    (hsin : Real.sin (lam/2)≠0) (m K : ℕ) (hturn : lam*(m:ℝ)=2*Real.pi*K) :
    linearSineMoment lam m = -(m:ℝ)*phaseCosineCoefficient lam := by
  rw [linearSineMoment_eq hlam hsin m,(resonance_sin_cos m K hturn).1,
    (resonance_sin_cos m K hturn).2]
  ring

/-- Exact second moment, obtained by differentiating before imposing the phase coincidence. -/
theorem linearSecondCosineMoment_at_resonance {lam : ℝ} (hlam : lam ≠ 0)
    (hsin : Real.sin (lam/2)≠0) (m K : ℕ) (hturn : lam*(m:ℝ)=2*Real.pi*K) :
    linearSecondCosineMoment lam m = -2*(m:ℝ)*phaseCosineCoefficientDeriv lam := by
  have hd := coefficient_hasDerivAt hlam hsin
  have hd' : DifferentiableAt ℝ phaseCosineCoefficientDeriv lam := by
    unfold phaseCosineCoefficientDeriv
    fun_prop (disch := positivity)
  have hc := (Real.hasDerivAt_cos (lam*(m:ℝ))).comp lam ((hasDerivAt_id lam).mul_const (m:ℝ))
  have hs := (Real.hasDerivAt_sin (lam*(m:ℝ))).comp lam ((hasDerivAt_id lam).mul_const (m:ℝ))
  have he : (fun l => linearSineMoment l m) =ᶠ[𝓝 lam]
      (fun l => -((m:ℝ)*Real.cos (l*(m:ℝ))*phaseCosineCoefficient l)-
        Real.sin (l*(m:ℝ))*phaseCosineCoefficientDeriv l) := by
    filter_upwards [coefficient_near hlam hsin] with l hl
    rw [linearSineMoment_eq hl.1 hl.2 m]
    ring
  have h := ((((hc.const_mul (m:ℝ)).mul hd).neg).sub (hs.mul hd'.hasDerivAt)).congr_of_eventuallyEq he
  have heq := (hasDerivAt_linearSineMoment lam m).deriv.symm.trans h.deriv
  simp only [one_mul,Function.comp_apply,id_eq] at heq
  rw [(resonance_sin_cos m K hturn).1,(resonance_sin_cos m K hturn).2] at heq
  linear_combination heq

/-- The literal combination predicted by first variation of the arithmetic clock. -/
def resonantClockMomentCoefficient (sigma lam : ℝ) (m : ℕ) : ℝ :=
  -(sigma+2)*linearSineMoment lam m-lam/2*linearSecondCosineMoment lam m

/-- The moment combination has an explicit closed value at every integer phase coincidence. -/
theorem resonantClockMomentCoefficient_eq {sigma lam : ℝ} (hlam : lam ≠ 0)
    (hsin : Real.sin (lam/2)≠0) (m K : ℕ) (hturn : lam*(m:ℝ)=2*Real.pi*K) :
    resonantClockMomentCoefficient sigma lam m = (m:ℝ)*
      ((1-sigma)/lam^3+sigma*Real.cos (lam/2)/(2*lam^2*Real.sin (lam/2))-
        1/(4*lam*Real.sin (lam/2)^2)) := by
  rw [resonantClockMomentCoefficient,linearSineMoment_at_resonance hlam hsin m K hturn,
    linearSecondCosineMoment_at_resonance hlam hsin m K hturn,
    phaseCosineCoefficient,phaseCosineCoefficientDeriv]
  field_simp
  ring


private theorem variation_sin_sub_mul_cos_pos {x : ℝ} (hx : 0<x) (hx' : x<Real.pi) :
    0<Real.sin x-x*Real.cos x := by
  have hd (y : ℝ) : HasDerivAt (fun z : ℝ => Real.sin z-z*Real.cos z)
      (y*Real.sin y) y := by
    convert! (Real.hasDerivAt_sin y).sub ((hasDerivAt_id y).mul (Real.hasDerivAt_cos y)) using 1
    simp [id_eq]
  have hm : StrictMonoOn (fun z : ℝ => Real.sin z-z*Real.cos z) (Icc 0 Real.pi) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _) (by fun_prop)
    intro y hy
    rw [interior_Icc] at hy
    rw [(hd y).deriv]
    exact mul_pos hy.1 (Real.sin_pos_of_pos_of_lt_pi hy.1 hy.2)
  simpa using hm (show (0:ℝ)∈Icc 0 Real.pi from ⟨le_rfl,Real.pi_pos.le⟩)
    (show x∈Icc 0 Real.pi from ⟨hx.le,hx'.le⟩) hx

/-- The trigonometric quantity controlling the sign of the undamped first variation. -/
def resonantPhaseSignDefect (x : ℝ) : ℝ :=
  x^2+x*Real.sin x*Real.cos x-2*Real.sin x^2

private def resonantPhaseSignSlope (x : ℝ) : ℝ :=
  2*x+x*(Real.cos x^2-Real.sin x^2)-3*Real.sin x*Real.cos x

private theorem signSlope_deriv (x : ℝ) :
    HasDerivAt resonantPhaseSignSlope (4*Real.sin x*(Real.sin x-x*Real.cos x)) x := by
  have hi := hasDerivAt_id x
  have hs := Real.hasDerivAt_sin x
  have hc := Real.hasDerivAt_cos x
  have h := ((hi.const_mul 2).add (hi.mul ((hc.pow 2).sub (hs.pow 2)))).sub
    (((hs.const_mul 3).mul hc))
  convert! h using 1
  dsimp [resonantPhaseSignSlope]
  norm_num
  nlinarith [Real.sin_sq_add_cos_sq x]

private theorem signDefect_deriv (x : ℝ) :
    HasDerivAt resonantPhaseSignDefect (resonantPhaseSignSlope x) x := by
  have hi := hasDerivAt_id x
  have hs := Real.hasDerivAt_sin x
  have hc := Real.hasDerivAt_cos x
  have h := ((hi.pow 2).add ((hi.mul hs).mul hc)).sub ((hs.pow 2).const_mul 2)
  convert! h using 1
  dsimp [resonantPhaseSignDefect,resonantPhaseSignSlope]
  norm_num
  ring

private theorem signSlope_pos {x : ℝ} (hx : 0<x) (hx' : x<Real.pi) :
    0<resonantPhaseSignSlope x := by
  have hm : StrictMonoOn resonantPhaseSignSlope (Icc 0 Real.pi) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _) (by unfold resonantPhaseSignSlope; fun_prop)
    intro y hy
    rw [interior_Icc] at hy
    rw [(signSlope_deriv y).deriv]
    exact mul_pos (mul_pos (by norm_num) (Real.sin_pos_of_pos_of_lt_pi hy.1 hy.2))
      (variation_sin_sub_mul_cos_pos hy.1 hy.2)
  simpa [resonantPhaseSignSlope] using hm
    (show (0:ℝ)∈Icc 0 Real.pi from ⟨le_rfl,Real.pi_pos.le⟩)
    (show x∈Icc 0 Real.pi from ⟨hx.le,hx'.le⟩) hx

/-- Two derivative comparisons give a strict sign throughout the interval from zero to pi. -/
theorem resonantPhaseSignDefect_pos {x : ℝ} (hx : 0<x) (hx' : x<Real.pi) :
    0<resonantPhaseSignDefect x := by
  have hm : StrictMonoOn resonantPhaseSignDefect (Icc 0 Real.pi) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _) (by unfold resonantPhaseSignDefect; fun_prop)
    intro y hy
    rw [interior_Icc] at hy
    rw [(signDefect_deriv y).deriv]
    exact signSlope_pos hy.1 hy.2
  simpa [resonantPhaseSignDefect] using hm
    (show (0:ℝ)∈Icc 0 Real.pi from ⟨le_rfl,Real.pi_pos.le⟩)
    (show x∈Icc 0 Real.pi from ⟨hx.le,hx'.le⟩) hx

/-- The cosine coefficient is strictly negative below the first full arithmetic frequency. -/
theorem phaseCosineCoefficient_neg {lam : ℝ} (hlam : 0<lam) (hlam' : lam<2*Real.pi) :
    phaseCosineCoefficient lam<0 := by
  have hx : 0<lam/2 := by positivity
  have hx' : lam/2<Real.pi := by linarith
  have hs := Real.sin_pos_of_pos_of_lt_pi hx hx'
  have he : phaseCosineCoefficient lam =
      ((lam/2)*Real.cos (lam/2)-Real.sin (lam/2))/(8*(lam/2)^3*Real.sin (lam/2)) := by
    rw [phaseCosineCoefficient]
    field_simp
    ring
  rw [he]
  exact div_neg_of_neg_of_pos (by linarith [variation_sin_sub_mul_cos_pos hx hx']) (by positivity)

/-- The actual arithmetic moment combination is strictly negative, including the undamped boundary. -/
theorem resonantClockMomentCoefficient_neg {sigma lam : ℝ} (hsigma : -1 ≤ sigma)
    (hlam : 0<lam) (hlam' : lam<2*Real.pi) {m : ℕ} (hm : 0 < m)
    (K : ℕ) (hturn : lam*(m:ℝ)=2*Real.pi*K) :
    resonantClockMomentCoefficient sigma lam m < 0 := by
  have hx : 0<lam/2 := by positivity
  have hx' : lam/2<Real.pi := by linarith
  have hs := Real.sin_pos_of_pos_of_lt_pi hx hx'
  have he : resonantClockMomentCoefficient sigma lam m = (m:ℝ)*
      (-resonantPhaseSignDefect (lam/2)/(8*(lam/2)^3*Real.sin (lam/2)^2)+
        (sigma+1)*phaseCosineCoefficient lam) := by
    rw [resonantClockMomentCoefficient_eq hlam.ne' hs.ne' m K hturn,
      resonantPhaseSignDefect,phaseCosineCoefficient]
    field_simp
    ring
  rw [he]
  apply mul_neg_of_pos_of_neg (by exact_mod_cast hm)
  have hb : -resonantPhaseSignDefect (lam/2)/(8*(lam/2)^3*Real.sin (lam/2)^2)<0 :=
    div_neg_of_neg_of_pos (neg_neg_of_pos (resonantPhaseSignDefect_pos hx hx')) (by positivity)
  have hn := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ sigma+1 by linarith)
    (phaseCosineCoefficient_neg hlam hlam').le
  linarith

end RHTower.DeletionMixedRefinement
