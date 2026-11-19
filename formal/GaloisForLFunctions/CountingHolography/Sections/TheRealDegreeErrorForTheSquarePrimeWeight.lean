import GaloisForLFunctions.CountingHolography.Sections.RoundingTheRealDegreesOfTheFactorialInterpolant
import GaloisForLFunctions.CountingHolography.Sections.CriticalZerosSeparateThePrimeProfileFromFactorialKernels
import Mathlib.Analysis.Calculus.Deriv.Support
import GaloisForLFunctions.RHTower.PrimeCountingLiLandau
import GaloisForLFunctions.CountingHolography.Sections.TheSquareRootContractionInTheStirlingRemainder

/-! # Real-degree interpolation for the actual square prime weight

The spline weight and its logarithmic derivative have compact support
away from zero. The Mertens exponent bounds the height and integrated
error of the canonical factorial interpolant.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections
open Finset Filter Topology MeasureTheory ArithmeticOfSquareRootPrecision
open _root_.RHTower _root_.RHTower.WeilDeletion BiScaleUncertainty.ChebyshevGauge
open ArithmeticWeightTheory ArithmeticCastelnuovoSeveri ArithmeticOrientationGeometry

private abbrev a := Real.exp (-8)
private abbrev b := Real.exp (8+Real.log 4)

/-- The positive-argument prime test extended by zero on the negative axis. -/
def squareFactorialTest (x : ℝ) := if 0 < x then (squarePrimeWeight x).re else 0

private theorem test_zero {x : ℝ} (h : x ∉ Set.Icc a b) : squareFactorialTest x = 0 := by
  by_cases hx : 0 < x
  · rw [squareFactorialTest,if_pos hx,squarePrimeWeight_zero_outside hx h,Complex.zero_re]
  · simp [squareFactorialTest,hx]

private theorem test_compact : HasCompactSupport squareFactorialTest := by
  apply (isCompact_Icc (a := a) (b := b)).of_isClosed_subset isClosed_closure
  refine closure_minimal ?_ isClosed_Icc
  intro x hx
  by_contra h
  exact hx (test_zero h)

private theorem test_regular : ContDiff ℝ 2 squareFactorialTest := by
  have hH : ContDiff ℝ 2 splineAutoCorr := by
    rw [show splineAutoCorr = upow 1 7 from funext splineAutoCorr_eq_eight_boxes]
    exact (contDiff_upow one_pos 6).of_le (by norm_num)
  have hF : ContDiff ℝ 2 squareLogProfile := (contDiff_const.mul hH).sub
    (hH.comp (contDiff_id.sub contDiff_const))
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : 0 < x
  · have hl := (Real.contDiffAt_log (n := 2)).mpr hx.ne'
    have hr : ContDiffAt ℝ 2 (fun y => Real.exp (-Real.log y/2)*squareLogProfile (Real.log y)) x :=
      (Real.contDiff_exp.contDiffAt.comp x (hl.neg.div_const _)).mul (hF.contDiffAt.comp x hl)
    apply hr.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hx] with y hy
    have hy' : 0 < y := hy
    have hre : (Complex.exp (-↑(Real.log y) / 2)).re = Real.exp (-Real.log y / 2) := by
      rw [show -(↑(Real.log y) : ℂ) / 2 = ((-Real.log y / 2 : ℝ) : ℂ) by push_cast; ring,
        Complex.exp_ofReal_re]
    simp [squareFactorialTest,hy',squarePrimeWeight,hre]
  · apply (contDiffAt_const (c := (0:ℝ))).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds ((le_of_not_gt hx).trans_lt (Real.exp_pos (-8)))] with y hy
    exact test_zero (fun h => hy.not_ge h.1)

private theorem scaled_test_data : ∃ L : ℝ, 0 ≤ L ∧ ∀ {X : ℝ}, 0 < X →
    let W := fun x : ℝ => squareFactorialTest (x/X)
    let D := fun x : ℝ => deriv squareFactorialTest (x/X)/X
    (∀ x, b*X < x → W x=0) ∧ (∀ x, 0 < x → HasDerivAt W (D x) x) ∧
    (∀ u v : ℝ, 0 < u → u ≤ v → |W v-W u| ≤ (L/X)*(v-u)) ∧
    (∀ u v : ℝ, 0 < u → u ≤ v → |v*D v-u*D u| ≤ (L/X)*(v-u)) := by
  let G := fun x : ℝ => x*deriv squareFactorialTest x
  have hG : ContDiff ℝ 1 G := contDiff_id.mul (test_regular.deriv')
  have hGc : HasCompactSupport G := test_compact.deriv.mul_left
  obtain ⟨L,hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport test_compact test_regular (by norm_num)
  obtain ⟨K,hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hGc hG (by norm_num)
  refine ⟨max (L:ℝ) K, L.coe_nonneg.trans (le_max_left _ _),fun {X} hX => ⟨?_,?_,?_,?_⟩⟩
  · intro x hx
    exact test_zero (fun H => ((lt_div_iff₀ hX).mpr hx).not_ge H.2)
  · intro x _
    have hd := (test_regular.differentiable (by norm_num) (x/X)).hasDerivAt.comp x ((hasDerivAt_id x).div_const X)
    simpa only [Function.comp_def,id_eq,div_eq_mul_inv,one_mul] using hd
  · intro u v _ huv
    have hh := hL.dist_le_mul (v/X) (u/X)
    rw [Real.dist_eq,Real.dist_eq,← sub_div,abs_div,abs_of_pos hX,abs_of_nonneg (sub_nonneg.mpr huv)] at hh
    exact hh.trans ((mul_le_mul_of_nonneg_right (le_max_left _ _) (div_nonneg (sub_nonneg.mpr huv) hX.le)).trans_eq (by ring))
  · intro u v _ huv
    have hh := hK.dist_le_mul (v/X) (u/X)
    rw [Real.dist_eq,Real.dist_eq,← sub_div,abs_div,abs_of_pos hX,abs_of_nonneg (sub_nonneg.mpr huv)] at hh
    change |v*(deriv squareFactorialTest (v/X)/X)-u*(deriv squareFactorialTest (u/X)/X)| ≤ _
    rw [show v*(deriv squareFactorialTest (v/X)/X)=G (v/X) by dsimp only [G]; ring,
      show u*(deriv squareFactorialTest (u/X)/X)=G (u/X) by dsimp only [G]; ring]
    exact hh.trans ((mul_le_mul_of_nonneg_right (le_max_right _ _) (div_nonneg (sub_nonneg.mpr huv) hX.le)).trans_eq (by ring))

/-- The canonical real-degree factorial reading at square-profile scale X. -/
def squareFactorialInterpolant (X y : ℝ) := roundedFactorialReading (fun t => squareFactorialTest (t/X)) (b*X) y

theorem squareFactorialInterpolant_exact {X : ℝ} (hX : 0 < X) {n : ℕ} (hn : 0 < n) :
    squareFactorialInterpolant X n = (squarePrimeWeight ((n:ℝ)/X)).re := by
  obtain ⟨_,_,hs⟩ := scaled_test_data
  rw [squareFactorialInterpolant,roundedFactorialReading_nat _ _ (hs hX).1 hn,squareFactorialTest,
    if_pos (div_pos (Nat.cast_pos.mpr hn) hX)]

/-- Uniform quadratic decay in the positive real degree, without a
cancellation estimate for Möbius. -/
theorem squareFactorialInterpolant_error : ∃ D : ℝ, 0 ≤ D ∧ ∀ {X y : ℝ}, 0 < X → 0 < y →
    |squareFactorialInterpolant X y-(squarePrimeWeight (y/X)).re| ≤ D*X/y^2 := by
  obtain ⟨L,hL,hs⟩ := scaled_test_data
  refine ⟨2*L*b^2,by positivity,fun {X y} hX hy => ?_⟩
  obtain ⟨hz,_,hl,_⟩ := hs hX
  have h := roundedFactorialReading_error (mul_nonneg (Real.exp_pos _).le hX.le) (div_nonneg hL hX.le) hz hl hy
  change |squareFactorialInterpolant X y-squareFactorialTest (y/X)| ≤ _ at h
  rw [squareFactorialTest,if_pos (div_pos hy hX)] at h
  exact h.trans_eq (by field_simp [hX.ne',hy.ne'])

/-- Under a Mertens power bound the interpolant controls both small
degrees and the integrable tail at the same scale. -/
theorem squareFactorialInterpolant_mertens_error {σ C : ℝ} (hσ : 0 < σ) (hC : 0 ≤ C)
    (hM : ∀ n : ℕ, 0 < n → |mertens n| ≤ C*(n:ℝ)^σ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ X : ℝ in atTop, ∀ {y : ℝ}, 0 < y →
      |squareFactorialInterpolant X y-(squarePrimeWeight (y/X)).re| ≤
        if y ≤ 1 then D*X^σ else D*X^σ/y^(1+σ) := by
  obtain ⟨L,hL,hs⟩ := scaled_test_data
  let Z := factorialInterpolationPSeries σ
  let D := Z*(C*L*b)*b^σ
  have hZ : 0 ≤ Z := tsum_nonneg fun _ => inv_nonneg.mpr (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  refine ⟨D,by dsimp only [D]; positivity,?_⟩
  filter_upwards [eventually_gt_atTop (1/a)] with X hX₀
  have hX := (one_div_pos.mpr (Real.exp_pos _)).trans hX₀
  have hB : 0 ≤ b*X := mul_nonneg (Real.exp_pos _).le hX.le
  obtain ⟨hz,hd,_,hl⟩ := hs hX
  intro y hy
  change |roundedFactorialReading _ _ y-(squarePrimeWeight (y/X)).re| ≤ _
  rw [← show squareFactorialTest (y/X)=(squarePrimeWeight (y/X)).re from if_pos (div_pos hy hX)]
  have hscale : C*(L/X)*(b*X)=C*L*b := by field_simp [hX.ne']
  by_cases h : y ≤ 1
  · rw [if_pos h]
    have hsmall (t : ℝ) (_ : 0 < t) (ht : t ≤ 1) : squareFactorialTest (t/X)=0 := by
      have ht' : t < a*X := ht.trans_lt (by simpa only [mul_comm] using (div_lt_iff₀ (Real.exp_pos _)).mp hX₀)
      exact test_zero (fun H => ((div_lt_iff₀ hX).mpr ht').not_ge H.1)
    refine (roundedFactorialReading_mertens_small hB (div_nonneg hL hX.le) hC hσ hz hd hl hM hsmall hy h).trans_eq ?_
    rw [hscale,Real.mul_rpow (Real.exp_pos _).le hX.le]
    dsimp only [D,Z]; ring
  · rw [if_neg h]
    refine (roundedFactorialReading_mertens_error hB (div_nonneg hL hX.le) hC hσ hz hd hl hM hy).trans_eq ?_
    rw [hscale,Real.div_rpow hB hy.le,Real.mul_rpow (Real.exp_pos _).le hX.le,Real.rpow_add hy,Real.rpow_one]
    dsimp only [D,Z]; ring

private def errorAt (X y : ℝ) := |squareFactorialInterpolant X y-(squarePrimeWeight (y/X)).re|

private theorem errorAt_measurable {X : ℝ} (hX : 0 < X) :
    AEStronglyMeasurable (errorAt X) (volume.restrict (Set.Ioi 0)) := by
  let c := fun j : ℕ => mobiusFactorialSample (fun t => squareFactorialTest (t/X)) (b*X) j -
    mobiusFactorialSample (fun t => squareFactorialTest (t/X)) (b*X) (j+1:ℕ)
  let F := fun y : ℝ => |(∑ j ∈ Icc 1 ⌊b*X⌋₊, c j*(⌊(j:ℝ)/y⌋₊:ℝ)) - squareFactorialTest (y/X)|
  have hw : Measurable squareFactorialTest := test_regular.continuous.measurable
  have hF : Measurable F := by dsimp only [F]; fun_prop
  apply hF.aestronglyMeasurable.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  dsimp only [F,errorAt,squareFactorialInterpolant]
  rw [roundedFactorialReading_eq_floor_sum _ (mul_nonneg (Real.exp_pos _).le hX.le) hy,
    show squareFactorialTest (y/X)=_ from if_pos (div_pos hy hX)]

/-- Beyond K the scaled integral of the unconditional rounding error is
at most a constant divided by K. -/
theorem squareFactorialInterpolant_integral_tail : ∃ D : ℝ, 0 ≤ D ∧ ∀ {X K : ℝ}, 0 < X → 0 < K →
    (∫ y in Set.Ioi K, |squareFactorialInterpolant X y-(squarePrimeWeight (y/X)).re|)/X ≤ D/K := by
  obtain ⟨D,hD,hd⟩ := squareFactorialInterpolant_error
  refine ⟨D,hD,fun {X K} hX hK => ?_⟩
  have hg := (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2:ℝ) < -1) hK).const_mul (D*X)
  have he : ∀ᵐ y ∂volume.restrict (Set.Ioi K), errorAt X y ≤ D*X*y^(-2:ℝ) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    simpa only [errorAt,Real.rpow_neg (hK.trans hy).le,Real.rpow_two,div_eq_mul_inv] using hd hX (hK.trans hy)
  have h := integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => abs_nonneg _) hg he
  change (∫ y in Set.Ioi K, errorAt X y)/X ≤ _
  rw [integral_const_mul,integral_Ioi_rpow_of_lt (by norm_num) hK] at h
  norm_num only [show (-2:ℝ)+1 = -1 by norm_num,Real.rpow_neg_one,div_neg,div_one,neg_neg] at h
  exact (div_le_div_of_nonneg_right h hX.le).trans_eq (by field_simp [hX.ne',hK.ne'])

/-- The scaled L¹ error is O(X^(σ−1)) under the positive Mertens power
bound, with finite mass for the actual interpolant. -/
theorem squareFactorialInterpolant_mertens_integral {σ C : ℝ} (hσ : 0 < σ) (hC : 0 ≤ C)
    (hM : ∀ n : ℕ, 0 < n → |mertens n| ≤ C*(n:ℝ)^σ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ X : ℝ in atTop,
      IntegrableOn (errorAt X) (Set.Ioi 0) ∧
      (∫ y in Set.Ioi 0, errorAt X y)/X ≤ A*X^(σ-1) := by
  obtain ⟨D,hD,h⟩ := squareFactorialInterpolant_mertens_error hσ hC hM
  refine ⟨D*(1+1/σ),by positivity,?_⟩
  filter_upwards [h,eventually_gt_atTop (0:ℝ)] with X h hX
  let E := D*X^σ
  have hE : 0 ≤ E := mul_nonneg hD (Real.rpow_nonneg hX.le _)
  have h₁ : ∀ᵐ y ∂volume.restrict (Set.Ioc 0 1), errorAt X y ≤ E := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
    simpa only [errorAt,E,if_pos hy.2] using h hy.1
  have h₂ : ∀ᵐ y ∂volume.restrict (Set.Ioi 1), errorAt X y ≤ E*y^(-(1+σ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    change 1 < y at hy
    have hy' : 0 < y := zero_lt_one.trans hy
    simpa only [errorAt,E,if_neg (not_le.mpr hy),Real.rpow_neg hy'.le,div_eq_mul_inv] using h hy'
  have hc : IntegrableOn (fun _ : ℝ => E) (Set.Ioc 0 1) := integrableOn_const
    (by simp : volume (Set.Ioc (0:ℝ) 1) ≠ ⊤)
  have hs : -(1+σ) < -1 := by linarith only [hσ]
  have hr := (integrableOn_Ioi_rpow_of_lt hs (by norm_num : (0:ℝ)<1)).const_mul E
  have hm := errorAt_measurable hX
  have hinner : IntegrableOn (errorAt X) (Set.Ioc 0 1) := hc.mono'
    (hm.mono_measure (Measure.restrict_mono_set _ Set.Ioc_subset_Ioi_self))
    (h₁.mono fun y hy => by simpa only [errorAt,Real.norm_eq_abs,abs_abs] using hy)
  have houter : IntegrableOn (errorAt X) (Set.Ioi 1) := hr.mono'
    (hm.mono_measure (Measure.restrict_mono_set _ (Set.Ioi_subset_Ioi zero_le_one)))
    (h₂.mono fun y hy => by simpa only [errorAt,Real.norm_eq_abs,abs_abs] using hy)
  have heq : Set.Ioc (0:ℝ) 1 ∪ Set.Ioi 1 = Set.Ioi 0 := by ext y; simp only [Set.mem_union,Set.mem_Ioc,Set.mem_Ioi]; constructor <;> intro hy <;> rcases le_or_gt y 1 with h|h <;> grind
  refine ⟨heq ▸ hinner.union houter,?_⟩
  rw [← heq,setIntegral_union (Set.disjoint_left.mpr fun y hy hy' => hy'.not_ge hy.2) measurableSet_Ioi hinner houter]
  have hi := integral_mono_ae hinner hc h₁
  have ho := integral_mono_ae houter hr h₂
  rw [setIntegral_const,Real.volume_real_Ioc_of_le zero_le_one,sub_zero,one_smul] at hi
  rw [integral_const_mul,integral_Ioi_rpow_of_lt hs zero_lt_one,Real.one_rpow] at ho
  have hp : -(1+σ)+1 = -σ := by ring
  rw [hp,neg_div_neg_eq] at ho
  refine (div_le_div_of_nonneg_right (add_le_add hi ho) hX.le).trans_eq ?_
  dsimp only [E]
  rw [Real.rpow_sub hX,Real.rpow_one]
  ring

/-- The unscaled Möbius inverse of the square prime test. -/
def squareFactorialMobiusWindow (x : ℝ) : ℂ := (mobiusFactorialSample squareFactorialTest b x : ℝ)

private theorem window_off {x : ℝ} (hx : b < x) : squareFactorialMobiusWindow x=0 := by
  have hp := (Real.exp_pos _).trans hx
  simp [squareFactorialMobiusWindow,mobiusFactorialSample,Nat.floor_eq_zero.mpr ((div_lt_one hp).mpr hx)]

private theorem window_zero : squareFactorialMobiusWindow 0=0 := by
  simp [squareFactorialMobiusWindow,mobiusFactorialSample]

private theorem test_end (x : ℝ) (hx : b < x) : squareFactorialTest x=0 :=
  test_zero fun h => hx.not_ge h.2

private theorem window_local : LocallyIntegrableOn squareFactorialMobiusWindow (Set.Ioi 0) := by
  apply ContinuousOn.locallyIntegrableOn _ measurableSet_Ioi
  intro x hx
  have hd := hasDerivAt_mobiusFactorialSample (Real.exp_pos _).le hx test_end
    (fun v _ => (test_regular.differentiable (by norm_num) v).hasDerivAt)
  exact (Complex.continuous_ofReal.continuousAt.comp hd.continuousAt).continuousWithinAt

private theorem window_top (r : ℝ) :
    Asymptotics.IsBigO atTop squareFactorialMobiusWindow (fun t : ℝ => t^(-r)) := by
  apply Asymptotics.IsBigO.of_bound 0
  filter_upwards [eventually_gt_atTop b] with t ht
  rw [window_off ht,norm_zero,zero_mul]

private theorem window_at_zero {σ C : ℝ} (hs : 0 ≤ σ) (hc : 0 ≤ C)
    (hm : ∀ n : ℕ, 0 < n → |mertens n| ≤ C*(n:ℝ)^σ) :
    Asymptotics.IsBigO (nhdsWithin 0 (Set.Ioi 0)) squareFactorialMobiusWindow (fun t : ℝ => t^(-σ)) := by
  obtain ⟨L,hL,hdata⟩ := scaled_test_data
  have hl (u v : ℝ) (hu : 0 < u) (hv : u ≤ v) : |squareFactorialTest v-squareFactorialTest u| ≤ L*(v-u) := by
    simpa only [div_one] using (hdata (X := 1) one_pos).2.2.1 u v hu hv
  apply Asymptotics.IsBigO.of_bound (C*L*b*b^σ)
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht' : 0 < t := ht
  have h := mobiusFactorialSample_mertens_bound (Real.exp_pos _).le hL hc hs test_end hl hm ht'
  rw [Real.div_rpow (Real.exp_pos _).le ht'.le] at h
  rw [squareFactorialMobiusWindow,Complex.norm_real,Real.norm_eq_abs,Real.norm_of_nonneg (Real.rpow_nonneg ht'.le _),
    Real.rpow_neg ht'.le]
  exact h.trans_eq (by ring)

private theorem dilated_norm_integral (g : ℝ → ℂ) (s : ℂ) {a : ℝ} (ha : 0 < a) :
    (∫ x in Set.Ioi (0:ℝ), ‖(x:ℂ)^(s-1) • g (a*x)‖) =
      a^(-s.re)*(∫ x in Set.Ioi (0:ℝ), ‖(x:ℂ)^(s-1) • g x‖) := by
  let G := fun x : ℝ => ‖(x:ℂ)^(s-1) • g x‖
  have he (x : ℝ) (hx : x ∈ Set.Ioi (0:ℝ)) :
      ‖(x:ℂ)^(s-1) • g (a*x)‖=a^(1-s.re)*G (a*x) := by
    simp only [G,norm_smul,Complex.norm_cpow_eq_rpow_re_of_pos hx,
      Complex.norm_cpow_eq_rpow_re_of_pos (mul_pos ha hx),Complex.sub_re,Complex.one_re,
      Real.mul_rpow ha.le hx.le]
    rw [← mul_assoc,← mul_assoc,← Real.rpow_add ha,show 1-s.re+(s.re-1)=0 by ring,Real.rpow_zero,one_mul]
  rw [setIntegral_congr_fun measurableSet_Ioi he,integral_const_mul,integral_comp_mul_left_Ioi G _ ha,
    mul_zero,smul_eq_mul,← mul_assoc,← Real.rpow_neg_one,← Real.rpow_add ha,
    show 1-s.re+(-1) = -s.re by ring]

private theorem window_times_zeta {s : ℂ} (hs : 1 < s.re) (hg : MellinConvergent squareFactorialMobiusWindow s) :
    riemannZeta s*mellin squareFactorialMobiusWindow s=mellin squarePrimeWeight s := by
  let g := squareFactorialMobiusWindow
  let F := fun (n : ℕ) (t : ℝ) => (t:ℂ)^(s-1) • g (n*t)
  have hFi (n : ℕ) : IntegrableOn (F n) (Set.Ioi 0) := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [F,g,window_zero]
    · exact (MellinConvergent.comp_mul_left (Nat.cast_pos.mpr hn)).mpr hg
  let A := ∫ x in Set.Ioi (0:ℝ), ‖(x:ℂ)^(s-1) • g x‖
  have hn (n : ℕ) : (∫ x in Set.Ioi (0:ℝ), ‖F n x‖)=(1/(n:ℝ)^s.re)*A := by
    rcases Nat.eq_zero_or_pos n with rfl | hp
    · simp [F,g,window_zero,Real.zero_rpow (zero_lt_one.trans hs).ne']
    · simpa only [F,Real.rpow_neg (Nat.cast_nonneg n),one_div] using
        dilated_norm_integral g s (Nat.cast_pos.mpr hp)
  have hi := integral_tsum_of_summable_integral_norm hFi
    (((Real.summable_one_div_nat_rpow.mpr hs).mul_right A).congr fun n => (hn n).symm)
  have hterm (n : ℕ) : (∫ t in Set.Ioi (0:ℝ), F n t) = (1/(n:ℂ)^s)*mellin g s := by
    rcases Nat.eq_zero_or_pos n with rfl | hp
    · simp [F,g,window_zero,Complex.zero_cpow (Complex.ne_zero_of_one_lt_re hs)]
    · simpa only [F,mellin,Complex.ofReal_natCast,Complex.cpow_neg,one_div,smul_eq_mul] using
        mellin_comp_mul_left g s (Nat.cast_pos.mpr hp : 0 < (n:ℝ))
  simp_rw [hterm] at hi
  rw [tsum_mul_right,← zeta_eq_tsum_one_div_nat_cpow hs] at hi
  refine hi.trans (setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_)
  change 0 < t at ht
  change (∑' n : ℕ, (t:ℂ)^(s-1) • g (n*t))=(t:ℂ)^(s-1) • squarePrimeWeight t
  simp only [smul_eq_mul,tsum_mul_left]
  congr 1
  let N := ⌊b/t⌋₊
  have hz (n : ℕ) (hne : n ∉ Icc 1 N) : g (n*t)=0 := by
    rcases Nat.eq_zero_or_pos n with rfl | hp
    · simp [g,window_zero]
    · have he : N < n := lt_of_not_ge fun h => hne (mem_Icc.mpr ⟨hp,h⟩)
      exact window_off ((div_lt_iff₀ ht).mp (Nat.lt_of_floor_lt he))
  rw [tsum_eq_sum hz]
  change (∑ n ∈ Icc 1 N, ((mobiusFactorialSample squareFactorialTest b (n*t):ℝ):ℂ))=_
  rw [← Complex.ofReal_sum,sum_mobiusFactorialSample _ _ test_end ht,squareFactorialTest,if_pos ht]
  rfl

private theorem sample_window_trivial {n : ℕ} (_ : 0 < n) : |mertens n| ≤ 1*(n:ℝ)^(1:ℝ) := by
  rw [Real.rpow_one,one_mul]
  refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum (g := fun _ => (1:ℝ)) (fun d _ => ?_)).trans_eq ?_)
  · exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d))
  · simp

/-- On the half-plane of absolute convergence the Mellin transform of the
canonical Möbius sample window is the square prime transform divided by zeta. -/
theorem mellin_squareFactorialMobiusWindow {s : ℂ} (hs : 1 < s.re) :
    mellin squareFactorialMobiusWindow s=mellin squarePrimeWeight s/riemannZeta s := by
  have hg := mellinConvergent_of_isBigO_rpow window_local (window_top (s.re+1)) (lt_add_one _)
    (window_at_zero zero_le_one zero_le_one (fun n hn => sample_window_trivial hn)) hs
  exact (eq_div_iff (riemannZeta_ne_zero_of_one_lt_re hs)).mpr ((mul_comm _ _).trans (window_times_zeta hs hg))

private theorem squareFactorialMellin_one : mellin squarePrimeWeight 1=0 := by
  simpa only [mellin,sub_self,Complex.cpow_zero,one_smul] using squarePrimeWeight_mean_zero

/-- A sublinear Mertens bound makes both the zeroth and first logarithmic
moments of the Möbius sample window vanish. -/
theorem squareFactorialMobiusWindow_moments {σ C : ℝ} (hs : 0 ≤ σ) (hs' : σ < 1) (hc : 0 ≤ C)
    (hm : ∀ n : ℕ, 0 < n → |mertens n| ≤ C*(n:ℝ)^σ) :
    (∫ x in Set.Ioi (0:ℝ), squareFactorialMobiusWindow x)=0 ∧
    (∫ x in Set.Ioi (0:ℝ), Real.log x • squareFactorialMobiusWindow x)=0 := by
  let g := squareFactorialMobiusWindow
  let M := mellin g
  let W := mellin squarePrimeWeight
  let U := {s : ℂ | σ < s.re}
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hd (s : ℂ) (hsU : s ∈ U) := (mellin_hasDerivAt_of_isBigO_rpow window_local (window_top (s.re+1))
    (lt_add_one _) (window_at_zero hs hc hm) hsU).2
  have hM : AnalyticOnNhd ℂ M U :=
    (show DifferentiableOn ℂ M U from fun s hsU => (hd s hsU).differentiableAt.differentiableWithinAt).analyticOnNhd hU
  have hW := differentiable_mellin_squarePrimeWeight.differentiableOn.analyticOnNhd isOpen_univ
  let L := fun s : ℂ => zetaResidueUnit s*M s
  let R := fun s : ℂ => (s-1)*W s
  have hL : AnalyticOnNhd ℂ L U := fun s h => (analyticAt_zetaResidueUnit s).mul (hM s h)
  have hR : AnalyticOnNhd ℂ R U := fun s _ => (analyticAt_id.sub analyticAt_const).mul (hW _ (Set.mem_univ _))
  have h2 : (2:ℂ) ∈ U := by change σ < (2:ℂ).re; norm_num; linarith only [hs']
  have h1 : (1:ℂ) ∈ U := hs'
  have hright : ∀ᶠ z : ℂ in 𝓝 2, 1 < z.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num : (1:ℝ) < (2:ℂ).re)
  have he := hL.eqOn_of_preconnected_of_eventuallyEq hR (convex_halfSpace_re_gt σ).isPreconnected h2 (by
    filter_upwards [hright] with z hz
    have hz' : z ≠ 1 := by rintro rfl; norm_num at hz
    dsimp only [L,R,M,W,g]
    rw [zetaResidueUnit,Function.update_of_ne hz',mellin_squareFactorialMobiusWindow hz]
    field_simp [riemannZeta_ne_zero_of_one_lt_re hz])
  have hzero : M 1=0 := by simpa only [L,R,zetaResidueUnit_one,one_mul,sub_self,zero_mul] using he h1
  have hW₀ : W 1=0 := squareFactorialMellin_one
  have hRL : R =ᶠ[𝓝 (1:ℂ)] L := eventually_of_mem (hU.mem_nhds h1) (fun z hz => (he hz).symm)
  have hder := (((analyticAt_zetaResidueUnit 1).differentiableAt.hasDerivAt).mul (hd 1 h1)).congr_of_eventuallyEq hRL
  have h := hder.unique (((hasDerivAt_id (1:ℂ)).sub_const 1).mul (differentiable_mellin_squarePrimeWeight 1).hasDerivAt)
  change deriv zetaResidueUnit 1*M 1+zetaResidueUnit 1*mellin (fun x => Real.log x • g x) 1 =
    1*W 1+((1:ℂ)-1)*deriv W 1 at h
  simp only [hzero,hW₀,zetaResidueUnit_one,mul_zero,one_mul,zero_add,sub_self,zero_mul,add_zero] at h
  simpa only [M,g,mellin,sub_self,Complex.cpow_zero,one_smul] using And.intro hzero h

private def floorDefect := (Set.Ioc (0:ℝ) 1).indicator fun x => (⌊1/x⌋₊:ℝ)-1/x

private theorem floorDefect_integrable : Integrable floorDefect := by
  have hc : IntegrableOn (fun _ : ℝ => (1:ℝ)) (Set.Ioc 0 1) := integrableOn_const (by simp)
  apply IntegrableOn.integrable_indicator _ measurableSet_Ioc
  have hm : Measurable (fun x : ℝ => (⌊1/x⌋₊:ℝ)-1/x) := by fun_prop
  apply hc.mono' hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  rw [Real.norm_eq_abs,abs_of_nonpos (sub_nonpos.mpr (Nat.floor_le (one_div_nonneg.mpr hx.1.le)))]
  linarith only [Nat.lt_floor_add_one (1/x)]

private def balancedFloor (j : ℕ) (x : ℝ) := (⌊(j:ℝ)/x⌋₊:ℝ)-(j:ℝ)*(⌊1/x⌋₊:ℝ)

/-- Subtracting j copies of the unit floor removes the singular term.
The remaining interval integral is j times the logarithm of j. -/
private theorem balancedFloor_integral {j : ℕ} (hj : 0 < j) :
    IntegrableOn (balancedFloor j) (Set.Ioi 0) ∧
    (∫ x in Set.Ioi (0:ℝ), balancedFloor j x)=(j:ℝ)*Real.log j := by
  have hj' : (0:ℝ) < j := Nat.cast_pos.mpr hj
  have hj₁ : (1:ℝ) ≤ j := by exact_mod_cast hj
  let J := Set.Ioc (1:ℝ) j
  let f := fun x : ℝ => floorDefect ((j:ℝ)⁻¹*x)
  let g := fun x : ℝ => (j:ℝ)*floorDefect x
  let u := J.indicator (fun x : ℝ => x⁻¹)
  have hf : IntegrableOn f (Set.Ioi 0) := (integrableOn_Ioi_comp_mul_left_iff floorDefect _ (inv_pos.mpr hj')).mpr
    (by simpa only [mul_zero] using floorDefect_integrable.integrableOn (s := Set.Ioi 0))
  have hg : IntegrableOn g (Set.Ioi 0) := (floorDefect_integrable.const_mul _).integrableOn
  have hu₀ : IntegrableOn (fun x : ℝ => x⁻¹) J :=
    (((continuousOn_id.inv₀ (fun x (hx : x ∈ Set.Icc (1:ℝ) j) => (zero_lt_one.trans_le hx.1).ne')).integrableOn_Icc).mono_set
      Set.Ioc_subset_Icc_self)
  have hu : IntegrableOn u (Set.Ioi 0) := (hu₀.integrable_indicator measurableSet_Ioc).integrableOn
  have he (x : ℝ) (hx : x ∈ Set.Ioi (0:ℝ)) : balancedFloor j x=f x-g x+j*u x := by
    change 0 < x at hx
    have hx' : 0 < (j:ℝ)⁻¹*x := mul_pos (inv_pos.mpr hj') hx
    have ha : 1/((j:ℝ)⁻¹*x)=(j:ℝ)/x := by field_simp [hj'.ne',hx.ne']
    have hiff : (j:ℝ)⁻¹*x ≤ 1 ↔ x ≤ j := by rw [← div_eq_inv_mul,div_le_iff₀ hj',one_mul]
    by_cases h : x ≤ 1
    · simp only [balancedFloor,f,g,u,floorDefect,Set.indicator_of_mem
        (show (j:ℝ)⁻¹*x ∈ Set.Ioc 0 1 from ⟨hx',hiff.mpr (h.trans hj₁)⟩),
        Set.indicator_of_mem (show x ∈ Set.Ioc (0:ℝ) 1 from ⟨hx,h⟩),
        Set.indicator_of_notMem (show x ∉ J from fun hh => hh.1.not_ge h),ha]
      ring
    · have hx1 := lt_of_not_ge h
      have hz : ⌊1/x⌋₊=0 := Nat.floor_eq_zero.mpr ((div_lt_one hx).mpr hx1)
      by_cases h₂ : x ≤ j
      · simp only [balancedFloor,f,g,u,floorDefect,Set.indicator_of_mem
            (show (j:ℝ)⁻¹*x ∈ Set.Ioc 0 1 from ⟨hx',hiff.mpr h₂⟩),
            Set.indicator_of_notMem (show x ∉ Set.Ioc (0:ℝ) 1 from fun hh => h hh.2),
            Set.indicator_of_mem (show x ∈ J from ⟨hx1,h₂⟩),ha,hz,Nat.cast_zero]
        ring
      · have hz' : ⌊(j:ℝ)/x⌋₊=0 := Nat.floor_eq_zero.mpr ((div_lt_one hx).mpr (lt_of_not_ge h₂))
        simp only [balancedFloor,f,g,u,floorDefect,Set.indicator_of_notMem
          (show (j:ℝ)⁻¹*x ∉ Set.Ioc 0 1 from fun hh => h₂ (hiff.mp hh.2)),
          Set.indicator_of_notMem (show x ∉ Set.Ioc (0:ℝ) 1 from fun hh => h hh.2),
          Set.indicator_of_notMem (show x ∉ J from fun hh => h₂ hh.2),hz,hz',Nat.cast_zero,
          mul_zero,sub_zero,add_zero]
  refine ⟨((hf.sub hg).add (hu.const_mul _)).congr_fun (fun x hx => (he x hx).symm) measurableSet_Ioi,?_⟩
  have hfgint : IntegrableOn (fun x => f x-g x) (Set.Ioi 0) := hf.sub hg
  rw [setIntegral_congr_fun measurableSet_Ioi he,integral_add hfgint (hu.const_mul (j:ℝ)),
    integral_sub hf hg]
  have hfg : (∫ x in Set.Ioi (0:ℝ), f x)=(∫ x in Set.Ioi (0:ℝ), g x) := by
    simp only [f,g,integral_comp_mul_left_Ioi floorDefect _ (inv_pos.mpr hj'),mul_zero,
      inv_inv,smul_eq_mul,integral_const_mul]
  rw [hfg,sub_self,zero_add,integral_const_mul]
  congr 1
  rw [show (∫ x in Set.Ioi (0:ℝ), u x)=∫ x in Set.Ioc (1:ℝ) j, x⁻¹ by
        rw [show u=J.indicator (fun x : ℝ => x⁻¹) from rfl,integral_indicator measurableSet_Ioc,
          Measure.restrict_restrict measurableSet_Ioc,Set.inter_eq_left.mpr (show Set.Ioc (1:ℝ) j ⊆ Set.Ioi 0 from fun x hx => zero_lt_one.trans hx.1)],
      ← intervalIntegral.integral_of_le hj₁,integral_inv_of_pos zero_lt_one hj',div_one]

private def coefficients (X : ℝ) (j : ℕ) :=
  let f := mobiusFactorialSample (fun x => squareFactorialTest (x/X)) (b*X)
  f j-f (j+1:ℕ)

/-- The two signed contributions of the explicit real factorial presentation. -/
def squareFactorialEntropy (X : ℝ) :=
  ∑ j ∈ Icc 1 ⌊b*X⌋₊, coefficients X j*((j:ℝ)*Real.log j)

def squareFactorialStirlingError (X : ℝ) :=
  ∑ j ∈ Icc 1 ⌊b*X⌋₊, coefficients X j*(Real.log (j.factorial:ℝ)-(j:ℝ)*Real.log j)

private theorem interpolant_balance {X : ℝ} (hX₀ : 1/a < X) :
    (∑ j ∈ Icc 1 ⌊b*X⌋₊, coefficients X j*(j:ℝ))=0 := by
  have hX := (one_div_pos.mpr (Real.exp_pos _)).trans hX₀
  have h := roundedFactorialReading_eq_floor_sum (B := b*X) (fun x => squareFactorialTest (x/X))
    (mul_nonneg (Real.exp_pos _).le hX.le) zero_lt_one
  change squareFactorialInterpolant X 1=_ at h
  have hz : squareFactorialTest (1/X)=0 := test_zero (fun hh => ((div_lt_iff₀ hX).mpr (by linarith only [(div_lt_iff₀ (Real.exp_pos _)).mp hX₀])).not_ge hh.1)
  have ht := squareFactorialInterpolant_exact hX (n := 1) Nat.one_pos
  simp only [squareFactorialTest,if_pos (one_div_pos.mpr hX)] at hz
  simp only [Nat.cast_one,hz] at ht
  simpa only [coefficients,div_one,Nat.floor_natCast,ht] using h.symm

private theorem interpolant_entropy_integral {X : ℝ} (hX₀ : 1/a < X) :
    IntegrableOn (squareFactorialInterpolant X) (Set.Ioi 0) ∧
      (∫ y in Set.Ioi (0:ℝ), squareFactorialInterpolant X y)=squareFactorialEntropy X := by
  let I := Icc 1 ⌊b*X⌋₊
  have hX := (one_div_pos.mpr (Real.exp_pos _)).trans hX₀
  have hb := interpolant_balance hX₀
  have he (y : ℝ) (hy : y ∈ Set.Ioi (0:ℝ)) : squareFactorialInterpolant X y=
      ∑ j ∈ I, coefficients X j*balancedFloor j y := by
    rw [squareFactorialInterpolant,roundedFactorialReading_eq_floor_sum _ (mul_nonneg (Real.exp_pos _).le hX.le) hy]
    simp only [balancedFloor,mul_sub,← mul_assoc,sum_sub_distrib,← sum_mul]
    rw [show (∑ j ∈ I, coefficients X j*(j:ℝ))=0 from hb,zero_mul,sub_zero]
    rfl
  have hf (j : ℕ) (hj : j ∈ I) := (balancedFloor_integral (mem_Icc.mp hj).1).1.const_mul (coefficients X j)
  have hi : IntegrableOn (fun y => ∑ j ∈ I, coefficients X j*balancedFloor j y) (Set.Ioi 0) := integrable_finsetSum I hf
  refine ⟨hi.congr_fun (fun y hy => (he y hy).symm) measurableSet_Ioi,?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioi he,integral_finsetSum _ hf]
  exact sum_congr rfl fun j hj => by rw [integral_const_mul,(balancedFloor_integral (mem_Icc.mp hj).1).2]

/-- The canonical entropy is bounded by the unscaled integral error, since
the mean of the square prime weight vanishes. -/
theorem squareFactorialEntropy_mertens {σ C : ℝ} (hs : 0 < σ) (hc : 0 ≤ C)
    (hm : ∀ n : ℕ, 0 < n → |mertens n| ≤ C*(n:ℝ)^σ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ X : ℝ in atTop, |squareFactorialEntropy X| ≤ A*X^σ := by
  obtain ⟨A,hA,he⟩ := squareFactorialInterpolant_mertens_integral hs hc hm
  refine ⟨A,hA,?_⟩
  filter_upwards [eventually_gt_atTop (1/a),he] with X hX₀ hE
  have hX := (one_div_pos.mpr (Real.exp_pos _)).trans hX₀
  let w := fun y : ℝ => (squarePrimeWeight (y/X)).re
  have hw₀ : IntegrableOn squarePrimeWeight (Set.Ioi 0) := by
    simpa only [MellinConvergent,sub_self,Complex.cpow_zero,one_smul] using mellinConvergent_squarePrimeWeight 1
  have hr : IntegrableOn (fun t => (squarePrimeWeight t).re) (Set.Ioi 0) := hw₀.re
  have hw : IntegrableOn w (Set.Ioi 0) := by
    simpa only [w,div_eq_inv_mul,mul_zero] using
      (integrableOn_Ioi_comp_mul_left_iff (fun t => (squarePrimeWeight t).re) 0 (inv_pos.mpr hX)).mpr
        (by simpa only [mul_zero] using hr)
  have hzero : (∫ y in Set.Ioi (0:ℝ), w y)=0 := by
    have h := squareFactorialMellin_one
    simp only [mellin,sub_self,Complex.cpow_zero,one_smul] at h
    have hz : (∫ t in Set.Ioi (0:ℝ), (squarePrimeWeight t).re)=0 :=
      (integral_re hw₀).trans (congrArg Complex.re h)
    simpa only [w,div_eq_inv_mul,mul_zero,hz,smul_zero] using
      integral_comp_mul_left_Ioi (fun t => (squarePrimeWeight t).re) 0 (inv_pos.mpr hX)
  obtain ⟨hi,hv⟩ := interpolant_entropy_integral hX₀
  have h := norm_integral_le_integral_norm (μ := volume.restrict (Set.Ioi 0))
    (fun y => squareFactorialInterpolant X y-w y)
  simp only [integral_sub hi hw,hv,hzero,sub_zero,Real.norm_eq_abs] at h
  refine h.trans (((div_le_iff₀ hX).mp hE.2).trans_eq ?_)
  rw [Real.rpow_sub hX,Real.rpow_one]; field_simp [hX.ne']

private theorem stirling_step_abs {j : ℕ} (hj : 0 < j) : |factorialStirlingStep j| ≤ (j:ℝ)⁻¹ := by
  let r := (j:ℝ)⁻¹
  let d := fun k : ℕ => ((k:ℝ)+1)*((k:ℝ)+2)
  have hr : 0 ≤ r := inv_nonneg.mpr (Nat.cast_nonneg _)
  have hr₁ : r ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast (show 1 ≤ j from hj))
  have h := hasSum_factorialStirlingStep hj
  have h₁ := (hasSum_factorialStirlingStep Nat.one_pos).mul_left r
  simp only [Nat.cast_one,inv_one,one_pow,factorialStirlingStep_one,mul_one] at h₁
  rw [← h.tsum_eq,abs_of_nonneg (tsum_nonneg (fun _ => by positivity))]
  refine (h.summable.tsum_le_tsum (g := fun k : ℕ => r*(1/d k)) (fun k => ?_) h₁.summable).trans_eq h₁.tsum_eq
  change r^(k+1)/d k ≤ r*(1/d k)
  simpa only [mul_one_div] using div_le_div_of_nonneg_right
    (show r^(k+1) ≤ r by rw [pow_succ]; exact mul_le_of_le_one_left hr (pow_le_one₀ hr hr₁)) (by dsimp [d]; positivity)

private theorem sum_first_differences (u f : ℕ → ℝ) (hf : f 0=0) (N : ℕ) :
    (∑ j ∈ Icc 1 N, (u j-u (j+1))*f j) =
      (∑ j ∈ Icc 1 N, u j*(f j-f (j-1)))-u (N+1)*f N := by
  induction N with
  | zero => simp [hf]
  | succ N ih =>
    rw [sum_Icc_succ_top (by omega),ih,sum_Icc_succ_top (by omega),Nat.add_sub_cancel]
    ring

/-- The coefficient-weighted Stirling error is bounded by the same Mertens
power. Each Stirling step costs at most the reciprocal of its degree. -/
theorem squareFactorialStirlingError_mertens {σ C : ℝ} (hs : 0 < σ) (hc : 0 ≤ C)
    (hm : ∀ n : ℕ, 0 < n → |mertens n| ≤ C*(n:ℝ)^σ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ X : ℝ in atTop, |squareFactorialStirlingError X| ≤ D*X^σ := by
  obtain ⟨L,hL,hd⟩ := scaled_test_data
  let A := C*L*b*b^σ
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hsum := Real.summable_nat_rpow_inv.mpr (by linarith only [hs] : 1 < 1+σ)
  have hZ : 0 ≤ factorialInterpolationPSeries σ := tsum_nonneg fun n => inv_nonneg.mpr (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  refine ⟨A*factorialInterpolationPSeries σ,mul_nonneg hA hZ,?_⟩
  filter_upwards [eventually_gt_atTop (1/a)] with X hX₀
  have hX := (one_div_pos.mpr (Real.exp_pos _)).trans hX₀
  obtain ⟨hz,_,hl,_⟩ := hd hX
  let W := fun x : ℝ => squareFactorialTest (x/X)
  let N := ⌊b*X⌋₊
  let u := fun j : ℕ => mobiusFactorialSample W (b*X) j
  let f := fun j : ℕ => Real.log (j.factorial:ℝ)-(j:ℝ)*Real.log j
  have htop : u (N+1)=0 := by
    have hn : b*X < ((N+1:ℕ):ℝ) := by simpa only [Nat.cast_add,Nat.cast_one] using Nat.lt_floor_add_one (b*X)
    have he := Nat.floor_eq_zero.mpr ((div_lt_one (Nat.cast_pos.mpr (Nat.succ_pos _))).mpr hn)
    change (∑ j ∈ Icc 1 ⌊b*X/((N+1:ℕ):ℝ)⌋₊, _) = 0
    rw [he]
    simp
  have hbal := sum_first_differences u (fun j => (j:ℝ)) (by simp) N
  rw [show (∑ j ∈ Icc 1 N, (u j-u (j+1))*(j:ℝ))=0 from interpolant_balance hX₀,htop,zero_mul,sub_zero] at hbal
  have hj (j : ℕ) (hj : j ∈ Icc 1 N) : (j:ℝ)-((j-1:ℕ):ℝ)=1 := by
    rw [Nat.cast_sub (mem_Icc.mp hj).1,Nat.cast_one]; ring
  rw [sum_congr rfl (fun j h => by rw [hj j h,mul_one])] at hbal
  have hf (j : ℕ) (hj : j ∈ Icc 1 N) : f j-f (j-1)=factorialStirlingStep j-1 := by
    obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (mem_Icc.mp hj).1)
    simp only [f,factorialStirlingStep,Nat.succ_eq_add_one,Nat.add_sub_cancel,Nat.factorial_succ,
      Nat.cast_mul,Real.log_mul (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _)) (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))]
    ring
  change |∑ j ∈ Icc 1 N, (u j-u (j+1))*f j| ≤ _
  rw [sum_first_differences _ _ (by simp [f]),htop,zero_mul,sub_zero,
    sum_congr rfl (fun j h => by rw [hf j h,mul_sub,mul_one]),sum_sub_distrib,← hbal,sub_zero]
  have row (j : ℕ) (hj : j ∈ Icc 1 N) :
      |u j*factorialStirlingStep j| ≤ (A*X^σ)*((j:ℝ)^(1+σ))⁻¹ := by
    have hj₀ := (mem_Icc.mp hj).1
    have hj' : 0 < (j:ℝ) := Nat.cast_pos.mpr hj₀
    have h := mobiusFactorialSample_mertens_bound (mul_nonneg (Real.exp_pos _).le hX.le)
      (div_nonneg hL hX.le) hc hs.le hz hl hm hj'
    rw [abs_mul]
    refine (mul_le_mul h (stirling_step_abs hj₀) (abs_nonneg _) (by positivity)).trans_eq ?_
    dsimp only [A]
    rw [Real.div_rpow (by positivity) hj'.le,Real.mul_rpow (Real.exp_pos _).le hX.le,Real.rpow_add hj',Real.rpow_one]
    field_simp [hX.ne'] <;> ring
  refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum row).trans ?_)
  rw [← mul_sum]
  exact (mul_le_mul_of_nonneg_left (hsum.sum_le_tsum _ (fun k _ => inv_nonneg.mpr
    (Real.rpow_nonneg (Nat.cast_nonneg k) _))) (mul_nonneg hA (Real.rpow_nonneg hX.le _))).trans_eq (by
      dsimp only [factorialInterpolationPSeries]; ring)

end GaloisForLFunctions.CountingHolography.Sections
