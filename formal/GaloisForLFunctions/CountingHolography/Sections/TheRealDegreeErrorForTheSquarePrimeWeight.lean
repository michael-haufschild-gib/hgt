import GaloisForLFunctions.CountingHolography.Sections.RoundingTheRealDegreesOfTheFactorialInterpolant
import GaloisForLFunctions.CountingHolography.Sections.CriticalZerosSeparateThePrimeProfileFromFactorialKernels
import Mathlib.Analysis.Calculus.Deriv.Support

/-! # Real-degree interpolation for the actual square prime weight

The spline weight and its logarithmic derivative have compact support
away from zero. The Mertens exponent bounds the height and integrated
error of the canonical factorial interpolant.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections
open Finset Filter Topology MeasureTheory ArithmeticOfSquareRootPrecision
open _root_.RHTower _root_.RHTower.WeilDeletion BiScaleUncertainty.ChebyshevGauge

private abbrev a := Real.exp (-8)
private abbrev b := Real.exp (8+Real.log 4)

/-- The positive-argument prime test extended by zero on the negative axis. -/
def squareFactorialTest (x : ℝ) := if 0 < x then (squarePrimeWeight x).re else 0

private theorem test_zero {x : ℝ} (h : x ∉ Set.Icc a b) : squareFactorialTest x = 0 := by
  by_cases hx : 0 < x
  · rw [squareFactorialTest,if_pos hx,squarePrimeWeight_zero_outside hx h,Complex.zero_re]
  · simp [squareFactorialTest,hx]

private theorem test_compact : HasCompactSupport squareFactorialTest := by
  apply isCompact_Icc.of_isClosed_subset isClosed_closure
  apply closure_minimal _ isClosed_Icc
  exact fun x hx => by by_contra h; exact hx (test_zero h)

private theorem test_regular : ContDiff ℝ 2 squareFactorialTest := by
  have hH : ContDiff ℝ 2 splineAutoCorr := by
    rw [show splineAutoCorr = upow 1 7 from funext splineAutoCorr_eq_eight_boxes]
    exact (contDiff_upow one_pos 6).of_le (by norm_num)
  have hF : ContDiff ℝ 2 squareLogProfile := (contDiff_const.mul hH).sub
    (hH.comp (contDiff_id.sub contDiff_const))
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : 0 < x
  · have hl := Real.contDiffAt_log (n := 2) hx.ne'
    have hr : ContDiffAt ℝ 2 (fun y => Real.exp (-Real.log y/2)*squareLogProfile (Real.log y)) x :=
      (Real.contDiff_exp.contDiffAt.comp x (hl.neg.div_const _)).mul (hF.contDiffAt.comp x hl)
    apply hr.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hx] with y hy
    simp [squareFactorialTest,hy,squarePrimeWeight]
  · apply (contDiffAt_const (c := (0:ℝ))).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds ((le_of_not_gt hx).trans_lt (Real.exp_pos _))] with y hy
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
    simpa only [div_eq_mul_inv,one_mul] using hd
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
  exact h.trans_eq (by field_simp [hX.ne',hy.ne']; ring)

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
  have hB := mul_nonneg (Real.exp_pos _).le hX.le
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
    squareFactorialTest (x := y/X),if_pos (div_pos hy hX)]

/-- Beyond K the scaled integral of the unconditional rounding error is
at most a constant divided by K. -/
theorem squareFactorialInterpolant_integral_tail : ∃ D : ℝ, 0 ≤ D ∧ ∀ {X K : ℝ}, 0 < X → 0 < K →
    (∫ y in Set.Ioi K, |squareFactorialInterpolant X y-(squarePrimeWeight (y/X)).re|)/X ≤ D/K := by
  obtain ⟨D,hD,hd⟩ := squareFactorialInterpolant_error
  refine ⟨D,hD,fun {X K} hX hK => ?_⟩
  have hg := (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2:ℝ) < -1) hK).const_mul (D*X)
  have he : ∀ᵐ y ∂volume.restrict (Set.Ioi K), errorAt X y ≤ D*X*y^(-2:ℝ) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    simpa only [Real.rpow_neg (hK.trans hy).le,Real.rpow_two,div_eq_mul_inv] using hd hX (hK.trans hy)
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
    simpa only [if_pos hy.2] using h hy.1
  have h₂ : ∀ᵐ y ∂volume.restrict (Set.Ioi 1), errorAt X y ≤ E*y^(-(1+σ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hy' := zero_lt_one.trans hy
    simpa only [if_neg (not_le.mpr hy),Real.rpow_neg hy'.le,div_eq_mul_inv] using h hy'
  have hc : IntegrableOn (fun _ : ℝ => E) (Set.Ioc 0 1) := integrableOn_const
    (by simp : volume (Set.Ioc (0:ℝ) 1) ≠ ⊤)
  have hs : -(1+σ) < -1 := by linarith only [hσ]
  have hr := (integrableOn_Ioi_rpow_of_lt hs (by norm_num : (0:ℝ)<1)).const_mul E
  have hm := errorAt_measurable hX
  have hinner : IntegrableOn (errorAt X) (Set.Ioc 0 1) := hc.mono'
    (hm.mono_measure (Measure.restrict_mono_set _ Set.Ioc_subset_Ioi_self))
    (h₁.mono fun y hy => by simpa only [Real.norm_of_nonneg (abs_nonneg _)] using hy)
  have houter : IntegrableOn (errorAt X) (Set.Ioi 1) := hr.mono'
    (hm.mono_measure (Measure.restrict_mono_set _ (Set.Ioi_subset_Ioi zero_le_one)))
    (h₂.mono fun y hy => by simpa only [Real.norm_of_nonneg (abs_nonneg _)] using hy)
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

end GaloisForLFunctions.CountingHolography.Sections
