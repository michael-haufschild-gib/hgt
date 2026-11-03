import GaloisForLFunctions.WindowTowerOfSpecZ.TheRetainedGammaLowerFormHasANegativeDirection
import GaloisForLFunctions.«arithmetic-positivity-theory».FactorialRampFullWeilSmoothingLimit

/-!
# Support-preserving smoothing of the negative retained form

Mollification followed by a compensating dilation preserves the unit support.
Uniform Lipschitz bounds dominate the logarithmic lag integrand at zero.
-/

noncomputable section
open Real MeasureTheory Set Filter Topology
open _root_.RHTower _root_.RHTower.CHMDDoobGraph
open _root_.RHTower.ArchimedeanAnomaly _root_.RHTower.WeilMarkovPole
namespace GaloisForLFunctions.WindowTowerOfSpecZ
open ArithmeticPositivityTheory

private def quinticPolynomial (x : ℝ) := 2*x-12*x^3+16*x^5

private theorem quinticPolynomial_deriv (x : ℝ) : HasDerivAt quinticPolynomial (2-36*x^2+80*x^4) x := by
  have h1 := (hasDerivAt_id x).const_mul 2
  have h2 := (hasDerivAt_pow 3 x).const_mul 12
  have h3 := (hasDerivAt_pow 5 x).const_mul 16
  exact ((h1.sub h2).add h3).congr_deriv (by ring)

private theorem quinticPolynomial_lipschitz : LipschitzOnWith 16 quinticPolynomial (Icc (-(1/2 : ℝ)) (1/2)) := by
  apply Convex.lipschitzOnWith_of_nnnorm_deriv_le
    (fun x _ => (quinticPolynomial_deriv x).differentiableAt) _ (convex_Icc _ _)
  intro x hx
  change ‖deriv quinticPolynomial x‖ ≤ (16 : ℝ)
  rw [(quinticPolynomial_deriv x).deriv, Real.norm_eq_abs]
  have h2 : x^2 ≤ 1/4 := by
    nlinarith only [mul_nonneg (by linarith only [hx.1] : 0 ≤ x+1/2)
      (by linarith only [hx.2] : 0 ≤ 1/2-x)]
  have h4 := pow_le_pow_left₀ (sq_nonneg x) h2 2
  rw [← pow_mul] at h4
  norm_num at h4
  apply abs_le.mpr
  constructor
  · nlinarith only [h2, sq_nonneg (x ^ 2)]
  · linarith only [h4, sq_nonneg x]

private theorem quinticWindow_lipschitz (x y : ℝ) : |quinticWindow x - quinticWindow y| ≤ 16 * |x-y| := by
  have hab : -(1/2 : ℝ) ≤ 1/2 := by norm_num
  let c := Set.projIcc (-(1/2 : ℝ)) (1/2) hab
  have he (z : ℝ) : quinticWindow z = quinticPolynomial (c z) := by
    by_cases hl : z < -(1/2 : ℝ)
    · have hz := quinticWindow_outside (x:=z) (fun h => not_lt_of_ge h.1 hl)
      rw [hz]
      change 0 = quinticPolynomial ((Set.projIcc _ _ hab z : Icc _ _) : ℝ)
      rw [Set.projIcc_of_le_left hab hl.le]
      norm_num [quinticPolynomial]
    · by_cases hr : (1/2 : ℝ) < z
      · have hz := quinticWindow_outside (x:=z) (fun h => not_lt_of_ge h.2 hr)
        rw [hz]
        change 0 = quinticPolynomial ((Set.projIcc _ _ hab z : Icc _ _) : ℝ)
        rw [Set.projIcc_of_right_le hab hr.le]
        norm_num [quinticPolynomial]
      · have hi : z ∈ Icc (-(1/2 : ℝ)) (1/2) := ⟨not_lt.mp hl, not_lt.mp hr⟩
        change quinticWindow z = quinticPolynomial ((Set.projIcc _ _ hab z : Icc _ _) : ℝ)
        rw [Set.projIcc_of_mem hab hi, quinticWindow_inside hi.1 hi.2]
        rfl
  have hc : |(c x : ℝ)-(c y : ℝ)| ≤ |x-y| := by
    have h := (LipschitzWith.projIcc hab).dist_le_mul x y
    change dist (c x : ℝ) (c y : ℝ) ≤ 1 * dist x y at h
    simpa only [Real.dist_eq, one_mul] using h
  rw [he x, he y]
  have h := quinticPolynomial_lipschitz.dist_le_mul (c x) (c x).property (c y) (c y).property
  have hp : |quinticPolynomial (c x)-quinticPolynomial (c y)| ≤ 16 * |(c x : ℝ)-(c y : ℝ)| := by
    simpa only [Real.dist_eq] using h
  exact hp.trans (mul_le_mul_of_nonneg_left hc (by norm_num))

private theorem quinticWindow_abs_le_one (x : ℝ) : |quinticWindow x| ≤ 1 := by
  by_cases hx : x ∈ Icc (-(1 / 2 : ℝ)) (1 / 2)
  · have hsq : x ^ 2 ≤ 1 / 4 := by
      nlinarith only [mul_nonneg (by linarith only [hx.1] : 0 ≤ x + 1 / 2)
        (by linarith only [hx.2] : 0 ≤ 1 / 2 - x)]
    have ha : 0 ≤ 1 - 4 * x ^ 2 := by linarith only [hsq]
    have hb : 0 ≤ 1 - 2 * x ^ 2 := by linarith only [hsq]
    have ha1 : 1 - 4 * x ^ 2 ≤ 1 := by linarith only [sq_nonneg x]
    have hb1 : 1 - 2 * x ^ 2 ≤ 1 := by linarith only [sq_nonneg x]
    have hp : (1 - 4 * x ^ 2) * (1 - 2 * x ^ 2) ≤ 1 := by
      simpa only [one_mul] using mul_le_mul ha1 hb1 hb (by norm_num : (0 : ℝ) ≤ 1)
    have h2 : 2 * |x| ≤ 1 := by linarith only [abs_le.mpr hx]
    have he : |quinticWindow x| =
        (2 * |x|) * ((1 - 4 * x ^ 2) * (1 - 2 * x ^ 2)) := by
      rw [quinticWindow, cubicWindow_inside hx.1 hx.2,
        abs_mul, abs_mul, abs_mul, abs_two, abs_of_nonneg ha, abs_of_nonneg hb]
      ring
    rw [he]
    simpa only [one_mul] using mul_le_mul h2 hp (mul_nonneg ha hb) (by norm_num : (0 : ℝ) ≤ 1)
  · rw [quinticWindow_outside hx, abs_zero]
    norm_num

private def quinticSmoothScale (n : ℕ) : ℝ := 1 + 1 / (2 * ((n : ℝ) + 1))

/-- Smoothing followed by contraction of the enlarged support to the unit window. -/
def unitSmoothQuintic (n : ℕ) (x : ℝ) : ℝ :=
  smooth quinticWindow n (quinticSmoothScale n * x)

private theorem quinticSmoothScale_bounds (n : ℕ) :
    1 ≤ quinticSmoothScale n ∧ quinticSmoothScale n ≤ 3 / 2 := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  unfold quinticSmoothScale
  constructor
  · have h : 0 ≤ 1 / (2 * ((n : ℝ) + 1)) := by positivity
    linarith only [h]
  · have h : 1 / (2 * ((n : ℝ) + 1)) ≤ (1 / 2 : ℝ) :=
      one_div_le_one_div_of_le (by norm_num) (by linarith only [hn])
    linarith only [h]

theorem unitSmoothQuintic_contDiff (n : ℕ) : ContDiff ℝ 2 (unitSmoothQuintic n) := by
  have hf2 : MemLp quinticWindow 2 volume :=
    continuous_quinticWindow.memLp_of_hasCompactSupport compact_quinticWindow
  have hs : ContDiff ℝ 2 (smooth quinticWindow n) :=
    (smooth_contDiff hf2 n).of_le (by simp)
  exact hs.comp (contDiff_const.mul contDiff_id)

private theorem quintic_mollifier_even (n : ℕ) (t : ℝ) : mollifier n (-t) = mollifier n t := by
  unfold mollifier
  rw [ContDiffBump.normed_def, ContDiffBump.normed_def, ContDiffBump.neg]

theorem unitSmoothQuintic_odd (n : ℕ) (x : ℝ) :
    unitSmoothQuintic n (-x) = -unitSmoothQuintic n x := by
  change (∫ t, mollifier n t * quinticWindow (quinticSmoothScale n * (-x) - t)) =
    -(∫ t, mollifier n t * quinticWindow (quinticSmoothScale n * x - t))
  rw [← integral_neg_eq_self (fun t => mollifier n t *
    quinticWindow (quinticSmoothScale n * (-x) - t)) volume]
  calc _ = ∫ t, -(mollifier n t * quinticWindow (quinticSmoothScale n * x - t)) := by
          apply integral_congr_ae
          exact Eventually.of_forall fun t => by
            rw [quintic_mollifier_even,
              show quinticSmoothScale n * (-x) - -t = -(quinticSmoothScale n * x - t) by ring,
              quinticWindow_odd, mul_neg]
    _ = _ := integral_neg _

theorem unitSmoothQuintic_outside (n : ℕ) {x : ℝ}
    (hx : x ∉ Icc (-(1 / 2 : ℝ)) (1 / 2)) : unitSmoothQuintic n x = 0 := by
  have hxa : 1 / 2 < |x| := not_le.mp fun h => hx (abs_le.mp h)
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hr : 0 ≤ 1 / (4 * ((n : ℝ) + 1)) := by positivity
  have hscale : quinticSmoothScale n = 1 + 2 * (1 / (4 * ((n : ℝ) + 1))) := by
    unfold quinticSmoothScale
    ring
  have hfar : 1 / 2 + 1 / (4 * ((n : ℝ) + 1)) < |quinticSmoothScale n * x| := by
    rw [abs_mul, abs_of_nonneg (by linarith only [(quinticSmoothScale_bounds n).1])]
    rw [hscale]
    nlinarith only [hxa, hr, mul_pos (by linarith only [hr] : (0 : ℝ) < 1 +
      2 * (1 / (4 * ((n : ℝ) + 1)))) (sub_pos.mpr hxa)]
  change (∫ t, mollifier n t * quinticWindow (quinticSmoothScale n * x - t)) = 0
  apply integral_eq_zero_of_ae
  exact Eventually.of_forall fun t => by
    by_cases ht : 1 / (4 * ((n : ℝ) + 1)) ≤ |t|
    · have hm : mollifier n t = 0 := by
        apply Function.notMem_support.mp
        change t ∉ Function.support ((WeilOneSided.narrowBump n).normed volume)
        rw [(WeilOneSided.narrowBump n).support_normed_eq, Metric.mem_ball,
          dist_zero_right, Real.norm_eq_abs]
        exact not_lt.mpr ht
      rw [hm, zero_mul]
    · have hz : quinticWindow (quinticSmoothScale n * x - t) = 0 := by
        apply quinticWindow_outside
        intro hi
        have ha := abs_le.mpr hi
        have h := abs_sub_abs_le_abs_sub (quinticSmoothScale n * x) t
        linarith only [ha, h, hfar, not_le.mp ht]
      rw [hz, mul_zero]

theorem unitSmoothQuintic_support (n : ℕ) :
    tsupport (unitSmoothQuintic n) ⊆ Icc (-(1 / 2 : ℝ)) (1 / 2) := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  by_contra hi
  exact hx (unitSmoothQuintic_outside n hi)

theorem unitSmoothQuintic_compact (n : ℕ) : HasCompactSupport (unitSmoothQuintic n) :=
  HasCompactSupport.intro isCompact_Icc (fun _ hx => unitSmoothQuintic_outside n hx)

theorem unitSmoothQuintic_abs_le_one (n : ℕ) (x : ℝ) : |unitSmoothQuintic n x| ≤ 1 :=
  smooth_bound (by norm_num : (0 : ℝ) ≤ 1) quinticWindow_abs_le_one n _

private theorem smooth_quintic_lipschitz (n : ℕ) (x y : ℝ) :
    |smooth quinticWindow n x - smooth quinticWindow n y| ≤ 16 * |x-y| := by
  have he := difference_smooth (v := quinticWindow) continuous_quinticWindow.measurable
    (by norm_num : (0 : ℝ) ≤ 1) quinticWindow_abs_le_one n (y-x) x
  rw [show x + (y-x) = y by ring] at he
  rw [he]
  exact smooth_bound (by positivity : 0 ≤ 16 * |x-y|)
    (fun z => by simpa only [show z - (z + (y-x)) = x-y by ring]
      using quinticWindow_lipschitz z (z + (y-x))) n x

theorem unitSmoothQuintic_lipschitz (n : ℕ) (x y : ℝ) :
    |unitSmoothQuintic n x - unitSmoothQuintic n y| ≤ 24 * |x-y| := by
  have h := smooth_quintic_lipschitz n (quinticSmoothScale n * x) (quinticSmoothScale n * y)
  have ha := quinticSmoothScale_bounds n
  rw [← mul_sub, abs_mul, abs_of_nonneg (by linarith only [ha.1] : 0 ≤ quinticSmoothScale n)] at h
  have hm := mul_le_mul_of_nonneg_right ha.2 (abs_nonneg (x-y))
  change |smooth quinticWindow n (quinticSmoothScale n * x) -
    smooth quinticWindow n (quinticSmoothScale n * y)| ≤ _
  linarith only [h, hm]

private theorem quinticSmoothScale_tendsto : Tendsto quinticSmoothScale atTop (𝓝 1) := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have hdiv : Tendsto (fun n : ℕ => 1 / (2 * ((n : ℝ) + 1))) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (hn.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
  simpa only [quinticSmoothScale, add_zero] using tendsto_const_nhds.add hdiv

/-- The compensating dilation tends to one, preserving the mollification limit. -/
theorem unitSmoothQuintic_tendsto (x : ℝ) :
    Tendsto (fun n => unitSmoothQuintic n x) atTop (𝓝 (quinticWindow x)) := by
  have hb (n : ℕ) : ‖unitSmoothQuintic n x - smooth quinticWindow n x‖ ≤
      16 * |(quinticSmoothScale n - 1) * x| := by
    have h := smooth_quintic_lipschitz n (quinticSmoothScale n * x) x
    rw [show quinticSmoothScale n * x - x = (quinticSmoothScale n - 1) * x by ring] at h
    exact h
  have hz : Tendsto (fun n => 16 * |(quinticSmoothScale n - 1) * x|) atTop (𝓝 0) := by
    have h := (((quinticSmoothScale_tendsto.sub_const 1).mul_const x).abs).const_mul 16
    simpa only [sub_self, zero_mul, abs_zero, mul_zero] using h
  have hd := squeeze_zero_norm hb hz
  have h := hd.add (smooth_tendsto_of_continuous continuous_quinticWindow x)
  simpa only [sub_add_cancel, zero_add] using h

end GaloisForLFunctions.WindowTowerOfSpecZ

#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.unitSmoothQuintic_support
#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.unitSmoothQuintic_tendsto
