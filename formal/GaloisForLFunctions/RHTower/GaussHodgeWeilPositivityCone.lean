import GaloisForLFunctions.RHTower.GaussHodgeWeilDeviationMoment
import GaloisForLFunctions.RHTower.XiResolventUnconditionalFloor

/-!
# An unconditional Weil-positivity cone

The deviation moment identity writes the diagonal Weil value as the even energy minus the
second moment of critical-line deviations.  Every deviation summand carries the factor
`(Im α)²`, so the moment is supported on the off-line copies — which the certified height floor
confines to `65 ≤ (Re α)²` — and on that tail the zero-density surrogate bounds the resolvent
mass by one logarithmic-derivative value of `ξ` on the real ray.

Consequently, for any square-summable test whose tail deviation summands are dominated by
resolvent mass, the diagonal Weil value is at least the even energy minus an explicit ray-jet
multiple of the domination constant: Weil positivity holds *unconditionally* on the cone of
tests whose even energy exceeds that explicit bound — numerically, `C·396/6475` at the
critical probe.  Outside the cone the positivity producer's burden is exactly RH; inside, it is
already paid by the certified spectral geometry.
-/

open Complex

namespace RHTower

noncomputable section

/-- **Floor localization of the deviation moment**: the deviation summands are supported on
the copies above the certified height floor. -/
theorem deviation_support_subset_tail {F : ℂ → ℂ} :
    Function.support (fun q : XiZeroCopy => (xiSpectralPoint q).im ^ 2 *
      ‖dslope F ((starRingEnd ℂ) (xiSpectralPoint q)) (xiSpectralPoint q)‖ ^ 2) ⊆
    {q : XiZeroCopy | (65 : ℝ) ≤ (xiSpectralPoint q).re ^ 2} := by
  intro q hq
  rw [Function.mem_support] at hq
  have him : (xiSpectralPoint q).im ≠ 0 := by
    intro h0
    apply hq
    rw [h0]
    ring
  exact le_of_lt (offline_height_sq_gt_sixtyfive q him)

/-- **The mass-dominated deviation bound**: if the tail deviation summands of a test are
dominated by resolvent mass, the whole deviation moment is bounded by an explicit ray-jet
multiple of the domination constant. -/
theorem deviation_moment_le_of_tail_dominated {X : ℝ} (hX : 0 ≤ X) {F : ℂ → ℂ}
    (hF : XiWeilSquareSummable F) {C c : ℝ} (hC : 0 ≤ C) (hc : 1 / 2 ≤ c)
    (hΔ : ∀ q : XiZeroCopy, (65 : ℝ) ≤ (xiSpectralPoint q).re ^ 2 →
      (xiSpectralPoint q).im ^ 2 *
        ‖dslope F ((starRingEnd ℂ) (xiSpectralPoint q)) (xiSpectralPoint q)‖ ^ 2 ≤
      C * ‖xiResolventPoint X q‖) :
    (∑' q : XiZeroCopy, (xiSpectralPoint q).im ^ 2 *
      ‖dslope F ((starRingEnd ℂ) (xiSpectralPoint q)) (xiSpectralPoint q)‖ ^ 2) ≤
    C * ((65 + (c + 1 / 2) ^ 2) / (2 * c * (65 - 1 / 4)) *
      (2 * (logDeriv xi ((1 / 2 : ℂ) + (c : ℂ))).re)) := by
  rw [← tsum_subtype_eq_of_support_subset (deviation_support_subset_tail (F := F))]
  have hdev_sub : Summable
      (fun q : {q : XiZeroCopy | (65 : ℝ) ≤ (xiSpectralPoint q).re ^ 2} =>
        (xiSpectralPoint (q : XiZeroCopy)).im ^ 2 *
          ‖dslope F ((starRingEnd ℂ) (xiSpectralPoint (q : XiZeroCopy)))
            (xiSpectralPoint (q : XiZeroCopy))‖ ^ 2) :=
    (deviation_dslope_energy_summable hF).subtype _
  have hmass_sub : Summable
      (fun q : {q : XiZeroCopy | (65 : ℝ) ≤ (xiSpectralPoint q).re ^ 2} =>
        C * ‖xiResolventPoint X (q : XiZeroCopy)‖) :=
    ((summable_norm_xiResolventPoint hX).subtype _).mul_left C
  calc (∑' q : {q : XiZeroCopy | (65 : ℝ) ≤ (xiSpectralPoint q).re ^ 2},
        (xiSpectralPoint (q : XiZeroCopy)).im ^ 2 *
          ‖dslope F ((starRingEnd ℂ) (xiSpectralPoint (q : XiZeroCopy)))
            (xiSpectralPoint (q : XiZeroCopy))‖ ^ 2)
      ≤ ∑' q : {q : XiZeroCopy | (65 : ℝ) ≤ (xiSpectralPoint q).re ^ 2},
          C * ‖xiResolventPoint X (q : XiZeroCopy)‖ :=
        Summable.tsum_le_tsum (fun q => hΔ q.1 q.2) hdev_sub hmass_sub
    _ = C * ∑' q : {q : XiZeroCopy | (65 : ℝ) ≤ (xiSpectralPoint q).re ^ 2},
          ‖xiResolventPoint X (q : XiZeroCopy)‖ := tsum_mul_left
    _ ≤ C * ((65 + (c + 1 / 2) ^ 2) / (2 * c * (65 - 1 / 4)) *
          (2 * (logDeriv xi ((1 / 2 : ℂ) + (c : ℂ))).re)) := by
        refine mul_le_mul_of_nonneg_left ?_ hC
        exact tsum_norm_xiResolventPoint_tail_le_logDeriv hX hc (by norm_num)

/-- **The unconditional Weil-positivity cone**: for any square-summable test whose tail
deviation summands are dominated by resolvent mass with constant `C`, the diagonal Weil value
is nonnegative as soon as the even energy exceeds the explicit ray-jet multiple of `C`. -/
theorem xiWeilPolarization_re_nonneg_of_tail_dominated {X : ℝ} (hX : 0 ≤ X) {F : ℂ → ℂ}
    (hF : XiWeilSquareSummable F) {C c : ℝ} (hC : 0 ≤ C) (hc : 1 / 2 ≤ c)
    (hΔ : ∀ q : XiZeroCopy, (65 : ℝ) ≤ (xiSpectralPoint q).re ^ 2 →
      (xiSpectralPoint q).im ^ 2 *
        ‖dslope F ((starRingEnd ℂ) (xiSpectralPoint q)) (xiSpectralPoint q)‖ ^ 2 ≤
      C * ‖xiResolventPoint X q‖)
    (heven : C * ((65 + (c + 1 / 2) ^ 2) / (2 * c * (65 - 1 / 4)) *
        (2 * (logDeriv xi ((1 / 2 : ℂ) + (c : ℂ))).re)) ≤
      ∑' q : XiZeroCopy, ‖xiWeilEvenPart F (xiSpectralPoint q)‖ ^ 2) :
    0 ≤ (xiWeilPolarization F F).re := by
  rw [xiWeilPolarization_re_eq_deviation_moment hF]
  have h := deviation_moment_le_of_tail_dominated hX hF hC hc hΔ
  linarith

/-- **The numeric cone at the critical probe**: Weil positivity is unconditional whenever the
even energy exceeds `396/6475` times the tail domination constant. -/
theorem xiWeilPolarization_re_nonneg_of_tail_dominated_numeric {X : ℝ} (hX : 0 ≤ X)
    {F : ℂ → ℂ} (hF : XiWeilSquareSummable F) {C : ℝ} (hC : 0 ≤ C)
    (hΔ : ∀ q : XiZeroCopy, (65 : ℝ) ≤ (xiSpectralPoint q).re ^ 2 →
      (xiSpectralPoint q).im ^ 2 *
        ‖dslope F ((starRingEnd ℂ) (xiSpectralPoint q)) (xiSpectralPoint q)‖ ^ 2 ≤
      C * ‖xiResolventPoint X q‖)
    (heven : C * (396 / 6475) ≤
      ∑' q : XiZeroCopy, ‖xiWeilEvenPart F (xiSpectralPoint q)‖ ^ 2) :
    0 ≤ (xiWeilPolarization F F).re := by
  refine xiWeilPolarization_re_nonneg_of_tail_dominated hX hF hC (le_refl (1 / 2)) hΔ ?_
  have harg : ((1 / 2 : ℂ)) + (((1 / 2 : ℝ)) : ℂ) = 1 := by
    norm_num
  rw [harg, logDeriv_xi_one]
  have hre : (completedRiemannZeta₀ 1).re ≤ ‖completedRiemannZeta₀ 1‖ :=
    Complex.re_le_norm _
  have hval := norm_completedRiemannZeta₀_one_le
  have hjet : 2 * (completedRiemannZeta₀ 1).re ≤ 3 / 50 := by linarith
  have hpref : (65 + (1 / 2 + 1 / 2 : ℝ) ^ 2) / (2 * (1 / 2) * (65 - 1 / 4)) = 264 / 259 := by
    norm_num
  calc C * ((65 + (1 / 2 + 1 / 2 : ℝ) ^ 2) / (2 * (1 / 2) * (65 - 1 / 4)) *
        (2 * (completedRiemannZeta₀ 1).re))
      ≤ C * (396 / 6475) := by
        rw [hpref]
        have hstep : (264 / 259 : ℝ) * (2 * (completedRiemannZeta₀ 1).re) ≤
            264 / 259 * (3 / 50) := by
          nlinarith [hjet]
        have hnum : (264 / 259 : ℝ) * (3 / 50) = 396 / 6475 := by
          norm_num
        nlinarith [mul_le_mul_of_nonneg_left hstep hC]
    _ ≤ ∑' q : XiZeroCopy, ‖xiWeilEvenPart F (xiSpectralPoint q)‖ ^ 2 := heven

end

end RHTower
namespace RHTower

noncomputable section

/-- The ray jet is strictly positive at every probe: the budget identity's right-hand side is
the corpus's strictly positive Euler-ray response. -/
theorem logDeriv_xi_ray_re_pos {c : ℝ} (hc : 1 / 2 ≤ c) :
    0 < (logDeriv xi ((1 / 2 : ℂ) + (c : ℂ))).re := by
  have hcpos : (0 : ℝ) < c := lt_of_lt_of_le (by norm_num) hc
  rw [← xiSquaredEulerFullQ_eq_logDeriv_re hcpos, xiSquaredEulerFullQ]
  exact mul_pos hcpos (xiSquaredEulerFullResponse_pos (by positivity))

/-- **Cones annihilate detectors**: a test inside the positivity cone whose even energy
vanishes has no deviation moment at all.  Divisor-odd negativity witnesses can never enter any
unconditional positivity cone — unconditional positivity regions are spectrally silent, so no
bootstrap "cone positivity contradicts an off-line zero" can exist in principle. -/
theorem deviation_moment_eq_zero_of_cone_of_even_energy_eq_zero {X : ℝ}
    {F : ℂ → ℂ} {C c : ℝ} (hC : 0 ≤ C) (hc : 1 / 2 ≤ c)
    (hΔ : ∀ q : XiZeroCopy, (65 : ℝ) ≤ (xiSpectralPoint q).re ^ 2 →
      (xiSpectralPoint q).im ^ 2 *
        ‖dslope F ((starRingEnd ℂ) (xiSpectralPoint q)) (xiSpectralPoint q)‖ ^ 2 ≤
      C * ‖xiResolventPoint X q‖)
    (heven : C * ((65 + (c + 1 / 2) ^ 2) / (2 * c * (65 - 1 / 4)) *
        (2 * (logDeriv xi ((1 / 2 : ℂ) + (c : ℂ))).re)) ≤
      ∑' q : XiZeroCopy, ‖xiWeilEvenPart F (xiSpectralPoint q)‖ ^ 2)
    (hzero : (∑' q : XiZeroCopy, ‖xiWeilEvenPart F (xiSpectralPoint q)‖ ^ 2) = 0) :
    (∑' q : XiZeroCopy, (xiSpectralPoint q).im ^ 2 *
      ‖dslope F ((starRingEnd ℂ) (xiSpectralPoint q)) (xiSpectralPoint q)‖ ^ 2) = 0 := by
  have hcpos : (0 : ℝ) < c := lt_of_lt_of_le (by norm_num) hc
  have hjet := logDeriv_xi_ray_re_pos hc
  have hpref : (0 : ℝ) < (65 + (c + 1 / 2) ^ 2) / (2 * c * (65 - 1 / 4)) := by
    have h1 : (0 : ℝ) < 2 * c * (65 - 1 / 4) := by nlinarith
    positivity
  have hε : (0 : ℝ) < (65 + (c + 1 / 2) ^ 2) / (2 * c * (65 - 1 / 4)) *
      (2 * (logDeriv xi ((1 / 2 : ℂ) + (c : ℂ))).re) := by positivity
  have hC0 : C = 0 := by
    rw [hzero] at heven
    nlinarith [heven, hε, hC]
  have hall : ∀ q : XiZeroCopy, (xiSpectralPoint q).im ^ 2 *
      ‖dslope F ((starRingEnd ℂ) (xiSpectralPoint q)) (xiSpectralPoint q)‖ ^ 2 = 0 := by
    intro q
    by_cases hq : (65 : ℝ) ≤ (xiSpectralPoint q).re ^ 2
    · have h1 := hΔ q hq
      rw [hC0, zero_mul] at h1
      have h2 : (0 : ℝ) ≤ (xiSpectralPoint q).im ^ 2 *
          ‖dslope F ((starRingEnd ℂ) (xiSpectralPoint q)) (xiSpectralPoint q)‖ ^ 2 :=
        mul_nonneg (sq_nonneg _) (sq_nonneg _)
      linarith
    · by_contra hne
      exact hq (deviation_support_subset_tail (F := F) (Function.mem_support.mpr hne))
  rw [show (fun q : XiZeroCopy => (xiSpectralPoint q).im ^ 2 *
    ‖dslope F ((starRingEnd ℂ) (xiSpectralPoint q)) (xiSpectralPoint q)‖ ^ 2) =
    fun _ => (0 : ℝ) from funext hall]
  exact tsum_zero

/-- **The vacuity corollary**: a divisor-odd test inside the cone has identically zero Weil
diagonal — it detects nothing.  The cone and the negativity witnesses are disjoint families. -/
theorem xiWeilPolarization_re_eq_zero_of_cone_of_even_energy_eq_zero {X : ℝ}
    {F : ℂ → ℂ} (hF : XiWeilSquareSummable F) {C c : ℝ} (hC : 0 ≤ C) (hc : 1 / 2 ≤ c)
    (hΔ : ∀ q : XiZeroCopy, (65 : ℝ) ≤ (xiSpectralPoint q).re ^ 2 →
      (xiSpectralPoint q).im ^ 2 *
        ‖dslope F ((starRingEnd ℂ) (xiSpectralPoint q)) (xiSpectralPoint q)‖ ^ 2 ≤
      C * ‖xiResolventPoint X q‖)
    (heven : C * ((65 + (c + 1 / 2) ^ 2) / (2 * c * (65 - 1 / 4)) *
        (2 * (logDeriv xi ((1 / 2 : ℂ) + (c : ℂ))).re)) ≤
      ∑' q : XiZeroCopy, ‖xiWeilEvenPart F (xiSpectralPoint q)‖ ^ 2)
    (hzero : (∑' q : XiZeroCopy, ‖xiWeilEvenPart F (xiSpectralPoint q)‖ ^ 2) = 0) :
    (xiWeilPolarization F F).re = 0 := by
  rw [xiWeilPolarization_re_eq_deviation_moment hF, hzero,
    deviation_moment_eq_zero_of_cone_of_even_energy_eq_zero hC hc hΔ heven hzero]
  ring

end

end RHTower
