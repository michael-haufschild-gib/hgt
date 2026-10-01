import GaloisForLFunctions.RHTower.ReflectedCompactComplementDomination
import GaloisForLFunctions.HTGeometry.CauchyDominatedIntegralHolomorphy

open Complex MeasureTheory Set Metric
noncomputable section
namespace RHTower

/-- The translated contour is a continuous real integrand throughout the strip. -/
theorem continuous_reflectedCompactDeepIntegrand {N : ℝ} (hN : 0 < N)
    {z : ℂ} (hz : z.re < 9 / 2) (n : ℕ) :
    Continuous (reflectedCompactDeepIntegrand z N n) := by
  haveI : NeZero (N : ℂ) := ⟨Complex.ofReal_ne_zero.mpr hN.ne'⟩
  haveI : NeZero (n + 1 : ℂ) := ⟨by exact_mod_cast Nat.succ_ne_zero n⟩
  have hchi : Continuous (fun v : ℝ => zetaChi ((-7 / 2 : ℂ) + (v : ℂ) * I)) := by
    rw [continuous_iff_continuousAt]
    intro v
    apply (zetaChi_analyticAt ?_).continuousAt.comp
    · fun_prop
    · apply Complex.Gammaℝ_ne_zero_of_re_pos
      simp
      norm_num
  have hw : Continuous (fun v : ℝ => z - 9 / 2 + (v : ℂ) * I) := by fun_prop
  have hne (v : ℝ) : z - 9 / 2 + (v : ℂ) * I ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    simp at hh
    linarith
  have hker : Continuous (fun v : ℝ => smoothAFEGaussianKernel (z - 9 / 2 + (v : ℂ) * I)) :=
    (hw.pow 2).cexp.div hw hne
  exact ((hchi.mul ((continuous_const_cpow (n + 1 : ℂ)).comp (by fun_prop))).mul
    ((continuous_const_cpow (N : ℂ)).comp hw)).mul hker

/-- Every literal deep complementary coefficient is holomorphic in the open strip. -/
theorem differentiableOn_reflectedCompactDeepCoefficient {N : ℝ} (hN : 0 < N) (n : ℕ) :
    DifferentiableOn ℂ (fun z => reflectedCompactDeepCoefficient z N n)
      {z : ℂ | 0 < z.re ∧ z.re < 1} := by
  intro z hz
  let R : ℝ := min z.re (1 - z.re) / 2
  have hR : 0 < R := by dsimp only [R]; exact half_pos (lt_min hz.1 (sub_pos.mpr hz.2))
  have hR0 : R ≤ z.re := by dsimp only [R]; linarith [min_le_left z.re (1-z.re), hz.1]
  have hR1 : R ≤ 1 - z.re := by dsimp only [R]; linarith [min_le_right z.re (1-z.re), hz.2]
  let B : ℝ := |z.im| + R
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  obtain ⟨g, hg, hg0, hgb⟩ := exists_reflectedCompactDeepIntegrand_majorant hN hB
  have hrect (w : ℂ) (hw : w ∈ ball z R) :
      0 ≤ w.re ∧ w.re ≤ 1 ∧ |w.im| ≤ B := by
    have hdist : ‖w - z‖ < R := by simpa only [mem_ball, Complex.dist_eq] using hw
    have hr := (Complex.abs_re_le_norm (w-z)).trans_lt hdist
    have hi := (Complex.abs_im_le_norm (w-z)).trans_lt hdist
    simp only [Complex.sub_re, Complex.sub_im] at hr hi
    have hr' := abs_lt.mp hr
    have him := abs_add_le (w.im-z.im) z.im
    refine ⟨by linarith, by linarith, ?_⟩
    dsimp only [B]
    rw [sub_add_cancel] at him
    linarith
  have hdiff : DifferentiableAt ℂ (fun w : ℂ => ∫ v : ℝ,
      reflectedCompactDeepIntegrand w N n v) z := by
    apply GaloisForLFunctions.HTGeometry.differentiableAt_integral_of_cauchy_dominated hR
      (bound := fun v => g v * (1 / (n + 1 : ℝ) ^ (9 / 2 : ℝ)))
    · intro w hw
      exact (continuous_reflectedCompactDeepIntegrand hN (by linarith [(hrect w hw).2.1]) n).aestronglyMeasurable
    · intro v
      exact (differentiableOn_reflectedCompactDeepIntegrand hN n v).mono
        (fun w hw => by have := (hrect w hw).2.1; dsimp; linarith)
    · intro v w hw
      exact hgb w (hrect w hw).1 (hrect w hw).2.1 (hrect w hw).2.2 n v
    · exact hg.mul_const _
  exact (hdiff.const_smul (1 / (2 * Real.pi) : ℝ)).differentiableWithinAt

/-- On each compact spectral rectangle, all deep coefficients share a summable
arithmetic envelope, with no phase or integer dependence in its constant. -/
theorem exists_reflectedCompactDeepCoefficient_bound {N : ℝ} (hN : 0 < N)
    {B : ℝ} (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 → |z.im| ≤ B → ∀ n : ℕ,
      ‖reflectedCompactDeepCoefficient z N n‖ ≤ C * (1 / (n + 1 : ℝ) ^ (9 / 2 : ℝ)) := by
  obtain ⟨g, hg, hg0, hgb⟩ := exists_reflectedCompactDeepIntegrand_majorant hN hB
  let A : ℝ := (1 / (2 * Real.pi)) * ∫ v : ℝ, g v
  refine ⟨max 1 A, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro z hz0 hz1 hzi n
  have hp : 0 ≤ (1 / (2 * Real.pi) : ℝ) := by positivity
  have hi : ‖∫ v : ℝ, reflectedCompactDeepIntegrand z N n v‖ ≤
      (∫ v : ℝ, g v) * (1 / (n + 1 : ℝ) ^ (9 / 2 : ℝ)) := by
    calc
      _ ≤ ∫ v : ℝ, g v * (1 / (n + 1 : ℝ) ^ (9 / 2 : ℝ)) :=
        norm_integral_le_of_norm_le (hg.mul_const _)
          (Filter.Eventually.of_forall (hgb z hz0 hz1 hzi n))
      _ = _ := integral_mul_const _ _
  unfold reflectedCompactDeepCoefficient
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hp]
  calc
    _ ≤ (1 / (2 * Real.pi)) * ((∫ v : ℝ, g v) * (1 / (n + 1 : ℝ) ^ (9 / 2 : ℝ))) :=
      mul_le_mul_of_nonneg_left hi hp
    _ = A * (1 / (n + 1 : ℝ) ^ (9 / 2 : ℝ)) := by dsimp only [A]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

end RHTower

