import Mathlib.Analysis.Calculus.SmoothSeries
import GaloisForLFunctions.RHTower.SmoothAFEZetaDisplacedDeepDualCoefficientDerivative

/-!
# Termwise displacement derivative of the deep reflected expansion

The coefficient derivatives inherit the fixed `(n+1)^(-9/2)` majorant from
the deep edge.  This supplies absolute derivative summability, legitimizes
termwise differentiation, and transports the resulting derivative back to
the original `Re w = -1` dual Mellin edge by the exact contour identity.
-/

noncomputable section

open Complex MeasureTheory Filter Set

namespace RHTower

theorem smoothAFEZetaDisplacedDeepIntegrandDerivative_integrable
    {x d : ℝ} (hx : 0 < x) (hd0 : 0 ≤ d) (hdhalf : d ≤ 1 / 2)
    (tau : ℝ) (n : ℕ) :
    Integrable (fun v : ℝ =>
      smoothAFEZetaDisplacedDeepIntegrandDerivative d x tau n v) := by
  obtain ⟨K, N, hK, hpoint⟩ :=
    exists_norm_smoothAFEZetaDisplacedDeepIntegrandDerivative_le hx
  let D : ℝ := K * (1 / (n + 1 : ℝ) ^ (9 / 2 : ℝ))
  apply Integrable.mono'
    ((integrable_shifted_pow_mul_exp_neg_sq (1 + |tau|) N).const_mul D)
  · exact (continuous_smoothAFEZetaDisplacedDeepIntegrandDerivative
      hx (by linarith) tau n).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun v => by
      simpa only [D] using hpoint d hd0 hdhalf tau n v

/-- Uniform fixed-power bound for the normalized deep coefficient derivative. -/
theorem exists_norm_smoothAFEZetaDisplacedDeepCoefficientDerivative_le
    {x : ℝ} (hx : 0 < x) (tau : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ d : ℝ, 0 ≤ d → d ≤ 1 / 2 → ∀ n : ℕ,
      ‖smoothAFEZetaDisplacedDeepCoefficientDerivative d x tau n‖ ≤
        B * (1 / (n + 1 : ℝ) ^ (9 / 2 : ℝ)) := by
  obtain ⟨K, N, hK, hpoint⟩ :=
    exists_norm_smoothAFEZetaDisplacedDeepIntegrandDerivative_le hx
  let J : ℝ := ∫ v : ℝ,
    (1 + |tau| + |v|) ^ N * Real.exp (-(v ^ 2))
  let c : ℝ := 1 / (2 * Real.pi)
  let B : ℝ := c * K * J
  have hc : 0 ≤ c := by dsimp only [c]; positivity
  have hJ : 0 ≤ J := by
    dsimp only [J]
    exact integral_nonneg fun v => by positivity
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  refine ⟨B, hB, fun d hd0 hdhalf n => ?_⟩
  let D : ℝ := K * (1 / (n + 1 : ℝ) ^ (9 / 2 : ℝ))
  have hmajor : Integrable (fun v : ℝ =>
      D * ((1 + |tau| + |v|) ^ N * Real.exp (-(v ^ 2)))) :=
    (integrable_shifted_pow_mul_exp_neg_sq (1 + |tau|) N).const_mul D
  have hint :
      ‖∫ v : ℝ, smoothAFEZetaDisplacedDeepIntegrandDerivative d x tau n v‖ ≤
        ∫ v : ℝ,
          D * ((1 + |tau| + |v|) ^ N * Real.exp (-(v ^ 2))) := by
    apply MeasureTheory.norm_integral_le_of_norm_le hmajor
    exact Filter.Eventually.of_forall fun v => by
      simpa only [D] using hpoint d hd0 hdhalf tau n v
  unfold smoothAFEZetaDisplacedDeepCoefficientDerivative
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc]
  calc
    c * ‖∫ v : ℝ,
        smoothAFEZetaDisplacedDeepIntegrandDerivative d x tau n v‖
      ≤ c * ∫ v : ℝ,
          D * ((1 + |tau| + |v|) ^ N * Real.exp (-(v ^ 2))) :=
        mul_le_mul_of_nonneg_left hint hc
    _ = B * (1 / (n + 1 : ℝ) ^ (9 / 2 : ℝ)) := by
      rw [integral_const_mul]
      dsimp only [B, D, J]
      ring

theorem summable_smoothAFEZetaDisplacedDeepCoefficientDerivative
    {x d : ℝ} (hx : 0 < x) (hd0 : 0 ≤ d) (hdhalf : d ≤ 1 / 2)
    (tau : ℝ) :
    Summable (fun n : ℕ =>
      smoothAFEZetaDisplacedDeepCoefficientDerivative d x tau n) := by
  obtain ⟨B, hB, hbound⟩ :=
    exists_norm_smoothAFEZetaDisplacedDeepCoefficientDerivative_le hx tau
  have hmajor := (summable_smoothAFEZetaMajorant
    (p := (9 / 2 : ℝ)) (by norm_num)).mul_left B
  exact Summable.of_norm_bounded hmajor (hbound d hd0 hdhalf)

theorem summable_smoothAFEZetaDisplacedDeepCoefficient
    {x d : ℝ} (hx : 0 < x) (hd : 0 < d) (hdq : d ≤ 1 / 4)
    (tau : ℝ) :
    Summable (fun n : ℕ => smoothAFEZetaDisplacedDeepCoefficient d tau x n) := by
  have hnorm :=
    summable_integral_norm_smoothAFEZetaReflectedTerm_displaced_deep
      hx hd hdq tau
  have hint : Summable (fun n : ℕ => ∫ v : ℝ,
      smoothAFEZetaReflectedTerm (displacedLinePt d tau) x n
        (((d - 4 : ℝ) : ℂ) + (v : ℂ) * I)) :=
    Summable.of_norm_bounded hnorm fun n =>
      MeasureTheory.norm_integral_le_integral_norm _
  have hscaled := hint.mul_left (((1 / (2 * Real.pi) : ℝ) : ℂ))
  simpa only [smoothAFEZetaDisplacedDeepCoefficient, Complex.real_smul] using hscaled

/-- The exact deep reflected coefficient series differentiates term by term. -/
theorem hasDerivAt_smoothAFEZetaDisplacedDeepCoefficient_tsum
    {x d : ℝ} (hx : 0 < x) (hd : 0 < d) (hdq : d < 1 / 4)
    (tau : ℝ) :
    HasDerivAt
      (fun u : ℝ => ∑' n : ℕ, smoothAFEZetaDisplacedDeepCoefficient u tau x n)
      (∑' n : ℕ, smoothAFEZetaDisplacedDeepCoefficientDerivative d x tau n) d := by
  obtain ⟨B, hB, hbound⟩ :=
    exists_norm_smoothAFEZetaDisplacedDeepCoefficientDerivative_le hx tau
  let major : ℕ → ℝ := fun n =>
    B * (1 / (n + 1 : ℝ) ^ (9 / 2 : ℝ))
  have hmajor : Summable major := by
    dsimp only [major]
    exact (summable_smoothAFEZetaMajorant
      (p := (9 / 2 : ℝ)) (by norm_num)).mul_left B
  have hterm : ∀ n : ℕ, ∀ u ∈ Ioo (0 : ℝ) (1 / 4),
      HasDerivAt
        (fun y : ℝ => smoothAFEZetaDisplacedDeepCoefficient y tau x n)
        (smoothAFEZetaDisplacedDeepCoefficientDerivative u x tau n) u := by
    intro n u hu
    exact hasDerivAt_smoothAFEZetaDisplacedDeepCoefficient
      hx hu.1 hu.2.le tau n
  have hderivBound : ∀ n : ℕ, ∀ u ∈ Ioo (0 : ℝ) (1 / 4),
      ‖smoothAFEZetaDisplacedDeepCoefficientDerivative u x tau n‖ ≤ major n := by
    intro n u hu
    dsimp only [major]
    exact hbound u hu.1.le (by linarith [hu.2]) n
  have hdmem : d ∈ Ioo (0 : ℝ) (1 / 4) := ⟨hd, hdq⟩
  exact hasDerivAt_tsum_of_isPreconnected hmajor isOpen_Ioo
    (convex_Ioo (0 : ℝ) (1 / 4)).isPreconnected hterm hderivBound hdmem
    (summable_smoothAFEZetaDisplacedDeepCoefficient hx hd hdq.le tau) hdmem

/-- Exact displacement derivative of the original reflected `Re w=-1` edge,
obtained by differentiating its equal fixed-exponent deep series. -/
theorem hasDerivAt_smoothAFEZetaDualMellinEdge_left_one_displaced_deep
    {x d : ℝ} (hx : 0 < x) (hd : 0 < d) (hdq : d < 1 / 4)
    (tau : ℝ) :
    HasDerivAt
      (fun u : ℝ =>
        smoothAFEZetaDualMellinEdge (displacedLinePt u tau) x 1)
      (∑' n : ℕ, smoothAFEZetaDisplacedDeepCoefficientDerivative d x tau n) d := by
  have hsum :=
    hasDerivAt_smoothAFEZetaDisplacedDeepCoefficient_tsum hx hd hdq tau
  have heq :
      (fun u : ℝ => smoothAFEZetaDualMellinEdge (displacedLinePt u tau) x 1) =ᶠ[nhds d]
        fun u : ℝ => ∑' n : ℕ, smoothAFEZetaDisplacedDeepCoefficient u tau x n := by
    filter_upwards [(isOpen_Ioo.mem_nhds ⟨hd, hdq⟩)] with u hu
    exact smoothAFEZetaDualMellinEdge_left_one_eq_displaced_deep_tsum
      hx hu.1 hu.2.le tau
  exact hsum.congr_of_eventuallyEq heq

end RHTower
