import GaloisForLFunctions.RHTower.SmoothAFEZetaDisplacedDeepValueTruncation
import GaloisForLFunctions.RHTower.SmoothAFEReflectedDeepFullStrip
import GaloisForLFunctions.RHTower.SmoothAFEZetaRightReflectedPrimal

open MeasureTheory Complex Filter
noncomputable section
namespace RHTower

/-- The deep coefficient bound keeps its exact smoothing power outside the constant. -/
theorem exists_norm_smoothAFEZetaDisplacedDeepCoefficient_uniform_scale_le
    {d : ℝ} (hd : 0 < d) (hdhalf : d < 1 / 2) :
    ∃ D : ℝ, 0 ≤ D ∧
      ∀ x : ℝ, 0 < x → ∀ tau : ℝ, ∀ n : ℕ,
      ‖smoothAFEZetaDisplacedDeepCoefficient d tau x n‖ ≤
        D * x ^ (d - 4) * (1 + |tau|) ^ 4 *
          (1 / (n + 1 : ℝ) ^ (9 / 2 : ℝ)) := by
  obtain ⟨C, hC, hchi⟩ :=
    exists_norm_zetaChi_neg_seven_halves_le
  let K : ℝ := (Real.exp ((d - 4) ^ 2) / |d - 4|) * C
  let J : ℝ := ∫ v : ℝ, (1 + |v|) ^ 4 * Real.exp (-(v ^ 2))
  let c : ℝ := 1 / (2 * Real.pi)
  let D : ℝ := c * K * J
  have hc : 0 ≤ c := by dsimp only [c]; positivity
  have hC0 : 0 ≤ C := hC.le
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hJ : 0 ≤ J := by
    dsimp only [J]
    exact integral_nonneg fun v => by positivity
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  refine ⟨D, hD, fun x hx tau n => ?_⟩
  let a : ℝ := 1 + |tau|
  let b : ℝ := 1 / (n + 1 : ℝ) ^ (9 / 2 : ℝ)
  let M : ℝ := K * x ^ (d - 4) * b * a ^ 4
  have hshift : ∀ v : ℝ,
      1 + |tau| + |v| ≤ a * (1 + |v|) := by
    intro v
    dsimp only [a]
    nlinarith [abs_nonneg tau, abs_nonneg v,
      mul_nonneg (abs_nonneg tau) (abs_nonneg v)]
  have hmajor : Integrable (fun v : ℝ =>
      M * ((1 + |v|) ^ 4 * Real.exp (-(v ^ 2)))) :=
    (integrable_shifted_pow_mul_exp_neg_sq 1 4).const_mul M
  have hint :
      ‖∫ v : ℝ,
          smoothAFEZetaReflectedTerm (displacedLinePt d tau) x n
            (((d - 4 : ℝ) : ℂ) + (v : ℂ) * I)‖ ≤
        ∫ v : ℝ, M * ((1 + |v|) ^ 4 * Real.exp (-(v ^ 2))) := by
    apply MeasureTheory.norm_integral_le_of_norm_le hmajor
    exact Filter.Eventually.of_forall fun v => by
      calc
        ‖smoothAFEZetaReflectedTerm (displacedLinePt d tau) x n
            (((d - 4 : ℝ) : ℂ) + (v : ℂ) * I)‖ ≤
            K * x ^ (d - 4) * b *
              ((1 + |tau| + |v|) ^ 4 * Real.exp (-(v ^ 2))) := by
          have h := norm_smoothAFEZetaReflectedTerm_displaced_deep_le_strip
            hx hd hdhalf hchi tau n v
          dsimp only [K, b]
          convert h using 1
          ring
        _ ≤ K * x ^ (d - 4) * b *
            ((a * (1 + |v|)) ^ 4 * Real.exp (-(v ^ 2))) := by
          gcongr
          exact hshift v
        _ = M * ((1 + |v|) ^ 4 * Real.exp (-(v ^ 2))) := by
          dsimp only [M]
          rw [mul_pow]
          ring
  unfold smoothAFEZetaDisplacedDeepCoefficient
  rw [Complex.real_smul, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hc]
  calc
    c * ‖∫ v : ℝ,
        smoothAFEZetaReflectedTerm (displacedLinePt d tau) x n
          (((d - 4 : ℝ) : ℂ) + (v : ℂ) * I)‖
      ≤ c * ∫ v : ℝ,
          M * ((1 + |v|) ^ 4 * Real.exp (-(v ^ 2))) :=
        mul_le_mul_of_nonneg_left hint hc
    _ = D * x ^ (d - 4) * (1 + |tau|) ^ 4 *
          (1 / (n + 1 : ℝ) ^ (9 / 2 : ℝ)) := by
      rw [integral_const_mul]
      dsimp only [D, M, J, a, b]
      ring

/-- The original complementary coefficient is the reflected literal deep coefficient. -/
theorem smoothAFEZetaRightComplementCoefficient_eq_neg_chi_mul_deep
    {d x : ℝ} (hd : 0 < d) (hdhalf : d < 1 / 2) (hx : 0 < x)
    (tau : ℝ) (n : ℕ) :
    smoothAFEZetaRightComplementCoefficient d tau x n =
      -zetaChi (rightDisplacedLinePt d tau) *
        smoothAFEZetaDisplacedDeepCoefficient d (-tau) x n := by
  rw [smoothAFEZetaDisplacedDeepCoefficient_eq_general_strip hx hd hdhalf,
    smoothAFEZetaDualCoefficientGeneral_displaced_eq_neg_weight hx]
  rw [displacedLinePt_neg_sub_one_eq_neg_rightDisplacedLinePt]
  unfold smoothAFEZetaRightComplementCoefficient
  have hchi := zetaChi_right_mul_reflected_left hd hdhalf tau
  calc
    _ = (zetaChi (rightDisplacedLinePt d tau) *
          zetaChi (displacedLinePt d (-tau))) *
        ((n + 1 : ℂ) ^ (-rightDisplacedLinePt d tau) *
          smoothAFEZetaDisplacedDualWeight d (-tau) ((n + 1 : ℝ) * x)) := by
      rw [hchi, one_mul]
    _ = _ := by ring

end RHTower
