import GaloisForLFunctions.RHTower.SmoothAFEZetaArbitraryNegativeEdge
import GaloisForLFunctions.RHTower.GammaDampedVerticalBound

/-!
# Deep reflected expansion on the displaced Levinson line

At `s = 1/2-d+i*tau`, choose the exact negative edge `Re w = d-4`.
Then `Re(s+w)=-7/2` and every reflected Dirichlet coefficient has the fixed
summable power `(n+1)^(-9/2)`.  No asymptotic replacement is made.
-/

noncomputable section

open Complex MeasureTheory Filter

namespace RHTower

theorem displacedLinePt_add_deepEdge
    (d tau v : ℝ) :
    displacedLinePt d tau + (((d - 4 : ℝ) : ℂ) + (v : ℂ) * I) =
      (((-7 / 2 : ℝ) : ℂ) + ((tau + v : ℝ) : ℂ) * I) := by
  unfold displacedLinePt
  push_cast
  ring

/-- Global polynomial growth of `chi` on `Re s=-7/2`, derived through the
zeta functional equation and Euler-half-plane reciprocal bound. -/
theorem exists_norm_zetaChi_neg_seven_halves_poly_le :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ t : ℝ,
      ‖zetaChi (((-7 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤
        C * (1 + |t|) ^ N := by
  obtain ⟨C, N, hC, hzeta⟩ :=
    exists_bound_norm_riemannZeta_vertical (-7 / 2) (by norm_num)
  refine ⟨2 * C, N, by positivity, fun t => ?_⟩
  let z : ℂ := (((-7 / 2 : ℝ) : ℂ) + (t : ℂ) * I)
  have hz0 : z ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    dsimp only [z] at hre
    norm_num at hre
  have hz1 : z ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    dsimp only [z] at hre
    norm_num at hre
  have hG : Complex.Gammaℝ (1 - z) ≠ 0 := by
    apply Complex.Gammaℝ_ne_zero_of_re_pos
    dsimp only [z]
    simp
    norm_num
  have hrightRe : (2 : ℝ) ≤ (1 - z).re := by
    dsimp only [z]
    simp
    norm_num
  have hright0 : riemannZeta (1 - z) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by linarith [hrightRe])
  have hfe := zeta_eq_zetaChi_mul hz0 hz1 hG
  have hchiEq : zetaChi z = riemannZeta z * (riemannZeta (1 - z))⁻¹ := by
    calc
      zetaChi z = zetaChi z * riemannZeta (1 - z) *
          (riemannZeta (1 - z))⁻¹ := by
            rw [mul_assoc, mul_inv_cancel₀ hright0, mul_one]
      _ = riemannZeta z * (riemannZeta (1 - z))⁻¹ := by rw [hfe]
  have hinv := norm_inv_riemannZeta_le_of_two_le_re hrightRe
  have hz := hzeta t
  rw [show (((-7 / 2 : ℝ) : ℂ) + (t : ℂ) * I) = z by rfl, hchiEq,
    norm_mul]
  calc
    ‖riemannZeta z‖ * ‖(riemannZeta (1 - z))⁻¹‖
      ≤ (C * (1 + |t|) ^ N) * 2 :=
        mul_le_mul hz hinv (norm_nonneg _) (by positivity)
    _ = (2 * C) * (1 + |t|) ^ N := by ring

theorem smoothAFEZetaMellinIntegrand_eq_reflected_tsum_displaced_deep
    {d tau x : ℝ} (v : ℝ) :
    smoothAFEZetaMellinIntegrand (displacedLinePt d tau) x
        (((d - 4 : ℝ) : ℂ) + (v : ℂ) * I) =
      ∑' n : ℕ, smoothAFEZetaReflectedTerm (displacedLinePt d tau) x n
        (((d - 4 : ℝ) : ℂ) + (v : ℂ) * I) := by
  apply smoothAFEZetaMellinIntegrand_eq_reflected_tsum
  rw [displacedLinePt_add_deepEdge]
  norm_num

theorem norm_smoothAFEZetaReflectedTerm_displaced_deep_le
    {x d : ℝ} (hx : 0 < x) (hd : 0 < d) (hdq : d ≤ 1 / 4)
    {C : ℝ} {N : ℕ} (hC : ∀ t : ℝ,
      ‖zetaChi (((-7 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤
        C * (1 + |t|) ^ N)
    (tau : ℝ) (n : ℕ) (v : ℝ) :
    ‖smoothAFEZetaReflectedTerm (displacedLinePt d tau) x n
        (((d - 4 : ℝ) : ℂ) + (v : ℂ) * I)‖ ≤
      (((1 / (n + 1 : ℝ) ^ (9 / 2 : ℝ)) * x ^ (d - 4) *
          (Real.exp ((d - 4) ^ 2) / |d - 4|) * C) *
        ((1 + |tau| + |v|) ^ N * Real.exp (-(v ^ 2)))) := by
  have hn : (0 : ℝ) < n + 1 := by exact_mod_cast Nat.succ_pos n
  have hdm4 : d - 4 ≠ 0 := by linarith
  have hkernel := norm_smoothAFEGaussianKernel_vertical_le_of_ne
    (σ := d - 4) hdm4 v
  have hchiBase := hC (tau + v)
  have hC0 : 0 ≤ C := by
    have hzero := hC 0
    simpa using (le_trans (norm_nonneg
      (zetaChi (((-7 / 2 : ℝ) : ℂ) + (0 : ℂ) * I))) hzero)
  have hshift : 1 + |tau + v| ≤ 1 + |tau| + |v| := by
    linarith [abs_add_le tau v]
  have hchi :
      ‖zetaChi (displacedLinePt d tau +
        (((d - 4 : ℝ) : ℂ) + (v : ℂ) * I))‖ ≤
        C * (1 + |tau| + |v|) ^ N := by
    rw [displacedLinePt_add_deepEdge]
    exact hchiBase.trans
      (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hshift N)
        hC0)
  rw [smoothAFEZetaReflectedTerm_eq_cpow, norm_mul, norm_mul, norm_mul,
    show (n : ℂ) + 1 = ((n + 1 : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_cpow_eq_rpow_re_of_pos hn,
    Complex.norm_cpow_eq_rpow_re_of_pos hx]
  have hexponent :
      (displacedLinePt d tau +
        (((d - 4 : ℝ) : ℂ) + (v : ℂ) * I) - 1).re = -9 / 2 := by
    rw [displacedLinePt_add_deepEdge]
    simp
    norm_num
  have hwre : ((((d - 4 : ℝ) : ℂ) + (v : ℂ) * I).re) = d - 4 := by simp
  rw [hexponent, show (-9 / 2 : ℝ) = -(9 / 2 : ℝ) by ring,
    Real.rpow_neg hn.le, hwre]
  calc
    ‖zetaChi (displacedLinePt d tau + (↑(d - 4) + ↑v * I))‖ *
          ((n + 1 : ℝ) ^ (9 / 2 : ℝ))⁻¹ * x ^ (d - 4) *
          ‖smoothAFEGaussianKernel (↑(d - 4) + ↑v * I)‖
      ≤ (C * (1 + |tau| + |v|) ^ N) *
          ((n + 1 : ℝ) ^ (9 / 2 : ℝ))⁻¹ * x ^ (d - 4) *
          ((Real.exp ((d - 4) ^ 2) / |d - 4|) * Real.exp (-(v ^ 2))) := by
        gcongr
    _ = (((1 / (n + 1 : ℝ) ^ (9 / 2 : ℝ)) * x ^ (d - 4) *
          (Real.exp ((d - 4) ^ 2) / |d - 4|) * C) *
        ((1 + |tau| + |v|) ^ N * Real.exp (-(v ^ 2)))) := by ring

theorem smoothAFEZetaReflectedTerm_displaced_deep_integrable
    {x d : ℝ} (hx : 0 < x) (hd : 0 < d) (hdq : d ≤ 1 / 4)
    (tau : ℝ) (n : ℕ) :
    Integrable (fun v : ℝ =>
      smoothAFEZetaReflectedTerm (displacedLinePt d tau) x n
        (((d - 4 : ℝ) : ℂ) + (v : ℂ) * I)) := by
  obtain ⟨C, N, hC, hchi⟩ := exists_norm_zetaChi_neg_seven_halves_poly_le
  let D : ℝ := (1 / (n + 1 : ℝ) ^ (9 / 2 : ℝ)) * x ^ (d - 4) *
    (Real.exp ((d - 4) ^ 2) / |d - 4|) * C
  apply Integrable.mono'
    ((integrable_shifted_pow_mul_exp_neg_sq (1 + |tau|) N).const_mul D)
  · haveI : NeZero (x : ℂ) :=
      ⟨Complex.ofReal_ne_zero.mpr hx.ne'⟩
    have hn : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    letI : NeZero (n + 1 : ℂ) := ⟨hn⟩
    let w : ℝ → ℂ := fun v => ((d - 4 : ℝ) : ℂ) + (v : ℂ) * I
    have hw : Continuous w := by dsimp only [w]; fun_prop
    have hchiCont : Continuous
        (fun v : ℝ => zetaChi (displacedLinePt d tau + w v)) := by
      rw [continuous_iff_continuousAt]
      intro v
      apply (zetaChi_analyticAt ?_).continuousAt.comp
      · fun_prop
      · apply Complex.Gammaℝ_ne_zero_of_re_pos
        have hpt := displacedLinePt_add_deepEdge d tau v
        dsimp only [w]
        rw [hpt]
        simp
        norm_num
    have hpowN : Continuous (fun v : ℝ =>
        (n + 1 : ℂ) ^ (displacedLinePt d tau + w v - 1)) :=
      (continuous_const_cpow (n + 1 : ℂ)).comp (by fun_prop)
    have hpowX : Continuous (fun v : ℝ => (x : ℂ) ^ (w v)) :=
      (continuous_const_cpow (x : ℂ)).comp hw
    have hwne : ∀ v : ℝ, w v ≠ 0 := by
      intro v hzero
      have hre := congrArg Complex.re hzero
      dsimp only [w] at hre
      simp at hre
      linarith
    have hkernel : Continuous
        (fun v : ℝ => smoothAFEGaussianKernel (w v)) := by
      unfold smoothAFEGaussianKernel
      exact (Complex.continuous_exp.comp (hw.pow 2)).div hw hwne
    rw [show (fun v : ℝ =>
        smoothAFEZetaReflectedTerm (displacedLinePt d tau) x n (w v)) =
      fun v => zetaChi (displacedLinePt d tau + w v) *
        (n + 1 : ℂ) ^ (displacedLinePt d tau + w v - 1) *
        (x : ℂ) ^ (w v) * smoothAFEGaussianKernel (w v) by
          funext v
          exact smoothAFEZetaReflectedTerm_eq_cpow _ _ _ _]
    exact (((hchiCont.mul hpowN).mul hpowX).mul hkernel).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun v => by
      simpa only [D, add_assoc] using
        norm_smoothAFEZetaReflectedTerm_displaced_deep_le hx hd hdq hchi tau n v

theorem summable_integral_norm_smoothAFEZetaReflectedTerm_displaced_deep
    {x d : ℝ} (hx : 0 < x) (hd : 0 < d) (hdq : d ≤ 1 / 4)
    (tau : ℝ) :
    Summable (fun n : ℕ => ∫ v : ℝ,
      ‖smoothAFEZetaReflectedTerm (displacedLinePt d tau) x n
        (((d - 4 : ℝ) : ℂ) + (v : ℂ) * I)‖) := by
  obtain ⟨C, N, hC, hchi⟩ := exists_norm_zetaChi_neg_seven_halves_poly_le
  let D : ℝ := x ^ (d - 4) *
    (Real.exp ((d - 4) ^ 2) / |d - 4|) * C *
      ∫ v : ℝ, (1 + |tau| + |v|) ^ N * Real.exp (-(v ^ 2))
  have hbase := summable_smoothAFEZetaMajorant
    (p := (9 / 2 : ℝ)) (by norm_num)
  have hmajor : Summable (fun n : ℕ =>
      (1 / (n + 1 : ℝ) ^ (9 / 2 : ℝ)) * D) := hbase.mul_right D
  refine Summable.of_nonneg_of_le
    (fun n => integral_nonneg fun _ => norm_nonneg _) (fun n => ?_) hmajor
  have hterm := smoothAFEZetaReflectedTerm_displaced_deep_integrable
    hx hd hdq tau n
  have hgauss := integrable_shifted_pow_mul_exp_neg_sq (1 + |tau|) N
  have hdom : Integrable (fun v : ℝ =>
      (((1 / (n + 1 : ℝ) ^ (9 / 2 : ℝ)) * x ^ (d - 4) *
          (Real.exp ((d - 4) ^ 2) / |d - 4|) * C) *
        ((1 + |tau| + |v|) ^ N * Real.exp (-(v ^ 2))))) := by
    simpa only [add_assoc] using hgauss.const_mul
      ((1 / (n + 1 : ℝ) ^ (9 / 2 : ℝ)) * x ^ (d - 4) *
        (Real.exp ((d - 4) ^ 2) / |d - 4|) * C)
  calc
    ∫ v : ℝ, ‖smoothAFEZetaReflectedTerm (displacedLinePt d tau) x n
        (((d - 4 : ℝ) : ℂ) + (v : ℂ) * I)‖
      ≤ ∫ v : ℝ,
          (((1 / (n + 1 : ℝ) ^ (9 / 2 : ℝ)) * x ^ (d - 4) *
              (Real.exp ((d - 4) ^ 2) / |d - 4|) * C) *
            ((1 + |tau| + |v|) ^ N * Real.exp (-(v ^ 2)))) := by
        apply integral_mono_ae hterm.norm hdom
        exact Filter.Eventually.of_forall fun v =>
          norm_smoothAFEZetaReflectedTerm_displaced_deep_le hx hd hdq hchi tau n v
    _ = (1 / (n + 1 : ℝ) ^ (9 / 2 : ℝ)) * D := by
      rw [integral_const_mul]
      dsimp only [D]
      ring

theorem integral_smoothAFEZetaMellinIntegrand_displaced_deep_eq_tsum
    {x d : ℝ} (hx : 0 < x) (hd : 0 < d) (hdq : d ≤ 1 / 4)
    (tau : ℝ) :
    (∫ v : ℝ, smoothAFEZetaMellinIntegrand (displacedLinePt d tau) x
        (((d - 4 : ℝ) : ℂ) + (v : ℂ) * I)) =
      ∑' n : ℕ, ∫ v : ℝ,
        smoothAFEZetaReflectedTerm (displacedLinePt d tau) x n
          (((d - 4 : ℝ) : ℂ) + (v : ℂ) * I) := by
  calc
    (∫ v : ℝ, smoothAFEZetaMellinIntegrand (displacedLinePt d tau) x
        (((d - 4 : ℝ) : ℂ) + (v : ℂ) * I)) =
      ∫ v : ℝ, ∑' n : ℕ,
        smoothAFEZetaReflectedTerm (displacedLinePt d tau) x n
          (((d - 4 : ℝ) : ℂ) + (v : ℂ) * I) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun v =>
          smoothAFEZetaMellinIntegrand_eq_reflected_tsum_displaced_deep v
    _ = ∑' n : ℕ, ∫ v : ℝ,
        smoothAFEZetaReflectedTerm (displacedLinePt d tau) x n
          (((d - 4 : ℝ) : ℂ) + (v : ℂ) * I) := by
      symm
      apply integral_tsum_of_summable_integral_norm
      · exact fun n =>
          smoothAFEZetaReflectedTerm_displaced_deep_integrable hx hd hdq tau n
      · exact summable_integral_norm_smoothAFEZetaReflectedTerm_displaced_deep
          hx hd hdq tau

/-- Normalized exact coefficient on the depth `4-d` reflected edge. -/
def smoothAFEZetaDisplacedDeepCoefficient
    (d tau x : ℝ) (n : ℕ) : ℂ :=
  (1 / (2 * Real.pi)) • ∫ v : ℝ,
    smoothAFEZetaReflectedTerm (displacedLinePt d tau) x n
      (((d - 4 : ℝ) : ℂ) + (v : ℂ) * I)

theorem smoothAFEZetaDualMellinEdge_displaced_deep_eq_tsum
    {x d : ℝ} (hx : 0 < x) (hd : 0 < d) (hdq : d ≤ 1 / 4)
    (tau : ℝ) :
    smoothAFEZetaDualMellinEdge (displacedLinePt d tau) x (4 - d) =
      ∑' n : ℕ, smoothAFEZetaDisplacedDeepCoefficient d tau x n := by
  unfold smoothAFEZetaDualMellinEdge smoothAFEZetaDisplacedDeepCoefficient
  rw [show (-(4 - d) : ℝ) = d - 4 by ring]
  rw [integral_smoothAFEZetaMellinIntegrand_displaced_deep_eq_tsum hx hd hdq]
  rw [Complex.real_smul, ← tsum_mul_left]
  apply tsum_congr
  intro n
  rw [Complex.real_smul]

/-- The original `Re w=-1` dual edge equals the fixed-exponent deep series. -/
theorem smoothAFEZetaDualMellinEdge_left_one_eq_displaced_deep_tsum
    {x d : ℝ} (hx : 0 < x) (hd : 0 < d) (hdq : d ≤ 1 / 4)
    (tau : ℝ) :
    smoothAFEZetaDualMellinEdge (displacedLinePt d tau) x 1 =
      ∑' n : ℕ, smoothAFEZetaDisplacedDeepCoefficient d tau x n := by
  rw [← smoothAFEZetaDualMellinEdge_displaced_deep_eq_tsum hx hd hdq tau]
  exact (smoothAFEZetaDualMellinEdge_displaced_deep_eq_left_one hx hd hdq).symm

end RHTower
