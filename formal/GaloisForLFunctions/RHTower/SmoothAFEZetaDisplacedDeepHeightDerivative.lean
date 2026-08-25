import GaloisForLFunctions.RHTower.SmoothAFEZetaDisplacedDeepCoefficientIdentification
import GaloisForLFunctions.RHTower.SmoothAFEZetaDisplacedFullDerivativeIdentity
import GaloisForLFunctions.HTGeometry.IntegralDerivativeZero
import GaloisForLFunctions.HTGeometry.CauchyFirstOrderStep

/-!
# Height derivative and Cauchy--Riemann transport on the deep AFE edge
-/

noncomputable section

open Complex MeasureTheory Filter Topology Set

namespace RHTower

/-- Height derivative of one reflected summand on the coupled deep edge. -/
def smoothAFEZetaDisplacedDeepHeightIntegrandDerivative
    (d x tau : ℝ) (n : ℕ) (v : ℝ) : ℂ :=
  let z : ℂ := (((-7 / 2 : ℝ) : ℂ) + ((tau + v : ℝ) : ℂ) * I)
  let w : ℂ := (((d - 4 : ℝ) : ℂ) + (v : ℂ) * I)
  (((deriv zetaChi z * I) * (n + 1 : ℂ) ^ (z - 1) +
      zetaChi z *
        ((n + 1 : ℂ) ^ (z - 1) * Complex.log (n + 1 : ℂ) * I)) *
    (x : ℂ) ^ w) * smoothAFEGaussianKernel w

/-- Normalized height derivative of one deep reflected coefficient. -/
def smoothAFEZetaDisplacedDeepCoefficientHeightDerivative
    (d x tau : ℝ) (n : ℕ) : ℂ :=
  (((1 / (2 * Real.pi) : ℝ) : ℂ)) *
    ∫ v : ℝ, smoothAFEZetaDisplacedDeepHeightIntegrandDerivative d x tau n v

/-- Compatible polynomial `chi` bound on the Cauchy strip surrounding
`Re z=-7/2`. -/
theorem exists_norm_zetaChi_deep_cauchy_strip_poly_le :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ (sigma t : ℝ),
      -(15 / 4 : ℝ) ≤ sigma → sigma ≤ -(13 / 4 : ℝ) → 1 ≤ |t| →
      ‖zetaChi ((sigma : ℂ) + (t : ℂ) * I)‖ ≤ C * (1 + |t|) ^ N := by
  obtain ⟨A, N, hA, hzeta⟩ := exists_bound_norm_riemannZeta_strip 4
  obtain ⟨B, hB, hinv⟩ :=
    exists_norm_inv_riemannZeta_le_of_three_halves_le_re
  refine ⟨A * B, N, mul_nonneg hA hB, fun sigma t hsLow hsHigh ht => ?_⟩
  let z : ℂ := (sigma : ℂ) + (t : ℂ) * I
  have hz0 : z ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    dsimp only [z] at hre
    simp at hre
    linarith
  have hz1 : z ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    dsimp only [z] at hre
    simp at hre
    linarith
  have hG : Complex.Gammaℝ (1 - z) ≠ 0 := by
    apply Complex.Gammaℝ_ne_zero_of_re_pos
    dsimp only [z]
    simp
    linarith
  have hright : (3 / 2 : ℝ) ≤ (1 - z).re := by
    dsimp only [z]
    simp
    linarith
  have hright0 : riemannZeta (1 - z) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by linarith [hright])
  have hfe := zeta_eq_zetaChi_mul hz0 hz1 hG
  have hchiEq : zetaChi z = riemannZeta z * (riemannZeta (1 - z))⁻¹ := by
    calc
      zetaChi z = zetaChi z * riemannZeta (1 - z) *
          (riemannZeta (1 - z))⁻¹ := by
        rw [mul_assoc, mul_inv_cancel₀ hright0, mul_one]
      _ = riemannZeta z * (riemannZeta (1 - z))⁻¹ := by rw [hfe]
  have hzeta' := hzeta sigma t
    (by rw [abs_of_nonpos (by linarith)]; linarith) ht
  have hinv' := hinv (1 - z) hright
  rw [show ((sigma : ℂ) + (t : ℂ) * I) = z by rfl, hchiEq, norm_mul]
  calc
    ‖riemannZeta z‖ * ‖(riemannZeta (1 - z))⁻¹‖ ≤
        (A * |t| ^ N) * B :=
      mul_le_mul hzeta' hinv' (norm_nonneg _) (by positivity)
    _ ≤ (A * B) * (1 + |t|) ^ N := by
      have hp : |t| ^ N ≤ (1 + |t|) ^ N :=
        pow_le_pow_left₀ (abs_nonneg t) (by linarith [abs_nonneg t]) N
      calc
        (A * |t| ^ N) * B = (A * B) * |t| ^ N := by ring
        _ ≤ (A * B) * (1 + |t|) ^ N :=
          mul_le_mul_of_nonneg_left hp (mul_nonneg hA hB)

theorem continuous_deriv_zetaChi_neg_seven_halves :
    Continuous (fun t : ℝ =>
      deriv zetaChi (((-7 / 2 : ℝ) : ℂ) + (t : ℂ) * I)) := by
  rw [continuous_iff_continuousAt]
  intro t
  let z : ℂ := (((-7 / 2 : ℝ) : ℂ) + (t : ℂ) * I)
  have hG : Complex.Gammaℝ (1 - z) ≠ 0 := by
    apply Complex.Gammaℝ_ne_zero_of_re_pos
    dsimp only [z]
    simp
    norm_num
  have hz := ((zetaChi_analyticAt hG).deriv).continuousAt
  have hline : ContinuousAt
      (fun u : ℝ => (((-7 / 2 : ℝ) : ℂ) + (u : ℂ) * I)) t := by
    fun_prop
  exact hz.comp_of_eq hline rfl

theorem continuous_zetaChi_neg_seven_halves_compatible :
    Continuous (fun t : ℝ =>
      zetaChi (((-7 / 2 : ℝ) : ℂ) + (t : ℂ) * I)) := by
  rw [continuous_iff_continuousAt]
  intro t
  let z : ℂ := (((-7 / 2 : ℝ) : ℂ) + (t : ℂ) * I)
  have hG : Complex.Gammaℝ (1 - z) ≠ 0 := by
    apply Complex.Gammaℝ_ne_zero_of_re_pos
    dsimp only [z]
    simp
    norm_num
  have hz := (zetaChi_analyticAt hG).continuousAt
  have hline : ContinuousAt
      (fun u : ℝ => (((-7 / 2 : ℝ) : ℂ) + (u : ℂ) * I)) t := by
    fun_prop
  exact hz.comp_of_eq hline rfl

/-- Compatible global polynomial bound for `chi'` on the fixed deep line,
obtained by one Cauchy step and compact control at bounded height. -/
theorem exists_norm_deriv_zetaChi_neg_seven_halves_compatible_le :
    ∃ (K : ℝ) (N : ℕ), 0 ≤ K ∧ ∀ t : ℝ,
      ‖deriv zetaChi (((-7 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤
        K * (1 + |t|) ^ N := by
  obtain ⟨C, N, hC, hchi⟩ := exists_norm_zetaChi_deep_cauchy_strip_poly_le
  obtain ⟨B, hB⟩ :=
    (isCompact_Icc (a := (-2 : ℝ)) (b := 2)).exists_bound_of_continuousOn
      continuous_deriv_zetaChi_neg_seven_halves.continuousOn
  let K : ℝ := 4 * C * 2 ^ N + max B 0
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  refine ⟨K, N, hK, fun t => ?_⟩
  by_cases ht : 2 ≤ |t|
  · let z : ℂ := (((-7 / 2 : ℝ) : ℂ) + (t : ℂ) * I)
    have hdiff : DiffContOnCl ℂ zetaChi (Metric.ball z (1 / 4 : ℝ)) := by
      have hd : DifferentiableOn ℂ zetaChi (Metric.closedBall z (1 / 4 : ℝ)) := by
        intro q hq
        have hreAbs : |q.re - z.re| ≤ (1 / 4 : ℝ) := by
          have h := Complex.abs_re_le_norm (q - z)
          have hdist : dist q z ≤ (1 / 4 : ℝ) :=
            Metric.mem_closedBall.mp hq
          have hnorm : ‖q - z‖ ≤ (1 / 4 : ℝ) := by
            simpa only [Complex.dist_eq] using hdist
          simpa only [Complex.sub_re] using h.trans hnorm
        have hqRe : q.re < 1 := by
          have hzRe : z.re = -7 / 2 := by simp [z]
          rw [hzRe] at hreAbs
          rcases abs_le.mp hreAbs with ⟨_, hu⟩
          linarith
        have hG : Complex.Gammaℝ (1 - q) ≠ 0 :=
          Complex.Gammaℝ_ne_zero_of_re_pos (by simp; linarith)
        exact (zetaChi_analyticAt hG).differentiableAt.differentiableWithinAt
      refine ⟨hd.mono Metric.ball_subset_closedBall, ?_⟩
      exact hd.continuousOn.mono Metric.closure_ball_subset_closedBall
    let M : ℝ := C * 2 ^ N * (1 + |t|) ^ N
    have hM : ∀ q ∈ Metric.sphere z (1 / 4 : ℝ), ‖zetaChi q‖ ≤ M := by
      intro q hq
      have hdist : dist q z = (1 / 4 : ℝ) := Metric.mem_sphere.mp hq
      have hreAbs : |q.re - z.re| ≤ (1 / 4 : ℝ) := by
        have h := Complex.abs_re_le_norm (q - z)
        have hnorm : ‖q - z‖ = (1 / 4 : ℝ) := by
          simpa only [Complex.dist_eq] using hdist
        simpa only [Complex.sub_re, hnorm] using h
      have himAbs : |q.im - z.im| ≤ (1 / 4 : ℝ) := by
        have h := Complex.abs_im_le_norm (q - z)
        have hnorm : ‖q - z‖ = (1 / 4 : ℝ) := by
          simpa only [Complex.dist_eq] using hdist
        simpa only [Complex.sub_im, hnorm] using h
      have hzRe : z.re = -7 / 2 := by simp [z]
      have hzIm : z.im = t := by simp [z]
      rw [hzRe] at hreAbs
      rw [hzIm] at himAbs
      have hqReLow : -(15 / 4 : ℝ) ≤ q.re := by
        rcases abs_le.mp hreAbs with ⟨hl, _⟩
        linarith
      have hqReHigh : q.re ≤ -(13 / 4 : ℝ) := by
        rcases abs_le.mp hreAbs with ⟨_, hu⟩
        linarith
      have hqImLow : 1 ≤ |q.im| := by
        have hrev := abs_sub_abs_le_abs_sub t q.im
        have hdiff : |t - q.im| ≤ (1 / 4 : ℝ) := by
          simpa only [abs_sub_comm] using himAbs
        linarith
      have hqImHigh : 1 + |q.im| ≤ 2 * (1 + |t|) := by
        have habs : |q.im| ≤ |t| + 1 / 4 := by
          linarith [abs_sub_abs_le_abs_sub q.im t]
        linarith [abs_nonneg t]
      have hbase := hchi q.re q.im hqReLow hqReHigh hqImLow
      have hzcart : ((q.re : ℂ) + (q.im : ℂ) * I) = q := by
        apply Complex.ext <;> simp
      rw [hzcart] at hbase
      calc
        ‖zetaChi q‖ ≤ C * (1 + |q.im|) ^ N := hbase
        _ ≤ C * (2 * (1 + |t|)) ^ N := by gcongr
        _ = M := by
          dsimp only [M]
          rw [mul_pow]
          ring
    have hcauchy := HTGeometry.norm_deriv_le_of_forall_mem_sphere_norm_le
      (f := zetaChi) (z := z) (R := (1 / 4 : ℝ)) (M := M)
      (by norm_num) hdiff hM
    have hcauchy' : ‖deriv zetaChi z‖ ≤ 4 * C * 2 ^ N * (1 + |t|) ^ N := by
      dsimp only [M] at hcauchy
      nlinarith
    dsimp only [K]
    dsimp only [z] at hcauchy'
    exact hcauchy'.trans (mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_right (le_max_right B 0))
      (pow_nonneg (by positivity) N))
  · have htIcc : t ∈ Icc (-2 : ℝ) 2 := by
      rw [not_le] at ht
      rcases abs_lt.mp ht with ⟨hl, hu⟩
      exact ⟨hl.le, hu.le⟩
    have hcompact := hB t htIcc
    have hpow : (1 : ℝ) ≤ (1 + |t|) ^ N :=
      one_le_pow₀ (by linarith [abs_nonneg t])
    calc
      ‖deriv zetaChi (((-7 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤ B := hcompact
      _ ≤ K := by
        dsimp only [K]
        exact (le_max_left B 0).trans (le_add_of_nonneg_left (by positivity))
      _ ≤ K * (1 + |t|) ^ N := by nlinarith

/-- Uniform Gaussian majorant for the deep-edge height derivative. -/
theorem exists_norm_smoothAFEZetaDisplacedDeepHeightIntegrandDerivative_le
    {x : ℝ} (hx : 0 < x) :
    ∃ (K : ℝ) (P : ℕ), 0 ≤ K ∧
      ∀ d : ℝ, 0 ≤ d → d ≤ 1 / 2 →
      ∀ tau : ℝ, ∀ n : ℕ, ∀ v : ℝ,
      ‖smoothAFEZetaDisplacedDeepHeightIntegrandDerivative d x tau n v‖ ≤
        K * (1 / (n + 1 : ℝ) ^ (9 / 2 : ℝ)) *
          (1 + Real.log (n + 1 : ℝ)) *
          ((1 + |tau| + |v|) ^ P * Real.exp (-(v ^ 2))) := by
  obtain ⟨C₀, N₀, hC₀, hchi₀⟩ := exists_norm_zetaChi_neg_seven_halves_poly_le
  obtain ⟨C₁, N₁, hC₁, hchi₁⟩ :=
    exists_norm_deriv_zetaChi_neg_seven_halves_compatible_le
  let P : ℕ := max N₀ N₁
  let K : ℝ := (C₀ + C₁) * Real.exp (4 * |Real.log x|) * Real.exp 16
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  refine ⟨K, P, hK, fun d hd₀ hdhalf tau n v => ?_⟩
  let z : ℂ := (((-7 / 2 : ℝ) : ℂ) + ((tau + v : ℝ) : ℂ) * I)
  let w : ℂ := (((d - 4 : ℝ) : ℂ) + (v : ℂ) * I)
  let q : ℝ := 1 + |tau| + |v|
  have hq1 : (1 : ℝ) ≤ q := by
    dsimp only [q]
    linarith [abs_nonneg tau, abs_nonneg v]
  have hshift : 1 + |tau + v| ≤ q := by
    dsimp only [q]
    linarith [abs_add_le tau v]
  have hchiBase := hchi₀ (tau + v)
  have hchiPow : (1 + |tau + v|) ^ N₀ ≤ q ^ P := by
    calc
      (1 + |tau + v|) ^ N₀ ≤ q ^ N₀ := by gcongr
      _ ≤ q ^ P := pow_le_pow_right₀ hq1 (Nat.le_max_left _ _)
  have hchi : ‖zetaChi z‖ ≤ C₀ * q ^ P := by
    dsimp only [z]
    exact hchiBase.trans (mul_le_mul_of_nonneg_left hchiPow hC₀)
  have hderivBase := hchi₁ (tau + v)
  have hderivPow : (1 + |tau + v|) ^ N₁ ≤ q ^ P := by
    calc
      (1 + |tau + v|) ^ N₁ ≤ q ^ N₁ := by gcongr
      _ ≤ q ^ P := pow_le_pow_right₀ hq1 (Nat.le_max_right _ _)
  have hderiv : ‖deriv zetaChi z‖ ≤ C₁ * q ^ P := by
    dsimp only [z]
    exact hderivBase.trans (mul_le_mul_of_nonneg_left hderivPow hC₁)
  have hn : (0 : ℝ) < n + 1 := by exact_mod_cast Nat.succ_pos n
  have hpowN : ‖(n + 1 : ℂ) ^ (z - 1)‖ =
      1 / (n + 1 : ℝ) ^ (9 / 2 : ℝ) := by
    rw [show (n + 1 : ℂ) = ((n + 1 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_cpow_eq_rpow_re_of_pos hn]
    have hre : (z - 1).re = -(9 / 2 : ℝ) := by
      dsimp only [z]
      simp
      norm_num
    rw [hre, Real.rpow_neg hn.le, one_div]
  have hlogNonneg : 0 ≤ Real.log (n + 1 : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ n + 1 by omega))
  have hlogEq : Complex.log (n + 1 : ℂ) =
      ((Real.log (n + 1 : ℝ) : ℝ) : ℂ) := by
    symm
    convert Complex.ofReal_log hn.le using 1
    norm_num
  have hlog : ‖Complex.log (n + 1 : ℂ)‖ = Real.log (n + 1 : ℝ) := by
    rw [hlogEq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlogNonneg]
  have hpowX : ‖(x : ℂ) ^ w‖ ≤ Real.exp (4 * |Real.log x|) := by
    have h := norm_cpow_horizontal_arbitrary_le
      (x := x) (c := (4 : ℝ)) (u := d - 4) (v := v)
      hx (by norm_num) (by linarith) (by linarith)
    norm_num at h ⊢
    dsimp only [w]
    convert h using 1
    push_cast
    ring
  have hdAbs : (1 : ℝ) ≤ |d - 4| := by
    rw [abs_of_nonpos (by linarith)]
    linarith
  have hdSq : (d - 4) ^ 2 ≤ 16 := by nlinarith [sq_nonneg d]
  have hkernel₀ := norm_smoothAFEGaussianKernel_vertical_le_of_ne
    (σ := d - 4) (by linarith) v
  have hkernel : ‖smoothAFEGaussianKernel w‖ ≤
      Real.exp 16 * Real.exp (-(v ^ 2)) := by
    dsimp only [w]
    calc
      ‖smoothAFEGaussianKernel (↑(d - 4) + ↑v * I)‖ ≤
          Real.exp ((d - 4) ^ 2) / |d - 4| * Real.exp (-(v ^ 2)) := hkernel₀
      _ ≤ Real.exp 16 * Real.exp (-(v ^ 2)) := by
        have he : Real.exp ((d - 4) ^ 2) ≤ Real.exp 16 :=
          Real.exp_le_exp.mpr hdSq
        have hi : Real.exp ((d - 4) ^ 2) / |d - 4| ≤ Real.exp 16 := by
          rw [div_le_iff₀ (zero_lt_one.trans_le hdAbs)]
          exact he.trans (le_mul_of_one_le_right (Real.exp_pos _).le hdAbs)
        gcongr
  have hcore :
      ‖(deriv zetaChi z * I) * (n + 1 : ℂ) ^ (z - 1) +
          zetaChi z * ((n + 1 : ℂ) ^ (z - 1) *
            Complex.log (n + 1 : ℂ) * I)‖ ≤
        (C₀ + C₁) * (1 / (n + 1 : ℝ) ^ (9 / 2 : ℝ)) *
          (1 + Real.log (n + 1 : ℝ)) * q ^ P := by
    calc
      _ ≤ ‖deriv zetaChi z‖ * ‖(n + 1 : ℂ) ^ (z - 1)‖ +
          ‖zetaChi z‖ * (‖(n + 1 : ℂ) ^ (z - 1)‖ *
            ‖Complex.log (n + 1 : ℂ)‖) := by
        simpa only [norm_mul, norm_I, one_mul, mul_one, mul_assoc] using
          norm_add_le
            ((deriv zetaChi z * I) * (n + 1 : ℂ) ^ (z - 1))
            (zetaChi z * ((n + 1 : ℂ) ^ (z - 1) *
              Complex.log (n + 1 : ℂ) * I))
      _ ≤ (C₁ * q ^ P) * (1 / (n + 1 : ℝ) ^ (9 / 2 : ℝ)) +
          (C₀ * q ^ P) * ((1 / (n + 1 : ℝ) ^ (9 / 2 : ℝ)) *
            Real.log (n + 1 : ℝ)) := by
        rw [hpowN, hlog]
        gcongr
      _ ≤ (C₀ + C₁) * (1 / (n + 1 : ℝ) ^ (9 / 2 : ℝ)) *
          (1 + Real.log (n + 1 : ℝ)) * q ^ P := by
        have hinv : 0 ≤ 1 / (n + 1 : ℝ) ^ (9 / 2 : ℝ) := by positivity
        have hq : 0 ≤ q ^ P := by positivity
        have hmissing₀ :
            0 ≤ C₀ * (1 / (n + 1 : ℝ) ^ (9 / 2 : ℝ)) * q ^ P := by
          positivity
        have hmissing₁ :
            0 ≤ C₁ * (1 / (n + 1 : ℝ) ^ (9 / 2 : ℝ)) *
              Real.log (n + 1 : ℝ) * q ^ P := by
          positivity
        nlinarith
  unfold smoothAFEZetaDisplacedDeepHeightIntegrandDerivative
  change ‖(((deriv zetaChi z * I) * (n + 1 : ℂ) ^ (z - 1) +
      zetaChi z * ((n + 1 : ℂ) ^ (z - 1) *
        Complex.log (n + 1 : ℂ) * I)) * (x : ℂ) ^ w) *
        smoothAFEGaussianKernel w‖ ≤ _
  rw [norm_mul, norm_mul]
  calc
    _ ≤ ((C₀ + C₁) * (1 / (n + 1 : ℝ) ^ (9 / 2 : ℝ)) *
          (1 + Real.log (n + 1 : ℝ)) * q ^ P) *
        Real.exp (4 * |Real.log x|) *
          (Real.exp 16 * Real.exp (-(v ^ 2))) := by gcongr
    _ = K * (1 / (n + 1 : ℝ) ^ (9 / 2 : ℝ)) *
          (1 + Real.log (n + 1 : ℝ)) *
          ((1 + |tau| + |v|) ^ P * Real.exp (-(v ^ 2))) := by
      dsimp only [K, q]
      ring

theorem continuous_smoothAFEZetaDisplacedDeepHeightIntegrandDerivative
    {x d : ℝ} (hx : 0 < x) (hd4 : d ≠ 4) (tau : ℝ) (n : ℕ) :
    Continuous (fun v : ℝ =>
      smoothAFEZetaDisplacedDeepHeightIntegrandDerivative d x tau n v) := by
  have hn : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  let Z : ℝ → ℂ := fun v =>
    (((-7 / 2 : ℝ) : ℂ) + ((tau + v : ℝ) : ℂ) * I)
  let W : ℝ → ℂ := fun v => (((d - 4 : ℝ) : ℂ) + (v : ℂ) * I)
  let chi : ℝ → ℂ := fun v => zetaChi (Z v)
  let dchi : ℝ → ℂ := fun v => deriv zetaChi (Z v)
  let powN : ℝ → ℂ := fun v => (n + 1 : ℂ) ^ (Z v - 1)
  let powX : ℝ → ℂ := fun v => (x : ℂ) ^ (W v)
  let kernel : ℝ → ℂ := fun v => smoothAFEGaussianKernel (W v)
  have hZ : Continuous Z := by dsimp only [Z]; fun_prop
  have hW : Continuous W := by dsimp only [W]; fun_prop
  have hchi : Continuous chi :=
    continuous_zetaChi_neg_seven_halves_compatible.comp
      (continuous_const.add continuous_id)
  have hderiv : Continuous dchi :=
    continuous_deriv_zetaChi_neg_seven_halves.comp
      (continuous_const.add continuous_id)
  have hpowN : Continuous powN := by
    rw [continuous_iff_continuousAt]
    intro v
    exact (Complex.hasStrictDerivAt_const_cpow
      (x := (n + 1 : ℂ)) (y := Z v - 1) (Or.inl hn)).hasDerivAt.continuousAt.comp_of_eq
        (hZ.continuousAt.sub continuousAt_const) rfl
  have hpowX : Continuous powX := by
    rw [continuous_iff_continuousAt]
    intro v
    exact (Complex.hasStrictDerivAt_const_cpow
      (x := (x : ℂ)) (y := W v) (Or.inl hxC)).hasDerivAt.continuousAt.comp_of_eq
        hW.continuousAt rfl
  have hkernel : Continuous kernel := by
    rw [continuous_iff_continuousAt]
    intro v
    have hW0 : W v ≠ 0 := by
      intro h
      have hre := congrArg Complex.re h
      dsimp only [W] at hre
      simp at hre
      exact hd4 (by linarith)
    exact (hasDerivAt_smoothAFEGaussianKernel hW0).continuousAt.comp_of_eq
      hW.continuousAt rfl
  change Continuous (fun v : ℝ =>
    (((dchi v * I) * powN v +
        chi v * (powN v *
          Complex.log (n + 1 : ℂ) * I)) *
      powX v) * kernel v)
  fun_prop

theorem hasDerivAt_smoothAFEZetaReflectedTerm_displaced_deep_height
    {d x : ℝ} (tau : ℝ) (n : ℕ) (v : ℝ) :
    HasDerivAt
      (fun u : ℝ => smoothAFEZetaReflectedTerm (displacedLinePt d u) x n
        (((d - 4 : ℝ) : ℂ) + (v : ℂ) * I))
      (smoothAFEZetaDisplacedDeepHeightIntegrandDerivative d x tau n v) tau := by
  let w : ℂ := (((d - 4 : ℝ) : ℂ) + (v : ℂ) * I)
  let z : ℂ := displacedLinePt d tau + w
  have hn : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hGamma : Gammaℝ (1 - z) ≠ 0 := by
    apply Gammaℝ_ne_zero_of_re_pos
    rw [show z = (((-7 / 2 : ℝ) : ℂ) +
        ((tau + v : ℝ) : ℂ) * I) by
      dsimp only [z, w]
      exact displacedLinePt_add_deepEdge d tau v]
    simp
    norm_num
  have hline := (hasDerivAt_displacedLinePt d tau).add_const w
  have hchi := ((zetaChi_analyticAt hGamma).differentiableAt.hasDerivAt.comp tau hline)
  have hpowC := (Complex.hasStrictDerivAt_const_cpow
    (x := (n + 1 : ℂ)) (y := z - 1) (Or.inl hn)).hasDerivAt
  have hpow := hpowC.comp tau (hline.sub_const 1)
  have hmain := (hchi.mul hpow).mul_const ((x : ℂ) ^ w)
  have hfull := hmain.mul_const (smoothAFEGaussianKernel w)
  have hfun : (fun u : ℝ =>
      smoothAFEZetaReflectedTerm (displacedLinePt d u) x n w) =
      fun u : ℝ =>
        ((zetaChi (displacedLinePt d u + w) *
          (n + 1 : ℂ) ^ (displacedLinePt d u + w - 1)) *
          (x : ℂ) ^ w) * smoothAFEGaussianKernel w := by
    funext u
    exact smoothAFEZetaReflectedTerm_eq_cpow (displacedLinePt d u) x n w
  rw [hfun]
  dsimp only [smoothAFEZetaDisplacedDeepHeightIntegrandDerivative]
  have hzw : displacedLinePt d tau + w = z := by rfl
  have hzDeep : z =
      (((-7 / 2 : ℝ) : ℂ) + ((tau + v : ℝ) : ℂ) * I) := by
    dsimp only [z, w]
    exact displacedLinePt_add_deepEdge d tau v
  have hzwDeep : displacedLinePt d tau + w =
      (((-7 / 2 : ℝ) : ℂ) + ((tau + v : ℝ) : ℂ) * I) := by
    rw [hzw, hzDeep]
  simp only [Function.comp_apply, Pi.mul_apply] at hfull
  rw [hzwDeep] at hfull
  rw [hzDeep] at hfull
  simpa [hzw, hzwDeep, hzDeep, z, w, mul_assoc,
    mul_left_comm, mul_comm] using hfull

theorem smoothAFEZetaDisplacedDeepHeightIntegrandDerivative_integrable
    {x d : ℝ} (hx : 0 < x) (hd₀ : 0 ≤ d) (hdhalf : d ≤ 1 / 2)
    (tau : ℝ) (n : ℕ) :
    Integrable (fun v : ℝ =>
      smoothAFEZetaDisplacedDeepHeightIntegrandDerivative d x tau n v) := by
  obtain ⟨K, P, hK, hpoint⟩ :=
    exists_norm_smoothAFEZetaDisplacedDeepHeightIntegrandDerivative_le hx
  let A : ℝ := K * (1 / (n + 1 : ℝ) ^ (9 / 2 : ℝ)) *
    (1 + Real.log (n + 1 : ℝ))
  apply Integrable.mono'
    ((integrable_shifted_pow_mul_exp_neg_sq (1 + |tau|) P).const_mul A)
  · exact (continuous_smoothAFEZetaDisplacedDeepHeightIntegrandDerivative
      hx (by linarith) tau n).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun v => by
      simpa only [A] using hpoint d hd₀ hdhalf tau n v

theorem hasDerivAt_smoothAFEZetaDisplacedDeepCoefficient_height
    {x d : ℝ} (hx : 0 < x) (hd : 0 < d) (hdq : d ≤ 1 / 4)
    (tau : ℝ) (n : ℕ) :
    HasDerivAt
      (fun u : ℝ => smoothAFEZetaDisplacedDeepCoefficient d u x n)
      (smoothAFEZetaDisplacedDeepCoefficientHeightDerivative d x tau n) tau := by
  let F : ℝ → ℝ → ℂ := fun u v =>
    smoothAFEZetaReflectedTerm (displacedLinePt d u) x n
      (((d - 4 : ℝ) : ℂ) + (v : ℂ) * I)
  let F' : ℝ → ℝ → ℂ := fun u v =>
    smoothAFEZetaDisplacedDeepHeightIntegrandDerivative d x u n v
  obtain ⟨K, P, hK, hpoint⟩ :=
    exists_norm_smoothAFEZetaDisplacedDeepHeightIntegrandDerivative_le hx
  let A : ℝ := K * (1 / (n + 1 : ℝ) ^ (9 / 2 : ℝ)) *
    (1 + Real.log (n + 1 : ℝ))
  let bound : ℝ → ℝ := fun v =>
    A * ((2 + |tau| + |v|) ^ P * Real.exp (-(v ^ 2)))
  have hparam := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (s := Metric.ball tau 1) (bound := bound)
    (Metric.ball_mem_nhds tau (by norm_num : (0 : ℝ) < 1))
    (Filter.Eventually.of_forall fun u =>
      (continuous_smoothAFEZetaReflectedTerm_displaced_deep
        hx (by linarith) u n).aestronglyMeasurable)
    (smoothAFEZetaReflectedTerm_displaced_deep_integrable hx hd hdq tau n)
    (smoothAFEZetaDisplacedDeepHeightIntegrandDerivative_integrable
      hx hd.le (hdq.trans (by norm_num)) tau n).aestronglyMeasurable
    (Filter.Eventually.of_forall fun v u hu => by
      have hudist : |u - tau| < 1 := by
        have hdist := Metric.mem_ball.mp hu
        simpa only [Real.dist_eq, abs_sub_comm] using hdist
      have huabs : |u| < |tau| + 1 := by
        calc
          |u| = |(u - tau) + tau| := by ring_nf
          _ ≤ |u - tau| + |tau| := abs_add_le _ _
          _ < 1 + |tau| := by linarith
          _ = |tau| + 1 := by ring
      have hheight : 1 + |u| + |v| ≤ 2 + |tau| + |v| := by
        linarith
      have hlogn : 0 ≤ Real.log (n + 1 : ℝ) :=
        Real.log_nonneg (by exact_mod_cast (show 1 ≤ n + 1 by omega))
      have hpref :
          0 ≤ K * (1 / (n + 1 : ℝ) ^ (9 / 2 : ℝ)) *
            (1 + Real.log (n + 1 : ℝ)) := by
        positivity
      dsimp only [F']
      calc
        ‖smoothAFEZetaDisplacedDeepHeightIntegrandDerivative d x u n v‖ ≤
            K * (1 / (n + 1 : ℝ) ^ (9 / 2 : ℝ)) *
              (1 + Real.log (n + 1 : ℝ)) *
              ((1 + |u| + |v|) ^ P * Real.exp (-(v ^ 2))) :=
          hpoint d hd.le (hdq.trans (by norm_num)) u n v
        _ ≤ K * (1 / (n + 1 : ℝ) ^ (9 / 2 : ℝ)) *
              (1 + Real.log (n + 1 : ℝ)) *
              ((2 + |tau| + |v|) ^ P * Real.exp (-(v ^ 2))) := by
          gcongr
        _ = bound v := by
          dsimp only [bound, A])
    ((integrable_shifted_pow_mul_exp_neg_sq (2 + |tau|) P).const_mul A)
    (Filter.Eventually.of_forall fun v u hu => by
      dsimp only [F, F']
      exact hasDerivAt_smoothAFEZetaReflectedTerm_displaced_deep_height
        u n v)
  have hfun :
      (fun u : ℝ => smoothAFEZetaDisplacedDeepCoefficient d u x n) =
        fun u : ℝ => (((1 / (2 * Real.pi) : ℝ) : ℂ)) *
          ∫ v : ℝ, smoothAFEZetaReflectedTerm (displacedLinePt d u) x n
            (((d - 4 : ℝ) : ℂ) + (v : ℂ) * I) := by
    funext u
    unfold smoothAFEZetaDisplacedDeepCoefficient
    rw [Complex.real_smul]
  rw [hfun]
  unfold smoothAFEZetaDisplacedDeepCoefficientHeightDerivative
  exact hparam.2.const_mul (((1 / (2 * Real.pi) : ℝ) : ℂ))

theorem smoothAFEZetaDisplacedDeepCoefficientHeightDerivative_eq_general
    {x d : ℝ} (hx : 0 < x) (hd : 0 < d) (hdq : d ≤ 1 / 4)
    (tau : ℝ) (n : ℕ) :
    smoothAFEZetaDisplacedDeepCoefficientHeightDerivative d x tau n =
      smoothAFEZetaDisplacedDualCoefficientHeightDerivative d x tau n := by
  have hdeep := hasDerivAt_smoothAFEZetaDisplacedDeepCoefficient_height
    hx hd hdq tau n
  have hgeneral := hasDerivAt_smoothAFEZetaDualCoefficientGeneral_displaced
    hd hdq hx tau n
  have hfun :
      (fun u : ℝ => smoothAFEZetaDisplacedDeepCoefficient d u x n) =
        fun u : ℝ => smoothAFEZetaDualCoefficientGeneral
          (displacedLinePt d u) x n := by
    funext u
    exact smoothAFEZetaDisplacedDeepCoefficient_eq_general hx hd hdq u n
  rw [hfun] at hdeep
  exact hdeep.unique hgeneral

/-- Frequency differentiation on the deep edge is the sum of height
differentiation and `i` times coupled displacement differentiation. -/
theorem hasDerivAt_smoothAFEZetaReflectedTerm_displaced_deep_frequency
    {x d : ℝ} (hx : 0 < x) (hd4 : d ≠ 4)
    (tau : ℝ) (n : ℕ) (v : ℝ) :
    HasDerivAt
      (fun u : ℝ => smoothAFEZetaReflectedTerm (displacedLinePt d tau) x n
        (((d - 4 : ℝ) : ℂ) + (u : ℂ) * I))
      (smoothAFEZetaDisplacedDeepHeightIntegrandDerivative d x tau n v +
        I * smoothAFEZetaDisplacedDeepIntegrandDerivative d x tau n v) v := by
  let W : ℝ → ℂ := fun u => (((d - 4 : ℝ) : ℂ) + (u : ℂ) * I)
  let Z : ℝ → ℂ := fun u => displacedLinePt d tau + W u
  have hn : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hW0 : W v ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    dsimp only [W] at hre
    simp at hre
    exact hd4 (by linarith)
  have hGamma : Gammaℝ (1 - Z v) ≠ 0 := by
    apply Gammaℝ_ne_zero_of_re_pos
    rw [show Z v = (((-7 / 2 : ℝ) : ℂ) +
        ((tau + v : ℝ) : ℂ) * I) by
      dsimp only [Z, W]
      exact displacedLinePt_add_deepEdge d tau v]
    simp
    norm_num
  have hW : HasDerivAt W I v := by
    have hreal := (hasDerivAt_id v).ofReal_comp
    simpa [W] using
      (hreal.mul_const I).const_add (((d - 4 : ℝ) : ℂ))
  have hZ : HasDerivAt Z I v := by
    simpa [Z] using hW.const_add (displacedLinePt d tau)
  have hchi := (zetaChi_analyticAt hGamma).differentiableAt.hasDerivAt.comp v hZ
  have hpowC := (Complex.hasStrictDerivAt_const_cpow
    (x := (n + 1 : ℂ)) (y := Z v - 1) (Or.inl hn)).hasDerivAt
  have hpow := hpowC.comp v (hZ.sub_const 1)
  have hpowXC := (Complex.hasStrictDerivAt_const_cpow
    (x := (x : ℂ)) (y := W v) (Or.inl hxC)).hasDerivAt
  have hpowX := hpowXC.comp v hW
  have hkernel := (hasDerivAt_smoothAFEGaussianKernel hW0).comp v hW
  let D : ℂ :=
    (((deriv zetaChi (Z v) * I) * (n + 1 : ℂ) ^ (Z v - 1) +
        zetaChi (Z v) * ((n + 1 : ℂ) ^ (Z v - 1) *
          Complex.log (n + 1 : ℂ) * I)) * (x : ℂ) ^ (W v) +
      (zetaChi (Z v) * (n + 1 : ℂ) ^ (Z v - 1)) *
        ((x : ℂ) ^ (W v) * Complex.log (x : ℂ) * I)) *
        smoothAFEGaussianKernel (W v) +
      (zetaChi (Z v) * (n + 1 : ℂ) ^ (Z v - 1) *
        (x : ℂ) ^ (W v)) *
          (smoothAFEGaussianKernelDerivative (W v) * I)
  have hfull : HasDerivAt
      ((((zetaChi ∘ Z) *
          ((fun y : ℂ => (n + 1 : ℂ) ^ y) ∘ fun u : ℝ => Z u - 1)) *
          ((fun y : ℂ => (x : ℂ) ^ y) ∘ W)) *
            (smoothAFEGaussianKernel ∘ W)) D v := by
    dsimp only [D]
    exact (((hchi.mul hpow).mul hpowX).mul hkernel)
  have hfun :
      (fun u : ℝ => smoothAFEZetaReflectedTerm (displacedLinePt d tau) x n (W u)) =
        fun u : ℝ =>
          zetaChi (Z u) * (n + 1 : ℂ) ^ (Z u - 1) *
            (x : ℂ) ^ (W u) * smoothAFEGaussianKernel (W u) := by
    funext u
    exact smoothAFEZetaReflectedTerm_eq_cpow
      (displacedLinePt d tau) x n (W u)
  change HasDerivAt (fun u : ℝ =>
    smoothAFEZetaReflectedTerm (displacedLinePt d tau) x n (W u)) _ v
  rw [hfun]
  have hprod :
      (fun u : ℝ => zetaChi (Z u) * (n + 1 : ℂ) ^ (Z u - 1) *
          (x : ℂ) ^ (W u) * smoothAFEGaussianKernel (W u)) =
        (((zetaChi ∘ Z) *
          ((fun y : ℂ => (n + 1 : ℂ) ^ y) ∘ fun u : ℝ => Z u - 1)) *
          ((fun y : ℂ => (x : ℂ) ^ y) ∘ W)) *
            (smoothAFEGaussianKernel ∘ W) := by
    rfl
  rw [hprod]
  unfold smoothAFEZetaDisplacedDeepHeightIntegrandDerivative
    smoothAFEZetaDisplacedDeepIntegrandDerivative
  have hZdeep : Z v =
      (((-7 / 2 : ℝ) : ℂ) + ((tau + v : ℝ) : ℂ) * I) := by
    dsimp only [Z, W]
    exact displacedLinePt_add_deepEdge d tau v
  have hderivEq :
      (((deriv zetaChi
          (((-7 / 2 : ℝ) : ℂ) + ((tau + v : ℝ) : ℂ) * I) * I) *
            (n + 1 : ℂ) ^
              ((((-7 / 2 : ℝ) : ℂ) + ((tau + v : ℝ) : ℂ) * I) - 1) +
          zetaChi (((-7 / 2 : ℝ) : ℂ) + ((tau + v : ℝ) : ℂ) * I) *
            ((n + 1 : ℂ) ^
                ((((-7 / 2 : ℝ) : ℂ) + ((tau + v : ℝ) : ℂ) * I) - 1) *
              Complex.log (n + 1 : ℂ) * I)) *
          (x : ℂ) ^ (((d - 4 : ℝ) : ℂ) + (v : ℂ) * I)) *
            smoothAFEGaussianKernel (((d - 4 : ℝ) : ℂ) + (v : ℂ) * I) +
        I *
          ((zetaChi (((-7 / 2 : ℝ) : ℂ) + ((tau + v : ℝ) : ℂ) * I) *
              (n + 1 : ℂ) ^
                ((((-7 / 2 : ℝ) : ℂ) + ((tau + v : ℝ) : ℂ) * I) - 1)) *
            (((x : ℂ) ^ (((d - 4 : ℝ) : ℂ) + (v : ℂ) * I) *
                Complex.log (x : ℂ)) *
                smoothAFEGaussianKernel (((d - 4 : ℝ) : ℂ) + (v : ℂ) * I) +
              (x : ℂ) ^ (((d - 4 : ℝ) : ℂ) + (v : ℂ) * I) *
                smoothAFEGaussianKernelDerivative
                  (((d - 4 : ℝ) : ℂ) + (v : ℂ) * I))) = D := by
    dsimp only [D]
    rw [hZdeep]
    ring
  rw [hderivEq]
  exact hfull

theorem tendsto_smoothAFEZetaReflectedTerm_displaced_deep_atTop_zero
    {x d : ℝ} (hx : 0 < x) (hd : 0 < d) (hdq : d ≤ 1 / 4)
    (tau : ℝ) (n : ℕ) :
    Tendsto (fun v : ℝ =>
      smoothAFEZetaReflectedTerm (displacedLinePt d tau) x n
        (((d - 4 : ℝ) : ℂ) + (v : ℂ) * I)) atTop (nhds 0) := by
  obtain ⟨C, N, hC, hchi⟩ := exists_norm_zetaChi_neg_seven_halves_poly_le
  let D : ℝ := (1 / (n + 1 : ℝ) ^ (9 / 2 : ℝ)) * x ^ (d - 4) *
    (Real.exp ((d - 4) ^ 2) / |d - 4|) * C
  let M : ℝ → ℝ := fun v =>
    D * ((1 + |tau| + v) ^ N * Real.exp (-(v ^ 2)))
  have hM : Tendsto M atTop (nhds 0) := by
    have h := tendsto_shifted_pow_mul_exp_neg_sq (1 + |tau|) N
    simpa only [M, mul_zero] using h.const_mul D
  refine squeeze_zero_norm' ?_ hM
  filter_upwards [eventually_ge_atTop 0] with v hv
  have hb := norm_smoothAFEZetaReflectedTerm_displaced_deep_le
    hx hd hdq hchi tau n v
  simpa only [M, abs_of_nonneg hv] using hb

theorem tendsto_smoothAFEZetaReflectedTerm_displaced_deep_atBot_zero
    {x d : ℝ} (hx : 0 < x) (hd : 0 < d) (hdq : d ≤ 1 / 4)
    (tau : ℝ) (n : ℕ) :
    Tendsto (fun v : ℝ =>
      smoothAFEZetaReflectedTerm (displacedLinePt d tau) x n
        (((d - 4 : ℝ) : ℂ) + (v : ℂ) * I)) atBot (nhds 0) := by
  obtain ⟨C, N, hC, hchi⟩ := exists_norm_zetaChi_neg_seven_halves_poly_le
  let D : ℝ := (1 / (n + 1 : ℝ) ^ (9 / 2 : ℝ)) * x ^ (d - 4) *
    (Real.exp ((d - 4) ^ 2) / |d - 4|) * C
  let M : ℝ → ℝ := fun v =>
    D * ((1 + |tau| - v) ^ N * Real.exp (-(v ^ 2)))
  have htop := tendsto_shifted_pow_mul_exp_neg_sq (1 + |tau|) N
  have hM : Tendsto M atBot (nhds 0) := by
    have hcomp := (htop.const_mul D).comp tendsto_neg_atBot_atTop
    change Tendsto (fun v : ℝ =>
      D * ((1 + |tau| - v) ^ N * Real.exp (-(v ^ 2)))) atBot (nhds 0)
    convert hcomp using 1
    · funext v
      simp only [Function.comp_apply, neg_sq, sub_eq_add_neg]
    · simp
  refine squeeze_zero_norm' ?_ hM
  filter_upwards [eventually_le_atBot 0] with v hv
  have hb := norm_smoothAFEZetaReflectedTerm_displaced_deep_le
    hx hd hdq hchi tau n v
  simpa only [M, D, abs_of_nonpos hv, sub_eq_add_neg] using hb

/-- The coupled displacement derivative is `i` times the height derivative
of the same deep coefficient. -/
theorem smoothAFEZetaDisplacedDeepCoefficientDerivative_eq_I_mul_height
    {x d : ℝ} (hx : 0 < x) (hd : 0 < d) (hdq : d ≤ 1 / 4)
    (tau : ℝ) (n : ℕ) :
    smoothAFEZetaDisplacedDeepCoefficientDerivative d x tau n =
      I * smoothAFEZetaDisplacedDeepCoefficientHeightDerivative d x tau n := by
  let H : ℝ → ℂ := fun v =>
    smoothAFEZetaDisplacedDeepHeightIntegrandDerivative d x tau n v
  let D : ℝ → ℂ := fun v =>
    smoothAFEZetaDisplacedDeepIntegrandDerivative d x tau n v
  let F : ℝ → ℂ := fun v =>
    smoothAFEZetaReflectedTerm (displacedLinePt d tau) x n
      (((d - 4 : ℝ) : ℂ) + (v : ℂ) * I)
  have hH : Integrable H := by
    dsimp only [H]
    exact smoothAFEZetaDisplacedDeepHeightIntegrandDerivative_integrable
      hx hd.le (hdq.trans (by norm_num)) tau n
  have hD : Integrable D := by
    dsimp only [D]
    exact smoothAFEZetaDisplacedDeepIntegrandDerivative_integrable
      hx hd.le (hdq.trans (by norm_num)) tau n
  have hderiv : ∀ v : ℝ, HasDerivAt F (H v + I * D v) v := by
    intro v
    exact hasDerivAt_smoothAFEZetaReflectedTerm_displaced_deep_frequency
      hx (by linarith) tau n v
  have htop : Tendsto F atTop (nhds 0) := by
    dsimp only [F]
    exact tendsto_smoothAFEZetaReflectedTerm_displaced_deep_atTop_zero
      hx hd hdq tau n
  have hbot : Tendsto F atBot (nhds 0) := by
    dsimp only [F]
    exact tendsto_smoothAFEZetaReflectedTerm_displaced_deep_atBot_zero
      hx hd hdq tau n
  have hzero :=
    GaloisForLFunctions.HTGeometry.integral_derivative_eq_zero_of_tendsto
      hderiv (hH.add (hD.const_mul I)) htop hbot
  have hzero' : (∫ v : ℝ, H v) + I * (∫ v : ℝ, D v) = 0 := by
    simpa only [integral_add hH (hD.const_mul I), integral_const_mul] using hzero
  have hDI : (∫ v : ℝ, D v) = I * (∫ v : ℝ, H v) := by
    have hmul : I * ((∫ v : ℝ, H v) + I * (∫ v : ℝ, D v)) = 0 := by
      rw [hzero', mul_zero]
    rw [mul_add, ← mul_assoc, I_mul_I, neg_one_mul] at hmul
    linear_combination -hmul
  unfold smoothAFEZetaDisplacedDeepCoefficientDerivative
    smoothAFEZetaDisplacedDeepCoefficientHeightDerivative
  dsimp only [D, H] at hDI ⊢
  rw [hDI]
  ring

/-- The deep coupled-displacement derivative is the conductor-oriented
weighted height derivative, rotated by `-i`. -/
theorem smoothAFEZetaDisplacedDeepCoefficientDerivative_eq_neg_I_mul_weighted
    {x d : ℝ} (hx : 0 < x) (hd : 0 < d) (hdq : d ≤ 1 / 4)
    (tau : ℝ) (n : ℕ) :
    smoothAFEZetaDisplacedDeepCoefficientDerivative d x tau n =
      -I * smoothAFEZetaDisplacedReflectedWeightedHeightDerivativeTerm
        d x tau n := by
  rw [smoothAFEZetaDisplacedDeepCoefficientDerivative_eq_I_mul_height
      hx hd hdq tau n,
    smoothAFEZetaDisplacedDeepCoefficientHeightDerivative_eq_general
      hx hd hdq tau n,
    smoothAFEZetaDisplacedDualCoefficientHeightDerivative_eq_neg_weighted
      hd hdq (by norm_num : (0 : ℝ) < 1 / 4)
        (by norm_num : (1 / 4 : ℝ) ≤ 1 / 4) hx tau n]
  ring

/-- Finite reflected heads inherit the same quarter-turn relation. -/
theorem sum_smoothAFEZetaDisplacedReflectedWeightedHeightDerivativeTerm_eq_I_mul_deep
    {x d : ℝ} (hx : 0 < x) (hd : 0 < d) (hdq : d ≤ 1 / 4)
    (tau : ℝ) (L : ℕ) :
    (∑ n ∈ Finset.range L,
        smoothAFEZetaDisplacedReflectedWeightedHeightDerivativeTerm
          d x tau n) =
      I * ∑ n ∈ Finset.range L,
        smoothAFEZetaDisplacedDeepCoefficientDerivative d x tau n := by
  have hpoint : ∀ n : ℕ,
      smoothAFEZetaDisplacedReflectedWeightedHeightDerivativeTerm d x tau n =
        I * smoothAFEZetaDisplacedDeepCoefficientDerivative d x tau n := by
    intro n
    rw [smoothAFEZetaDisplacedDeepCoefficientDerivative_eq_neg_I_mul_weighted
      hx hd hdq tau n]
    rw [neg_mul, mul_neg, ← mul_assoc, I_mul_I]
    ring
  simp_rw [hpoint]
  rw [Finset.mul_sum]

end RHTower
