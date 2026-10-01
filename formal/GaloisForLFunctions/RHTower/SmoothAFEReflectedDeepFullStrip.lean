import GaloisForLFunctions.RHTower.SmoothAFEZetaDisplacedDeepCoefficientIdentification

open Complex MeasureTheory Filter Topology Set
noncomputable section
namespace RHTower

/-! The coupled deep edge is valid throughout the full strict strip. The base parameter
has real part 1/2-d in (0,1); the shifted numerator stays on Re=-7/2. -/

theorem norm_smoothAFEZetaReflectedTerm_displaced_deep_le_strip
    {x d : ℝ} (hx : 0 < x) (hd : 0 < d) (hdhalf : d < 1 / 2)
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

theorem smoothAFEZetaReflectedTerm_displaced_deep_integrable_strip
    {x d : ℝ} (hx : 0 < x) (hd : 0 < d) (hdhalf : d < 1 / 2)
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
        norm_smoothAFEZetaReflectedTerm_displaced_deep_le_strip hx hd hdhalf hchi tau n v

theorem tendsto_smoothAFEZetaReflectedTerm_deep_horizontal_strip
    {x d : ℝ} (hx : 0 < x) (hd0 : 0 ≤ d) (hdhalf : d < 1 / 2)
    (tau : ℝ) (n : ℕ) (epsilon : ℝ) (hepsilon : |epsilon| = 1) :
    Tendsto (fun T : ℝ => ∫ u in (d - 4)..(-1),
        smoothAFEZetaReflectedTerm (displacedLinePt d tau) x n
          ((u : ℂ) + ((epsilon * T : ℝ) : ℂ) * I))
      atTop (nhds 0) := by
  obtain ⟨C, N, hC, hchi⟩ := exists_norm_zetaChi_closed_deep_strip_poly_le
  let D : ℝ := C * Real.exp (4 * |Real.log x|) * Real.exp 16
  let M : ℝ → ℝ := fun T =>
    D * ((1 + |tau| + T) ^ N * Real.exp (-(T ^ 2)))
  have hM : Tendsto M atTop (nhds 0) := by
    have h := tendsto_shifted_pow_mul_exp_neg_sq (1 + |tau|) N
    simpa only [M, mul_zero] using h.const_mul D
  apply GaloisForLFunctions.HTGeometry.tendsto_intervalIntegral_of_tendsto_bound
    (M := M) (hgt := fun T => epsilon * T)
  · filter_upwards [eventually_ge_atTop (|tau| + 1)] with T hT
    intro u hu
    rw [uIoc_of_le (by linarith [hdhalf] : d - 4 ≤ -1)] at hu
    have hT0 : 0 ≤ T := by linarith [abs_nonneg tau]
    have hTne : (1 : ℝ) ≤ |epsilon * T| := by
      rw [abs_mul, hepsilon, one_mul, abs_of_nonneg hT0]
      linarith [abs_nonneg tau]
    let w : ℂ := (u : ℂ) + ((epsilon * T : ℝ) : ℂ) * I
    let z : ℂ := displacedLinePt d tau + w
    have hzReLow : -(7 / 2 : ℝ) ≤ z.re := by
      dsimp [z, w, displacedLinePt]
      norm_num
      linarith [hu.1]
    have hzReHigh : z.re ≤ -(1 / 2 : ℝ) := by
      dsimp [z, w, displacedLinePt]
      norm_num
      linarith [hu.2, hd0]
    have hzIm : z.im = tau + epsilon * T := by
      dsimp [z, w, displacedLinePt]
      simp [Complex.mul_im]
    have hheightLow : 1 ≤ |tau + epsilon * T| := by
      have hepsT : |epsilon * T| = T := by
        rw [abs_mul, hepsilon, one_mul, abs_of_nonneg hT0]
      calc
        (1 : ℝ) ≤ T - |tau| := by linarith
        _ ≤ |tau + epsilon * T| := by
          have hrev := abs_sub_abs_le_abs_sub (epsilon * T) (-tau)
          rw [hepsT, abs_neg, sub_neg_eq_add] at hrev
          simpa only [add_comm] using hrev
    have hchi' : ‖zetaChi z‖ ≤ C * (1 + |tau + epsilon * T|) ^ N := by
      have hzcart : ((z.re : ℂ) + (z.im : ℂ) * I) = z := by
        apply Complex.ext <;> simp
      rw [← hzcart]
      have hb := hchi z.re z.im hzReLow hzReHigh
        (by simpa only [hzIm] using hheightLow)
      simpa only [hzIm] using hb
    have hheight : 1 + |tau + epsilon * T| ≤ 1 + |tau| + T := by
      have hepsT : |epsilon * T| = T := by
        rw [abs_mul, hepsilon, one_mul, abs_of_nonneg hT0]
      linarith [abs_add_le tau (epsilon * T)]
    have hchi'' : ‖zetaChi z‖ ≤ C * (1 + |tau| + T) ^ N :=
      hchi'.trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hheight N) hC)
    have hn0 : (0 : ℝ) < n + 1 := by exact_mod_cast Nat.succ_pos n
    have hpowN : ‖(n + 1 : ℂ) ^ (z - 1)‖ ≤ 1 := by
      rw [show (n + 1 : ℂ) = ((n + 1 : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_cpow_eq_rpow_re_of_pos hn0]
      have hre : (z - 1).re ≤ 0 := by
        change z.re - 1 ≤ 0
        linarith [hzReHigh]
      have hn1R : (1 : ℝ) ≤ n + 1 := by
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
      simpa using Real.rpow_le_one_of_one_le_of_nonpos hn1R hre
    have hpowX : ‖(x : ℂ) ^ w‖ ≤ Real.exp (4 * |Real.log x|) := by
      have h := norm_cpow_horizontal_arbitrary_le
        (x := x) (c := (4 : ℝ)) (u := u) (v := epsilon * T)
        hx (by norm_num) (by linarith [hu.1, hd0]) (by linarith [hu.2])
      norm_num at h ⊢
      dsimp only [w]
      convert h using 1
      push_cast
      ring
    have hkernel0 := norm_smoothAFEGaussianKernel_horizontal_arbitrary_le
      (c := (4 : ℝ)) (u := u) (v := epsilon * T)
      (by norm_num) (by linarith [hu.1, hd0]) (by linarith [hu.2]) hTne
    have hkernel : ‖smoothAFEGaussianKernel w‖ ≤
        Real.exp 16 * Real.exp (-((epsilon * T) ^ 2)) := by
      dsimp only [w]
      norm_num at hkernel0 ⊢
      exact hkernel0
    rw [smoothAFEZetaReflectedTerm_eq_cpow, norm_mul, norm_mul, norm_mul]
    change ‖zetaChi z‖ * ‖(n + 1 : ℂ) ^ (z - 1)‖ *
        ‖(x : ℂ) ^ w‖ * ‖smoothAFEGaussianKernel w‖ ≤ M T
    calc
      ‖zetaChi z‖ * ‖(n + 1 : ℂ) ^ (z - 1)‖ *
          ‖(x : ℂ) ^ w‖ * ‖smoothAFEGaussianKernel w‖ ≤
        (C * (1 + |tau| + T) ^ N) * 1 *
          Real.exp (4 * |Real.log x|) *
          (Real.exp 16 * Real.exp (-((epsilon * T) ^ 2))) := by
        gcongr
      _ = M T := by
        dsimp only [M, D]
        have hepsilonSq : epsilon ^ 2 = 1 := by
          nlinarith [sq_abs epsilon]
        rw [show (epsilon * T) ^ 2 = T ^ 2 by
          calc
            (epsilon * T) ^ 2 = epsilon ^ 2 * T ^ 2 := by ring
            _ = T ^ 2 := by rw [hepsilonSq]; ring]
        ring
  · exact hM

/-- The deep coefficient is exactly the original conductor-oriented reflected
coefficient, coefficient by coefficient. -/
theorem smoothAFEZetaDisplacedDeepCoefficient_eq_general_strip
    {x d : ℝ} (hx : 0 < x) (hd : 0 < d) (hdhalf : d < 1 / 2)
    (tau : ℝ) (n : ℕ) :
    smoothAFEZetaDisplacedDeepCoefficient d tau x n =
      smoothAFEZetaDualCoefficientGeneral (displacedLinePt d tau) x n := by
  let G : ℂ → ℂ := fun w =>
    smoothAFEZetaReflectedTerm (displacedLinePt d tau) x n w
  have hbot := tendsto_smoothAFEZetaReflectedTerm_deep_horizontal_strip
    hx hd.le hdhalf tau n (-1) (by norm_num)
  have htop := tendsto_smoothAFEZetaReflectedTerm_deep_horizontal_strip
    hx hd.le hdhalf tau n 1 (by norm_num)
  have hshift :
      (∫ y : ℝ, G (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) =
        ∫ y : ℝ, G (((d - 4 : ℝ) : ℂ) + (y : ℂ) * I) := by
    apply GaloisForLFunctions.HTGeometry.integral_vertical_line_eq_of_horizontal_tendsto
      (G := G) (c := d - 4) (d := -1)
    · linarith [hdhalf]
    · dsimp only [G]
      exact differentiableOn_smoothAFEZetaReflectedTerm_deep_strip hx hd.le tau n
    · dsimp only [G]
      exact smoothAFEZetaReflectedTerm_displaced_deep_integrable_strip hx hd hdhalf tau n
    · dsimp only [G]
      norm_num
      exact smoothAFEZetaReflectedTerm_general_left_one_integrable hx
        (by rw [displacedLinePt_re]; linarith [hdhalf])
        (by rw [displacedLinePt_re]; linarith) n
    · dsimp only [G]
      simpa only [neg_one_mul] using hbot
    · dsimp only [G]
      simpa only [one_mul] using htop
  have hgeneral :
      smoothAFEZetaDualCoefficientGeneral (displacedLinePt d tau) x n =
        (((1 / (2 * Real.pi) : ℝ) : ℂ)) *
          ∫ v : ℝ, G ((-1 : ℂ) + (v : ℂ) * I) := by
    unfold smoothAFEZetaDualCoefficientGeneral smoothAFEZetaDualCutoffGeneral
    rw [Complex.real_smul,
      integral_smoothAFEZetaReflectedTerm_general_left_one_eq hx
        (by rw [displacedLinePt_re]; linarith [hdhalf])
        (by rw [displacedLinePt_re]; linarith) n]
    have hline :
        (∫ v : ℝ, smoothAFEDualRatioIntegrand (displacedLinePt d tau)
          (1 / (((n : ℝ) + 1) * x))
          (((-1 : ℝ) : ℂ) + (v : ℂ) * I)) =
        ∫ v : ℝ, smoothAFEDualRatioIntegrand (displacedLinePt d tau)
          (1 / (((n : ℝ) + 1) * x)) ((-1 : ℂ) + (v : ℂ) * I) := by
      apply integral_congr_ae
      filter_upwards [] with v
      congr 1
      norm_num
    rw [hline]
    ring
  unfold smoothAFEZetaDisplacedDeepCoefficient
  rw [Complex.real_smul]
  rw [hgeneral]
  congr 1
  simpa [G] using hshift.symm

end RHTower
