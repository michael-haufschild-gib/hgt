import GaloisForLFunctions.RHTower.SmoothAFEZetaDisplacedDeepDerivativeTruncation
import GaloisForLFunctions.RHTower.DeningerPoissonMoebius
import GaloisForLFunctions.HTGeometry.VerticalStripContourShift

/-!
# Identification of deep and conductor-oriented reflected coefficients

Each reflected summand is holomorphic between the original `Re w=-1` edge
and the coupled deep edge `Re w=d-4`.  Gaussian horizontal decay therefore
shifts the contour coefficient-by-coefficient, not merely after summing.
-/

noncomputable section

open Complex MeasureTheory Filter Topology Set LSeries

namespace RHTower

private theorem summable_nat_rpow_neg_three_halves :
    Summable (fun n : ℕ => (n : ℝ) ^ (-(3 / 2 : ℝ))) :=
  Real.summable_nat_rpow.mpr (by norm_num)

private theorem norm_moebius_lSeries_term_le_three_halves
    {s : ℂ} (hs : (3 / 2 : ℝ) ≤ s.re) (n : ℕ) :
    ‖LSeries.term (fun m => ((ArithmeticFunction.moebius m : ℤ) : ℂ)) s n‖ ≤
      (n : ℝ) ^ (-(3 / 2 : ℝ)) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    have hn0 : (0 : ℝ) < n := by positivity
    have hcoeff :
        ‖((ArithmeticFunction.moebius n : ℤ) : ℂ)‖ ≤ 1 :=
      norm_moebius_le_one n
    rw [LSeries.term_of_ne_zero hn, norm_div, norm_natCast_cpow hn1]
    have hpowPos : (0 : ℝ) < (n : ℝ) ^ s.re :=
      Real.rpow_pos_of_pos hn0 _
    rw [Real.rpow_neg hn0.le]
    apply (div_le_iff₀ hpowPos).2
    calc
      ‖((ArithmeticFunction.moebius n : ℤ) : ℂ)‖ ≤ 1 := hcoeff
      _ ≤ ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹ * (n : ℝ) ^ s.re := by
        rw [inv_mul_eq_div, le_div_iff₀ (Real.rpow_pos_of_pos hn0 _)]
        simpa only [one_mul] using Real.rpow_le_rpow_of_exponent_le hnR hs

/-- Reciprocal zeta is uniformly bounded on `Re s ≥ 3/2`. -/
theorem exists_norm_inv_riemannZeta_le_of_three_halves_le_re :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s : ℂ, (3 / 2 : ℝ) ≤ s.re →
      ‖(riemannZeta s)⁻¹‖ ≤ B := by
  let B : ℝ := ∑' n : ℕ, (n : ℝ) ^ (-(3 / 2 : ℝ))
  have hB : 0 ≤ B := tsum_nonneg fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _
  refine ⟨B, hB, fun s hs => ?_⟩
  have hs1 : 1 < s.re := by linarith
  rw [← LSeries_moebius_eq_inv_riemannZeta hs1]
  exact norm_lSeries_le_of_term_bound summable_nat_rpow_neg_three_halves
    (norm_moebius_lSeries_term_le_three_halves hs)

/-- Polynomial `chi` growth uniformly on the closed negative strip used by
the coefficient contour shift, at height at least one. -/
theorem exists_norm_zetaChi_closed_deep_strip_poly_le :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ (sigma t : ℝ),
      -(7 / 2 : ℝ) ≤ sigma → sigma ≤ -(1 / 2 : ℝ) → 1 ≤ |t| →
      ‖zetaChi ((sigma : ℂ) + (t : ℂ) * I)‖ ≤ C * (1 + |t|) ^ N := by
  obtain ⟨A, N, hA, hzeta⟩ := exists_bound_norm_riemannZeta_strip (7 / 2)
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
  have hzeta' := hzeta sigma t (by rw [abs_of_nonpos (by linarith)]; linarith) ht
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

theorem differentiableOn_smoothAFEZetaReflectedTerm_deep_strip
    {x d : ℝ} (hx : 0 < x) (hd0 : 0 ≤ d)
    (tau : ℝ) (n : ℕ) :
    DifferentiableOn ℂ
      (fun w : ℂ =>
        smoothAFEZetaReflectedTerm (displacedLinePt d tau) x n w)
      (GaloisForLFunctions.HTGeometry.verticalStrip (d - 4) (-1)) := by
  intro w hw
  have hn : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hw0 : w ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith [hw.2]
  have hG : Complex.Gammaℝ (1 - (displacedLinePt d tau + w)) ≠ 0 := by
    apply Complex.Gammaℝ_ne_zero_of_re_pos
    change 0 < 1 - ((displacedLinePt d tau).re + w.re)
    rw [displacedLinePt_re]
    linarith [hw.2]
  have hadd : HasDerivAt (fun q : ℂ => displacedLinePt d tau + q) 1 w := by
    simpa using (hasDerivAt_id w).const_add (displacedLinePt d tau)
  have hchi := (zetaChi_analyticAt hG).differentiableAt.hasDerivAt.comp w hadd
  have hexponent : HasDerivAt
      (fun q : ℂ => displacedLinePt d tau + q - 1) 1 w :=
    hadd.sub_const 1
  have hpowN :=
    (Complex.hasStrictDerivAt_const_cpow
      (x := (n + 1 : ℂ)) (y := displacedLinePt d tau + w - 1)
      (Or.inl hn)).hasDerivAt.comp w hexponent
  have hpowX :=
    (Complex.hasStrictDerivAt_const_cpow
      (x := (x : ℂ)) (y := w) (Or.inl hxC)).hasDerivAt
  have hkernel := hasDerivAt_smoothAFEGaussianKernel hw0
  have hfun :
      (fun q : ℂ =>
        smoothAFEZetaReflectedTerm (displacedLinePt d tau) x n q) =
        fun q : ℂ =>
          zetaChi (displacedLinePt d tau + q) *
            (n + 1 : ℂ) ^ (displacedLinePt d tau + q - 1) *
              (x : ℂ) ^ q * smoothAFEGaussianKernel q := by
    funext q
    rw [smoothAFEZetaReflectedTerm_eq_cpow]
  rw [hfun]
  apply DifferentiableAt.differentiableWithinAt
  exact (((hchi.differentiableAt.mul hpowN.differentiableAt).mul
    hpowX.differentiableAt).mul hkernel.differentiableAt)

theorem tendsto_smoothAFEZetaReflectedTerm_deep_horizontal
    {x d : ℝ} (hx : 0 < x) (hd0 : 0 ≤ d) (hdq : d ≤ 1 / 4)
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
    rw [uIoc_of_le (by linarith [hdq] : d - 4 ≤ -1)] at hu
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
theorem smoothAFEZetaDisplacedDeepCoefficient_eq_general
    {x d : ℝ} (hx : 0 < x) (hd : 0 < d) (hdq : d ≤ 1 / 4)
    (tau : ℝ) (n : ℕ) :
    smoothAFEZetaDisplacedDeepCoefficient d tau x n =
      smoothAFEZetaDualCoefficientGeneral (displacedLinePt d tau) x n := by
  let G : ℂ → ℂ := fun w =>
    smoothAFEZetaReflectedTerm (displacedLinePt d tau) x n w
  have hbot := tendsto_smoothAFEZetaReflectedTerm_deep_horizontal
    hx hd.le hdq tau n (-1) (by norm_num)
  have htop := tendsto_smoothAFEZetaReflectedTerm_deep_horizontal
    hx hd.le hdq tau n 1 (by norm_num)
  have hshift :
      (∫ y : ℝ, G (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) =
        ∫ y : ℝ, G (((d - 4 : ℝ) : ℂ) + (y : ℂ) * I) := by
    apply GaloisForLFunctions.HTGeometry.integral_vertical_line_eq_of_horizontal_tendsto
      (G := G) (c := d - 4) (d := -1)
    · linarith [hdq]
    · dsimp only [G]
      exact differentiableOn_smoothAFEZetaReflectedTerm_deep_strip hx hd.le tau n
    · dsimp only [G]
      exact smoothAFEZetaReflectedTerm_displaced_deep_integrable hx hd hdq tau n
    · dsimp only [G]
      norm_num
      exact smoothAFEZetaReflectedTerm_general_left_one_integrable hx
        (by rw [displacedLinePt_re]; linarith [hdq])
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
        (by rw [displacedLinePt_re]; linarith [hdq])
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
