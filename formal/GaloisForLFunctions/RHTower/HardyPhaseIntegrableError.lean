import GaloisForLFunctions.RHTower.HardyZPhaseAsymptotic
import GaloisForLFunctions.HTGeometry.GammaDigammaStirlingBound

open Complex Filter Topology
open GaloisForLFunctions.HTGeometry
noncomputable section
namespace RHTower

/-- The actual Hardy phase velocity has an integrable conductor error.
The real part of the reciprocal Stirling term is retained rather than
bounded by its complex norm. -/
theorem gammaHardyPhaseRate_sub_log_conductor_integrable_bound
    {t : ℝ} (ht4 : 4 ≤ t) :
    |gammaHardyPhaseRate t - Real.log (t / (2 * Real.pi)) / 2| ≤ 13 / t ^ 2 := by
  have ht : 0 < t := by linarith
  let z : ℂ := ((1 / 4 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I
  have hzarg : linePt t / 2 = z := by
    dsimp only [z, linePt]
    push_cast
    ring
  have hzre : z.re = 1 / 4 := by simp [z]
  have hzim : z.im = t / 2 := by simp [z]
  have hz2 : 2 ≤ ‖z‖ := by
    have h := Complex.abs_im_le_norm z
    rw [hzim, abs_of_pos (half_pos ht)] at h
    linarith
  have hzpos : 0 < ‖z‖ := by linarith
  have hQ : ‖z‖ ^ 2 = (1 / 4 : ℝ) ^ 2 + (t / 2) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hzre, hzim]
    ring
  have hQpos : 0 < ‖z‖ ^ 2 := sq_pos_of_pos hzpos
  have hinv : ((1 / (2 * z) : ℂ)).re = 1 / (8 * ‖z‖ ^ 2) := by
    rw [one_div, Complex.inv_re, Complex.normSq_mul, Complex.normSq_eq_norm_sq z]
    norm_num [Complex.mul_re, hzre]
    ring
  have hdef := (Complex.abs_re_le_norm (digammaStirlingDefect z)).trans
    (norm_digammaStirlingDefect_le (by rw [hzre]; norm_num) hz2)
  simp only [digammaStirlingDefect, Complex.add_re, Complex.sub_re, Complex.log_re, hinv] at hdef
  have hpsi : |(Complex.digamma z).re - Real.log ‖z‖| ≤
      6 / ‖z‖ ^ 2 + 1 / (8 * ‖z‖ ^ 2) := by
    obtain ⟨hl, hu⟩ := abs_le.mp hdef
    have hi : 0 ≤ 1 / (8 * ‖z‖ ^ 2) := by positivity
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  let radial : ℝ := (1 / 4 : ℝ) *
    Real.log ((1 / 4 : ℝ) ^ 2 + (t / 2) ^ 2) - Real.log Real.pi / 2
  have hrad : radial = Real.log ‖z‖ / 2 - Real.log Real.pi / 2 := by
    dsimp only [radial]
    rw [← hQ, Real.log_pow]
    ring
  have hrate : |gammaHardyPhaseRate t - radial| ≤ 49 / (4 * t ^ 2) := by
    have he : gammaHardyPhaseRate t - radial =
        ((Complex.digamma z).re - Real.log ‖z‖) / 2 := by
      rw [gammaHardyPhaseRate, hzarg, hrad]
      ring
    rw [he, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    calc
      _ ≤ (6 / ‖z‖ ^ 2 + 1 / (8 * ‖z‖ ^ 2)) / 2 :=
        div_le_div_of_nonneg_right hpsi (by norm_num)
      _ = (49 / 16 : ℝ) / ‖z‖ ^ 2 := by ring
      _ ≤ (49 / 16 : ℝ) / ((t / 2) ^ 2) :=
        div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos (half_pos ht)) (by
          rw [hQ]; nlinarith)
      _ = 49 / (4 * t ^ 2) := by field_simp [ht.ne']; ring
  have honepos : 0 < 1 + 1 / (4 * t ^ 2) := by positivity
  have hradarg : (1 / 4 : ℝ) ^ 2 + (t / 2) ^ 2 =
      (t / 2) ^ 2 * (1 + 1 / (4 * t ^ 2)) := by
    field_simp [ht.ne']
    ring
  have hcorr : radial - Real.log (t / (2 * Real.pi)) / 2 =
      (1 / 4 : ℝ) * Real.log (1 + 1 / (4 * t ^ 2)) := by
    dsimp only [radial]
    rw [hradarg, Real.log_mul (pow_ne_zero 2 (div_ne_zero ht.ne' (by norm_num))) honepos.ne',
      Real.log_pow, Real.log_div ht.ne' (mul_ne_zero (by norm_num) Real.pi_ne_zero),
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero,
      Real.log_div ht.ne' (by norm_num : (2 : ℝ) ≠ 0)]
    ring
  have hcorr0 : 0 ≤ radial - Real.log (t / (2 * Real.pi)) / 2 := by
    rw [hcorr]
    exact mul_nonneg (by norm_num) (Real.log_nonneg (by
      have : 0 ≤ 1 / (4 * t ^ 2) := by positivity
      linarith))
  have hcorrle : radial - Real.log (t / (2 * Real.pi)) / 2 ≤ 1 / (16 * t ^ 2) := by
    rw [hcorr]
    have hlog := Real.log_le_sub_one_of_pos honepos
    calc
      _ ≤ (1 / 4 : ℝ) * ((1 + 1 / (4 * t ^ 2)) - 1) :=
        mul_le_mul_of_nonneg_left hlog (by norm_num)
      _ = _ := by ring
  calc
    _ ≤ |gammaHardyPhaseRate t - radial| +
        |radial - Real.log (t / (2 * Real.pi)) / 2| := by
      simpa only [sub_add_sub_cancel] using abs_add_le
        (gammaHardyPhaseRate t - radial) (radial - Real.log (t / (2 * Real.pi)) / 2)
    _ ≤ 49 / (4 * t ^ 2) + 1 / (16 * t ^ 2) :=
      add_le_add hrate (by simpa only [abs_of_nonneg hcorr0] using hcorrle)
    _ ≤ 13 / t ^ 2 := by
      have hpos : 0 < t ^ 2 := sq_pos_of_pos ht
      field_simp [ht.ne']
      nlinarith

end RHTower
