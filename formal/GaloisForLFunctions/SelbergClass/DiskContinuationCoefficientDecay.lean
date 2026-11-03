import GaloisForLFunctions.SelbergClass.OrdinaryFourierExtraction
import GaloisForLFunctions.SelbergClass.PositiveDegreeAbscissa
import GaloisForLFunctions.HTGeometry.CompactContinuousNormBound
import GaloisForLFunctions.HTGeometry.BoundedCoefficientLaplaceMellin

/-!+# A disk crossing a full exponential period forces degree zero

If the ordinary exponential series continues holomorphically to a disk of
radius greater than `π`, its imaginary period propagates across that disk.
A rectangle spanning one period then moves Fourier extraction to a negative
vertical line. The resulting exponential coefficient decay forces degree zero.
-/

noncomputable section
open Complex Filter Topology Set MeasureTheory
open GaloisForLFunctions.HTGeometry RHTower

namespace GaloisForLFunctions.SelbergClass

private theorem norm_pi_I : ‖(Real.pi : ℂ) * I‖ = Real.pi := by
  rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
    Real.norm_of_nonneg Real.pi_pos.le]

private theorem disk_periodic (F : ExtendedSelbergClass) {g : ℂ → ℂ} {R : ℝ}
    (hR : Real.pi < R) (hg : AnalyticOnNhd ℂ g (Metric.ball 0 R))
    (heq : ∀ z, ‖z‖ < R → 0 < z.re → g z = ordinaryExponentialSeries F z)
    {z : ℂ} (hz : ‖z‖ < R - Real.pi) :
    g (z + (Real.pi : ℂ) * I) = g (z - (Real.pi : ℂ) * I) := by
  have hshift : ∀ w ∈ Metric.ball (0 : ℂ) (R - Real.pi),
      ‖w + (Real.pi : ℂ) * I‖ < R ∧ ‖w - (Real.pi : ℂ) * I‖ < R := by
    intro w hw
    have hw' : ‖w‖ < R - Real.pi := by simpa only [Metric.mem_ball, dist_zero_right] using hw
    constructor
    · have h := norm_add_le w ((Real.pi : ℂ) * I)
      rw [norm_pi_I] at h
      linarith
    · have h := norm_sub_le w ((Real.pi : ℂ) * I)
      rw [norm_pi_I] at h
      linarith
  have hp : AnalyticOnNhd ℂ (fun w => g (w + (Real.pi : ℂ) * I))
      (Metric.ball 0 (R - Real.pi)) := by
    intro w hw
    exact (hg _ (by simpa only [Metric.mem_ball, dist_zero_right] using (hshift w hw).1)).comp
      (by fun_prop)
  have hm : AnalyticOnNhd ℂ (fun w => g (w - (Real.pi : ℂ) * I))
      (Metric.ball 0 (R - Real.pi)) := by
    intro w hw
    exact (hg _ (by simpa only [Metric.mem_ball, dist_zero_right] using (hshift w hw).2)).comp
      (by fun_prop)
  let b : ℝ := (R - Real.pi) / 2
  have hb : 0 < b := by dsimp only [b]; linarith
  have hbmem : (b : ℂ) ∈ Metric.ball 0 (R - Real.pi) := by
    simp only [Metric.mem_ball, dist_zero_right, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hb]
    dsimp only [b]
    linarith
  have hnear : (fun w => g (w + (Real.pi : ℂ) * I)) =ᶠ[𝓝 (b : ℂ)]
      (fun w => g (w - (Real.pi : ℂ) * I)) := by
    have hopen : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [Metric.isOpen_ball.mem_nhds hbmem,
      hopen.mem_nhds (by simpa using hb)] with w hw hwre
    rw [heq _ (hshift w hw).1 (by simpa using hwre),
      heq _ (hshift w hw).2 (by simpa using hwre)]
    have he : w - (Real.pi : ℂ) * I + 2 * (Real.pi : ℂ) * I =
        w + (Real.pi : ℂ) * I := by ring
    simpa only [he] using ordinaryExponentialSeries_periodic F (w - (Real.pi : ℂ) * I)
  exact hp.eqOn_of_preconnected_of_eventuallyEq hm (convex_ball _ _).isPreconnected hbmem
    hnear (by simpa only [Metric.mem_ball, dist_zero_right] using hz)

/-- A holomorphic disk crossing a complete imaginary period gives exponential
decay of the Dirichlet coefficients. -/
theorem exists_exponential_coeff_bound_of_disk_extension (F : ExtendedSelbergClass)
    {g : ℂ → ℂ} {R : ℝ} (hR : Real.pi < R)
    (hg : AnalyticOnNhd ℂ g (Metric.ball 0 R))
    (heq : ∀ z, ‖z‖ < R → 0 < z.re → g z = ordinaryExponentialSeries F z) :
    ∃ a : ℝ, 0 < a ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ n : ℕ, ‖F.coeff n‖ ≤ C * Real.exp (-a * n) := by
  let a : ℝ := (R - Real.pi) / 2
  have ha : 0 < a := by dsimp only [a]; linarith
  have hap : a + Real.pi < R := by dsimp only [a]; linarith
  have hrect : ∀ z : ℂ, z.re ∈ Icc (-a) a → z.im ∈ Icc (-Real.pi) Real.pi → ‖z‖ < R := by
    intro z hx hy
    have hx' : |z.re| ≤ a := abs_le.mpr hx
    have hy' : |z.im| ≤ Real.pi := abs_le.mpr hy
    exact lt_of_le_of_lt (Complex.norm_le_abs_re_add_abs_im z)
      (lt_of_le_of_lt (add_le_add hx' hy') hap)
  have hint : ∀ n : ℕ,
      (∫ t in (-Real.pi)..Real.pi,
        g ((-a : ℂ) + (t : ℂ) * I) *
          Complex.exp ((n : ℂ) * ((-a : ℂ) + (t : ℂ) * I))) =
        2 * (Real.pi : ℂ) * F.coeff n := by
    intro n
    let K : ℂ → ℂ := fun z => g z * Complex.exp ((n : ℂ) * z)
    have hK : DifferentiableOn ℂ K (uIcc (-a) a ×ℂ uIcc (-Real.pi) Real.pi) := by
      intro z hz
      have hzRe : z.re ∈ uIcc (-a) a := hz.1
      have hzIm : z.im ∈ uIcc (-Real.pi) Real.pi := hz.2
      have hx : z.re ∈ Icc (-a) a := by
        simpa only [uIcc_of_le (by linarith : -a ≤ a)] using hzRe
      have hy : z.im ∈ Icc (-Real.pi) Real.pi := by
        simpa only [uIcc_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)] using hzIm
      exact ((hg z (by simpa only [Metric.mem_ball, dist_zero_right] using hrect z hx hy)).mul
        (by fun_prop)).differentiableAt.differentiableWithinAt
    have hc := Complex.integral_boundary_rect_eq_zero_of_differentiableOn K
      ⟨-a, -Real.pi⟩ ⟨a, Real.pi⟩ hK
    simp only [Complex.ofReal_neg] at hc
    change ((∫ x in (-a)..a, K ((x : ℂ) + (-(Real.pi : ℂ)) * I)) -
      (∫ x in (-a)..a, K ((x : ℂ) + (Real.pi : ℂ) * I))) +
      I • (∫ t in (-Real.pi)..Real.pi, K ((a : ℂ) + (t : ℂ) * I)) -
      I • (∫ t in (-Real.pi)..Real.pi, K ((-a : ℂ) + (t : ℂ) * I)) = 0 at hc
    have hhor : (∫ x in (-a)..a, K ((x : ℂ) + (-(Real.pi : ℂ)) * I)) =
        ∫ x in (-a)..a, K ((x : ℂ) + (Real.pi : ℂ) * I) := by
      apply intervalIntegral.integral_congr
      intro x hx
      have hx' : x ∈ Icc (-a) a := by
        simpa only [uIcc_of_le (by linarith : -a ≤ a)] using hx
      have hxb : ‖(x : ℂ)‖ < R - Real.pi := by
        rw [Complex.norm_real, Real.norm_eq_abs]
        exact (abs_le.mpr hx').trans_lt (by dsimp only [a]; linarith)
      have hp := disk_periodic F hR hg heq hxb
      have hexp : Complex.exp ((n : ℂ) * (2 * (Real.pi : ℂ) * I)) = 1 := by
        rw [Complex.exp_nat_mul, Complex.exp_two_pi_mul_I, one_pow]
      have he : (x : ℂ) + (Real.pi : ℂ) * I =
          ((x : ℂ) - (Real.pi : ℂ) * I) + 2 * (Real.pi : ℂ) * I := by ring
      dsimp only [K]
      simp only [neg_mul, ← sub_eq_add_neg]
      rw [hp, he, mul_add, Complex.exp_add, hexp, mul_one]
    rw [hhor, sub_self, zero_add, smul_eq_mul, smul_eq_mul] at hc
    have hv := (mul_left_cancel₀ Complex.I_ne_zero (sub_eq_zero.mp hc)).symm
    change (∫ t in (-Real.pi)..Real.pi, K ((-a : ℂ) + (t : ℂ) * I)) = _
    rw [hv, ← integral_ordinaryExponentialSeries_mul_exp_at F n ha]
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Icc (-Real.pi) Real.pi := by
      simpa only [uIcc_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)] using ht
    dsimp only [K]
    rw [heq _ (hrect _ (by simpa using (show a ∈ Icc (-a) a by constructor <;> linarith))
      (by simpa using ht')) (by simpa using ha)]
  let f : ℝ → ℂ := fun t => g ((-a : ℂ) + (t : ℂ) * I)
  have hf : ContinuousOn f (Icc (-Real.pi) Real.pi) := by
    intro t ht
    have hz : ‖(-a : ℂ) + (t : ℂ) * I‖ < R :=
      hrect _ (by simpa using ha.le) (by simpa using ht)
    exact ((hg _ (by simpa only [Metric.mem_ball, dist_zero_right] using hz)).continuousAt.comp
      (by fun_prop)).continuousWithinAt
  obtain ⟨C, hC0, hC⟩ := exists_compact_continuous_norm_bound isCompact_Icc f hf
  refine ⟨a, ha, C, hC0, fun n => ?_⟩
  have hb : ∀ t ∈ uIoc (-Real.pi) Real.pi,
      ‖g ((-a : ℂ) + (t : ℂ) * I) * Complex.exp ((n : ℂ) * ((-a : ℂ) + (t : ℂ) * I))‖ ≤
        C * Real.exp (-a * n) := by
    intro t ht
    have ht' : t ∈ Icc (-Real.pi) Real.pi := by
      rw [uIoc_of_le (by linarith [Real.pi_pos])] at ht
      exact ⟨ht.1.le, ht.2⟩
    have he : ‖Complex.exp ((n : ℂ) * ((-a : ℂ) + (t : ℂ) * I))‖ =
        Real.exp (-a * n) := by
      rw [Complex.norm_exp]
      congr 1
      simp [Complex.mul_re, Complex.mul_im]
      ring
    rw [norm_mul, he]
    exact mul_le_mul_of_nonneg_right (hC t ht') (Real.exp_pos _).le
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const hb
  rw [hint n, norm_mul, norm_mul, show ‖(2 : ℂ)‖ = (2 : ℝ) by norm_num,
    Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le,
    show |Real.pi - -Real.pi| = 2 * Real.pi by
      rw [abs_of_pos (by linarith [Real.pi_pos])]; ring] at hi
  apply (mul_le_mul_iff_right₀ (by positivity : 0 < 2 * Real.pi)).mp
  nlinarith only [hi]

/-- Positive degree forbids a holomorphic disk crossing a full imaginary period. -/
theorem degree_eq_zero_of_disk_extension (F : ExtendedSelbergClass)
    {g : ℂ → ℂ} {R : ℝ} (hR : Real.pi < R)
    (hg : AnalyticOnNhd ℂ g (Metric.ball 0 R))
    (heq : ∀ z, ‖z‖ < R → 0 < z.re → g z = ordinaryExponentialSeries F z) :
    F.gammaData.degree = 0 := by
  obtain ⟨a, ha, C, _, hC⟩ := exists_exponential_coeff_bound_of_disk_extension F hR hg heq
  have hs : Summable (fun n : ℕ => C * Real.exp (-a * n)) := by
    simpa only [neg_mul, mul_comm a] using (summable_exp_neg_nat_mul ha).mul_left C
  have hsum : Summable (fun n : ℕ => ‖F.coeff n‖) :=
    hs.of_nonneg_of_le (fun n => norm_nonneg _) hC
  apply degree_eq_zero_of_summable_zero F
  apply Summable.of_norm
  apply hsum.of_nonneg_of_le (fun n => norm_nonneg _)
  intro n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · simp [LSeries.term_of_ne_zero hn.ne']

end GaloisForLFunctions.SelbergClass
