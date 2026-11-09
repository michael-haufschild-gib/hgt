import GaloisForLFunctions.ExceptionalLayerTheory.EulerBoundsForDampingFilters

/-!
# Gaussian damping toward the imaginary axis

Rotating the damping by `φ` multiplies each Mellin mode by `exp(-iφw/2)`.
This removes the fixed vertical Gamma loss as `φ` approaches `-π/2`.
The right-half-plane Mellin inversion keeps the observable a literal prime sum.
-/

open Complex Filter Set Topology MeasureTheory RHTower XiAtlasFinitePart

noncomputable section
namespace GaloisForLFunctions.ExceptionalLayerTheory

/-- The Gaussian kernel for damping `y exp(iφ)`. -/
def rotatedGaussianKernel (y φ : ℝ) (w : ℂ) : ℂ :=
  Complex.exp (-(φ : ℂ) * I * w / 2) * gaussianMBKernel y w

/-- Rotation acts on the modulus through the Mellin ordinate alone. -/
theorem norm_rotatedGaussianKernel (y φ : ℝ) (w : ℂ) :
    ‖rotatedGaussianKernel y φ w‖ =
      Real.exp (φ * w.im / 2) * ‖gaussianMBKernel y w‖ := by
  rw [rotatedGaussianKernel, norm_mul, Complex.norm_exp]
  congr 2
  simp only [Complex.div_ofNat_re, Complex.mul_re, Complex.neg_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.neg_im, Complex.I_re,
    Complex.I_im, Complex.mul_im]
  ring

/-- The rotated mode and its inverse have opposite exponential envelopes,
uniformly throughout the closed angular sector. -/
theorem exists_rotatedGaussianMode_exponential_bounds (ρ : ℂ) (σ : ℝ) :
    ∃ (C D : ℝ) (N M : ℕ), 0 ≤ C ∧ 0 ≤ D ∧
      ∀ t : ℝ, |ρ.im| + 2 ≤ t → ∀ a φ : ℝ, |φ| ≤ Real.pi / 2 →
        ‖rotatedGaussianKernel (Real.exp (-a * t)) φ (ρ - ((σ : ℂ) + t * I))‖ ≤
          C * t ^ N * Real.exp ((gaussianObservationRate ρ σ a - φ / 2) * t) ∧
        ‖(rotatedGaussianKernel (Real.exp (-a * t)) φ (ρ - ((σ : ℂ) + t * I)))⁻¹‖ ≤
          D * t ^ M * Real.exp (-((gaussianObservationRate ρ σ a - φ / 2) * t)) := by
  obtain ⟨C, D, N, M, hC, hD, hb⟩ := exists_gaussianMode_exponential_bounds ρ σ
  let B := Real.exp (Real.pi * |ρ.im| / 4)
  refine ⟨B * C, B * D, N, M, by positivity, by positivity, ?_⟩
  intro t ht a φ hφ
  have ht0 : 0 ≤ t := by linarith only [ht, abs_nonneg ρ.im]
  have hphase : |φ * ρ.im / 2| ≤ Real.pi * |ρ.im| / 4 := by
    rw [abs_div, abs_two, abs_mul]
    have hh := mul_le_mul_of_nonneg_right hφ (abs_nonneg ρ.im)
    linarith only [hh]
  have hu := (hb t ht a).1
  have hd := (hb t ht a).2
  have him : (ρ - ((σ : ℂ) + t * I)).im = ρ.im - t := by simp
  constructor
  · rw [norm_rotatedGaussianKernel, him]
    calc
      _ ≤ Real.exp (φ * (ρ.im - t) / 2) *
          (C * t ^ N * Real.exp (gaussianObservationRate ρ σ a * t)) :=
        mul_le_mul_of_nonneg_left hu (Real.exp_pos _).le
      _ = Real.exp (φ * ρ.im / 2) * C * t ^ N *
          Real.exp ((gaussianObservationRate ρ σ a - φ / 2) * t) := by
        rw [show φ * (ρ.im - t) / 2 = φ * ρ.im / 2 - φ / 2 * t by ring,
          Real.exp_sub, sub_mul, Real.exp_sub]
        ring
      _ ≤ _ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              (Real.exp_le_exp.mpr ((le_abs_self _).trans hphase)) hC)
            (pow_nonneg ht0 N)) (Real.exp_pos _).le
  · rw [norm_inv, norm_rotatedGaussianKernel, him, mul_inv, ← Real.exp_neg, ← norm_inv]
    calc
      _ ≤ Real.exp (-(φ * (ρ.im - t) / 2)) *
          (D * t ^ M * Real.exp (-(gaussianObservationRate ρ σ a * t))) :=
        mul_le_mul_of_nonneg_left hd (Real.exp_pos _).le
      _ = Real.exp (-(φ * ρ.im / 2)) * D * t ^ M *
          Real.exp (-((gaussianObservationRate ρ σ a - φ / 2) * t)) := by
        rw [show -(φ * (ρ.im - t) / 2) = -(φ * ρ.im / 2) + φ / 2 * t by ring,
          Real.exp_add, show -((gaussianObservationRate ρ σ a - φ / 2) * t) =
            φ / 2 * t + -(gaussianObservationRate ρ σ a * t) by ring, Real.exp_add]
        ring
      _ ≤ _ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              (Real.exp_le_exp.mpr ((neg_le_abs _).trans hphase)) hD)
            (pow_nonneg ht0 M)) (Real.exp_pos _).le

/-- An angle approaching the negative imaginary axis at reciprocal height. -/
def boundaryDampingAngle (t : ℝ) : ℝ := -Real.pi / 2 + 1 / t

/-- The rotating mode has no fixed Gamma penalty: its reciprocal tends to
zero at every positive horizontal amplification rate. -/
theorem tendsto_inv_boundaryGaussianMode_zero (ρ : ℂ) (σ a : ℝ)
    (hr : 0 < a * (ρ.re - σ)) :
    Tendsto (fun t : ℝ => (rotatedGaussianKernel (Real.exp (-a * t))
      (boundaryDampingAngle t) (ρ - ((σ : ℂ) + t * I)))⁻¹) atTop (𝓝 0) := by
  obtain ⟨C, D, N, M, _, hD, hb⟩ := exists_rotatedGaussianMode_exponential_bounds ρ σ
  apply HTGeometry.tendsto_zero_of_eventually_norm_le_polyExp
    (C := D * Real.exp (1 / 2)) (N := M) (show 0 < a * (ρ.re - σ) / 2 by positivity)
  filter_upwards [eventually_ge_atTop (|ρ.im| + 2), eventually_ge_atTop (1 : ℝ)]
    with t ht ht1
  have ht0 : 0 < t := zero_lt_one.trans_le ht1
  have hinv : 0 < 1 / t := by positivity
  have hinv1 : 1 / t ≤ 1 := (div_le_one ht0).mpr ht1
  have hφ : |boundaryDampingAngle t| ≤ Real.pi / 2 := by
    apply abs_le.mpr
    dsimp only [boundaryDampingAngle]
    constructor <;> linarith only [hinv, hinv1, Real.pi_gt_three]
  have he : -((gaussianObservationRate ρ σ a - boundaryDampingAngle t / 2) * t) =
      1 / 2 - (a * (ρ.re - σ) / 2) * t := by
    dsimp only [gaussianObservationRate, boundaryDampingAngle]
    field_simp [ht0.ne']
    ring
  have hh := (hb t ht a _ hφ).2
  rw [he, Real.exp_sub] at hh
  calc
    _ ≤ D * t ^ M * (Real.exp (1 / 2) / Real.exp (a * (ρ.re - σ) / 2 * t)) := hh
    _ = _ := by rw [Real.exp_neg]; ring

/-- Interior rotations preserve polynomially weighted Mellin integrability. -/
theorem integrable_norm_rotatedGaussianKernel_mul_pow {y c φ : ℝ}
    (hy : 0 < y) (hc : 0 < c) (hφ : |φ| < Real.pi / 2) (n : ℕ) :
    Integrable (fun v : ℝ =>
      ‖rotatedGaussianKernel y φ ((c : ℂ) + v * I)‖ * (1 + |v|) ^ n) := by
  obtain ⟨B, N, hB, hb⟩ := exists_norm_Gamma_line_le (by positivity : 0 < c / 2)
  have hδ : 0 < Real.pi / 4 - |φ| / 2 := by linarith only [hφ]
  have hi := (SelbergClass.integrable_one_add_abs_pow_mul_exp_neg_abs (N + n) hδ).const_mul
    (1 / 2 * y ^ (-(c / 2)) * B)
  apply hi.mono'
  · have hcont : Continuous (fun v : ℝ => rotatedGaussianKernel y φ ((c : ℂ) + v * I)) :=
      (by fun_prop : Continuous (fun v : ℝ => Complex.exp (-(φ : ℂ) * I *
        ((c : ℂ) + v * I) / 2))).mul (continuous_gaussianMBKernel_line hy hc)
    exact (hcont.norm.mul (by fun_prop)).aestronglyMeasurable
  · refine Eventually.of_forall fun v => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), norm_rotatedGaussianKernel,
      norm_gaussianMBKernel_line hy]
    have him : ((c : ℂ) + v * I).im = v := by simp
    rw [him]
    have hv : |v / 2| ≤ |v| := by rw [abs_div, abs_two]; linarith only [abs_nonneg v]
    have hG := (hb (v / 2)).trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (by positivity) (add_le_add (le_refl (1 : ℝ)) hv) N)
          (Real.exp_pos _).le) hB)
    rw [show -(Real.pi / 2) * |v / 2| = -(Real.pi / 4) * |v| by
      rw [abs_div, abs_two]; ring] at hG
    have hφv : φ * v / 2 ≤ |φ| * |v| / 2 := by
      have hh := le_abs_self (φ * v)
      rw [abs_mul] at hh
      linarith only [hh]
    calc
      _ ≤ Real.exp (|φ| * |v| / 2) *
          (1 / 2 * (B * ((1 + |v|) ^ N * Real.exp (-(Real.pi / 4) * |v|))) *
            y ^ (-(c / 2))) * (1 + |v|) ^ n := by
        gcongr
      _ = _ := by
        rw [pow_add, show -(Real.pi / 4 - |φ| / 2) * |v| =
          |φ| * |v| / 2 + -(Real.pi / 4) * |v| by ring, Real.exp_add]
        ring

/-- The rotated kernel is absolutely integrable on every positive Mellin line. -/
theorem integrable_rotatedGaussianKernel_line {y c φ : ℝ}
    (hy : 0 < y) (hc : 0 < c) (hφ : |φ| < Real.pi / 2) :
    Integrable (fun v : ℝ => rotatedGaussianKernel y φ ((c : ℂ) + v * I)) := by
  apply (integrable_norm_rotatedGaussianKernel_mul_pow hy hc hφ 0).mono'
  · exact ((by fun_prop : Continuous (fun v : ℝ =>
      Complex.exp (-(φ : ℂ) * I * ((c : ℂ) + v * I) / 2))).mul
        (continuous_gaussianMBKernel_line hy hc)).aestronglyMeasurable
  · exact Eventually.of_forall fun v => by simp

/-- The complex damping parameter, with its logarithm chosen in the sector. -/
def complexGaussianDamping (y φ : ℝ) : ℂ :=
  Complex.exp ((Real.log y : ℂ) + (φ : ℂ) * I)

theorem complexGaussianDamping_eq {y : ℝ} (hy : 0 < y) (φ : ℝ) :
    complexGaussianDamping y φ = (y : ℂ) * Complex.exp ((φ : ℂ) * I) := by
  rw [complexGaussianDamping, Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log hy]

theorem complexGaussianDamping_re_pos {y φ : ℝ} (_hy : 0 < y)
    (hφ : |φ| < Real.pi / 2) : 0 < (complexGaussianDamping y φ).re := by
  rw [complexGaussianDamping, Complex.exp_re]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, sub_zero, add_zero,
    Complex.add_im, Complex.mul_im, mul_one, zero_add]
  exact mul_pos (Real.exp_pos _) (Real.cos_pos_of_mem_Ioo (abs_lt.mp hφ))

/-- Rotation gives the complex-power kernel on the full open Gaussian sector. -/
theorem rotatedGaussianKernel_eq_cpow {y φ : ℝ} (hy : 0 < y)
    (hφ : |φ| < Real.pi / 2) (w : ℂ) :
    rotatedGaussianKernel y φ w =
      (1 / 2 : ℂ) * Complex.Gamma (w / 2) *
        (complexGaussianDamping y φ) ^ (-(w / 2)) := by
  have hyc : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  have him : ((Real.log y : ℂ) + (φ : ℂ) * I).im = φ := by simp
  have hlo : -Real.pi < ((Real.log y : ℂ) + (φ : ℂ) * I).im := by
    rw [him]; linarith only [(abs_lt.mp hφ).1, Real.pi_pos]
  have hhi : ((Real.log y : ℂ) + (φ : ℂ) * I).im ≤ Real.pi := by
    rw [him]; linarith only [(abs_lt.mp hφ).2, Real.pi_pos]
  rw [rotatedGaussianKernel, gaussianMBKernel, complexGaussianDamping,
    Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero _), Complex.log_exp hlo hhi,
    Complex.cpow_def_of_ne_zero hyc, ← Complex.ofReal_log hy.le]
  rw [show ((Real.log y : ℂ) + (φ : ℂ) * I) * -(w / 2) =
    -(φ : ℂ) * I * w / 2 + (Real.log y : ℂ) * -(w / 2) by ring, Complex.exp_add]
  ring

/-- Complex Gaussian inversion on every positive Mellin line. -/
theorem rotatedGaussianKernel_line_integral {y c φ : ℝ} (hy : 0 < y)
    (hc : 0 < c) (hφ : |φ| < Real.pi / 2) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
      ∫ v : ℝ, rotatedGaussianKernel y φ ((c : ℂ) + v * I) =
        Complex.exp (-complexGaussianDamping y φ) := by
  let g : ℝ → ℂ := fun v => (complexGaussianDamping y φ) ^
    (-(((c / 2 : ℝ) : ℂ) + v * I)) *
      Complex.Gamma (((c / 2 : ℝ) : ℂ) + v * I)
  have he (v : ℝ) : rotatedGaussianKernel y φ ((c : ℂ) + v * I) =
      (1 / 2 : ℂ) * g ((1 / 2) * v) := by
    rw [rotatedGaussianKernel_eq_cpow hy hφ, half_line]
    dsimp only [g]
    rw [show (v / 2 : ℝ) = 1 / 2 * v by ring]
    ring
  simp_rw [he]
  rw [integral_const_mul, Measure.integral_comp_mul_left g (1 / 2)]
  have hi := SelbergClass.complexMellinInvLine_Gamma_eq_exp_neg
    (by positivity : 0 < c / 2) (complexGaussianDamping_re_pos hy hφ)
  change (1 / (2 * Real.pi) : ℝ) • (∫ v : ℝ, g v) = _ at hi
  rw [Complex.real_smul] at hi
  rw [← hi, show |(1 / 2 : ℝ)⁻¹| = 2 by norm_num, Complex.real_smul]
  push_cast
  ring

/-- Multiplying the damping by a square is Mellin dilation, also after rotation. -/
theorem rotatedGaussianKernel_mul_cpow_neg {y u : ℝ} (hy : 0 < y)
    (hu : 0 < u) (φ : ℝ) (w : ℂ) :
    rotatedGaussianKernel y φ w * (u : ℂ) ^ (-w) =
      rotatedGaussianKernel (y * u ^ 2) φ w := by
  rw [rotatedGaussianKernel, rotatedGaussianKernel, mul_assoc,
    gaussianMBKernel_mul_cpow_neg hy hu]

/-- The Mellin inverse remains the literal complex Gaussian at every integer. -/
theorem rotatedGaussianKernel_line_integral_mul_cpow {y c u φ : ℝ}
    (hy : 0 < y) (hc : 0 < c) (hu : 0 < u) (hφ : |φ| < Real.pi / 2) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ v : ℝ,
      rotatedGaussianKernel y φ ((c : ℂ) + v * I) *
        (u : ℂ) ^ (-((c : ℂ) + v * I)) =
      Complex.exp (-(complexGaussianDamping y φ * (u : ℂ) ^ 2)) := by
  simp_rw [rotatedGaussianKernel_mul_cpow_neg hy hu]
  rw [rotatedGaussianKernel_line_integral (by positivity) hc hφ,
    complexGaussianDamping_eq (by positivity), complexGaussianDamping_eq hy]
  congr 2
  push_cast
  ring

/-- The prime observable with complex Gaussian damping. -/
def rotatedGaussianPrimeSum (s : ℂ) (y φ : ℝ) : ℂ :=
  ∑' n : ℕ, LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s n *
    Complex.exp (-(complexGaussianDamping y φ * (n : ℂ) ^ 2))

/-- Absolute Euler convergence justifies the rotated prime Mellin identity. -/
theorem tsum_term_mul_rotated_exp_eq_line_integral {y c φ : ℝ} (hy : 0 < y) (hc : 0 < c) (hφ : |φ| < Real.pi / 2)
    (f : ℕ → ℂ) (s : ℂ) (hf : Summable fun n : ℕ => ‖f n‖ * (n : ℝ) ^ (-(s.re + c))) :
    ∑' n : ℕ, LSeries.term f s n * Complex.exp (-(complexGaussianDamping y φ * (n : ℂ) ^ 2)) =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ v : ℝ, rotatedGaussianKernel y φ ((c : ℂ) + (v : ℂ) * I) *
          LSeries f (s + ((c : ℂ) + (v : ℂ) * I)) := by
  set K : ℝ → ℂ := fun v => rotatedGaussianKernel y φ ((c : ℂ) + (v : ℂ) * I) with hKdef
  set G : ℕ → ℝ → ℂ := fun n v => K v * LSeries.term f (s + ((c : ℂ) + (v : ℂ) * I)) n with hG
  have hnorm : ∀ n : ℕ, ∀ v : ℝ, ‖G n v‖ = ‖K v‖ * (if n = 0 then 0 else ‖f n‖ * (n : ℝ) ^ (-(s.re + c))) := by
    intro n v
    simp only [hG, norm_mul]
    rcases eq_or_ne n 0 with rfl | hn
    · simp [LSeries.term_def]
    · rw [LSeries.term_of_ne_zero hn, if_neg hn, norm_div,
        Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero]
      rw [Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]
  have hKint : Integrable K := integrable_rotatedGaussianKernel_line hy hc hφ
  have hKnorm : Integrable fun v => ‖K v‖ := hKint.norm
  have hGint : ∀ n, Integrable (G n) := by
    intro n
    refine (hKnorm.mul_const (if n = 0 then 0 else ‖f n‖ * (n : ℝ) ^ (-(s.re + c)))).mono' ?_
      (Eventually.of_forall fun v => (hnorm n v).le)
    exact hKint.aestronglyMeasurable.mul (by
      rcases eq_or_ne n 0 with rfl | hn
      · simp only [LSeries.term_def, if_pos]; exact aestronglyMeasurable_const
      · simp only [LSeries.term_of_ne_zero hn]
        exact (continuous_const.div (Continuous.const_cpow (by fun_prop)
          (Or.inl (by exact_mod_cast hn))) fun v => by
            simp [hn]).aestronglyMeasurable)
  have hsumm : Summable fun n => ∫ v, ‖G n v‖ := by
    simp_rw [hnorm]
    simp_rw [integral_mul_const]
    refine (hf.mul_left (∫ v, ‖K v‖)).of_nonneg_of_le (fun n => ?_) (fun n => ?_)
    · exact mul_nonneg (integral_nonneg fun v => norm_nonneg _) (by split_ifs <;> positivity)
    · split_ifs with hn
      · rw [mul_zero]; positivity
      · exact le_rfl
  have hLS : ∀ v : ℝ, rotatedGaussianKernel y φ ((c : ℂ) + (v : ℂ) * I) *
      LSeries f (s + ((c : ℂ) + (v : ℂ) * I)) = ∑' n, G n v := by
    intro v
    rw [LSeries, ← tsum_mul_left]
  simp_rw [hLS]
  rw [← integral_tsum_of_summable_integral_norm hGint hsumm, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp [hG, LSeries.term_def]
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hn1 : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    have hsplit : ∀ v : ℝ, G n v =
        LSeries.term f s n * (K v * ((n : ℝ) : ℂ) ^ (-((c : ℂ) + (v : ℂ) * I))) := by
      intro v
      show K v * LSeries.term f (s + ((c : ℂ) + (v : ℂ) * I)) n = _
      rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, Complex.cpow_add _ _ hn1,
        Complex.ofReal_natCast, Complex.cpow_neg]
      have h1 : (n : ℂ) ^ s ≠ 0 := by
        rw [Complex.cpow_def_of_ne_zero hn1]; exact Complex.exp_ne_zero _
      field_simp
    simp_rw [hsplit]
    rw [integral_const_mul, mul_left_comm, rotatedGaussianKernel_line_integral_mul_cpow hy hc hn0 hφ]
    simp only [Complex.ofReal_natCast]

/-- Rotation commutes with geometric changes of the positive damping radius. -/
theorem rotatedGaussianKernel_geometric_damping (a h t φ : ℝ) (j : ℕ) (w : ℂ) :
    rotatedGaussianKernel (geometricGaussianDamping a h t j) φ w =
      Complex.exp ((j : ℂ) * h * w) *
        rotatedGaussianKernel (Real.exp (-a * t)) φ w := by
  rw [rotatedGaussianKernel, gaussianMode_geometric_damping, rotatedGaussianKernel]
  ring

/-- Finite filtering retains the exact polynomial multiplier after rotation. -/
theorem polynomial_dampingFilter_rotatedGaussianKernel (P : Polynomial ℂ)
    (β a h t φ : ℝ) (s z : ℂ) :
    (∑ j ∈ Finset.range (P.natDegree + 1), P.coeff j * dampingSampleWeight β h s j *
      rotatedGaussianKernel (geometricGaussianDamping a h t j) φ (z - s)) =
      P.eval (Complex.exp ((h : ℂ) * (z - β))) *
        rotatedGaussianKernel (Real.exp (-a * t)) φ (z - s) := by
  simp only [rotatedGaussianKernel]
  have he := polynomial_dampingFilter_gaussianMode P β a h t s z
  calc
    _ = Complex.exp (-(φ : ℂ) * I * (z - s) / 2) *
        (∑ j ∈ Finset.range (P.natDegree + 1), P.coeff j * dampingSampleWeight β h s j *
          gaussianMBKernel (geometricGaussianDamping a h t j) (z - s)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by rw [he]; ring

/-- A finite combination of literal prime sums at complex Gaussian dampings. -/
def rotatedPrimeDampingFilter (P : Polynomial ℂ) (σ β a h φ t : ℝ) : ℂ :=
  ∑ j ∈ Finset.range (P.natDegree + 1),
    P.coeff j * dampingSampleWeight β h ((σ : ℂ) + t * I) j *
      rotatedGaussianPrimeSum ((σ : ℂ) + t * I) (geometricGaussianDamping a h t j) φ

private theorem integrable_rotated_gaussian_euler_line {s : ℂ} {c y φ : ℝ}
    (hy : 0 < y) (hc : 0 < c) (hφ : |φ| < Real.pi / 2) (hs : 1 < s.re + c) :
    Integrable (fun v : ℝ => rotatedGaussianKernel y φ ((c : ℂ) + v * I) *
      LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
        (s + ((c : ℂ) + v * I))) := by
  refine ((integrable_rotatedGaussianKernel_line hy hc hφ).norm.mul_const
    (∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (s.re + c))).mono'
      (((by fun_prop : Continuous (fun v : ℝ =>
        Complex.exp (-(φ : ℂ) * I * ((c : ℂ) + v * I) / 2))).mul
          (continuous_gaussianMBKernel_line hy hc)).mul
        (continuous_LSeries_vonMangoldt_line hs)).aestronglyMeasurable ?_
  refine Eventually.of_forall fun v => ?_
  rw [norm_mul]
  have hb := norm_LSeries_vonMangoldt_le
    (s := s + ((c : ℂ) + v * I)) (by simpa using hs)
  simpa using mul_le_mul_of_nonneg_left hb
    (norm_nonneg (rotatedGaussianKernel y φ ((c : ℂ) + v * I)))

/-- Mellin inversion of the literal filtered prime sum. Every root remains
inside the absolutely convergent Euler integral. -/
theorem rotatedPrimeDampingFilter_eq_euler_integral (P : Polynomial ℂ)
    (σ β a h φ t c : ℝ) (hc : 0 < c) (hφ : |φ| < Real.pi / 2) (hs : 1 < σ + c) :
    rotatedPrimeDampingFilter P σ β a h φ t = ((1 / (2 * Real.pi) : ℝ) : ℂ) *
      ∫ v : ℝ, P.eval (Complex.exp ((h : ℂ) *
          ((((σ : ℂ) + t * I) + ((c : ℂ) + v * I)) - β))) *
        rotatedGaussianKernel (Real.exp (-a * t)) φ ((c : ℂ) + v * I) *
        LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
          (((σ : ℂ) + t * I) + ((c : ℂ) + v * I)) := by
  let s : ℂ := (σ : ℂ) + t * I
  let k : ℂ := ((1 / (2 * Real.pi) : ℝ) : ℂ)
  let L : ℝ → ℂ := fun v =>
    LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (s + ((c : ℂ) + v * I))
  let J := Finset.range (P.natDegree + 1)
  have hs' : 1 < s.re + c := by simpa [s] using hs
  have hi (j : ℕ) : Integrable (fun v : ℝ =>
      P.coeff j * dampingSampleWeight β h s j *
        (rotatedGaussianKernel (geometricGaussianDamping a h t j) φ ((c : ℂ) + v * I) * L v)) :=
    (integrable_rotated_gaussian_euler_line (Real.exp_pos _) hc hφ hs').const_mul _
  have he (j : ℕ) :
      P.coeff j * dampingSampleWeight β h s j *
        rotatedGaussianPrimeSum s (geometricGaussianDamping a h t j) φ =
      k * ∫ v : ℝ, P.coeff j * dampingSampleWeight β h s j *
        (rotatedGaussianKernel (geometricGaussianDamping a h t j) φ ((c : ℂ) + v * I) * L v) := by
    rw [rotatedGaussianPrimeSum, tsum_term_mul_rotated_exp_eq_line_integral
      (y := geometricGaussianDamping a h t j)
      (by exact Real.exp_pos _) hc hφ _ s (summable_vonMangoldt_rpow_neg hs'), integral_const_mul]
    ring
  calc
    rotatedPrimeDampingFilter P σ β a h φ t = k * ∫ v : ℝ,
        ∑ j ∈ J, P.coeff j * dampingSampleWeight β h s j *
          (rotatedGaussianKernel (geometricGaussianDamping a h t j) φ ((c : ℂ) + v * I) * L v) := by
      change (∑ j ∈ J, P.coeff j * dampingSampleWeight β h s j *
        rotatedGaussianPrimeSum s (geometricGaussianDamping a h t j) φ) = _
      simp_rw [he]
      rw [← Finset.mul_sum, integral_finsetSum J (fun j _ => hi j)]
    _ = _ := by
      congr 1
      apply integral_congr_ae
      refine Eventually.of_forall fun v => ?_
      have hm := polynomial_dampingFilter_rotatedGaussianKernel P β a h t φ s
        (s + ((c : ℂ) + v * I))
      simp only [add_sub_cancel_left] at hm
      calc
        _ = (∑ j ∈ J, P.coeff j * dampingSampleWeight β h s j *
              rotatedGaussianKernel (geometricGaussianDamping a h t j) φ ((c : ℂ) + v * I)) * L v := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro j _
          ring
        _ = _ := by rw [hm]

/-- Rescaling the Mellin height pays only a polynomial when the angular
margin is reciprocal height. -/
private theorem integral_scaled_exponential_moment_le (n : ℕ) {t : ℝ} (ht : 1 ≤ t) :
    (∫ v : ℝ, (1 + |v|) ^ n * Real.exp (-(1 / (2 * t)) * |v|)) ≤
      t ^ (n + 1) * (∫ v : ℝ, (1 + |v|) ^ n * Real.exp (-(1 / 2 : ℝ) * |v|)) := by
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  let H : ℝ → ℝ := fun v => (1 + |v|) ^ n * Real.exp (-(1 / 2 : ℝ) * |v|)
  let G : ℝ → ℝ := fun v => (1 + |v|) ^ n * Real.exp (-(1 / (2 * t)) * |v|)
  have hGi : Integrable G :=
    SelbergClass.integrable_one_add_abs_pow_mul_exp_neg_abs n (by positivity)
  have hexp (v : ℝ) : -(1 / 2 : ℝ) * |t⁻¹ * v| = -(1 / (2 * t)) * |v| := by
    rw [abs_mul, abs_inv, abs_of_pos ht0]
    field_simp
  have hsmall (v : ℝ) : |t⁻¹ * v| ≤ |v| := by
    rw [abs_mul, abs_inv, abs_of_pos ht0]
    exact mul_le_of_le_one_left (abs_nonneg v) ((inv_le_one₀ ht0).mpr ht)
  have hHi : Integrable (fun v : ℝ => H (t⁻¹ * v)) := by
    apply hGi.mono' (by fun_prop : Continuous (fun v : ℝ => H (t⁻¹ * v))).aestronglyMeasurable
    refine Eventually.of_forall fun v => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (by dsimp only [H]; positivity)]
    dsimp only [H, G]
    rw [hexp]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (by positivity) (by linarith only [hsmall v]) n) (Real.exp_pos _).le
  have hb (v : ℝ) : G v ≤ t ^ n * H (t⁻¹ * v) := by
    have he : t * (1 + |t⁻¹ * v|) = t + |v| := by
      rw [abs_mul, abs_inv, abs_of_pos ht0]
      field_simp
    have hp : 1 + |v| ≤ t * (1 + |t⁻¹ * v|) := by rw [he]; linarith only [ht]
    dsimp only [G, H]
    rw [hexp, ← mul_assoc, ← mul_pow]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (by positivity) hp n) (Real.exp_pos _).le
  calc
    _ ≤ ∫ v : ℝ, t ^ n * H (t⁻¹ * v) := integral_mono hGi (hHi.const_mul _) hb
    _ = t ^ (n + 1) * (∫ v : ℝ, H v) := by
      rw [integral_const_mul, Measure.integral_comp_mul_left H, inv_inv, abs_of_pos ht0,
        smul_eq_mul, pow_succ]
      ring

/-- The sector envelope is uniform in the angle, including angles outside
absolute convergence; its exponential margin records the exact sector loss. -/
theorem exists_rotatedGaussianKernel_line_envelope {c : ℝ} (hc : 0 < c) :
    ∃ B : ℝ, ∃ N : ℕ, 0 ≤ B ∧ ∀ φ v : ℝ,
      ‖rotatedGaussianKernel 1 φ ((c : ℂ) + v * I)‖ ≤
        B * (1 + |v|) ^ N * Real.exp (-(Real.pi / 4 - |φ| / 2) * |v|) := by
  obtain ⟨B, N, hB, hb⟩ := exists_norm_Gamma_line_le (by positivity : 0 < c / 2)
  refine ⟨B / 2, N, by positivity, ?_⟩
  intro φ v
  rw [norm_rotatedGaussianKernel, norm_gaussianMBKernel_line zero_lt_one,
    Real.one_rpow, mul_one]
  have him : ((c : ℂ) + v * I).im = v := by simp
  rw [him]
  have hv : |v / 2| ≤ |v| := by rw [abs_div, abs_two]; linarith only [abs_nonneg v]
  have hG := (hb (v / 2)).trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (by positivity) (add_le_add (le_refl (1 : ℝ)) hv) N)
        (Real.exp_pos _).le) hB)
  rw [show -(Real.pi / 2) * |v / 2| = -(Real.pi / 4) * |v| by
    rw [abs_div, abs_two]; ring] at hG
  have hφv : φ * v / 2 ≤ |φ| * |v| / 2 := by
    have hh := le_abs_self (φ * v)
    rw [abs_mul] at hh
    linarith only [hh]
  calc
    _ ≤ Real.exp (|φ| * |v| / 2) *
        (1 / 2 * (B * ((1 + |v|) ^ N * Real.exp (-(Real.pi / 4) * |v|)))) := by
      gcongr
    _ = _ := by
      rw [show -(Real.pi / 4 - |φ| / 2) * |v| =
        |φ| * |v| / 2 + -(Real.pi / 4) * |v| by ring, Real.exp_add]
      ring

/-- All polynomially weighted kernel moments grow at most polynomially when
the angular margin is at least reciprocal height. -/
theorem exists_rotatedGaussianKernel_boundary_moment_bound {c : ℝ} (hc : 0 < c) (d : ℕ) :
    ∃ C : ℝ, ∃ m : ℕ, 0 ≤ C ∧ ∀ t φ : ℝ, 1 ≤ t → |φ| ≤ Real.pi / 2 - 1 / t →
      (∫ v : ℝ, ‖rotatedGaussianKernel 1 φ ((c : ℂ) + v * I)‖ * (1 + |v|) ^ d) ≤ C * t ^ m := by
  obtain ⟨B, N, hB, hb⟩ := exists_rotatedGaussianKernel_line_envelope hc
  let H : ℝ → ℝ := fun v => (1 + |v|) ^ (N + d) * Real.exp (-(1 / 2 : ℝ) * |v|)
  refine ⟨B * ∫ v : ℝ, H v, N + d + 1, mul_nonneg hB (integral_nonneg fun v => by
    dsimp only [H]; positivity), ?_⟩
  intro t φ ht hφ
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hφ' : |φ| < Real.pi / 2 := by linarith only [hφ, one_div_pos.mpr ht0]
  have hgap : 1 / (2 * t) ≤ Real.pi / 4 - |φ| / 2 := by
    have he : 1 / (2 * t) = (1 / t) / 2 := by ring
    rw [he]
    linarith only [hφ]
  have hi := integrable_norm_rotatedGaussianKernel_mul_pow zero_lt_one hc hφ' d
  have hG := SelbergClass.integrable_one_add_abs_pow_mul_exp_neg_abs (N + d)
    (by positivity : 0 < 1 / (2 * t))
  calc
    _ ≤ ∫ v : ℝ, B * ((1 + |v|) ^ (N + d) * Real.exp (-(1 / (2 * t)) * |v|)) := by
      apply integral_mono hi (hG.const_mul B)
      intro v
      calc
        _ ≤ (B * (1 + |v|) ^ N * Real.exp (-(Real.pi / 4 - |φ| / 2) * |v|)) *
            (1 + |v|) ^ d := mul_le_mul_of_nonneg_right (hb φ v) (by positivity)
        _ ≤ B * ((1 + |v|) ^ (N + d) * Real.exp (-(1 / (2 * t)) * |v|)) := by
          rw [pow_add]
          have he : Real.exp (-(Real.pi / 4 - |φ| / 2) * |v|) ≤
              Real.exp (-(1 / (2 * t)) * |v|) := by
            apply Real.exp_le_exp.mpr
            exact mul_le_mul_of_nonneg_right (neg_le_neg hgap) (abs_nonneg v)
          calc
            _ ≤ (B * (1 + |v|) ^ N * Real.exp (-(1 / (2 * t)) * |v|)) *
                (1 + |v|) ^ d := by gcongr
            _ = _ := by ring
    _ = B * ∫ v : ℝ, (1 + |v|) ^ (N + d) * Real.exp (-(1 / (2 * t)) * |v|) :=
      integral_const_mul _ _
    _ ≤ B * (t ^ (N + d + 1) * ∫ v : ℝ, H v) :=
      mul_le_mul_of_nonneg_left (integral_scaled_exponential_moment_le (N + d) ht) hB
    _ = _ := by ring

/-- The Euler bound isolates all angular dependence in one kernel moment. -/
theorem exists_rotatedPrimeDampingFilter_euler_moment_bound (F : Finset XiZeroCopy)
    (ρ : ℂ) (σ β c : ℝ) (hc : 1 < c) (hσc : σ < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ a h φ t : ℝ, |φ| < Real.pi / 2 → 0 ≤ h → h ≤ 1 →
      ‖rotatedPrimeDampingFilter (divisorDampingFilter F ρ β h) σ β a h φ t‖ ≤
        C * h ^ (1 + (F.filter (fun q => xiZero q ≠ ρ)).card) *
          (1 + |t|) ^ (1 + (F.filter (fun q => xiZero q ≠ ρ)).card) *
            Real.exp (a * t * (c - σ) / 2) *
              (∫ v : ℝ, ‖rotatedGaussianKernel 1 φ (((c - σ : ℝ) : ℂ) + v * I)‖ *
                (1 + |v|) ^ (1 + (F.filter (fun q => xiZero q ≠ ρ)).card)) := by
  classical
  let d := 1 + (F.filter (fun q => xiZero q ≠ ρ)).card
  let δ := c - σ
  have hδ : 0 < δ := sub_pos.mpr hσc
  obtain ⟨B, hB, hfilter⟩ := exists_divisorDampingFilter_euler_bound F ρ β c
  let E : ℝ := ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ c
  have hE : 0 ≤ E := tsum_nonneg fun n => div_nonneg
    ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  let k : ℝ := 1 / (2 * Real.pi)
  have hk : 0 ≤ k := by dsimp only [k]; positivity
  let C₀ := k * B ^ d * E
  have hC₀ : 0 ≤ C₀ := by dsimp only [C₀]; positivity
  refine ⟨C₀ + 1, by positivity, ?_⟩
  intro a h φ t hφ hh hh1
  let W : ℝ → ℝ := fun v => ‖rotatedGaussianKernel 1 φ ((δ : ℂ) + v * I)‖ * (1 + |v|) ^ d
  have hWi : Integrable W := integrable_norm_rotatedGaussianKernel_mul_pow zero_lt_one hδ hφ d
  let I₀ : ℝ := ∫ v : ℝ, W v
  have hI₀ : 0 ≤ I₀ := integral_nonneg fun v => by dsimp only [W]; positivity
  let s : ℂ := (σ : ℂ) + t * I
  let P := divisorDampingFilter F ρ β h
  let Z := h ^ d * (1 + |t|) ^ d * Real.exp (a * t * δ / 2)
  have hZ : 0 ≤ Z := by dsimp only [Z]; positivity
  let Q : ℝ → ℂ := fun v =>
    P.eval (Complex.exp ((h : ℂ) * ((s + ((δ : ℂ) + v * I)) - β))) *
      rotatedGaussianKernel (Real.exp (-a * t)) φ ((δ : ℂ) + v * I) *
        LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
          (s + ((δ : ℂ) + v * I))
  have hre (v : ℝ) : (s + ((δ : ℂ) + v * I)).re = c := by
    simp only [s, δ, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
    ring
  have hsδ : 1 < s.re + δ := by
    have he : s.re + δ = c := by simpa using hre 0
    rwa [he]
  have hpoint (v : ℝ) : ‖Q v‖ ≤ (B ^ d * E * Z) * W v := by
    have hp := hfilter h t v hh hh1
    have hline : s + ((δ : ℂ) + v * I) = (c : ℂ) + (t + v) * I := by
      dsimp only [s, δ]
      push_cast
      ring
    have hL := norm_LSeries_vonMangoldt_le
      (s := s + ((δ : ℂ) + v * I)) (by rw [hre]; exact hc)
    rw [hre] at hL
    have hK : ‖rotatedGaussianKernel (Real.exp (-a * t)) φ ((δ : ℂ) + v * I)‖ =
        Real.exp (a * t * δ / 2) * ‖rotatedGaussianKernel 1 φ ((δ : ℂ) + v * I)‖ := by
      rw [norm_rotatedGaussianKernel, norm_rotatedGaussianKernel,
        norm_gaussianMBKernel_line (Real.exp_pos _),
        norm_gaussianMBKernel_line zero_lt_one, Real.one_rpow, mul_one,
        Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
      rw [show (-a * t) * -(δ / 2) = a * t * δ / 2 by ring]
      ring
    dsimp only [Q]
    rw [norm_mul, norm_mul]
    calc
      _ ≤ (h * B * (1 + |t|) * (1 + |v|)) ^ d *
          ‖rotatedGaussianKernel (Real.exp (-a * t)) φ ((δ : ℂ) + v * I)‖ * E := by
        apply mul_le_mul
        · apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          simpa only [hline, P, d] using hp
        · exact hL
        · exact norm_nonneg _
        · positivity
      _ = _ := by
        rw [hK]
        dsimp only [W, Z]
        simp only [mul_pow]
        ring
  have hcont : Continuous Q := by
    have hp : Continuous (fun v : ℝ => P.eval (Complex.exp
        ((h : ℂ) * ((s + ((δ : ℂ) + v * I)) - β)))) := by
      simp_rw [Polynomial.eval_eq_sum_range]
      fun_prop
    exact (hp.mul ((by fun_prop : Continuous (fun v : ℝ =>
      Complex.exp (-(φ : ℂ) * I * ((δ : ℂ) + v * I) / 2))).mul
        (continuous_gaussianMBKernel_line (Real.exp_pos _) hδ))).mul
      (continuous_LSeries_vonMangoldt_line hsδ)
  have hQi : Integrable Q :=
    (hWi.const_mul (B ^ d * E * Z)).mono' hcont.aestronglyMeasurable
      (Eventually.of_forall hpoint)
  have hnorm : ‖∫ v : ℝ, Q v‖ ≤ (B ^ d * E * Z) * I₀ := by
    calc
      _ ≤ ∫ v : ℝ, ‖Q v‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ v : ℝ, (B ^ d * E * Z) * W v :=
        integral_mono hQi.norm (hWi.const_mul _) hpoint
      _ = _ := integral_const_mul _ _
  have heq := rotatedPrimeDampingFilter_eq_euler_integral P σ β a h φ t δ hδ hφ
    (by dsimp only [δ]; linarith only [hc])
  change rotatedPrimeDampingFilter P σ β a h φ t = (k : ℂ) * ∫ v : ℝ, Q v at heq
  rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hk]
  calc
    k * ‖∫ v : ℝ, Q v‖ ≤ k * ((B ^ d * E * Z) * I₀) :=
      mul_le_mul_of_nonneg_left hnorm hk
    _ = C₀ * Z * I₀ := by dsimp only [C₀]; ring
    _ ≤ (C₀ + 1) * Z * I₀ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith) hZ) hI₀
    _ = _ := by dsimp only [Z, d, δ, I₀, W]; ring

/-- The explicit angle stays inside the Gaussian sector with margin `1/t`. -/
theorem abs_boundaryDampingAngle {t : ℝ} (ht : 1 ≤ t) :
    |boundaryDampingAngle t| = Real.pi / 2 - 1 / t := by
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hh : 1 / t ≤ 1 := (div_le_one ht0).mpr ht
  rw [boundaryDampingAngle, abs_of_nonpos (by linarith only [hh, Real.pi_gt_three])]
  ring

/-- Moving to reciprocal angular distance from the imaginary axis costs only
polynomial height. The full `h^d` gain remains in the literal prime filter. -/
theorem exists_boundaryPrimeDampingFilter_arithmetic_bound (F : Finset XiZeroCopy)
    (ρ : ℂ) (σ β c : ℝ) (hc : 1 < c) (hσc : σ < c) :
    ∃ C : ℝ, ∃ N : ℕ, 0 < C ∧ ∀ a h t : ℝ, 1 ≤ t → 0 ≤ h → h ≤ 1 →
      ‖rotatedPrimeDampingFilter (divisorDampingFilter F ρ β h)
        σ β a h (boundaryDampingAngle t) t‖ ≤
      C * h ^ (1 + (F.filter (fun q => xiZero q ≠ ρ)).card) * t ^ N *
        Real.exp (a * t * (c - σ) / 2) := by
  classical
  let d := 1 + (F.filter (fun q => xiZero q ≠ ρ)).card
  obtain ⟨A, hA, ha⟩ := exists_rotatedPrimeDampingFilter_euler_moment_bound F ρ σ β c hc hσc
  obtain ⟨B, m, hB, hb⟩ := exists_rotatedGaussianKernel_boundary_moment_bound
    (sub_pos.mpr hσc) d
  refine ⟨A * (B + 1) * 2 ^ d, d + m, by positivity, ?_⟩
  intro a h t ht hh hh1
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hφ : |boundaryDampingAngle t| < Real.pi / 2 := by
    rw [abs_boundaryDampingAngle ht]
    linarith only [one_div_pos.mpr ht0]
  have hm := hb t (boundaryDampingAngle t) ht (le_of_eq (abs_boundaryDampingAngle ht))
  have hp : (1 + |t|) ^ d ≤ (2 : ℝ) ^ d * t ^ d := by
    rw [abs_of_pos ht0, ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by linarith only [ht]) d
  calc
    _ ≤ A * h ^ d * (1 + |t|) ^ d * Real.exp (a * t * (c - σ) / 2) *
        (∫ v : ℝ, ‖rotatedGaussianKernel 1 (boundaryDampingAngle t)
          (((c - σ : ℝ) : ℂ) + v * I)‖ * (1 + |v|) ^ d) := ha a h _ t hφ hh hh1
    _ ≤ A * h ^ d * (1 + |t|) ^ d * Real.exp (a * t * (c - σ) / 2) * (B * t ^ m) :=
      mul_le_mul_of_nonneg_left hm (by positivity)
    _ ≤ A * h ^ d * ((2 : ℝ) ^ d * t ^ d) * Real.exp (a * t * (c - σ) / 2) *
        ((B + 1) * t ^ m) := by gcongr; linarith
    _ = _ := by rw [pow_add]; ring

/-- Boundary rotation makes every mode to the right of the observation line
unbounded, for every positive horizontal damping speed. -/
theorem tendsto_norm_boundaryGaussianMode_atTop (ρ : ℂ) (σ a : ℝ)
    (hr : 0 < a * (ρ.re - σ)) :
    Tendsto (fun t : ℝ => ‖rotatedGaussianKernel (Real.exp (-a * t))
      (boundaryDampingAngle t) (ρ - ((σ : ℂ) + t * I))‖) atTop atTop := by
  have hi := (tendsto_inv_boundaryGaussianMode_zero ρ σ a hr).norm
  have hn : ∀ᶠ t : ℝ in atTop, rotatedGaussianKernel (Real.exp (-a * t))
      (boundaryDampingAngle t) (ρ - ((σ : ℂ) + t * I)) ≠ 0 := by
    filter_upwards [eventually_ge_atTop (|ρ.im| + 2)] with t ht
    apply mul_ne_zero (Complex.exp_ne_zero _)
    apply mul_ne_zero
    · apply mul_ne_zero (by norm_num : (1 / 2 : ℂ) ≠ 0)
      apply Complex.Gamma_ne_zero
      intro n he
      have hh := congrArg Complex.im he
      simp only [Complex.div_ofNat_im, Complex.sub_im, Complex.add_im,
        Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
        Complex.I_re, mul_one, mul_zero, add_zero, zero_add, Complex.neg_im,
        Complex.natCast_im, neg_zero] at hh
      linarith only [hh, ht, le_abs_self ρ.im]
    · rw [Complex.cpow_def_of_ne_zero
        (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero (-a * t)))]
      exact Complex.exp_ne_zero _
  have hp : ∀ᶠ t : ℝ in atTop, 0 < ‖(rotatedGaussianKernel (Real.exp (-a * t))
      (boundaryDampingAngle t) (ρ - ((σ : ℂ) + t * I)))⁻¹‖ := by
    filter_upwards [hn] with t ht
    exact norm_pos_iff.mpr (inv_ne_zero ht)
  have hright := tendsto_nhdsWithin_iff.mpr
    ⟨by simpa only [norm_zero] using hi, hp⟩
  simpa only [Function.comp_def, norm_inv, inv_inv] using
    tendsto_inv_nhdsGT_zero.comp hright

#print axioms exists_rotatedGaussianMode_exponential_bounds
#print axioms tendsto_norm_boundaryGaussianMode_atTop
#print axioms rotatedPrimeDampingFilter_eq_euler_integral
#print axioms exists_rotatedGaussianKernel_boundary_moment_bound
#print axioms exists_boundaryPrimeDampingFilter_arithmetic_bound

end GaloisForLFunctions.ExceptionalLayerTheory
