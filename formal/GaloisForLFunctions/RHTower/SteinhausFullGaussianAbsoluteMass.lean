import GaloisForLFunctions.RHTower.SteinhausFullGaussianCofactorMean
import GaloisForLFunctions.RHTower.SteinhausFullGaussianCofactorTail

open Complex Filter Topology
noncomputable section
namespace RHTower

/-- Positive absolute mass of the actual Gaussian coefficients at real abscissa,
with the smoothing power removed. -/
def normalizedGaussianAbsoluteMass (σ R : ℝ) : ℝ :=
  (∑' n : ℕ, ‖((n + 1 : ℕ) : ℂ) ^ ((σ : ℂ) - 1) *
    smoothAFECutoff (((n + 1 : ℕ) : ℝ) / R)‖) * R ^ (-σ)

private theorem summable_gaussian_real_coefficients (σ : ℝ) {R : ℝ} (hR : 0 < R) :
    Summable (fun n : ℕ => ((n + 1 : ℕ) : ℂ) ^ ((σ : ℂ) - 1) *
      smoothAFECutoff (((n + 1 : ℕ) : ℝ) / R)) := by
  have h := summable_steinhausFullGaussianCofactor
    (A := max σ 0 + 1) (by have := le_max_right σ 0; linarith)
    (s := (σ : ℂ)) (by simp only [Complex.ofReal_re]; have := le_max_left σ 0; linarith)
    hR (fun _ => 0)
  simpa only [SteinhausModel.X, mul_zero, Finset.sum_const_zero, Complex.ofReal_zero,
    Complex.exp_zero, one_mul] using h

/-- The normalized positive coefficients form an actual summable sequence. -/
theorem summable_normalizedGaussianAbsoluteTerms (σ : ℝ) {R : ℝ} (hR : 0 < R) :
    Summable (fun n : ℕ => ‖((n + 1 : ℕ) : ℂ) ^ ((σ : ℂ) - 1) *
      smoothAFECutoff (((n + 1 : ℕ) : ℝ) / R)‖ * R ^ (-σ)) :=
  (summable_gaussian_real_coefficients σ hR).norm.mul_right _

private theorem gaussian_real_coefficient_norm_eq_re (σ : ℝ) {R : ℝ} (hR : 0 < R)
    (n : ℕ) :
    ‖((n + 1 : ℕ) : ℂ) ^ ((σ : ℂ) - 1) *
      smoothAFECutoff (((n + 1 : ℕ) : ℝ) / R)‖ =
    (((n + 1 : ℕ) : ℂ) ^ ((σ : ℂ) - 1) *
      smoothAFECutoff (((n + 1 : ℕ) : ℝ) / R)).re := by
  have hn : 0 < (n + 1 : ℝ) := by positivity
  have hx : 0 < ((n + 1 : ℕ) : ℝ) / R := div_pos (by positivity) hR
  have hcpow : ((n + 1 : ℕ) : ℂ) ^ ((σ : ℂ) - 1) =
      (((n + 1 : ℝ) ^ (σ - 1) : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_add,
      Complex.ofReal_natCast, Nat.cast_add, Nat.cast_one] using
        (Complex.ofReal_cpow hn.le (σ - 1)).symm
  have hcut : smoothAFECutoff (((n + 1 : ℕ) : ℝ) / R) =
      ((smoothAFECutoff (((n + 1 : ℕ) : ℝ) / R)).re : ℂ) := by
    apply Complex.ext
    · rfl
    · exact smoothAFECutoff_im_eq_zero hx
  rw [hcpow, hcut, ← Complex.ofReal_mul,
    Complex.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg hn.le _)
      (smoothAFECutoff_re_nonneg hx)), Complex.ofReal_re]

/-- The absolute mass is the real untwisted cofactor, with its true scale normalization. -/
theorem normalizedGaussianAbsoluteMass_eq_re (σ : ℝ) {R : ℝ} (hR : 0 < R) :
    normalizedGaussianAbsoluteMass σ R =
      (steinhausFullGaussianCofactor (σ : ℂ) R (fun _ => 0)).re * R ^ (-σ) := by
  have hX (n : ℕ) : SteinhausModel.X n (fun _ => 0) = 1 := by simp [SteinhausModel.X]
  unfold normalizedGaussianAbsoluteMass steinhausFullGaussianCofactor
  simp only [hX, one_mul]
  rw [Complex.re_tsum (summable_gaussian_real_coefficients σ hR)]
  congr 1
  exact tsum_congr (gaussian_real_coefficient_norm_eq_re σ hR)

/-- The absolute mass has a finite limit throughout the open unit strip. -/
theorem tendsto_normalizedGaussianAbsoluteMass {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ < 1) :
    Tendsto (normalizedGaussianAbsoluteMass σ) atTop
      (𝓝 ((Complex.exp ((σ : ℂ) ^ 2) / (σ : ℂ)).re)) := by
  have h := tendsto_finitePrimeTwistExtension_gaussian_mean ∅ (fun _ => 0) 0
    (s := (σ : ℂ)) (by simpa using hσ) (by simpa using hσ1)
  have hext : finitePrimeTwistExtension ∅ (fun _ => 0) 0 = (fun _ => 0) := by
    funext p
    simp [finitePrimeTwistExtension]
  rw [hext] at h
  have hc : Tendsto (fun R : ℝ =>
      steinhausFullGaussianCofactor (σ : ℂ) R (fun _ => 0) * (R : ℂ) ^ (-(σ : ℂ)))
      atTop (𝓝 (Complex.exp ((σ : ℂ) ^ 2) / (σ : ℂ))) := by
    simpa [steinhausFullGaussianCofactor, finitePrimePhaseMean] using h
  have hr : Tendsto (fun R : ℝ =>
      (steinhausFullGaussianCofactor (σ : ℂ) R (fun _ => 0) * (R : ℂ) ^ (-(σ : ℂ))).re)
      atTop (𝓝 ((Complex.exp ((σ : ℂ) ^ 2) / (σ : ℂ)).re)) :=
    Complex.continuous_re.continuousAt.tendsto.comp hc
  apply hr.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  rw [normalizedGaussianAbsoluteMass_eq_re σ hR]
  have hpow : (R : ℂ) ^ (-(σ : ℂ)) = ((R ^ (-σ) : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_neg] using (Complex.ofReal_cpow hR.le (-σ)).symm
  rw [hpow]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]

/-- Every phase and coherent twist obey the same positive absolute-mass bound. -/
theorem norm_normalizedFullGaussianCofactor_le_absoluteMass
    (s : ℂ) {R : ℝ} (hR : 0 < R) (ω : SteinhausModel.Omega) (t : ℝ) :
    ‖steinhausFullGaussianCofactor s R ω * (R : ℂ) ^ (-(s + (t : ℂ) * I))‖ ≤
      normalizedGaussianAbsoluteMass s.re R := by
  have hs := summable_steinhausFullGaussianCofactor
    (A := max s.re 0 + 1) (by have := le_max_right s.re 0; linarith)
    (by have := le_max_left s.re 0; linarith) hR ω
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hR]
  simp only [Complex.neg_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.I_re, Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  unfold steinhausFullGaussianCofactor normalizedGaussianAbsoluteMass
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hR.le _)
  calc
    _ ≤ ∑' n : ℕ, ‖SteinhausModel.X (n + 1) ω *
        ((n + 1 : ℕ) : ℂ) ^ (s - 1) * smoothAFECutoff (((n + 1 : ℕ) : ℝ) / R)‖ :=
      norm_tsum_le_tsum_norm hs.norm
    _ = _ := by
      apply tsum_congr
      intro n
      simp only [norm_mul, SteinhausModel.norm_X, one_mul,
        Complex.norm_natCast_cpow_of_pos (Nat.succ_pos n), Complex.sub_re,
        Complex.ofReal_re, Complex.one_re]

end RHTower
