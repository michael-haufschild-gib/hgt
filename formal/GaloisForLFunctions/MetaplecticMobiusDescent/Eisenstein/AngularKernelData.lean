import GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.AngularSourceMellin

/-!
# Angular reflected Mellin and Fourier data

The shifted cubic Gamma quotient is unitary on the imaginary axis. Multiplying the source's
logarithmic Fourier transform by this quotient preserves every absolute Fourier moment.
Compact smooth sources therefore give smooth reflected logarithmic profiles. On vertical
strips, the same data and all Euler weights decay faster than any prescribed power.
-/

open Complex MeasureTheory Set Filter Asymptotics
open scoped ContDiff ComplexConjugate Classical Topology FourierTransform SchwartzMap
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicJacobi CubicKubota CubicRamified RationalSource
noncomputable section

def angularMellinData (k : ℕ) (V : ℝ → ℂ) (s : ℂ) : ℂ :=
  mellin V (-s) * angularCubicReflectionGamma k s

def angularMellinEulerData (k : ℕ) (V : ℝ → ℂ) (j : ℕ) (s : ℂ) : ℂ :=
  (-s) ^ j * angularMellinData k V s

def angularPaperKernel (k : ℕ) (V : ℝ → ℂ) (x : ℝ) : ℂ :=
  mellinInv 0 (angularMellinData k V) (paperScale * x)

def angularPaperKernelLogDerivative (k : ℕ) (V : ℝ → ℂ) (j : ℕ) (x : ℝ) : ℂ :=
  mellinInv 0 (angularMellinEulerData k V j) (paperScale * x)

/-- The angular Mellin data are holomorphic throughout a common left half-strip. -/
theorem angularMellinEulerData_differentiableAt (k : ℕ) (V : ℝ → ℂ) (a b : ℝ)
    (ha : 0 < a) (hVs : Function.support V ⊆ Icc a b) (hV : ContDiff ℝ ∞ V)
    (j : ℕ) (s : ℂ) (hs : -(5 / 6 : ℝ) < s.re) :
    DifferentiableAt ℂ (angularMellinEulerData k V j) s := by
  have hm := ((compact_source_mellin_differentiable V a b ha hVs hV (-s)).comp s
    differentiableAt_id.neg)
  have hg := angularCubicReflectionGamma_differentiableAt k s (by
    have hk : (0 : ℝ) ≤ (3 * k : ℕ) := Nat.cast_nonneg _
    linarith only [hs, hk])
  exact (differentiableAt_id.neg.pow j).mul (hm.mul hg)

/-- Polynomial Gamma growth is absorbed by rapid Mellin decay of the compact source. -/
theorem angularMellinData_strip_decay (k : ℕ) (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hVs : Function.support V ⊆ Icc a b) (hV : ContDiff ℝ ∞ V) (A j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ Icc (-(1 / 4 : ℝ)) (A : ℝ), ∀ t : ℝ,
      (1 + |t|) ^ j * ‖angularMellinData k V ((σ : ℂ) + t * Complex.I)‖ ≤ C := by
  obtain ⟨Cγ, hCγ, hγ⟩ := angularCubicReflectionGamma_strip_bound k A
  obtain ⟨CV, hCV, hVb⟩ := compact_source_mellin_strip_decay V a b ha hVs hV
    (-(A : ℝ)) (1 / 4) (4 * A + 4 + j)
  refine ⟨Cγ * CV, mul_pos hCγ hCV, ?_⟩
  intro σ hσ t
  have hσ' : -σ ∈ Icc (-(A : ℝ)) (1 / 4) := by constructor <;> linarith only [hσ.1, hσ.2]
  have hmb := hVb (-σ) hσ' (-t)
  have he : ((-σ : ℝ) : ℂ) + (-t : ℝ) * Complex.I = -((σ : ℂ) + t * Complex.I) := by
    push_cast
    ring
  rw [he, abs_neg] at hmb
  rw [angularMellinData, norm_mul]
  calc
    _ = ((1 + |t|) ^ j * ‖mellin V (-((σ : ℂ) + t * Complex.I))‖) *
        ‖angularCubicReflectionGamma k ((σ : ℂ) + t * Complex.I)‖ := by ring
    _ ≤ ((1 + |t|) ^ j * ‖mellin V (-((σ : ℂ) + t * Complex.I))‖) *
        (Cγ * (1 + |t|) ^ (4 * A + 4)) :=
      mul_le_mul_of_nonneg_left (hγ σ hσ t) (by positivity)
    _ = Cγ * ((1 + |t|) ^ (4 * A + 4 + j) * ‖mellin V (-((σ : ℂ) + t * Complex.I))‖) := by
      rw [pow_add]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hmb hCγ.le

/-- Every Euler-weighted angular Mellin datum has an integrable common strip majorant. -/
theorem angularMellinEulerData_strip_bound (k : ℕ) (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hVs : Function.support V ⊆ Icc a b) (hV : ContDiff ℝ ∞ V) (A j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ Icc (-(1 / 4 : ℝ)) (A : ℝ), ∀ t : ℝ,
      ‖angularMellinEulerData k V j ((σ : ℂ) + t * Complex.I)‖ ≤ C / (1 + t ^ 2) := by
  obtain ⟨C, hC, hb⟩ := angularMellinData_strip_decay k V a b ha hVs hV A (j + 2)
  refine ⟨((A : ℝ) + 2) ^ j * C, by positivity, ?_⟩
  intro σ hσ t
  apply weighted_two_to_cauchy (norm_nonneg _) t
  have hσabs : |σ| ≤ (A : ℝ) + 1 := by
    apply abs_le.mpr
    constructor <;> linarith only [hσ.1, hσ.2, (Nat.cast_nonneg A : (0 : ℝ) ≤ A)]
  have hz : ‖(σ : ℂ) + t * Complex.I‖ ≤ ((A : ℝ) + 2) * (1 + |t|) := by
    have hn := norm_add_le (σ : ℂ) ((t : ℂ) * Complex.I)
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one] at hn
    nlinarith only [hn, hσabs, abs_nonneg t, (Nat.cast_nonneg A : (0 : ℝ) ≤ A),
      mul_nonneg (Nat.cast_nonneg A : (0 : ℝ) ≤ A) (abs_nonneg t)]
  rw [angularMellinEulerData, norm_mul, norm_pow, norm_neg]
  calc
    _ ≤ (1 + |t|) ^ 2 * ((((A : ℝ) + 2) * (1 + |t|)) ^ j *
        ‖angularMellinData k V ((σ : ℂ) + t * Complex.I)‖) := by gcongr
    _ = ((A : ℝ) + 2) ^ j * ((1 + |t|) ^ (j + 2) *
        ‖angularMellinData k V ((σ : ℂ) + t * Complex.I)‖) := by rw [mul_pow, pow_add]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hb σ hσ t) (by positivity)

/-- The angular quotient gives a continuous unitary multiplier on logarithmic frequencies. -/
def angularKernelAxisMultiplier (k : ℕ) (u : ℝ) : ℂ :=
  angularCubicReflectionGamma k (((2 * Real.pi * u : ℝ) : ℂ) * Complex.I)

lemma angularKernelAxisMultiplier_continuous (k : ℕ) : Continuous (angularKernelAxisMultiplier k) := by
  have hl : Continuous (fun u : ℝ => ((2 * Real.pi * u : ℝ) : ℂ) * Complex.I) := by fun_prop
  apply continuous_iff_continuousAt.2
  intro u
  apply (angularCubicReflectionGamma_differentiableAt k _ ?_).continuousAt.comp hl.continuousAt
  have hk : (0 : ℝ) ≤ (3 * k : ℕ) := Nat.cast_nonneg _
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_zero, zero_mul, sub_zero]
  linarith only [hk]

def angularKernelSpectralProfile (k : ℕ) (f : SchwartzMap ℝ ℂ) (u : ℝ) : ℂ :=
  angularKernelAxisMultiplier k u * (𝓕 f) u

lemma angularKernelSpectralProfile_norm (k : ℕ) (f : SchwartzMap ℝ ℂ) (u : ℝ) :
    ‖angularKernelSpectralProfile k f u‖ = ‖(𝓕 f) u‖ := by
  rw [angularKernelSpectralProfile, norm_mul, angularKernelAxisMultiplier,
    angularCubicReflectionGamma_axis_norm, one_mul]

lemma angularKernelSpectralProfile_continuous (k : ℕ) (f : SchwartzMap ℝ ℂ) :
    Continuous (angularKernelSpectralProfile k f) :=
  (angularKernelAxisMultiplier_continuous k).mul (𝓕 f).continuous

lemma angularKernelSpectralProfile_moment_integrable (k : ℕ) (f : SchwartzMap ℝ ℂ) (j : ℕ) :
    Integrable (fun u : ℝ => ‖u‖ ^ j * ‖angularKernelSpectralProfile k f u‖) := by
  simpa only [angularKernelSpectralProfile_norm] using (𝓕 f).integrable_pow_mul volume j

lemma angularKernelSpectralProfile_pow_integrable (k : ℕ) (f : SchwartzMap ℝ ℂ) (j : ℕ) :
    Integrable (fun u : ℝ => u ^ j • angularKernelSpectralProfile k f u) := by
  have hn (u : ℝ) : ‖(u ^ j : ℝ) • angularKernelSpectralProfile k f u‖ =
      ‖u‖ ^ j * ‖angularKernelSpectralProfile k f u‖ := by rw [norm_smul, norm_pow]
  apply (angularKernelSpectralProfile_moment_integrable k f j).mono'
    ((continuous_id.pow j).smul (angularKernelSpectralProfile_continuous k f)).aestronglyMeasurable
  exact Eventually.of_forall (fun u => (hn u).le)

def angularReflectedKernelLogProfile (k : ℕ) (f : SchwartzMap ℝ ℂ) : ℝ → ℂ :=
  𝓕 (angularKernelSpectralProfile k f)

lemma angularReflectedKernelLogProfile_smooth (k : ℕ) (f : SchwartzMap ℝ ℂ) :
    ContDiff ℝ ∞ (angularReflectedKernelLogProfile k f) :=
  Real.contDiff_fourier (fun j _ => angularKernelSpectralProfile_moment_integrable k f j)

lemma angularReflectedKernelLogProfile_deriv (k : ℕ) (f : SchwartzMap ℝ ℂ) (j : ℕ) :
    iteratedDeriv j (angularReflectedKernelLogProfile k f) =
      𝓕 (fun u : ℝ => (-2 * Real.pi * Complex.I * u) ^ j * angularKernelSpectralProfile k f u) := by
  simpa only [angularReflectedKernelLogProfile, smul_eq_mul] using
    Real.iteratedDeriv_fourier (N := (⊤ : ℕ∞))
      (fun n _ => angularKernelSpectralProfile_pow_integrable k f n) (by simp : (j : ℕ∞) ≤ ⊤)

/-- The inverse Mellin kernel is the Fourier transform of its logarithmic spectrum. -/
lemma angularPaperKernel_eq_logFourier (k : ℕ) (V : ℝ → ℂ) (f : SchwartzMap ℝ ℂ)
    (hf : ∀ u, f u = V (Real.exp u)) (x : ℝ) (hx : 0 < x) :
    angularPaperKernel k V x = angularReflectedKernelLogProfile k f (Real.log (paperScale * x)) := by
  unfold angularPaperKernel
  rw [mellinInv_eq_fourierInv 0 _ (mul_pos paperScale_pos hx)]
  simp only [Complex.ofReal_zero, neg_zero, Complex.cpow_zero, one_smul]
  rw [Real.fourierInv_eq_fourier_neg, neg_neg]
  have he : (fun y : ℝ => angularMellinData k V (0 + 2 * Real.pi * y * Complex.I)) =
      angularKernelSpectralProfile k f := by
    funext y
    have hy : (0 + 2 * Real.pi * y * Complex.I : ℂ) =
        ((2 * Real.pi * y : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [hy, angularMellinData, mellin_imaginary_eq_logFourier V f hf]
    exact mul_comm _ _
  rw [he]
  rfl

lemma angularPaperKernelLogDerivative_zero (k : ℕ) (V : ℝ → ℂ) (x : ℝ) :
    angularPaperKernelLogDerivative k V 0 x = angularPaperKernel k V x := by
  have he : angularMellinEulerData k V 0 = angularMellinData k V := by
    funext s
    simp only [angularMellinEulerData, pow_zero, one_mul]
  rw [angularPaperKernelLogDerivative, angularPaperKernel, he]

/-- Euler-weighted Mellin inversion gives the ordinary derivatives on logarithmic coordinates. -/
lemma angularPaperKernelLogDerivative_eq_logFourier (k : ℕ) (V : ℝ → ℂ) (f : SchwartzMap ℝ ℂ)
    (hf : ∀ u, f u = V (Real.exp u)) (j : ℕ) (x : ℝ) (hx : 0 < x) :
    angularPaperKernelLogDerivative k V j x =
      iteratedDeriv j (angularReflectedKernelLogProfile k f) (Real.log (paperScale * x)) := by
  rw [angularPaperKernelLogDerivative, mellinInv_eq_fourierInv 0 _ (mul_pos paperScale_pos hx)]
  simp only [Complex.ofReal_zero, neg_zero, Complex.cpow_zero, one_smul]
  rw [Real.fourierInv_eq_fourier_neg, neg_neg, angularReflectedKernelLogProfile_deriv]
  have he : (fun y : ℝ => angularMellinEulerData k V j (0 + 2 * Real.pi * y * Complex.I)) =
      fun u : ℝ => (-2 * Real.pi * Complex.I * u) ^ j * angularKernelSpectralProfile k f u := by
    funext u
    have hu : (0 + 2 * Real.pi * u * Complex.I : ℂ) =
        ((2 * Real.pi * u : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [hu, angularMellinEulerData, angularMellinData, mellin_imaginary_eq_logFourier V f hf]
    have hp : -(((2 * Real.pi * u : ℝ) : ℂ) * Complex.I) = -2 * Real.pi * Complex.I * u := by
      push_cast
      ring
    rw [hp]
    dsimp only [angularKernelSpectralProfile, angularKernelAxisMultiplier]
    ring
  rw [he]

/-- The angular inverse Mellin kernel is smooth on the positive axis. -/
theorem angularPaperKernel_compact_source_smooth (k : ℕ) (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hVs : Function.support V ⊆ Icc a b) (hV : ContDiff ℝ ∞ V) :
    ContDiffOn ℝ ∞ (angularPaperKernel k V) (Ioi 0) := by
  let f := kernelLogSource V a b ha hVs hV
  have hf : ∀ u, f u = V (Real.exp u) := fun u => rfl
  have hg : ContDiffOn ℝ ∞
      (fun x => angularReflectedKernelLogProfile k f (Real.log (paperScale * x))) (Ioi 0) := by
    intro x hx
    apply (angularReflectedKernelLogProfile_smooth k f).contDiffAt.comp_contDiffWithinAt x
    exact ((contDiffAt_const.mul contDiffAt_id).log
      (ne_of_gt (mul_pos paperScale_pos hx))).contDiffWithinAt
  apply hg.congr
  intro x hx
  exact angularPaperKernel_eq_logFourier k V f hf x hx

lemma iteratedDeriv_angularPaperKernel_exp (k : ℕ) (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hVs : Function.support V ⊆ Icc a b) (hV : ContDiff ℝ ∞ V)
    (R : ℝ) (hR : 0 < R) (j : ℕ) (u : ℝ) :
    iteratedDeriv j (fun v : ℝ => angularPaperKernel k V (R * Real.exp v)) u =
      angularPaperKernelLogDerivative k V j (R * Real.exp u) := by
  let f := kernelLogSource V a b ha hVs hV
  have hf : ∀ v, f v = V (Real.exp v) := fun _ => rfl
  have he (v : ℝ) : Real.log (paperScale * (R * Real.exp v)) = Real.log (paperScale * R) + v := by
    rw [← mul_assoc, Real.log_mul (mul_pos paperScale_pos hR).ne' (Real.exp_pos v).ne', Real.log_exp]
  have hfun : (fun v : ℝ => angularPaperKernel k V (R * Real.exp v)) =
      fun v : ℝ => angularReflectedKernelLogProfile k f (Real.log (paperScale * R) + v) := by
    funext v
    rw [angularPaperKernel_eq_logFourier k V f hf _ (mul_pos hR (Real.exp_pos v)), he]
  rw [hfun, iteratedDeriv_comp_const_add,
    angularPaperKernelLogDerivative_eq_logFourier k V f hf j _ (mul_pos hR (Real.exp_pos u)), he]

lemma angularPaperKernel_exp_smooth (k : ℕ) (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hVs : Function.support V ⊆ Icc a b) (hV : ContDiff ℝ ∞ V) (R : ℝ) (hR : 0 < R) :
    ContDiff ℝ ∞ (fun u : ℝ => angularPaperKernel k V (R * Real.exp u)) := by
  let f := kernelLogSource V a b ha hVs hV
  have he : (fun u : ℝ => angularPaperKernel k V (R * Real.exp u)) =
      fun u : ℝ => angularReflectedKernelLogProfile k f (Real.log (paperScale * R) + u) := by
    funext u
    rw [angularPaperKernel_eq_logFourier k V f (fun _ => rfl) _ (mul_pos hR (Real.exp_pos u))]
    rw [← mul_assoc, Real.log_mul (mul_pos paperScale_pos hR).ne' (Real.exp_pos u).ne', Real.log_exp]
  rw [he]
  exact (angularReflectedKernelLogProfile_smooth k f).comp (contDiff_const.add contDiff_id)

end
end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
