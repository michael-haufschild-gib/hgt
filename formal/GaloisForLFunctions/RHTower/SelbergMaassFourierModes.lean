import GaloisForLFunctions.RHTower.SelbergMaassFourierMean
import GaloisForLFunctions.RHTower.DeningerFourierDecay

/-!
# Actual Fourier coefficients of congruence Maass eigenforms

The literal normalized Fourier integral of a principal-congruence Maass cusp eigenform has
both height derivatives. Integration by parts and actual horizontal periodicity turn its
horizontal second derivative into multiplication by the negative squared physical frequency.
Integrating the source hyperbolic PDE therefore proves the modal equation for every integer
index, including the constant mode.

The defining cusp decay gives height decay uniformly over all Fourier indices. At each positive
height, the source C² regularity also bounds squared frequency times coefficient norm uniformly
in the index. No Bessel ansatz, automorphic lift, or global spectral bound is assumed.
-/

open MeasureTheory Set Filter Topology UpperHalfPlane
open scoped ContDiff
namespace GaloisForLFunctions.RHTower.SelbergMaassFourier
open SelbergMaassMean
open _root_.RHTower
noncomputable section

/-- The normalized Fourier coefficient of a horizontal slice in the actual complex chart. -/
def coefficient (w : ℝ) (n : ℤ) (F : ℂ → ℂ) (y : ℝ) : ℂ :=
  deningerFourierCoeff w (fun x => F (point x y)) n

private theorem kernel_continuous (w : ℝ) (n : ℤ) : Continuous (deningerFourierKernel w n) :=
  continuous_iff_continuousAt.mpr (fun x => (deningerFourierKernel_hasDerivAt w n x).continuousAt)

private theorem weighted_slice_continuous (w : ℝ) (n : ℤ) {F : ℂ → ℂ}
    (hf : ContinuousOn F {z : ℂ | 0 < z.im}) {y : ℝ} (hy : 0 < y) :
    Continuous (fun x => deningerFourierKernel w n x * F (point x y)) :=
  (kernel_continuous w n).mul (slice_continuous hf hy)

/-- Local compact domination justifies height differentiation of the weighted integral. -/
theorem coefficient_hasDerivAt (w : ℝ) (hw : 0 ≤ w) (n : ℤ) {F : ℂ → ℂ}
    (hf : ContDiffOn ℝ 1 F {z : ℂ | 0 < z.im}) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (coefficient w n F) (coefficient w n (directional Complex.I F) y) y := by
  have hd := directional_contDiffOn hf (m := 0) (by simp) Complex.I
  let K : Set (ℝ × ℝ) := Icc 0 w ×ˢ Icc (y / 2) (y + 1)
  have hcont : ContinuousOn (fun xy : ℝ × ℝ =>
      deningerFourierKernel w n xy.1 * directional Complex.I F (point xy.1 xy.2)) K := by
    apply ((kernel_continuous w n).comp continuous_fst).continuousOn.mul
    apply hd.continuousOn.comp (show Continuous (fun xy : ℝ × ℝ => point xy.1 xy.2) by
      unfold point; fun_prop).continuousOn
    intro xy hxy
    have hlow := hxy.2.1
    change 0 < (point xy.1 xy.2).im
    simp only [point, Complex.add_im, Complex.ofReal_im, Complex.mul_I_im,
      Complex.ofReal_re, zero_add]
    linarith
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hcont
  have hn : Ioo (y / 2) (y + 1) ∈ 𝓝 y := Ioo_mem_nhds (by linarith) (by linarith)
  have hpos : ∀ t ∈ Ioo (y / 2) (y + 1), 0 < t := by intro t ht; linarith [ht.1]
  have h := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioc 0 w))
    (F := fun t x => deningerFourierKernel w n x * F (point x t))
    (F' := fun t x => deningerFourierKernel w n x * directional Complex.I F (point x t))
    (bound := fun _ => C) hn
    (by filter_upwards [hn] with t ht
        exact (weighted_slice_continuous w n hf.continuousOn (hpos t ht)).aestronglyMeasurable.restrict)
    ((weighted_slice_continuous w n hf.continuousOn hy).integrableOn_Icc.mono_set Ioc_subset_Icc_self)
    ((weighted_slice_continuous w n hd.continuousOn hy).aestronglyMeasurable.restrict)
    (by filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
        intro t ht
        exact hC (x, t) ⟨⟨hx.1.le, hx.2⟩, ⟨ht.1.le, ht.2.le⟩⟩)
    (integrable_const C)
    (by filter_upwards with x
        intro t ht
        exact (slice_vertical hf x (hpos t ht)).const_mul (deningerFourierKernel w n x))).2
  change HasDerivAt (fun t => coefficient w n F t) _ _
  simpa only [coefficient, deningerFourierCoeff, intervalIntegral.integral_of_le hw] using
    h.const_mul (1 / (w : ℂ))

/-- The actual second height derivative is the coefficient of the second vertical derivative. -/
theorem coefficient_second_hasDerivAt (w : ℝ) (hw : 0 ≤ w) (n : ℤ) {F : ℂ → ℂ}
    (hf : ContDiffOn ℝ 2 F {z : ℂ | 0 < z.im}) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (deriv (coefficient w n F))
      (coefficient w n (directional Complex.I (directional Complex.I F)) y) y := by
  have hd := directional_contDiffOn hf (m := 1) le_rfl Complex.I
  apply (coefficient_hasDerivAt w hw n hd hy).congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hy] with t ht
  exact (coefficient_hasDerivAt w hw n (hf.of_le (by simp : (1 : WithTop ℕ∞) ≤ 2)) ht).deriv

/-- Signed physical frequency at the chosen positive period. -/
def signedFrequency (w : ℝ) (n : ℤ) : ℝ := 2 * Real.pi * n / w

/-- Two integrations by parts over an arbitrary horizontal window.

Unlike the periodic mode formula, both endpoint seams remain visible.  This is
the form needed for rationally scaled trace windows. -/
theorem coefficient_horizontal_second_with_boundary (w : ℝ) (hw : 0 < w) (n : ℤ) {F : ℂ → ℂ}
    (hf : ContDiffOn ℝ 2 F {z : ℂ | 0 < z.im}) {y : ℝ} (hy : 0 < y) :
    coefficient w n (directional 1 (directional 1 F)) y =
      (directional 1 F (point w y) - directional 1 F (point 0 y)) / w +
        ((2 * Real.pi * Complex.I * n) / w) * (F (point w y) - F (point 0 y)) / w -
          ((signedFrequency w n : ℝ) : ℂ) ^ 2 * coefficient w n F y := by
  have hf1 := hf.of_le (by simp : (1 : WithTop ℕ∞) ≤ 2)
  have hd := directional_contDiffOn hf (m := 1) le_rfl (1 : ℂ)
  have hdd := directional_contDiffOn hd (m := 0) (by simp) (1 : ℂ)
  have h1 := deningerFourierCoeff_deriv_with_boundary hw.ne'
    (slice_horizontal hf1 hy) (slice_continuous hd.continuousOn hy) n
  have h2 := deningerFourierCoeff_deriv_with_boundary hw.ne'
    (slice_horizontal hd hy) (slice_continuous hdd.continuousOn hy) n
  rw [h1] at h2
  change coefficient w n (directional 1 (directional 1 F)) y =
      (directional 1 F (point w y) - directional 1 F (point 0 y)) / w +
        ((2 * Real.pi * Complex.I * n) / w) *
          ((F (point w y) - F (point 0 y)) / w +
            ((2 * Real.pi * Complex.I * n) / w) * coefficient w n F y) at h2
  rw [h2]
  have hr : ((2 * Real.pi * Complex.I * n) / (w : ℂ)) ^ 2 =
      -((signedFrequency w n : ℝ) : ℂ) ^ 2 := by
    unfold signedFrequency
    push_cast
    simp only [div_pow, mul_pow, Complex.I_sq]
    ring
  calc
    _ = (directional 1 F (point w y) - directional 1 F (point 0 y)) / w +
        ((2 * Real.pi * Complex.I * n) / w) * (F (point w y) - F (point 0 y)) / w +
          ((2 * Real.pi * Complex.I * n) / w) ^ 2 * coefficient w n F y := by ring
    _ = _ := by rw [hr]; ring

/-- The Maass equation over an arbitrary horizontal Fourier window.

The two seam terms are the exact defect from the homogeneous modal equation.
No periodicity is used. -/
theorem windowedCoefficient_modal_equation {lam : ℝ}
    (f : ℍ → ℂ) (hfmaass : IsMaassEigenfunction lam f)
    (w : ℝ) (hw : 0 < w) (n : ℤ) {y : ℝ} (hy : 0 < y) :
    -(y : ℂ) ^ 2 * (deriv (deriv (coefficient w n (f ∘ ofComplex))) y -
      ((signedFrequency w n : ℝ) : ℂ) ^ 2 * coefficient w n (f ∘ ofComplex) y +
        (directional 1 (f ∘ ofComplex) (point w y) -
          directional 1 (f ∘ ofComplex) (point 0 y)) / w +
        ((2 * Real.pi * Complex.I * n) / w) *
          ((f ∘ ofComplex) (point w y) - (f ∘ ofComplex) (point 0 y)) / w) =
        (lam : ℂ) * coefficient w n (f ∘ ofComplex) y := by
  let F := f ∘ ofComplex
  have hf : ContDiffOn ℝ 2 F {z : ℂ | 0 < z.im} := hfmaass.1
  have hd1 := directional_contDiffOn hf (m := 1) le_rfl (1 : ℂ)
  have hdI := directional_contDiffOn hf (m := 1) le_rfl Complex.I
  have hi1 : IntegrableOn (fun x => deningerFourierKernel w n x *
      directional 1 (directional 1 F) (point x y)) (Ioc 0 w) :=
    (weighted_slice_continuous w n
      (directional_contDiffOn hd1 (m := 0) (by simp) 1).continuousOn hy
      ).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hiI : IntegrableOn (fun x => deningerFourierKernel w n x *
      directional Complex.I (directional Complex.I F) (point x y)) (Ioc 0 w) :=
    (weighted_slice_continuous w n
      (directional_contDiffOn hdI (m := 0) (by simp) Complex.I).continuousOn hy
      ).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have he : ∀ x : ℝ,
      -(y : ℂ) ^ 2 * (directional 1 (directional 1 F) (point x y) +
        directional Complex.I (directional Complex.I F) (point x y)) =
      (lam : ℂ) * F (point x y) := by
    intro x
    have hp : 0 < (point x y).im := by simpa [point] using hy
    have hh := hfmaass.2 ⟨point x y, hp⟩
    change -(y : ℂ) ^ 2 * (directional 1 (directional 1 F) (point x y) +
      directional Complex.I (directional Complex.I F) (point x y)) =
      (lam : ℂ) * f (ofComplex (point x y))
    rw [ofComplex_apply_of_im_pos hp]
    convert hh using 1
    simp [positiveHyperbolicLaplacian, directional, F, UpperHalfPlane.im, point]
    exact Or.inl rfl
  have hew : ∀ x : ℝ,
      -(y : ℂ) ^ 2 * (deningerFourierKernel w n x *
        directional 1 (directional 1 F) (point x y) + deningerFourierKernel w n x *
        directional Complex.I (directional Complex.I F) (point x y)) =
      (lam : ℂ) * (deningerFourierKernel w n x * F (point x y)) := by
    intro x
    linear_combination deningerFourierKernel w n x * he x
  have hint := integral_congr_ae (μ := volume.restrict (Ioc (0 : ℝ) w))
    (Filter.Eventually.of_forall hew)
  rw [integral_const_mul, integral_const_mul, integral_add hi1 hiI] at hint
  have hnorm := congrArg (fun q : ℂ => (1 / (w : ℂ)) * q) hint
  have hc : -(y : ℂ) ^ 2 *
      (coefficient w n (directional 1 (directional 1 F)) y +
        coefficient w n (directional Complex.I (directional Complex.I F)) y) =
      (lam : ℂ) * coefficient w n F y := by
    simp only [coefficient, deningerFourierCoeff, intervalIntegral.integral_of_le hw.le]
    linear_combination hnorm
  rw [coefficient_horizontal_second_with_boundary w hw n hf hy,
    ← (coefficient_second_hasDerivAt w hw.le n hf hy).deriv] at hc
  change -(y : ℂ) ^ 2 * (deriv (deriv (coefficient w n F)) y -
      ((signedFrequency w n : ℝ) : ℂ) ^ 2 * coefficient w n F y +
        (directional 1 F (point w y) - directional 1 F (point 0 y)) / w +
        ((2 * Real.pi * Complex.I * n) / w) *
          (F (point w y) - F (point 0 y)) / w) =
        (lam : ℂ) * coefficient w n F y
  linear_combination hc

/-- The arbitrary-window equation specialized to a Maass cusp eigenform. -/
theorem maassWindowedCoefficient_modal_equation {Γ : Subgroup SL2R} {lam : ℝ}
    (f : MaassCuspEigenform Γ lam) (w : ℝ) (hw : 0 < w) (n : ℤ) {y : ℝ} (hy : 0 < y) :
    -(y : ℂ) ^ 2 * (deriv (deriv (coefficient w n (f.1.1 ∘ ofComplex))) y -
      ((signedFrequency w n : ℝ) : ℂ) ^ 2 * coefficient w n (f.1.1 ∘ ofComplex) y +
        (directional 1 (f.1.1 ∘ ofComplex) (point w y) -
          directional 1 (f.1.1 ∘ ofComplex) (point 0 y)) / w +
        ((2 * Real.pi * Complex.I * n) / w) *
          ((f.1.1 ∘ ofComplex) (point w y) - (f.1.1 ∘ ofComplex) (point 0 y)) / w) =
        (lam : ℂ) * coefficient w n (f.1.1 ∘ ofComplex) y :=
  windowedCoefficient_modal_equation f.1.1 f.2.2.1 w hw n hy

/-- Two integrations by parts give the literal squared-frequency multiplier. -/
theorem coefficient_horizontal_second (w : ℝ) (hw : 0 < w) (n : ℤ) {F : ℂ → ℂ}
    (hf : ContDiffOn ℝ 2 F {z : ℂ | 0 < z.im}) {y : ℝ} (hy : 0 < y)
    (hp : ∀ x, F (point (x + w) y) = F (point x y)) :
    coefficient w n (directional 1 (directional 1 F)) y =
      -((signedFrequency w n : ℝ) : ℂ) ^ 2 * coefficient w n F y := by
  have hf1 := hf.of_le (by simp : (1 : WithTop ℕ∞) ≤ 2)
  have hd := directional_contDiffOn hf (m := 1) le_rfl (1 : ℂ)
  have hdd := directional_contDiffOn hd (m := 0) (by simp) (1 : ℂ)
  have hper : F (point w y) = F (point 0 y) := by simpa only [zero_add] using hp 0
  have hdper : directional 1 F (point w y) = directional 1 F (point 0 y) := by
    simpa only [zero_add] using directional_periodic hf1 hy w hp 0
  have h1 := deningerFourierCoeff_deriv hw.ne' (slice_horizontal hf1 hy)
    (slice_continuous hd.continuousOn hy) hper n
  have h2 := deningerFourierCoeff_deriv hw.ne' (slice_horizontal hd hy)
    (slice_continuous hdd.continuousOn hy) hdper n
  rw [h1] at h2
  change coefficient w n (directional 1 (directional 1 F)) y =
    ((2 * Real.pi * Complex.I * n) / w) *
      (((2 * Real.pi * Complex.I * n) / w) * coefficient w n F y) at h2
  rw [h2]
  have hr : ((2 * Real.pi * Complex.I * n) / (w : ℂ)) ^ 2 =
      -((signedFrequency w n : ℝ) : ℂ) ^ 2 := by
    unfold signedFrequency
    push_cast
    simp only [div_pow, mul_pow, Complex.I_sq]
    ring
  rw [← mul_assoc, ← pow_two, hr]

/-- The actual normalized Fourier coefficient of a principal-congruence Maass cusp eigenform. -/
def maassCoefficient (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)
    (n : ℤ) : ℝ → ℂ := coefficient (N + 1 : ℕ) n (f.1.1 ∘ ofComplex)

/-- Every actual modal coefficient has its first height derivative. -/
theorem maassCoefficient_hasDerivAt (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)
    (n : ℤ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (maassCoefficient N f n) (deriv (maassCoefficient N f n) y) y :=
  (coefficient_hasDerivAt (N + 1 : ℕ) (by positivity) n
    (f.2.2.1.1.of_le (by simp : (1 : WithTop ℕ∞) ≤ 2)) hy).differentiableAt.hasDerivAt

/-- Every actual modal coefficient has its second height derivative. -/
theorem maassCoefficient_second_hasDerivAt (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)
    (n : ℤ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (deriv (maassCoefficient N f n)) (deriv (deriv (maassCoefficient N f n)) y) y :=
  (coefficient_second_hasDerivAt (N + 1 : ℕ) (by positivity) n f.2.2.1.1 hy).differentiableAt.hasDerivAt

/-- The defining Maass PDE implies the actual modal equation at every integer index. -/
theorem maassCoefficient_modal_equation (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)
    (n : ℤ) {y : ℝ} (hy : 0 < y) :
    -(y : ℂ) ^ 2 * (deriv (deriv (maassCoefficient N f n)) y -
      ((signedFrequency (N + 1 : ℕ) n : ℝ) : ℂ) ^ 2 * maassCoefficient N f n y) =
        (lam : ℂ) * maassCoefficient N f n y := by
  let F := f.1.1 ∘ ofComplex
  have hf : ContDiffOn ℝ 2 F {z : ℂ | 0 < z.im} := f.2.2.1.1
  have hd1 := directional_contDiffOn hf (m := 1) le_rfl (1 : ℂ)
  have hdI := directional_contDiffOn hf (m := 1) le_rfl Complex.I
  have hi1 : IntegrableOn (fun x => deningerFourierKernel (N + 1 : ℕ) n x *
      directional 1 (directional 1 F) (point x y)) (Ioc 0 (N + 1 : ℕ)) :=
    (weighted_slice_continuous (N + 1 : ℕ) n
      (directional_contDiffOn hd1 (m := 0) (by simp) 1).continuousOn hy
      ).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hiI : IntegrableOn (fun x => deningerFourierKernel (N + 1 : ℕ) n x *
      directional Complex.I (directional Complex.I F) (point x y)) (Ioc 0 (N + 1 : ℕ)) :=
    (weighted_slice_continuous (N + 1 : ℕ) n
      (directional_contDiffOn hdI (m := 0) (by simp) Complex.I).continuousOn hy
      ).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have he : ∀ x : ℝ,
      -(y : ℂ) ^ 2 * (directional 1 (directional 1 F) (point x y) +
        directional Complex.I (directional Complex.I F) (point x y)) =
      (lam : ℂ) * F (point x y) := by
    intro x
    have hp : 0 < (point x y).im := by simpa [point] using hy
    have hh := f.2.2.1.2 ⟨point x y, hp⟩
    change -(y : ℂ) ^ 2 * (directional 1 (directional 1 F) (point x y) +
      directional Complex.I (directional Complex.I F) (point x y)) =
      (lam : ℂ) * f.1.1 (ofComplex (point x y))
    rw [ofComplex_apply_of_im_pos hp]
    convert hh using 1
    simp [positiveHyperbolicLaplacian, directional, F, UpperHalfPlane.im, point]
    exact Or.inl rfl
  have hew : ∀ x : ℝ,
      -(y : ℂ) ^ 2 * (deningerFourierKernel (N + 1 : ℕ) n x *
        directional 1 (directional 1 F) (point x y) + deningerFourierKernel (N + 1 : ℕ) n x *
        directional Complex.I (directional Complex.I F) (point x y)) =
      (lam : ℂ) * (deningerFourierKernel (N + 1 : ℕ) n x * F (point x y)) := by
    intro x
    linear_combination deningerFourierKernel (N + 1 : ℕ) n x * he x
  have hint := integral_congr_ae (μ := volume.restrict (Ioc (0 : ℝ) (N + 1 : ℕ)))
    (Filter.Eventually.of_forall hew)
  rw [integral_const_mul, integral_const_mul, integral_add hi1 hiI] at hint
  have hnorm := congrArg (fun q : ℂ => (1 / ((N + 1 : ℕ) : ℂ)) * q) hint
  have hc : -(y : ℂ) ^ 2 *
      (coefficient (N + 1 : ℕ) n (directional 1 (directional 1 F)) y +
        coefficient (N + 1 : ℕ) n (directional Complex.I (directional Complex.I F)) y) =
      (lam : ℂ) * coefficient (N + 1 : ℕ) n F y := by
    simp only [coefficient, deningerFourierCoeff, intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ (N + 1 : ℕ))]
    linear_combination hnorm
  rw [coefficient_horizontal_second (N + 1 : ℕ) (by positivity) n hf hy
      (fun x => maass_periodic N f x hy),
    ← (coefficient_second_hasDerivAt (N + 1 : ℕ) (by positivity) n hf hy).deriv] at hc
  change -(y : ℂ) ^ 2 * (deriv (deriv (coefficient (N + 1 : ℕ) n F)) y -
      ((signedFrequency (N + 1 : ℕ) n : ℝ) : ℂ) ^ 2 * coefficient (N + 1 : ℕ) n F y) =
        (lam : ℂ) * coefficient (N + 1 : ℕ) n F y
  linear_combination hc

/-- The zero mode agrees exactly with the previously constructed unnormalized mean. -/
theorem maassCoefficient_zero (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam) (y : ℝ) :
    maassCoefficient N f 0 y = (1 / ((N + 1 : ℕ) : ℂ)) * maassMean N f y := by
  unfold maassCoefficient coefficient deningerFourierCoeff maassMean periodIntegral
  rw [intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ (N + 1 : ℕ))]
  simp [deningerFourierKernel]

/-- Cusp decay forces all modal coefficients to zero uniformly in their integer index. -/
theorem maassCoefficient_uniform_decay (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam) :
    ∀ ε : ℝ, 0 < ε → ∃ A : ℝ, ∀ y : ℝ, A ≤ y →
      ∀ n : ℤ, ‖maassCoefficient N f n y‖ < ε := by
  have hc : IsZeroAtImInfty f.1.1 := by
    simpa only [map_one, one_smul] using f.2.2.2 (1 : SL2Z)
  rw [isZeroAtImInfty_iff] at hc
  intro ε hε
  obtain ⟨A, hA⟩ := hc (ε / 2) (by positivity)
  refine ⟨max A 1, fun y hy n => ?_⟩
  have hAy : A ≤ y := (le_max_left A 1).trans hy
  have hypos : 0 < y := lt_of_lt_of_le (by linarith : (0 : ℝ) < 1) ((le_max_right A 1).trans hy)
  have hb : ∀ x ∈ uIoc (0 : ℝ) (N + 1 : ℕ),
      ‖(f.1.1 ∘ ofComplex) (point x y)‖ ≤ ε / 2 := by
    intro x _
    have hp : 0 < (point x y).im := by simpa [point] using hypos
    simpa only [Function.comp_apply, ofComplex_apply_of_im_pos hp] using
      hA ⟨point x y, hp⟩ (by simpa [UpperHalfPlane.im, point] using hAy)
  simpa only [maassCoefficient, coefficient] using
    (deningerFourierCoeff_norm_le (by positivity : (0 : ℝ) < (N + 1 : ℕ)) hb n).trans_lt
      (by linarith : ε / 2 < ε)

/-- Each actual coefficient tends to zero at infinite height. -/
theorem maassCoefficient_decay (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam) (n : ℤ) :
    Tendsto (maassCoefficient N f n) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨A, hA⟩ := maassCoefficient_uniform_decay N f ε hε
  exact ⟨A, fun y hy => by simpa only [dist_zero_right] using hA y hy n⟩

/-- At every positive height, C² regularity gives a uniform inverse-square frequency bound. -/
theorem maassCoefficient_frequency_square_bound (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)
    {y : ℝ} (hy : 0 < y) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℤ,
      signedFrequency (N + 1 : ℕ) n ^ 2 * ‖maassCoefficient N f n y‖ ≤ M := by
  let F := f.1.1 ∘ ofComplex
  have hf : ContDiffOn ℝ 2 F {z : ℂ | 0 < z.im} := f.2.2.1.1
  have hd := directional_contDiffOn hf (m := 1) le_rfl (1 : ℂ)
  have hdd := directional_contDiffOn hd (m := 0) (by simp) (1 : ℂ)
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := (N + 1 : ℕ))).exists_bound_of_continuousOn
    (slice_continuous hdd.continuousOn hy).continuousOn
  refine ⟨max C 0, le_max_right _ _, fun n => ?_⟩
  have hb : ‖coefficient (N + 1 : ℕ) n (directional 1 (directional 1 F)) y‖ ≤ max C 0 := by
    apply deningerFourierCoeff_norm_le (by positivity : (0 : ℝ) < (N + 1 : ℕ))
    intro x hx
    rw [uIoc_of_le (by positivity : (0 : ℝ) ≤ (N + 1 : ℕ))] at hx
    exact (hC x ⟨hx.1.le, hx.2⟩).trans (le_max_left _ _)
  rw [coefficient_horizontal_second (N + 1 : ℕ) (by positivity) n hf hy
    (fun x => maass_periodic N f x hy)] at hb
  simpa only [maassCoefficient, F, norm_mul, norm_neg, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    using hb

end
end GaloisForLFunctions.RHTower.SelbergMaassFourier
