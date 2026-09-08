import GaloisForLFunctions.RHTower.SelbergMaassParseval
import GaloisForLFunctions.RHTower.SelbergExceptionalCuspMean
import Mathlib.Analysis.Complex.RealDeriv

/-!
# Actual Maass slice mass, flux, and quarter-energy balance

Real C² regularity and horizontal periodicity give exact Green and height-derivative
identities for the literal source chart. With period-normalized mass `M`, boundary
flux `J`, and gradient energy `G`, these are `M'=2J` and `J'=G-lam*M/y²`.
Parseval identifies the physical quarter-energy slice with
`J' + (lam-1/4)*M/y²`. The defining cusp filter forces `M` to zero.

For actual positive sub-quarter eigenforms the previously proved zero constant
coefficient and integer frequency gap give `G ≥ (2*pi/w)²*M`.
This supplies actual differential data, without a modal ansatz or assumed lift.
The quotient-core inequality and the global Selberg conclusion remain open.
-/

open MeasureTheory Set Filter Topology UpperHalfPlane Complex
open scoped ContDiff
namespace GaloisForLFunctions.RHTower.SelbergMaassFlux
open SelbergMaassMean SelbergMaassParseval
noncomputable section

private def productChart (F G : ℂ → ℂ) (z : ℂ) : ℂ := F z * (starRingEnd ℂ) (G z)

/-- Unnormalized real Hermitian pairing of two literal horizontal chart slices. -/
def pairing (w : ℝ) (F G : ℂ → ℂ) (y : ℝ) : ℝ := (periodIntegral w (productChart F G) y).re

private theorem product_contDiffOn {F G : ℂ → ℂ} {n : WithTop ℕ∞}
    (hf : ContDiffOn ℝ n F {z : ℂ | 0 < z.im})
    (hg : ContDiffOn ℝ n G {z : ℂ | 0 < z.im}) :
    ContDiffOn ℝ n (productChart F G) {z : ℂ | 0 < z.im} :=
  hf.mul (Complex.conjCLE.contDiff.comp_contDiffOn hg)

private theorem product_continuousOn {F G : ℂ → ℂ}
    (hf : ContinuousOn F {z : ℂ | 0 < z.im})
    (hg : ContinuousOn G {z : ℂ | 0 < z.im}) :
    ContinuousOn (productChart F G) {z : ℂ | 0 < z.im} :=
  hf.mul (Complex.continuous_conj.comp_continuousOn hg)

private theorem product_integrable (w : ℝ) {F G : ℂ → ℂ}
    (hf : ContinuousOn F {z : ℂ | 0 < z.im})
    (hg : ContinuousOn G {z : ℂ | 0 < z.im}) {y : ℝ} (hy : 0 < y) :
    IntegrableOn (fun x => productChart F G (point x y)) (Ioc 0 w) :=
  (slice_continuous (product_continuousOn hf hg) hy).integrableOn_Icc.mono_set Ioc_subset_Icc_self

private theorem conj_hasDerivAt {f : ℝ → ℂ} {f' : ℂ} {y : ℝ} (h : HasDerivAt f f' y) :
    HasDerivAt (fun t => (starRingEnd ℂ) (f t)) ((starRingEnd ℂ) f') y :=
  (Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt.comp_hasDerivAt y h

private theorem product_vertical {F G : ℂ → ℂ}
    (hf : ContDiffOn ℝ 1 F {z : ℂ | 0 < z.im})
    (hg : ContDiffOn ℝ 1 G {z : ℂ | 0 < z.im}) (x : ℝ) {y : ℝ} (hy : 0 < y) :
    directional Complex.I (productChart F G) (point x y) =
      productChart (directional Complex.I F) G (point x y) +
      productChart F (directional Complex.I G) (point x y) := by
  have h := (slice_vertical hf x hy).mul (conj_hasDerivAt (slice_vertical hg x hy))
  exact (slice_vertical (product_contDiffOn hf hg) x hy).unique h

/-- The real pairing is the integral of the literal real Hermitian product. -/
theorem pairing_eq_integral (w : ℝ) {F G : ℂ → ℂ}
    (hf : ContinuousOn F {z : ℂ | 0 < z.im})
    (hg : ContinuousOn G {z : ℂ | 0 < z.im}) {y : ℝ} (hy : 0 < y) :
    pairing w F G y = ∫ x in Ioc 0 w, (F (point x y) * (starRingEnd ℂ) (G (point x y))).re := by
  unfold pairing periodIntegral
  exact (integral_re (product_integrable w hf hg hy)).symm

/-- Real Hermitian pairing is symmetric. -/
theorem pairing_symm (w : ℝ) {F G : ℂ → ℂ}
    (hf : ContinuousOn F {z : ℂ | 0 < z.im})
    (hg : ContinuousOn G {z : ℂ | 0 < z.im}) {y : ℝ} (hy : 0 < y) :
    pairing w F G y = pairing w G F y := by
  rw [pairing_eq_integral w hf hg hy, pairing_eq_integral w hg hf hy]
  apply integral_congr_ae
  filter_upwards with x
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- Pairing a slice with itself gives its physical squared mass. -/
theorem pairing_self (w : ℝ) {F : ℂ → ℂ}
    (hf : ContinuousOn F {z : ℂ | 0 < z.im}) {y : ℝ} (hy : 0 < y) :
    pairing w F F y = ∫ x in Ioc 0 w, Complex.normSq (F (point x y)) := by
  rw [pairing_eq_integral w hf hf hy]
  apply integral_congr_ae
  filter_upwards with x
  rw [Complex.mul_conj, Complex.ofReal_re]

/-- Local compact domination and the product rule differentiate the actual pairing. -/
theorem pairing_hasDerivAt (w : ℝ) {F G : ℂ → ℂ}
    (hf : ContDiffOn ℝ 1 F {z : ℂ | 0 < z.im})
    (hg : ContDiffOn ℝ 1 G {z : ℂ | 0 < z.im}) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (pairing w F G)
      (pairing w (directional Complex.I F) G y + pairing w F (directional Complex.I G) y) y := by
  have hdF := directional_contDiffOn hf (m := 0) (by simp) Complex.I
  have hdG := directional_contDiffOn hg (m := 0) (by simp) Complex.I
  have h := periodIntegral_hasDerivAt w (product_contDiffOn hf hg) hy
  have he : periodIntegral w (directional Complex.I (productChart F G)) y =
      periodIntegral w (productChart (directional Complex.I F) G) y +
      periodIntegral w (productChart F (directional Complex.I G)) y := by
    unfold periodIntegral
    rw [integral_congr_ae (Filter.Eventually.of_forall (fun x => product_vertical hf hg x hy))]
    exact integral_add (product_integrable w hdF.continuousOn hg.continuousOn hy)
      (product_integrable w hf.continuousOn hdG.continuousOn hy)
  have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt y h
  change HasDerivAt (pairing w F G) (periodIntegral w (directional Complex.I (productChart F G)) y).re y at hr
  rw [he, Complex.add_re] at hr
  exact hr

/-- Actual periodicity cancels both endpoint terms in horizontal Green integration. -/
theorem pairing_horizontal_green (w : ℝ) (hw : 0 ≤ w) {F : ℂ → ℂ}
    (hf : ContDiffOn ℝ 2 F {z : ℂ | 0 < z.im}) {y : ℝ} (hy : 0 < y)
    (hp : ∀ x, F (point (x + w) y) = F (point x y)) :
    pairing w (directional 1 (directional 1 F)) F y =
      -pairing w (directional 1 F) (directional 1 F) y := by
  have hf1 := hf.of_le (by simp : (1 : WithTop ℕ∞) ≤ 2)
  have hd := directional_contDiffOn hf (m := 1) le_rfl (1 : ℂ)
  have hdd := directional_contDiffOn hd (m := 0) (by simp) (1 : ℂ)
  have hp0 : F (point w y) = F (point 0 y) := by simpa only [zero_add] using hp 0
  have hp1 : directional 1 F (point w y) = directional 1 F (point 0 y) := by
    simpa only [zero_add] using directional_periodic hf1 hy w hp 0
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := 0) (b := w)
    (fun x _ => conj_hasDerivAt (slice_horizontal hf1 hy x))
    (fun x _ => slice_horizontal hd hy x)
    ((Complex.continuous_conj.comp (slice_continuous hd.continuousOn hy)).intervalIntegrable _ _)
    ((slice_continuous hdd.continuousOn hy).intervalIntegrable _ _)
  rw [hp0, hp1, sub_self, zero_sub] at h
  simp only [intervalIntegral.integral_of_le hw] at h
  simpa only [pairing, periodIntegral, productChart, Complex.neg_re, mul_comm] using congrArg Complex.re h

/-- Period-normalized physical squared mass of the actual Maass slice. -/
def mass (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam) (y : ℝ) : ℝ :=
  ((N + 1 : ℕ) : ℝ)⁻¹ * pairing (N + 1 : ℕ) (f.1.1 ∘ ofComplex) (f.1.1 ∘ ofComplex) y

/-- Period-normalized outgoing vertical mass pairing at the actual height. -/
def flux (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam) (y : ℝ) : ℝ :=
  ((N + 1 : ℕ) : ℝ)⁻¹ * pairing (N + 1 : ℕ)
    (directional Complex.I (f.1.1 ∘ ofComplex)) (f.1.1 ∘ ofComplex) y

/-- Period-normalized sum of horizontal and vertical derivative energies. -/
def gradientEnergy (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam) (y : ℝ) : ℝ :=
  ((N + 1 : ℕ) : ℝ)⁻¹ *
    (pairing (N + 1 : ℕ) (directional 1 (f.1.1 ∘ ofComplex)) (directional 1 (f.1.1 ∘ ofComplex)) y +
    pairing (N + 1 : ℕ) (directional Complex.I (f.1.1 ∘ ofComplex)) (directional Complex.I (f.1.1 ∘ ofComplex)) y)

/-- The actual mass derivative is twice the actual boundary flux. -/
theorem mass_hasDerivAt (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)
    {y : ℝ} (hy : 0 < y) : HasDerivAt (mass N f) (2 * flux N f y) y := by
  let F := f.1.1 ∘ ofComplex
  have hf : ContDiffOn ℝ 1 F {z : ℂ | 0 < z.im} := f.2.2.1.1.of_le (by simp)
  have hd := directional_contDiffOn hf (m := 0) (by simp) Complex.I
  change HasDerivAt (fun t => ((N + 1 : ℕ) : ℝ)⁻¹ * pairing (N + 1 : ℕ) F F t) _ y
  apply ((pairing_hasDerivAt (N + 1 : ℕ) hf hf hy).const_mul ((N + 1 : ℕ) : ℝ)⁻¹).congr_deriv
  rw [pairing_symm (N + 1 : ℕ) hf.continuousOn hd.continuousOn hy]
  change _ = 2 * (((N + 1 : ℕ) : ℝ)⁻¹ * pairing (N + 1 : ℕ) (directional Complex.I F) F y)
  ring

private theorem maass_pairing_equation (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)
    {y : ℝ} (hy : 0 < y) :
    -y ^ 2 * (pairing (N + 1 : ℕ) (directional 1 (directional 1 (f.1.1 ∘ ofComplex)))
      (f.1.1 ∘ ofComplex) y +
      pairing (N + 1 : ℕ) (directional Complex.I (directional Complex.I (f.1.1 ∘ ofComplex)))
      (f.1.1 ∘ ofComplex) y) = lam * pairing (N + 1 : ℕ) (f.1.1 ∘ ofComplex) (f.1.1 ∘ ofComplex) y := by
  let F := f.1.1 ∘ ofComplex
  have hf : ContDiffOn ℝ 2 F {z : ℂ | 0 < z.im} := f.2.2.1.1
  have hd1 := directional_contDiffOn hf (m := 1) le_rfl (1 : ℂ)
  have hdI := directional_contDiffOn hf (m := 1) le_rfl Complex.I
  have hdd1 := directional_contDiffOn hd1 (m := 0) (by simp) (1 : ℂ)
  have hddI := directional_contDiffOn hdI (m := 0) (by simp) Complex.I
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
  have hew : ∀ x : ℝ, -(y : ℂ) ^ 2 *
      (productChart (directional 1 (directional 1 F)) F (point x y) +
        productChart (directional Complex.I (directional Complex.I F)) F (point x y)) =
      (lam : ℂ) * productChart F F (point x y) := by
    intro x
    unfold productChart
    linear_combination (starRingEnd ℂ) (F (point x y)) * he x
  have h := integral_congr_ae (μ := volume.restrict (Ioc (0 : ℝ) (N + 1 : ℕ)))
    (Filter.Eventually.of_forall hew)
  rw [integral_const_mul, integral_const_mul,
    integral_add (product_integrable (N + 1 : ℕ) hdd1.continuousOn hf.continuousOn hy)
      (product_integrable (N + 1 : ℕ) hddI.continuousOn hf.continuousOn hy)] at h
  have hr := congrArg Complex.re h
  simp only [← Complex.ofReal_pow, ← Complex.ofReal_neg, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.add_re] at hr
  exact hr

/-- The source Maass PDE and horizontal Green identity give the actual flux derivative. -/
theorem flux_hasDerivAt (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)
    {y : ℝ} (hy : 0 < y) :
    HasDerivAt (flux N f) (gradientEnergy N f y - lam / y ^ 2 * mass N f y) y := by
  let F := f.1.1 ∘ ofComplex
  have hf : ContDiffOn ℝ 2 F {z : ℂ | 0 < z.im} := f.2.2.1.1
  have hdI := directional_contDiffOn hf (m := 1) le_rfl Complex.I
  have h := maass_pairing_equation N f hy
  rw [pairing_horizontal_green (N + 1 : ℕ) (by positivity) hf hy
    (fun x => maass_periodic N f x hy)] at h
  have he : pairing (N + 1 : ℕ) (directional Complex.I (directional Complex.I F)) F y =
      pairing (N + 1 : ℕ) (directional 1 F) (directional 1 F) y -
        lam / y ^ 2 * pairing (N + 1 : ℕ) F F y := by
    field_simp
    nlinarith [h]
  change HasDerivAt (fun t => ((N + 1 : ℕ) : ℝ)⁻¹ * pairing (N + 1 : ℕ) (directional Complex.I F) F t) _ y
  apply ((pairing_hasDerivAt (N + 1 : ℕ) hdI
    (hf.of_le (by simp : (1 : WithTop ℕ∞) ≤ 2)) hy).const_mul ((N + 1 : ℕ) : ℝ)⁻¹).congr_deriv
  rw [he]
  unfold gradientEnergy mass
  change _ = ((N + 1 : ℕ) : ℝ)⁻¹ *
    (pairing (N + 1 : ℕ) (directional 1 F) (directional 1 F) y +
      pairing (N + 1 : ℕ) (directional Complex.I F) (directional Complex.I F) y) -
    lam / y ^ 2 * (((N + 1 : ℕ) : ℝ)⁻¹ * pairing (N + 1 : ℕ) F F y)
  ring

/-- The actual second mass derivative equals twice gradient energy minus spectral mass. -/
theorem mass_second_hasDerivAt (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)
    {y : ℝ} (hy : 0 < y) :
    HasDerivAt (deriv (mass N f)) (2 * (gradientEnergy N f y - lam / y ^ 2 * mass N f y)) y := by
  apply ((flux_hasDerivAt N f hy).const_mul 2).congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hy] with t ht
  exact (mass_hasDerivAt N f ht).deriv

/-- The defined mass agrees with the literal normalized interval integral. -/
theorem mass_eq_integral (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)
    {y : ℝ} (hy : 0 < y) :
    mass N f y = ((N + 1 : ℕ) : ℝ)⁻¹ * ∫ x in (0 : ℝ)..(N + 1 : ℕ),
      Complex.normSq ((f.1.1 ∘ ofComplex) (point x y)) := by
  rw [mass, pairing_self _ f.2.2.1.1.continuousOn hy,
    intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ (N + 1 : ℕ))]

/-- Actual physical mass is nonnegative. -/
theorem mass_nonneg (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)
    {y : ℝ} (hy : 0 < y) : 0 ≤ mass N f y := by
  rw [mass, pairing_self _ f.2.2.1.1.continuousOn hy]
  exact mul_nonneg (by positivity) (integral_nonneg (fun _ => Complex.normSq_nonneg _))

/-- The literal squared Fourier coefficients sum to actual normalized mass. -/
theorem mass_hasSum (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)
    {y : ℝ} (hy : 0 < y) :
    HasSum (fun n : ℤ => Complex.normSq (SelbergMaassFourier.maassCoefficient N f n y))
      (mass N f y) := by
  rw [mass_eq_integral N f hy]
  exact maass_mass_hasSum N f hy

/-- The actual horizontal and vertical modal derivative energies sum to physical gradient energy. -/
theorem gradientEnergy_hasSum (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)
    {y : ℝ} (hy : 0 < y) :
    HasSum (fun n : ℤ => SelbergMaassFourier.signedFrequency (N + 1 : ℕ) n ^ 2 *
        Complex.normSq (SelbergMaassFourier.maassCoefficient N f n y) +
        Complex.normSq (deriv (SelbergMaassFourier.maassCoefficient N f n) y))
      (gradientEnergy N f y) := by
  have hf := f.2.2.1.1
  have hd1 := directional_contDiffOn hf (m := 1) le_rfl (1 : ℂ)
  have hdI := directional_contDiffOn hf (m := 1) le_rfl Complex.I
  rw [gradientEnergy, pairing_self _ hd1.continuousOn hy, pairing_self _ hdI.continuousOn hy,
    mul_add]
  simpa only [intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ (N + 1 : ℕ))] using
    (maass_horizontal_hasSum N f hy).add (maass_vertical_hasSum N f hy)

/-- The literal physical quarter-energy slice equals gradient energy minus quarter mass. -/
theorem quarterSlice_eq_gradient_mass (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)
    {y : ℝ} (hy : 0 < y) :
    ((N + 1 : ℕ) : ℝ)⁻¹ * quarterSlice N f y =
      gradientEnergy N f y - 1 / (4 * y ^ 2) * mass N f y := by
  have hs := (gradientEnergy_hasSum N f hy).sub ((mass_hasSum N f hy).mul_left (1 / (4 * y ^ 2)))
  apply (maass_quarter_hasSum N f hy).unique
  apply hs.congr_fun
  intro n
  unfold modalQuarter
  ring

/-- Exact quarter-energy flux balance at every positive source height. -/
theorem quarterSlice_eq_flux_deriv (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)
    {y : ℝ} (hy : 0 < y) :
    ((N + 1 : ℕ) : ℝ)⁻¹ * quarterSlice N f y =
      deriv (flux N f) y + (lam - 1 / 4) / y ^ 2 * mass N f y := by
  rw [quarterSlice_eq_gradient_mass N f hy, (flux_hasDerivAt N f hy).deriv]
  ring

/-- The defining uniform cusp filter forces actual squared slice mass to zero. -/
theorem mass_decay (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam) :
    Tendsto (mass N f) atTop (𝓝 0) := by
  have hc : IsZeroAtImInfty f.1.1 := by
    simpa only [map_one, one_smul] using f.2.2.2 (1 : SL2Z)
  rw [isZeroAtImInfty_iff] at hc
  refine Metric.tendsto_atTop.mpr ?_
  intro ε hε
  obtain ⟨A, hA⟩ := hc (Real.sqrt (ε / 2)) (Real.sqrt_pos.mpr (by positivity))
  refine ⟨max A 1, fun y hy => ?_⟩
  have hAy : A ≤ y := (le_max_left A 1).trans hy
  have hypos : 0 < y := lt_of_lt_of_le (by linarith : (0 : ℝ) < 1) ((le_max_right A 1).trans hy)
  have hb : ∀ x ∈ Ioc (0 : ℝ) (N + 1 : ℕ),
      ‖Complex.normSq ((f.1.1 ∘ ofComplex) (point x y))‖ ≤ ε / 2 := by
    intro x _
    have hp : 0 < (point x y).im := by simpa [point] using hypos
    have hh : ‖(f.1.1 ∘ ofComplex) (point x y)‖ ≤ Real.sqrt (ε / 2) := by
      simpa only [Function.comp_apply, ofComplex_apply_of_im_pos hp] using
        hA ⟨point x y, hp⟩ (by simpa [UpperHalfPlane.im, point] using hAy)
    rw [Real.norm_eq_abs, abs_of_nonneg (Complex.normSq_nonneg _), Complex.normSq_eq_norm_sq]
    nlinarith [Real.sq_sqrt (show 0 ≤ ε / 2 by positivity), norm_nonneg ((f.1.1 ∘ ofComplex) (point x y))]
  have hb' := norm_setIntegral_le_of_norm_le_const (μ := volume) measure_Ioc_lt_top hb
  have hw : 0 < ((N + 1 : ℕ) : ℝ) := by positivity
  rw [Real.volume_real_Ioc_of_le hw.le, sub_zero] at hb'
  have hmass : ‖mass N f y‖ ≤ ε / 2 := by
    rw [mass, pairing_self _ f.2.2.1.1.continuousOn hypos, norm_mul,
      Real.norm_eq_abs ((N + 1 : ℕ) : ℝ)⁻¹, abs_of_nonneg (inv_nonneg.mpr hw.le)]
    calc _ ≤ ((N + 1 : ℕ) : ℝ)⁻¹ * (ε / 2 * (N + 1 : ℕ)) :=
        mul_le_mul_of_nonneg_left hb' (by positivity)
      _ = ε / 2 := by field_simp
  simpa only [dist_zero_right] using hmass.trans_lt (by linarith : ε / 2 < ε)

open SelbergMaassFourier

/-- Zero constant term and the integer frequency gap bound actual sub-quarter slice energy. -/
theorem gradientEnergy_ge_first_frequency (N : ℕ) (lam : Ioo (0 : ℝ) (1 / 4))
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) (lam : ℝ))
    {y : ℝ} (hy : 0 < y) :
    (2 * Real.pi / (N + 1 : ℕ)) ^ 2 * mass N f y ≤ gradientEnergy N f y := by
  have hz : maassCoefficient N f 0 y = 0 := by
    rw [maassCoefficient_zero]
    have hp : 0 < (point 0 y).im := by simpa [point] using hy
    have h := SelbergEulerDecay.maassMean_subquarter_zero N lam f ⟨point 0 y, hp⟩
    have hm : maassMean N f y = 0 := by simpa [UpperHalfPlane.im, point] using h
    rw [hm, mul_zero]
  apply hasSum_le (g := fun n : ℤ => signedFrequency (N + 1 : ℕ) n ^ 2 *
      Complex.normSq (maassCoefficient N f n y) + Complex.normSq (deriv (maassCoefficient N f n) y))
    ?_ ((mass_hasSum N f hy).mul_left ((2 * Real.pi / (N + 1 : ℕ)) ^ 2)) (gradientEnergy_hasSum N f hy)
  intro n
  by_cases hn : n = 0
  · subst n
    simp only [hz, Complex.normSq_zero, mul_zero, zero_add]
    exact Complex.normSq_nonneg _
  · have hn2 : (1 : ℤ) ≤ n ^ 2 := Int.add_one_le_iff.mpr (sq_pos_of_ne_zero hn)
    have hnR : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by exact_mod_cast hn2
    have he : signedFrequency (N + 1 : ℕ) n ^ 2 =
        (2 * Real.pi / (N + 1 : ℕ)) ^ 2 * (n : ℝ) ^ 2 := by
      unfold signedFrequency
      ring
    rw [he]
    have hle := mul_le_mul_of_nonneg_left hnR (sq_nonneg (2 * Real.pi / (N + 1 : ℕ)))
    have hle' := mul_le_mul_of_nonneg_right hle (Complex.normSq_nonneg (maassCoefficient N f n y))
    nlinarith [Complex.normSq_nonneg (deriv (maassCoefficient N f n) y)]

end
end GaloisForLFunctions.RHTower.SelbergMaassFlux
