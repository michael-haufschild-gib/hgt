import GaloisForLFunctions.RHTower.XiShiftedHardEdgePolynomialGaussianExponentialSchwartz
import GaloisForLFunctions.RHTower.XiShiftedHardEdgeComplexPaleyWienerDivisorLimit
import GaloisForLFunctions.RHTower.Deninger.DeningerPaleyWiener

/-!
# Compact-transfer theorem for the Route-U polynomial--Gaussian carrier

This module closes complex HEPW.16. Expanding compact cutoffs converge at every complex frequency
for exponential-Schwartz sources. Uniform derivative control over all cutoff indices supplies a
reciprocal-square majorant on the complete multiplicity-labelled Xi divisor, so dominated
convergence passes through the infinite divisor. For the exact Route-U physical carrier, the uncut
entire transform is identified with the unsquared polynomial--Gaussian profile and the cutoff
divisor traces converge to the existing polynomial--Gaussian Xi heat trace.
-/

open scoped FourierTransform SchwartzMap BigOperators
open Complex MeasureTheory Filter

noncomputable section

namespace RHTower

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry


/-- Uncut positive-sign Fourier--Laplace extension. -/
def routeUEntirePositiveFourierExtension (f : SchwartzMap ℝ ℂ) (z : ℂ) : ℂ :=
  deningerFourierLaplace f (-z)

theorem routeUEntirePositiveFourierExtension_eq_integral (f : SchwartzMap ℝ ℂ) (z : ℂ) :
    routeUEntirePositiveFourierExtension f z =
      ∫ t : ℝ, Complex.exp (Complex.I * z * (t : ℂ)) * f t := by
  rw [routeUEntirePositiveFourierExtension, deningerFourierLaplace]
  apply integral_congr_ae
  filter_upwards with t
  rw [deningerLaplaceKernel]
  have hexp : -(Complex.I * -z * (t : ℂ)) =
      Complex.I * z * (t : ℂ) := by ring
  rw [hexp]
  ring

theorem tendsto_routeUComplexPositiveFourierExtension_cutoff (f : SchwartzMap ℝ ℂ)
    (hf : f ∈ DeningerExpSchwartz) (z : ℂ) :
    Tendsto (fun n : ℕ => routeUComplexPositiveFourierExtension n f z)
      atTop (nhds (routeUEntirePositiveFourierExtension f z)) := by
  have hmeas : ∀ n, AEStronglyMeasurable (fun t : ℝ =>
      Complex.exp (Complex.I * z * (t : ℂ)) *
        SchwartzMap.compactSupportApproximation n f t) := by
    intro n
    exact (by fun_prop : Continuous fun t : ℝ =>
      Complex.exp (Complex.I * z * (t : ℂ)) *
        SchwartzMap.compactSupportApproximation n f t).aestronglyMeasurable
  have hdomInt : Integrable (fun t : ℝ =>
      ‖(f : ℝ → ℂ) t * deningerLaplaceKernel (-z) t‖) :=
    (deningerFourierLaplace_integrable hf (-z) 0).norm.congr
      (Filter.Eventually.of_forall fun t => by simp)
  have hbound : ∀ n, ∀ᵐ t : ℝ ∂volume,
      ‖Complex.exp (Complex.I * z * (t : ℂ)) *
          SchwartzMap.compactSupportApproximation n f t‖ ≤
        ‖(f : ℝ → ℂ) t * deningerLaplaceKernel (-z) t‖ := by
    intro n
    filter_upwards with t
    rw [SchwartzMap.compactSupportApproximation_apply, norm_mul, norm_mul,
      norm_mul]
    have hcut := SchwartzMap.scaledUnitCutoff_norm_le_one n t
    have hexp : Complex.exp (Complex.I * z * (t : ℂ)) =
        deningerLaplaceKernel (-z) t := by
      rw [deningerLaplaceKernel]
      congr 1
      ring
    rw [hexp]
    calc
      ‖deningerLaplaceKernel (-z) t‖ *
          (‖SchwartzMap.scaledUnitCutoff n t‖ * ‖f t‖) ≤
        ‖deningerLaplaceKernel (-z) t‖ * (1 * ‖f t‖) := by gcongr
      _ = ‖f t‖ * ‖deningerLaplaceKernel (-z) t‖ := by ring
  have hlim : ∀ᵐ t : ℝ ∂volume,
      Tendsto (fun n : ℕ =>
        Complex.exp (Complex.I * z * (t : ℂ)) *
          SchwartzMap.compactSupportApproximation n f t) atTop
        (nhds (Complex.exp (Complex.I * z * (t : ℂ)) * f t)) := by
    filter_upwards with t
    obtain ⟨N, hN⟩ := exists_nat_ge |t|
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop N] with n hn
    rw [SchwartzMap.compactSupportApproximation_apply,
      SchwartzMap.scaledUnitCutoff_apply_of_abs_le]
    · simp
    · have hcast : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      exact hN.trans (by linarith)
  have hdct := tendsto_integral_of_dominated_convergence
    (fun t : ℝ => ‖(f : ℝ → ℂ) t * deningerLaplaceKernel (-z) t‖)
    hmeas hdomInt hbound hlim
  simpa only [routeUComplexPositiveFourierExtension_eq_integral,
    routeUEntirePositiveFourierExtension_eq_integral] using hdct

theorem routeUEntirePositiveFourierExtension_ofReal (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    routeUEntirePositiveFourierExtension f (x : ℂ) = routeUPositiveFourierExtension f x := by
  rw [routeUEntirePositiveFourierExtension_eq_integral, routeUPositiveFourierExtension,
    SchwartzMap.fourier_coe, Real.fourier_eq]
  apply integral_congr_ae
  filter_upwards with t
  simp only [Real.inner_apply, Circle.smul_def, Real.fourierChar_apply,
    smul_eq_mul]
  congr 2
  push_cast
  field_simp [Real.pi_ne_zero]

theorem routeUEntirePositiveFourierExtension_differentiable (f : SchwartzMap ℝ ℂ)
    (hf : f ∈ DeningerExpSchwartz) :
    Differentiable ℂ (routeUEntirePositiveFourierExtension f) := by
  exact (deningerFourierLaplace_differentiable hf).comp differentiable_neg

theorem routeUXiPolynomialGaussianProfile_differentiable (P : Polynomial ℝ)
    (t : {τ : ℝ // 0 < τ}) :
    Differentiable ℂ (routeUXiPolynomialGaussianProfile P t) := by
  unfold routeUXiPolynomialGaussianProfile evalRealPolynomial
  fun_prop

theorem routeUEntirePositiveFourierExtension_heatPhysical_eq
    (P : Polynomial ℝ) (t : {τ : ℝ // 0 < τ}) (z : ℂ) :
    routeUEntirePositiveFourierExtension (routeUXiHeatPhysicalComplex P t) z =
      routeUXiPolynomialGaussianProfile P t z := by
  have hdiff : Differentiable ℂ (fun w : ℂ =>
      routeUEntirePositiveFourierExtension (routeUXiHeatPhysicalComplex P t) w -
        routeUXiPolynomialGaussianProfile P t w) :=
    (routeUEntirePositiveFourierExtension_differentiable _
      (routeUXiHeatPhysicalComplex_mem_deningerExpSchwartz P t)).sub
        (routeUXiPolynomialGaussianProfile_differentiable P t)
  have hzero : ∀ x : ℝ, |x - 0| < 1 →
      routeUEntirePositiveFourierExtension (routeUXiHeatPhysicalComplex P t) (x : ℂ) -
        routeUXiPolynomialGaussianProfile P t (x : ℂ) = 0 := by
    intro x hx
    rw [routeUEntirePositiveFourierExtension_ofReal,
      ← routeURealEvenAmplitude_heatPhysical_eq,
      routeUPositiveFourierExtension_heatPhysical_eq]
    simp
  exact sub_eq_zero.mp
    (entire_eq_zero_of_vanishing_on_real_interval hdiff one_pos hzero z)

theorem tendsto_routeUXiHeatPhysicalComplex_cutoff
    (P : Polynomial ℝ) (t : {τ : ℝ // 0 < τ}) (z : ℂ) :
    Tendsto (fun n : ℕ => routeUComplexPositiveFourierExtension n
        (routeUXiHeatPhysicalComplex P t) z)
      atTop (nhds (routeUXiPolynomialGaussianProfile P t z)) := by
  simpa only [routeUEntirePositiveFourierExtension_heatPhysical_eq] using
    tendsto_routeUComplexPositiveFourierExtension_cutoff (routeUXiHeatPhysicalComplex P t)
      (routeUXiHeatPhysicalComplex_mem_deningerExpSchwartz P t) z

/-- Uniform derivative cost of the expanding cutoff. -/
def routeUScaledCutoffDerivUniformBound (i : ℕ) : ℝ :=
  if i = 0 then 1 else
    SchwartzMap.seminorm ℂ 0 i (SchwartzMap.compactIntervalCutoff 0)

theorem routeUScaledCutoffDerivUniformBound_nonneg (i : ℕ) :
    0 ≤ routeUScaledCutoffDerivUniformBound i := by
  rw [routeUScaledCutoffDerivUniformBound]
  split_ifs
  · norm_num
  · exact apply_nonneg _ _

theorem norm_iteratedDeriv_scaledUnitCutoff_le_uniformBound
    (n i : ℕ) (x : ℝ) :
    ‖iteratedDeriv i (SchwartzMap.scaledUnitCutoff n) x‖ ≤
      routeUScaledCutoffDerivUniformBound i := by
  by_cases hi : i = 0
  · subst i
    simpa [routeUScaledCutoffDerivUniformBound] using
      SchwartzMap.scaledUnitCutoff_norm_le_one n x
  · rw [routeUScaledCutoffDerivUniformBound, if_neg hi,
      SchwartzMap.iteratedDeriv_scaledUnitCutoff, norm_smul,
      Real.norm_eq_abs]
    have hsnonneg : 0 ≤ ((n : ℝ) + 1)⁻¹ := by positivity
    have hsle : ((n : ℝ) + 1)⁻¹ ≤ 1 := by
      have hr : 1 ≤ (n : ℝ) + 1 := by
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
      exact (inv_le_one₀ (by positivity)).mpr hr
    have hpow : |((n : ℝ) + 1)⁻¹ ^ i| ≤ 1 := by
      rw [abs_of_nonneg (pow_nonneg hsnonneg i)]
      exact pow_le_one₀ hsnonneg hsle
    have hbase :
        ‖iteratedDeriv i (SchwartzMap.compactIntervalCutoff 0)
          (((n : ℝ) + 1)⁻¹ * x)‖ ≤
        SchwartzMap.seminorm ℂ 0 i (SchwartzMap.compactIntervalCutoff 0) := by
      simpa only [pow_zero, one_mul] using
        SchwartzMap.le_seminorm' ℂ 0 i (SchwartzMap.compactIntervalCutoff 0)
          (((n : ℝ) + 1)⁻¹ * x)
    calc
      |((n : ℝ) + 1)⁻¹ ^ i| *
          ‖iteratedDeriv i (SchwartzMap.compactIntervalCutoff 0)
            (((n : ℝ) + 1)⁻¹ * x)‖ ≤
        1 * SchwartzMap.seminorm ℂ 0 i
          (SchwartzMap.compactIntervalCutoff 0) := by
          exact mul_le_mul hpow hbase (norm_nonneg _) zero_le_one
      _ = _ := one_mul _

theorem exists_uniform_compactSupportApproximation_deriv_bound
    (f : SchwartzMap ℝ ℂ) (hf : f ∈ DeningerExpSchwartz) (r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (x : ℝ),
      ‖iteratedDeriv r (SchwartzMap.compactSupportApproximation n f) x‖ ≤
        C * Real.exp (-(2 * |x|)) := by
  let C : ℕ → ℝ := fun i => Classical.choose
    (deningerExpSchwartz_iteratedDeriv_norm_le hf 2 (r - i))
  have hCnn : ∀ i, 0 ≤ C i := fun i =>
    (Classical.choose_spec
      (deningerExpSchwartz_iteratedDeriv_norm_le hf 2 (r - i))).1
  have hC : ∀ i x,
      ‖iteratedDeriv (r - i) (f : ℝ → ℂ) x‖ ≤
        C i * Real.exp (-(2 * |x|)) := fun i =>
    (Classical.choose_spec
      (deningerExpSchwartz_iteratedDeriv_norm_le hf 2 (r - i))).2
  let K : ℝ := ∑ i ∈ Finset.range (r + 1),
    (r.choose i : ℝ) * routeUScaledCutoffDerivUniformBound i * C i
  have hK : 0 ≤ K := by
    dsimp only [K]
    exact Finset.sum_nonneg fun i hi =>
      mul_nonneg
        (mul_nonneg (Nat.cast_nonneg _) (routeUScaledCutoffDerivUniformBound_nonneg i))
        (hCnn i)
  refine ⟨K, hK, fun n x => ?_⟩
  have hfun :
      (fun y : ℝ => SchwartzMap.compactSupportApproximation n f y) =
        ((SchwartzMap.scaledUnitCutoff n : ℝ → ℂ) * (f : ℝ → ℂ)) := by
    funext y
    rw [SchwartzMap.compactSupportApproximation_apply]
    rfl
  change ‖iteratedDeriv r
    (fun y : ℝ => SchwartzMap.compactSupportApproximation n f y) x‖ ≤ _
  rw [hfun, iteratedDeriv_mul
    (((SchwartzMap.scaledUnitCutoff n).smooth r).contDiffAt)
    ((f.smooth r).contDiffAt)]
  calc
    ‖∑ i ∈ Finset.range (r + 1),
        (r.choose i : ℂ) *
          iteratedDeriv i (SchwartzMap.scaledUnitCutoff n) x *
          iteratedDeriv (r - i) (f : ℝ → ℂ) x‖ ≤
      ∑ i ∈ Finset.range (r + 1),
        ‖(r.choose i : ℂ) *
          iteratedDeriv i (SchwartzMap.scaledUnitCutoff n) x *
          iteratedDeriv (r - i) (f : ℝ → ℂ) x‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range (r + 1),
        ((r.choose i : ℝ) * routeUScaledCutoffDerivUniformBound i * C i) *
          Real.exp (-(2 * |x|)) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul, norm_mul, Complex.norm_natCast]
      calc
        (r.choose i : ℝ) *
            ‖iteratedDeriv i (SchwartzMap.scaledUnitCutoff n) x‖ *
            ‖iteratedDeriv (r - i) (f : ℝ → ℂ) x‖ ≤
          (r.choose i : ℝ) * routeUScaledCutoffDerivUniformBound i *
            ‖iteratedDeriv (r - i) (f : ℝ → ℂ) x‖ := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left
              (norm_iteratedDeriv_scaledUnitCutoff_le_uniformBound n i x)
              (Nat.cast_nonneg _))
            (norm_nonneg _)
        _ ≤ (r.choose i : ℝ) * routeUScaledCutoffDerivUniformBound i *
            (C i * Real.exp (-(2 * |x|))) := by
          exact mul_le_mul_of_nonneg_left (hC i x)
            (mul_nonneg (Nat.cast_nonneg _)
              (routeUScaledCutoffDerivUniformBound_nonneg i))
        _ = ((r.choose i : ℝ) * routeUScaledCutoffDerivUniformBound i * C i) *
            Real.exp (-(2 * |x|)) := by ring
    _ = K * Real.exp (-(2 * |x|)) := by
      rw [Finset.sum_mul]

theorem exists_uniform_routeUComplexTiltDerivMajorant_bound
    (f : SchwartzMap ℝ ℂ) (hf : f ∈ DeningerExpSchwartz) (q : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (x : ℝ),
      routeUComplexTiltDerivMajorant n f q x ≤
        C * Real.exp (-|x|) := by
  let D : ℕ → ℝ := fun i => Classical.choose
    (exists_uniform_compactSupportApproximation_deriv_bound
      f hf (q - i))
  have hDnn : ∀ i, 0 ≤ D i := fun i =>
    (Classical.choose_spec
      (exists_uniform_compactSupportApproximation_deriv_bound
        f hf (q - i))).1
  have hD : ∀ i n x,
      ‖iteratedDeriv (q - i)
        (SchwartzMap.compactSupportApproximation n f) x‖ ≤
          D i * Real.exp (-(2 * |x|)) := fun i =>
    (Classical.choose_spec
      (exists_uniform_compactSupportApproximation_deriv_bound
        f hf (q - i))).2
  let K : ℝ := ∑ i ∈ Finset.range (q + 1), (q.choose i : ℝ) * D i
  have hK : 0 ≤ K := by
    dsimp only [K]
    exact Finset.sum_nonneg fun i hi =>
      mul_nonneg (Nat.cast_nonneg _) (hDnn i)
  refine ⟨K, hK, fun n x => ?_⟩
  rw [routeUComplexTiltDerivMajorant]
  calc
    Real.exp |x| *
        ∑ i ∈ Finset.range (q + 1),
          (q.choose i : ℝ) *
            ‖iteratedFDeriv ℝ (q - i)
              (SchwartzMap.compactSupportApproximation n f) x‖ ≤
      Real.exp |x| *
        ∑ i ∈ Finset.range (q + 1),
          (q.choose i : ℝ) *
            (D i * Real.exp (-(2 * |x|))) := by
      gcongr with i hi
      rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
      exact hD i n x
    _ = Real.exp |x| * (K * Real.exp (-(2 * |x|))) := by
      congr 1
      calc
        ∑ i ∈ Finset.range (q + 1),
            (q.choose i : ℝ) * (D i * Real.exp (-(2 * |x|))) =
          ∑ i ∈ Finset.range (q + 1),
            ((q.choose i : ℝ) * D i) * Real.exp (-(2 * |x|)) := by
              apply Finset.sum_congr rfl
              intro i hi
              ring
        _ = K * Real.exp (-(2 * |x|)) := by
          dsimp only [K]
          rw [Finset.sum_mul]
    _ = K * Real.exp (-|x|) := by
      rw [show Real.exp |x| * (K * Real.exp (-(2 * |x|))) =
          K * (Real.exp |x| * Real.exp (-(2 * |x|))) by ring,
        ← Real.exp_add]
      congr 2
      ring

theorem exists_uniform_routeUComplexTiltDerivL1Bound
    (f : SchwartzMap ℝ ℂ) (hf : f ∈ DeningerExpSchwartz) (q : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
      routeUComplexTiltDerivL1Bound n f q ≤ C := by
  obtain ⟨K, hK, hpoint⟩ :=
    exists_uniform_routeUComplexTiltDerivMajorant_bound f hf q
  let E : ℝ := ∫ x : ℝ, Real.exp (-|x|)
  have hE : 0 ≤ E := integral_nonneg fun x => (Real.exp_pos _).le
  refine ⟨K * E, mul_nonneg hK hE, fun n => ?_⟩
  rw [routeUComplexTiltDerivL1Bound]
  have hmajorInt : Integrable (fun x : ℝ => K * Real.exp (-|x|)) := by
    simpa only [one_mul] using (deningerExpAbs_integrable one_pos).const_mul K
  calc
    ∫ x : ℝ, routeUComplexTiltDerivMajorant n f q x ≤
        ∫ x : ℝ, K * Real.exp (-|x|) := by
      apply integral_mono (integrable_routeUComplexTiltDerivMajorant n f q)
        hmajorInt
      exact hpoint n
    _ = K * E := by
      rw [integral_const_mul]

theorem exists_uniform_routeUComplexTiltUniformDecay_one
    (f : SchwartzMap ℝ ℂ) (hf : f ∈ DeningerExpSchwartz) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
      routeUComplexTiltUniformDecay n f 1 ≤ C := by
  obtain ⟨C0, hC0, h0⟩ :=
    exists_uniform_routeUComplexTiltDerivL1Bound f hf 0
  obtain ⟨C2, hC2, h2⟩ :=
    exists_uniform_routeUComplexTiltDerivL1Bound f hf 2
  let C : ℝ := 2 * (C0 + ((2 * Real.pi) ^ (2 : ℕ))⁻¹ * C2)
  have hC : 0 ≤ C := by
    dsimp only [C]
    positivity
  refine ⟨C, hC, fun n => ?_⟩
  rw [routeUComplexTiltUniformDecay]
  norm_num
  dsimp only [C]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact add_le_add (h0 n)
    (mul_le_mul_of_nonneg_left (h2 n) (by positivity))

theorem exists_uniform_routeUXiComplexCutoffDivisorMajorant
    (f : SchwartzMap ℝ ℂ) (hf : f ∈ DeningerExpSchwartz) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (q : XiZeroCopy),
      ‖routeUComplexPositiveFourierExtension n f (xiSpectralPoint q) ^ (2 : ℕ)‖ ≤
        C * ‖xiZeroCopyReciprocalSquare q‖ := by
  obtain ⟨D, hD, hdecayD⟩ :=
    exists_uniform_routeUComplexTiltUniformDecay_one f hf
  let A : ℝ := D * (2 * Real.pi) ^ (2 : ℕ)
  have hA : 0 ≤ A := mul_nonneg hD (sq_nonneg _)
  refine ⟨A ^ (2 : ℕ), sq_nonneg A, fun n q => ?_⟩
  let h : ℝ := |(xiSpectralPoint q).re|
  let x : ℝ := -(xiSpectralPoint q).re / (2 * Real.pi)
  have hreSq : 2 < (xiSpectralPoint q).re ^ (2 : ℕ) := by
    have hz := xiZeroCopy_two_lt_im_sq q
    simpa [xiSpectralPoint, Complex.mul_re] using hz
  have hh : 0 < h := by
    dsimp only [h]
    rw [abs_pos]
    nlinarith
  have hstrip : |(xiSpectralPoint q).im| ≤ 1 := by
    have hsupport := xi_divisor_support_re_mem_open_unit q.1
    have him : (xiSpectralPoint q).im = 1 / 2 - ((q.1 : ℂ)).re := by
      rw [xiSpectralPoint]
      simp [Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.neg_im,
        Complex.I_re, Complex.I_im]
    rw [him, abs_le]
    constructor <;> linarith
  have hdecay :
      kgFreq x ^ (2 : ℕ) *
          ‖routeUComplexPositiveFourierExtension n f (xiSpectralPoint q)‖ ≤ D := by
    exact (routeUComplexPositiveFourierExtension_uniform_decay n f hstrip 1).trans
      (hdecayD n)
  have hxabs : |x| = h / (2 * Real.pi) := by
    dsimp only [x, h]
    rw [abs_div, abs_neg, abs_of_pos (mul_pos two_pos Real.pi_pos)]
  have hlower : h / (2 * Real.pi) ≤ kgFreq x := by
    rw [← hxabs]
    exact abs_le_kgFreq_real x
  have hnorm :
      ‖routeUComplexPositiveFourierExtension n f (xiSpectralPoint q)‖ ≤
        A / h ^ (2 : ℕ) := by
    have hfirst :
        ‖routeUComplexPositiveFourierExtension n f (xiSpectralPoint q)‖ ≤
          D / kgFreq x ^ (2 : ℕ) := by
      apply (le_div_iff₀ (pow_pos (kgFreq_pos x) 2)).2
      simpa only [mul_comm] using hdecay
    calc
      ‖routeUComplexPositiveFourierExtension n f (xiSpectralPoint q)‖ ≤
          D / kgFreq x ^ (2 : ℕ) := hfirst
      _ ≤ D / (h / (2 * Real.pi)) ^ (2 : ℕ) := by
        exact div_le_div_of_nonneg_left hD (pow_pos (by positivity) 2)
          (pow_le_pow_left₀ (by positivity) hlower 2)
      _ = A / h ^ (2 : ℕ) := by
        dsimp only [A]
        field_simp [hh.ne', Real.pi_ne_zero]
  have hnormPos : 0 < ‖xiSpectralPoint q‖ ^ (2 : ℕ) := by
    have hz : xiSpectralPoint q ≠ 0 := by
      intro hz
      rw [hz] at hreSq
      norm_num at hreSq
    exact sq_pos_of_pos (norm_pos_iff.mpr hz)
  have hnormSq : ‖xiSpectralPoint q‖ ^ (2 : ℕ) ≤ h ^ (4 : ℕ) := by
    simpa only [h] using norm_xiSpectralPoint_sq_le_abs_re_pow_four q
  have hinv : 1 / h ^ (4 : ℕ) ≤ ‖xiZeroCopyReciprocalSquare q‖ := by
    rw [norm_xiZeroCopyReciprocalSquare_eq_inv_norm_sq]
    exact (div_le_div_iff₀ (pow_pos hh 4) hnormPos).2 (by simpa using hnormSq)
  rw [norm_pow]
  calc
    ‖routeUComplexPositiveFourierExtension n f (xiSpectralPoint q)‖ ^ (2 : ℕ) ≤
        (A / h ^ (2 : ℕ)) ^ (2 : ℕ) := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    _ = A ^ (2 : ℕ) * (1 / h ^ (4 : ℕ)) := by ring
    _ ≤ A ^ (2 : ℕ) * ‖xiZeroCopyReciprocalSquare q‖ := by gcongr

theorem tendsto_routeUXiComplexCutoffDivisorTrace
    (f : SchwartzMap ℝ ℂ) (hf : f ∈ DeningerExpSchwartz) :
    Tendsto (fun n : ℕ => ∑' q : XiZeroCopy,
        routeUComplexPositiveFourierExtension n f (xiSpectralPoint q) ^ (2 : ℕ))
      atTop
      (nhds (∑' q : XiZeroCopy,
        routeUEntirePositiveFourierExtension f (xiSpectralPoint q) ^ (2 : ℕ))) := by
  obtain ⟨C, hC, hmajor⟩ :=
    exists_uniform_routeUXiComplexCutoffDivisorMajorant f hf
  apply tendsto_tsum_of_dominated_convergence
    ((summable_xiZeroCopyReciprocalSquare_pow 0).norm.mul_left C)
  · intro q
    exact (tendsto_routeUComplexPositiveFourierExtension_cutoff f hf (xiSpectralPoint q)).pow 2
  · exact Filter.Eventually.of_forall fun n q => by
      simpa using hmajor n q

/-- Complete HEPW.16 cutoff passage for the exact polynomial--Gaussian Route-U carrier. -/
theorem tendsto_routeUXiPolynomialGaussianCutoffDivisorTrace
    (P : Polynomial ℝ) (t : {τ : ℝ // 0 < τ}) :
    Tendsto (fun n : ℕ => ∑' q : XiZeroCopy,
        routeUComplexPositiveFourierExtension n
          (routeUXiHeatPhysicalComplex P t) (xiSpectralPoint q) ^ (2 : ℕ))
      atTop (nhds (xiPolynomialGaussianHeatTrace P (t : ℝ))) := by
  have hlim := tendsto_routeUXiComplexCutoffDivisorTrace
    (routeUXiHeatPhysicalComplex P t)
    (routeUXiHeatPhysicalComplex_mem_deningerExpSchwartz P t)
  have heq :
      (∑' q : XiZeroCopy,
        routeUEntirePositiveFourierExtension (routeUXiHeatPhysicalComplex P t)
          (xiSpectralPoint q) ^ (2 : ℕ)) =
        xiPolynomialGaussianHeatTrace P (t : ℝ) := by
    rw [xiPolynomialGaussianHeatTrace]
    apply tsum_congr
    intro q
    rw [routeUEntirePositiveFourierExtension_heatPhysical_eq,
      routeUXiPolynomialGaussianProfile_sq_xiSpectralPoint]
  rwa [heq] at hlim

end RHTower

