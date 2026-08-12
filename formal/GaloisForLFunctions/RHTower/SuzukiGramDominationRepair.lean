import GaloisForLFunctions.HTGeometry.WeightedHolder
import GaloisForLFunctions.RHTower.SuzukiOrientedPrimitive
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Repairing the form-domination step in Suzuki's small-aperture argument

The proof of Suzuki (2022), Theorems 4.2--4.3, twice passes from a pointwise inequality between
kernel values to an inequality between the corresponding quadratic forms.  That implication is not
valid for general kernels.  The kernels in the proof have additional Gram structure, however.

This file formalizes the two form-level estimates which that structure supplies:

* multiplying the oriented primitive by the contour-shift weight `exp (-c x)` costs at most
  `exp (2 |c| a)` in squared `L²` energy on `[-a,a]`;
* any Fourier-like transform bounded pointwise by the `L¹` norm of a source supported on
  `[-a,a]` has low-frequency energy at most `4 a T` times its source `L²` energy on `[-T,T]`.

Both statements are inequalities of quadratic energies, so they remain valid for arbitrary complex
sources.  No pointwise ordering of kernels is used.
-/

open MeasureTheory Set
open GaloisForLFunctions.HTGeometry
open scoped FourierTransform

noncomputable section

namespace RHTower

/-! ## Why pointwise kernel ordering is insufficient -/

/-- A positive definite two-point kernel which is entrywise below `suzukiPointwiseMajorant`. -/
def suzukiPointwiseMinorant : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(1 : ℝ), 9 / 10; 9 / 10, 1]

/-- A positive semidefinite rank-one two-point kernel. -/
def suzukiPointwiseMajorant : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(1 : ℝ), 1; 1, 1]

theorem suzukiPointwiseMinorant_posSemidef : suzukiPointwiseMinorant.PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [suzukiPointwiseMinorant]
  · intro x
    norm_num [suzukiPointwiseMinorant, dotProduct, Matrix.mulVec, Fin.sum_univ_two,
      star_trivial]
    nlinarith [sq_nonneg (x 0 - x 1), sq_nonneg (x 0 + x 1)]

theorem suzukiPointwiseMajorant_posSemidef : suzukiPointwiseMajorant.PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [suzukiPointwiseMajorant]
  · intro x
    norm_num [suzukiPointwiseMajorant, dotProduct, Matrix.mulVec, Fin.sum_univ_two,
      star_trivial]
    nlinarith [sq_nonneg (x 0 + x 1)]

theorem suzukiPointwiseMinorant_entrywise_le_majorant :
    ∀ i j, suzukiPointwiseMinorant i j ≤ suzukiPointwiseMajorant i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [suzukiPointwiseMinorant, suzukiPointwiseMajorant]

/-- **Closed counterexample to the inference used in the printed proof.**  Two kernels can both be
positive semidefinite and ordered at every pair of points, while their quadratic forms have the
opposite order on a complex (already real) source. -/
theorem exists_posSemidef_entrywise_le_not_quadraticForm_le :
    ∃ A B : Matrix (Fin 2) (Fin 2) ℝ,
      A.PosSemidef ∧ B.PosSemidef ∧ (∀ i j, A i j ≤ B i j) ∧
      ∃ x : Fin 2 → ℝ,
        dotProduct (star x) (B.mulVec x) < dotProduct (star x) (A.mulVec x) := by
  refine ⟨suzukiPointwiseMinorant, suzukiPointwiseMajorant,
    suzukiPointwiseMinorant_posSemidef, suzukiPointwiseMajorant_posSemidef,
    suzukiPointwiseMinorant_entrywise_le_majorant, fun i => if i = 0 then 1 else -1, ?_⟩
  norm_num [suzukiPointwiseMinorant, suzukiPointwiseMajorant, dotProduct, Matrix.mulVec,
    Fin.sum_univ_two, star_trivial]

/-- Multiplication by a uniformly bounded complex weight is bounded on squared `L²` energy. -/
theorem integral_norm_sq_mul_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {m f : α → ℂ} {M : ℝ} (hM : 0 ≤ M)
    (hm : AEStronglyMeasurable m μ) (hf : AEStronglyMeasurable f μ)
    (hbound : ∀ᵐ x ∂μ, ‖m x‖ ≤ M)
    (hf2 : Integrable (fun x => ‖f x‖ ^ 2) μ) :
    (∫ x, ‖m x * f x‖ ^ 2 ∂μ) ≤ M ^ 2 * ∫ x, ‖f x‖ ^ 2 ∂μ := by
  have hmeas : AEStronglyMeasurable (fun x => ‖m x * f x‖ ^ 2) μ :=
    ((hm.mul hf).norm.pow 2)
  have hpoint : ∀ᵐ x ∂μ, ‖m x * f x‖ ^ 2 ≤ M ^ 2 * ‖f x‖ ^ 2 := by
    filter_upwards [hbound] with x hx
    rw [norm_mul, mul_pow]
    exact mul_le_mul_of_nonneg_right ((sq_le_sq₀ (norm_nonneg _) hM).mpr hx)
      (sq_nonneg ‖f x‖)
  have hright : Integrable (fun x => M ^ 2 * ‖f x‖ ^ 2) μ := hf2.const_mul _
  have hleft : Integrable (fun x => ‖m x * f x‖ ^ 2) μ := by
    refine hright.mono' hmeas ?_
    filter_upwards [hpoint] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hx
  calc
    (∫ x, ‖m x * f x‖ ^ 2 ∂μ) ≤ ∫ x, M ^ 2 * ‖f x‖ ^ 2 ∂μ :=
      integral_mono_ae hleft hright hpoint
    _ = M ^ 2 * ∫ x, ‖f x‖ ^ 2 ∂μ := by rw [integral_const_mul]

/-- **Contour-shift Gram domination.**  On `[-a,a]`, multiplication by `exp (-c x)` costs at most
`exp (2 |c| a)` in squared energy. -/
theorem integral_Icc_norm_sq_exp_mul_le {a c : ℝ} (_ha : 0 ≤ a) {f : ℝ → ℂ}
    (hf : AEStronglyMeasurable f (volume.restrict (Icc (-a) a)))
    (hf2 : Integrable (fun x => ‖f x‖ ^ 2) (volume.restrict (Icc (-a) a))) :
    (∫ x in Icc (-a) a, ‖((Real.exp (-c * x) : ℝ) : ℂ) * f x‖ ^ 2)
      ≤ Real.exp (2 * |c| * a) * ∫ x in Icc (-a) a, ‖f x‖ ^ 2 := by
  let m : ℝ → ℂ := fun x => ((Real.exp (-c * x) : ℝ) : ℂ)
  let M : ℝ := Real.exp (|c| * a)
  have hM : 0 ≤ M := (Real.exp_pos _).le
  have hm : AEStronglyMeasurable m (volume.restrict (Icc (-a) a)) := by
    have hcont : Continuous fun x : ℝ => ((Real.exp (-c * x) : ℝ) : ℂ) := by fun_prop
    simpa only [m] using hcont.aestronglyMeasurable.restrict
  have hbound : ∀ᵐ x ∂(volume.restrict (Icc (-a) a)), ‖m x‖ ≤ M := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    have hxa : |x| ≤ a := by
      rw [abs_le]
      exact hx
    have hcx : -c * x ≤ |c| * a := by
      calc
        -c * x ≤ |-c * x| := le_abs_self _
        _ = |c| * |x| := by rw [abs_mul, abs_neg]
        _ ≤ |c| * a := mul_le_mul_of_nonneg_left hxa (abs_nonneg c)
    simpa only [m, M, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)] using Real.exp_le_exp.mpr hcx
  have h := integral_norm_sq_mul_le hM hm hf hbound hf2
  have hM2 : M ^ 2 = Real.exp (2 * |c| * a) := by
    dsimp only [M]
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  simpa only [m, hM2] using h

/-- Cauchy--Schwarz on `[-a,a]`, in the measurable form needed for an oriented primitive. -/
theorem integral_Icc_norm_sq_l1_bound {a : ℝ} (ha : 0 ≤ a) {f : ℝ → ℂ}
    (hf : AEStronglyMeasurable f (volume.restrict (Icc (-a) a)))
    (hf2 : Integrable (fun x => ‖f x‖ ^ 2) (volume.restrict (Icc (-a) a))) :
    (∫ x in Icc (-a) a, ‖f x‖) ^ 2
      ≤ (2 * a) * ∫ x in Icc (-a) a, ‖f x‖ ^ 2 := by
  have hvol : volume (Icc (-a) a) ≠ ⊤ := by
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  have hone : Integrable (fun _ : ℝ => ‖(1 : ℂ)‖ ^ 2)
      (volume.restrict (Icc (-a) a)) :=
    MeasureTheory.integrableOn_const hvol (by simp)
  have hcs := integral_mul_le_sqrt_mul_sqrt_measure
    (μ := volume.restrict (Icc (-a) a)) (g₁ := f) (g₂ := fun _ => (1 : ℂ))
    hf aestronglyMeasurable_const hf2 hone
  simp only [norm_one, mul_one, one_pow] at hcs
  have hlen : (∫ _ : ℝ in Icc (-a) a, (1 : ℝ)) = 2 * a := by
    rw [MeasureTheory.setIntegral_const, Real.volume_real_Icc, smul_eq_mul, mul_one,
      max_eq_left (by linarith)]
    ring
  rw [hlen] at hcs
  have henergy : 0 ≤ ∫ x in Icc (-a) a, ‖f x‖ ^ 2 :=
    integral_nonneg fun _ => sq_nonneg _
  have hlen0 : 0 ≤ 2 * a := by linarith
  have hsquare : (∫ x in Icc (-a) a, ‖f x‖) ^ 2 ≤
      (Real.sqrt (∫ x in Icc (-a) a, ‖f x‖ ^ 2) * Real.sqrt (2 * a)) ^ 2 := by
    exact (sq_le_sq₀ (integral_nonneg fun _ => norm_nonneg _)
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mpr hcs
  rw [mul_pow, Real.sq_sqrt henergy, Real.sq_sqrt hlen0] at hsquare
  nlinarith

/-- **Low-frequency Gram loss.**  If `F` is pointwise bounded by the `L¹` norm of a source on
`[-a,a]`, then its energy on `[-T,T]` is at most `4 a T` times source energy.  The Fourier transform
of Suzuki's oriented primitive satisfies exactly the pointwise premise. -/
theorem integral_Icc_norm_sq_le_four_mul_of_le_l1 {a T : ℝ} (ha : 0 ≤ a) (hT : 0 ≤ T)
    {f F : ℝ → ℂ}
    (hf : AEStronglyMeasurable f (volume.restrict (Icc (-a) a)))
    (hf2 : Integrable (fun x => ‖f x‖ ^ 2) (volume.restrict (Icc (-a) a)))
    (hF : AEStronglyMeasurable F (volume.restrict (Icc (-T) T)))
    (hpoint : ∀ z : ℝ, ‖F z‖ ≤ ∫ x in Icc (-a) a, ‖f x‖) :
    (∫ z in Icc (-T) T, ‖F z‖ ^ 2)
      ≤ 4 * a * T * ∫ x in Icc (-a) a, ‖f x‖ ^ 2 := by
  let L : ℝ := ∫ x in Icc (-a) a, ‖f x‖
  have hL : 0 ≤ L := integral_nonneg fun _ => norm_nonneg _
  have hsq : L ^ 2 ≤ 2 * a * ∫ x in Icc (-a) a, ‖f x‖ ^ 2 := by
    simpa only [L] using integral_Icc_norm_sq_l1_bound ha hf hf2
  have hmeas : AEStronglyMeasurable (fun z => ‖F z‖ ^ 2)
      (volume.restrict (Icc (-T) T)) := hF.norm.pow 2
  have hconst : Integrable (fun _ : ℝ => L ^ 2) (volume.restrict (Icc (-T) T)) := by
    apply MeasureTheory.integrableOn_const
    · rw [Real.volume_Icc]
      exact ENNReal.ofReal_ne_top
    · simp
  have hmono : (∫ z in Icc (-T) T, ‖F z‖ ^ 2) ≤ ∫ _ : ℝ in Icc (-T) T, L ^ 2 := by
    have hbound : ∀ᵐ z ∂(volume.restrict (Icc (-T) T)), ‖F z‖ ^ 2 ≤ L ^ 2 :=
      Filter.Eventually.of_forall fun z => (sq_le_sq₀ (norm_nonneg _) hL).mpr (hpoint z)
    have hleft : Integrable (fun z => ‖F z‖ ^ 2)
        (volume.restrict (Icc (-T) T)) := by
      refine hconst.mono' hmeas ?_
      filter_upwards [hbound] with z hz
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hz
    exact integral_mono_ae hleft hconst hbound
  have hlen : (∫ _ : ℝ in Icc (-T) T, L ^ 2) = 2 * T * L ^ 2 := by
    rw [MeasureTheory.setIntegral_const, Real.volume_real_Icc, smul_eq_mul,
      max_eq_left (by linarith)]
    ring
  rw [hlen] at hmono
  have henergy : 0 ≤ ∫ x in Icc (-a) a, ‖f x‖ ^ 2 :=
    integral_nonneg fun _ => sq_nonneg _
  nlinarith

/-- **Literal finite-source contour-shift repair.**  For Suzuki's exact oriented primitive, shifting
the spectral contour by `q` multiplies the Gram feature by `exp (-q x)`.  Its quadratic energy on
`[-a,a]` is therefore dominated at form level by `exp (2 |q| a)`, uniformly for every finite
complex source. -/
theorem suzukiFiniteContourShiftForm_le {ι : Type*} (s : Finset ι)
    (c : ι → ℂ) (τ : ι → ℝ) {a q : ℝ} (ha : 0 ≤ a) :
    (∫ x in Icc (-a) a,
        ‖((Real.exp (-q * x) : ℝ) : ℂ) *
          suzukiFiniteOrientedPrimitive s c τ x‖ ^ 2)
      ≤ Real.exp (2 * |q| * a) *
        ∫ x in Icc (-a) a, ‖suzukiFiniteOrientedPrimitive s c τ x‖ ^ 2 := by
  apply integral_Icc_norm_sq_exp_mul_le ha
  · exact (stronglyMeasurable_suzukiFiniteOrientedPrimitive s c τ).aestronglyMeasurable.restrict
  · exact (integrable_norm_sq_suzukiFiniteOrientedPrimitive s c τ).restrict

/-- Exact shifted Gram energy of a finite Suzuki source. -/
def suzukiFiniteContourShiftEnergy {ι : Type*} (a q : ℝ) (s : Finset ι)
    (c : ι → ℂ) (τ : ι → ℝ) : ℝ :=
  ∫ x in Icc (-a) a,
    ‖((Real.exp (-q * x) : ℝ) : ℂ) * suzukiFiniteOrientedPrimitive s c τ x‖ ^ 2

theorem suzukiFiniteContourShiftEnergy_le_free {ι : Type*} (s : Finset ι)
    (c : ι → ℂ) (τ : ι → ℝ) {a q : ℝ} (ha : 0 ≤ a)
    (hτ : ∀ i ∈ s, τ i ∈ Icc (-a) a) :
    suzukiFiniteContourShiftEnergy a q s c τ ≤
      Real.exp (2 * |q| * a) * (suzukiFreeKernelQuadraticForm s c τ).re := by
  unfold suzukiFiniteContourShiftEnergy
  rw [suzukiFreeKernelQuadraticForm_re_eq_integral_Icc_norm_sq s c τ ha hτ]
  exact suzukiFiniteContourShiftForm_le s c τ ha

/-- At zero contour shift, shifted energy is exactly the free screw-kernel quadratic form. -/
theorem suzukiFiniteContourShiftEnergy_zero {ι : Type*} (s : Finset ι)
    (c : ι → ℂ) (τ : ι → ℝ) {a : ℝ} (ha : 0 ≤ a)
    (hτ : ∀ i ∈ s, τ i ∈ Icc (-a) a) :
    suzukiFiniteContourShiftEnergy a 0 s c τ =
      (suzukiFreeKernelQuadraticForm s c τ).re := by
  unfold suzukiFiniteContourShiftEnergy
  rw [suzukiFreeKernelQuadraticForm_re_eq_integral_Icc_norm_sq s c τ ha hτ]
  simp

/-- **Literal finite-source low-band repair.**  The ordinary Fourier transform of Suzuki's exact
oriented primitive has low-frequency energy at most `4 a T` times the free screw-kernel form.
This is the form-level replacement for the second invalid pointwise-kernel comparison in the
printed proof of Theorem 4.2. -/
theorem suzukiFiniteFourierLowBandEnergy_le {ι : Type*} (s : Finset ι)
    (c : ι → ℂ) (τ : ι → ℝ) {a T : ℝ} (ha : 0 ≤ a) (hT : 0 ≤ T)
    (hτ : ∀ i ∈ s, τ i ∈ Icc (-a) a) :
    (∫ w in Icc (-T) T,
        ‖𝓕 (suzukiFiniteOrientedPrimitive s c τ) w‖ ^ 2) ≤
      4 * a * T * (suzukiFreeKernelQuadraticForm s c τ).re := by
  let P := suzukiFiniteOrientedPrimitive s c τ
  have hP : Integrable P := integrable_suzukiFiniteOrientedPrimitive s c τ
  have hPmeas : StronglyMeasurable P :=
    stronglyMeasurable_suzukiFiniteOrientedPrimitive s c τ
  have hP2 : Integrable (fun x => ‖P x‖ ^ 2) :=
    integrable_norm_sq_suzukiFiniteOrientedPrimitive s c τ
  have hsupport : ∀ x, x ∉ Icc (-a) a → P x = 0 := fun x hx =>
    suzukiFiniteOrientedPrimitive_eq_zero_of_not_mem_Icc s c τ ha hτ hx
  have hmass : (∫ x, ‖P x‖) = ∫ x in Icc (-a) a, ‖P x‖ :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
      rw [hsupport x hx, norm_zero]).symm
  have hFcont : Continuous (𝓕 P) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hP
  rw [suzukiFreeKernelQuadraticForm_re_eq_integral_Icc_norm_sq s c τ ha hτ]
  apply integral_Icc_norm_sq_le_four_mul_of_le_l1 ha hT
  · exact hPmeas.aestronglyMeasurable.restrict
  · exact hP2.restrict
  · exact hFcont.aestronglyMeasurable.restrict
  · intro w
    rw [← hmass]
    exact VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _

/-- Angular Fourier convention used in Suzuki's paper. -/
def suzukiAngularFourierTransform (f : ℝ → ℂ) (z : ℝ) : ℂ :=
  ∫ x, f x * Complex.exp (Complex.I * (z : ℂ) * (x : ℂ))

/-- Exact normalization bridge: Suzuki's angular transform is mathlib's `2π` Fourier transform at
frequency `-z/(2π)`. -/
theorem suzukiAngularFourierTransform_eq_fourier (f : ℝ → ℂ) (z : ℝ) :
    suzukiAngularFourierTransform f z = 𝓕 f (-z / (2 * Real.pi)) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  unfold suzukiAngularFourierTransform
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    simp only [smul_eq_mul]
    have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
    have he : -2 * Real.pi * x * (-z / (2 * Real.pi)) = z * x := by
      field_simp
    rw [he]
    push_cast
    ring_nf

theorem intervalIntegral_comp_neg_div_two_pi (G : ℝ → ℝ) (T : ℝ) :
    (∫ z in -T..T, G (-z / (2 * Real.pi))) =
      (2 * Real.pi) *
        ∫ w in -(T / (2 * Real.pi))..(T / (2 * Real.pi)), G w := by
  have hpi : (2 * Real.pi : ℝ) ≠ 0 :=
    mul_ne_zero (by norm_num) (ne_of_gt Real.pi_pos)
  have hc : (-(1 / (2 * Real.pi)) : ℝ) ≠ 0 :=
    neg_ne_zero.mpr (one_div_ne_zero hpi)
  have h := intervalIntegral.integral_comp_mul_left (a := -T) (b := T) G hc
  rw [show (fun z => G (-(1 / (2 * Real.pi)) * z)) =
      fun z => G (-z / (2 * Real.pi)) by
    funext z
    congr 1
    ring] at h
  rw [show (-(1 / (2 * Real.pi)) : ℝ)⁻¹ = -(2 * Real.pi) by field_simp] at h
  rw [show (-(1 / (2 * Real.pi))) * (-T) = T / (2 * Real.pi) by ring,
    show (-(1 / (2 * Real.pi))) * T = -(T / (2 * Real.pi)) by ring] at h
  rw [h, intervalIntegral.integral_symm]
  simp [smul_eq_mul]

/-- **Suzuki-normalized low-band estimate.**  In angular-frequency convention, low-band energy of
the exact oriented primitive is at most `4 a T` times the free screw-kernel form. -/
theorem suzukiFiniteAngularLowBandEnergy_le {ι : Type*} (s : Finset ι)
    (c : ι → ℂ) (τ : ι → ℝ) {a T : ℝ} (ha : 0 ≤ a) (hT : 0 ≤ T)
    (hτ : ∀ i ∈ s, τ i ∈ Icc (-a) a) :
    (∫ z in Icc (-T) T,
        ‖suzukiAngularFourierTransform (suzukiFiniteOrientedPrimitive s c τ) z‖ ^ 2) ≤
      4 * a * T * (suzukiFreeKernelQuadraticForm s c τ).re := by
  let P := suzukiFiniteOrientedPrimitive s c τ
  let G : ℝ → ℝ := fun w => ‖𝓕 P w‖ ^ 2
  let U : ℝ := T / (2 * Real.pi)
  have hpi : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have hU : 0 ≤ U := div_nonneg hT hpi.le
  have hleU : -U ≤ U := by linarith
  have hLow := suzukiFiniteFourierLowBandEnergy_le s c τ ha hU hτ
  have hLowInterval : (∫ w in -U..U, G w) ≤
      4 * a * U * (suzukiFreeKernelQuadraticForm s c τ).re := by
    rw [intervalIntegral.integral_of_le hleU]
    rw [setIntegral_congr_set Ioc_ae_eq_Icc]
    exact hLow
  have hleft : (∫ z in Icc (-T) T,
        ‖suzukiAngularFourierTransform P z‖ ^ 2) =
      (2 * Real.pi) * ∫ w in -U..U, G w := by
    rw [show (∫ z in Icc (-T) T,
        ‖suzukiAngularFourierTransform P z‖ ^ 2) =
        ∫ z in -T..T, ‖suzukiAngularFourierTransform P z‖ ^ 2 by
      rw [intervalIntegral.integral_of_le (by linarith)]
      exact (setIntegral_congr_set Ioc_ae_eq_Icc).symm]
    rw [show (fun z => ‖suzukiAngularFourierTransform P z‖ ^ 2) =
        fun z => G (-z / (2 * Real.pi)) by
      funext z
      rw [suzukiAngularFourierTransform_eq_fourier]]
    simpa only [U] using intervalIntegral_comp_neg_div_two_pi G T
  rw [show suzukiFiniteOrientedPrimitive s c τ = P by rfl]
  rw [hleft]
  calc
    (2 * Real.pi) * ∫ w in -U..U, G w ≤
        (2 * Real.pi) *
          (4 * a * U * (suzukiFreeKernelQuadraticForm s c τ).re) :=
      mul_le_mul_of_nonneg_left hLowInterval hpi.le
    _ = 4 * a * T * (suzukiFreeKernelQuadraticForm s c τ).re := by
      dsimp only [U]
      field_simp

/-- Suzuki's finite divided-exponential feature is literally the angular Fourier transform of its
oriented primitive. -/
theorem suzukiFiniteDividedExponentialFeature_eq_angularFourier {ι : Type*}
    (s : Finset ι) (c : ι → ℂ) (τ : ι → ℝ) (z : ℝ) (hz : z ≠ 0) :
    suzukiFiniteDividedExponentialFeature s c τ z =
      suzukiAngularFourierTransform (suzukiFiniteOrientedPrimitive s c τ) z := by
  exact suzukiFiniteDividedExponentialFeature_eq_integral s c τ z hz

theorem integral_Icc_norm_sq_suzukiFiniteDividedExponentialFeature_eq {ι : Type*}
    (s : Finset ι) (c : ι → ℂ) (τ : ι → ℝ) (T : ℝ) :
    (∫ z in Icc (-T) T, ‖suzukiFiniteDividedExponentialFeature s c τ z‖ ^ 2) =
      ∫ z in Icc (-T) T,
        ‖suzukiAngularFourierTransform (suzukiFiniteOrientedPrimitive s c τ) z‖ ^ 2 := by
  apply setIntegral_congr_ae measurableSet_Icc
  filter_upwards [volume.ae_ne 0] with z hz hmem
  rw [suzukiFiniteDividedExponentialFeature_eq_angularFourier s c τ z hz]

/-- **Exact finite-source low-frequency bound in Suzuki's literal feature notation.** -/
theorem suzukiFiniteDividedExponentialLowBandEnergy_le {ι : Type*} (s : Finset ι)
    (c : ι → ℂ) (τ : ι → ℝ) {a T : ℝ} (ha : 0 ≤ a) (hT : 0 ≤ T)
    (hτ : ∀ i ∈ s, τ i ∈ Icc (-a) a) :
    (∫ z in Icc (-T) T, ‖suzukiFiniteDividedExponentialFeature s c τ z‖ ^ 2) ≤
      4 * a * T * (suzukiFreeKernelQuadraticForm s c τ).re := by
  rw [integral_Icc_norm_sq_suzukiFiniteDividedExponentialFeature_eq]
  exact suzukiFiniteAngularLowBandEnergy_le s c τ ha hT hτ

end RHTower

end
