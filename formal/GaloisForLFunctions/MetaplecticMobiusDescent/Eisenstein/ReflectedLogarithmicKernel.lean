/-
The reflected logarithmic kernel adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.SourceCuspMellinReflection

/-!
# The reflected logarithmic kernel

The cubic Gamma quotient is unitary on the imaginary axis, so the reflected logarithmic
spectrum is a unitary multiplier. Compact smooth sources give smooth reflected kernels
`reflectedKernelLogProfile` with uniform Fourier moments.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Classical Topology InnerProductSpace ComplexConjugate MatrixGroups ENNReal
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicJacobi CubicKubota CubicRamified
open scoped NNReal Pointwise
open RationalSource
open scoped Manifold ContDiff
open scoped Matrix
open UniqueFactorizationMonoid
open Asymptotics
open scoped ContDiff FourierTransform SchwartzMap
open scoped ContDiff FourierTransform SchwartzMap

def fixedCuspSector (M : SL(2, O)) : FixedCuspSector := ⟨fixedCuspReduction M, ⟨M, rfl⟩⟩

def fixedCuspRepresentative (s : FixedCuspSector) : SL(2, O) := s.property.choose

lemma fixedCuspRepresentative_reduction (s : FixedCuspSector) :
    fixedCuspReduction (fixedCuspRepresentative s) = s.val := s.property.choose_spec

lemma fixedCusp_difference_levelThree (M : SL(2, O)) :
    M * (fixedCuspRepresentative (fixedCuspSector M))⁻¹ ∈ levelThree := by
  change fixedCuspReduction (M * (fixedCuspRepresentative (fixedCuspSector M))⁻¹) = 1
  rw [map_mul, map_inv, fixedCuspRepresentative_reduction]
  change fixedCuspReduction M * (fixedCuspReduction M)⁻¹ = 1
  exact mul_inv_cancel _

/-- The triangular cusp coordinate change depends only on the residue of the matrix modulo three. -/
theorem exists_fixed_cusp_decomposition :
    ∃ (j : FixedCuspSector → Fin 3) (T : FixedCuspSector → SL(2, O))
      (G : SL(2, O) → rationalExtension),
      (∀ s, T s 1 0 = 0 ∧ IsUnit (T s 0 0) ∧ IsUnit (T s 1 1)) ∧
      ∀ M : SL(2, O), M = (G M : SL(2, O)) * cuspRepresentative (j (fixedCuspSector M)) *
        T (fixedCuspSector M) := by
  have h (s : FixedCuspSector) := three_cusp_decomposition (fixedCuspRepresentative s)
  choose G₀ j T hT hT0 hT1 he using h
  let D : SL(2, O) → rationalExtension := fun M =>
    ⟨M * (fixedCuspRepresentative (fixedCuspSector M))⁻¹,
      levelThree_le_rationalExtension (fixedCusp_difference_levelThree M)⟩
  refine ⟨j, T, fun M => D M * G₀ (fixedCuspSector M), fun s => ⟨hT s, hT0 s, hT1 s⟩, ?_⟩
  intro M
  change M = (M * (fixedCuspRepresentative (fixedCuspSector M))⁻¹) *
    (G₀ (fixedCuspSector M) : SL(2, O)) * cuspRepresentative (j (fixedCuspSector M)) * T (fixedCuspSector M)
  rw [he (fixedCuspSector M)]
  group

/-- The cubic Gamma quotient is unitary on the imaginary axis. -/
lemma cubicReflectionGamma_axis_norm (t : ℝ) : ‖cubicReflectionGamma (t * Complex.I)‖ = 1 := by
  have h₁ := Gamma_vertical_conj (7 / 6) t
  have h₂ := Gamma_vertical_conj (5 / 6) t
  norm_num only [Complex.ofReal_div, Complex.ofReal_ofNat] at h₁ h₂
  have hn₁ : Complex.Gamma ((7 / 6 : ℂ) + t * Complex.I) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by norm_num)
  have hn₂ : Complex.Gamma ((5 / 6 : ℂ) + t * Complex.I) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by norm_num)
  rw [cubicReflectionGamma, h₁, h₂, norm_div, norm_mul, norm_mul, norm_star, norm_star,
    div_self (mul_ne_zero (norm_ne_zero_iff.mpr hn₁) (norm_ne_zero_iff.mpr hn₂))]

def cubicKernelAxisMultiplier (u : ℝ) : ℂ :=
  cubicReflectionGamma (((2 * Real.pi * u : ℝ) : ℂ) * Complex.I)

lemma cubicKernelAxisMultiplier_continuous : Continuous cubicKernelAxisMultiplier := by
  have hl : Continuous (fun u : ℝ => ((2 * Real.pi * u : ℝ) : ℂ) * Complex.I) := by fun_prop
  apply continuous_iff_continuousAt.mpr
  intro u
  exact (cubicReflectionGamma_differentiableAt _ (by norm_num)).continuousAt.comp hl.continuousAt

/-- The reflected logarithmic spectrum is a unitary multiplier of the source Fourier transform. -/
def kernelSpectralProfile (f : SchwartzMap ℝ ℂ) (u : ℝ) : ℂ :=
  cubicKernelAxisMultiplier u * (𝓕 f) u

lemma kernelSpectralProfile_norm (f : SchwartzMap ℝ ℂ) (u : ℝ) :
    ‖kernelSpectralProfile f u‖ = ‖(𝓕 f) u‖ := by
  rw [kernelSpectralProfile, norm_mul, cubicKernelAxisMultiplier, cubicReflectionGamma_axis_norm, one_mul]

lemma kernelSpectralProfile_continuous (f : SchwartzMap ℝ ℂ) : Continuous (kernelSpectralProfile f) :=
  cubicKernelAxisMultiplier_continuous.mul (𝓕 f).continuous

lemma kernelSpectralProfile_moment_integrable (f : SchwartzMap ℝ ℂ) (j : ℕ) :
    Integrable (fun u : ℝ => ‖u‖ ^ j * ‖kernelSpectralProfile f u‖) := by
  simpa only [kernelSpectralProfile_norm] using (𝓕 f).integrable_pow_mul volume j

lemma kernelSpectralProfile_pow_integrable (f : SchwartzMap ℝ ℂ) (j : ℕ) :
    Integrable (fun u : ℝ => u ^ j • kernelSpectralProfile f u) := by
  have hn (u : ℝ) : ‖(u ^ j : ℝ) • kernelSpectralProfile f u‖ =
      ‖u‖ ^ j * ‖kernelSpectralProfile f u‖ := by rw [norm_smul, norm_pow]
  apply (kernelSpectralProfile_moment_integrable f j).mono'
    ((continuous_id.pow j).smul (kernelSpectralProfile_continuous f)).aestronglyMeasurable
  exact Eventually.of_forall (fun u => (hn u).le)

def reflectedKernelLogProfile (f : SchwartzMap ℝ ℂ) : ℝ → ℂ := 𝓕 (kernelSpectralProfile f)

lemma reflectedKernelLogProfile_smooth (f : SchwartzMap ℝ ℂ) :
    ContDiff ℝ ∞ (reflectedKernelLogProfile f) :=
  Real.contDiff_fourier (fun j _ => kernelSpectralProfile_moment_integrable f j)

lemma reflectedKernelLogProfile_deriv (f : SchwartzMap ℝ ℂ) (j : ℕ) :
    iteratedDeriv j (reflectedKernelLogProfile f) =
      𝓕 (fun u : ℝ => (-2 * Real.pi * Complex.I * u) ^ j * kernelSpectralProfile f u) := by
  simpa only [reflectedKernelLogProfile, smul_eq_mul] using
    Real.iteratedDeriv_fourier (N := (⊤ : ℕ∞))
      (fun n _ => kernelSpectralProfile_pow_integrable f n) (by simp : (j : ℕ∞) ≤ ⊤)

lemma kernelLogSource_compact (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support V ⊆ Set.Icc a b) : HasCompactSupport (fun u : ℝ => V (Real.exp u)) := by
  apply HasCompactSupport.of_support_subset_isCompact (K := Set.Icc (Real.log a) (Real.log b)) isCompact_Icc
  intro u hu
  have hm := hs (show V (Real.exp u) ≠ 0 from hu)
  constructor
  · simpa only [Real.log_exp] using Real.log_le_log ha hm.1
  · simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos u) hm.2

def kernelLogSource (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V) : SchwartzMap ℝ ℂ :=
  (kernelLogSource_compact V a b ha hs).toSchwartzMap (hV.comp Real.contDiff_exp)

lemma mellin_imaginary_eq_logFourier (V : ℝ → ℂ) (f : SchwartzMap ℝ ℂ)
    (hf : ∀ u, f u = V (Real.exp u)) (u : ℝ) :
    mellin V (-(((2 * Real.pi * u : ℝ) : ℂ) * Complex.I)) = (𝓕 f) u := by
  rw [mellin_eq_fourier]
  have hfreq : (-(((2 * Real.pi * u : ℝ) : ℂ) * Complex.I)).im / (2 * Real.pi) = -u := by
    simp only [Complex.neg_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
      Complex.ofReal_im, Complex.I_re, mul_one, mul_zero, add_zero]
    field_simp
  rw [hfreq]
  have hfun : (fun v : ℝ => Real.exp
      (-(-(((2 * Real.pi * u : ℝ) : ℂ) * Complex.I)).re * v) • V (Real.exp (-v))) =
      (f : ℝ → ℂ) ∘ LinearIsometryEquiv.neg ℝ := by
    funext v
    simp [hf]
  rw [hfun, Real.fourier_comp_linearIsometry]
  simp
  rfl

lemma paperKernel_eq_logFourier (V : ℝ → ℂ) (f : SchwartzMap ℝ ℂ)
    (hf : ∀ u, f u = V (Real.exp u)) (x : ℝ) (hx : 0 < x) :
    paperKernel V x = reflectedKernelLogProfile f (Real.log (paperScale * x)) := by
  unfold paperKernel
  rw [mellinInv_eq_fourierInv 0 _ (mul_pos paperScale_pos hx)]
  simp only [Complex.ofReal_zero, neg_zero, Complex.cpow_zero, one_smul]
  rw [Real.fourierInv_eq_fourier_neg, neg_neg]
  have hfun : (fun y : ℝ => mellin V (-(0 + 2 * Real.pi * y * Complex.I)) *
      cubicReflectionGamma (0 + 2 * Real.pi * y * Complex.I)) = kernelSpectralProfile f := by
    funext y
    have hy : (0 + 2 * Real.pi * y * Complex.I : ℂ) =
        ((2 * Real.pi * y : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [hy, mellin_imaginary_eq_logFourier V f hf]
    exact mul_comm _ _
  rw [hfun]
  rfl

/-- Compact smooth source functions produce smooth reflected kernels on the positive axis. -/
theorem paperKernel_compact_source_smooth (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V) :
    ContDiffOn ℝ ∞ (paperKernel V) (Set.Ioi 0) := by
  let f := kernelLogSource V a b ha hs hV
  have hf : ∀ u, f u = V (Real.exp u) := fun u => rfl
  have hg : ContDiffOn ℝ ∞
      (fun x => reflectedKernelLogProfile f (Real.log (paperScale * x))) (Set.Ioi 0) := by
    intro x hx
    apply (reflectedKernelLogProfile_smooth f).contDiffAt.comp_contDiffWithinAt x
    exact ((contDiffAt_const.mul contDiffAt_id).log
      (ne_of_gt (mul_pos paperScale_pos hx))).contDiffWithinAt
  apply hg.congr
  intro x hx
  exact paperKernel_eq_logFourier V f hf x hx

/-- Inverse Mellin representations of logarithmic derivatives of the reflected kernel. -/
def paperKernelLogDerivative (V : ℝ → ℂ) (j : ℕ) (x : ℝ) : ℂ :=
  mellinInv 0 (mellinEulerData V j) (paperScale * x)

lemma paperKernelLogDerivative_zero (V : ℝ → ℂ) (x : ℝ) :
    paperKernelLogDerivative V 0 x = paperKernel V x := by
  have he : mellinEulerData V 0 = fun s : ℂ => mellin V (-s) * cubicReflectionGamma s := by
    funext s
    simp only [mellinEulerData, pow_zero, one_mul, mellinData]
  rw [paperKernelLogDerivative, he]
  rfl

lemma paperKernelLogDerivative_eq (V : ℝ → ℂ) (f : SchwartzMap ℝ ℂ)
    (hf : ∀ u, f u = V (Real.exp u)) (j : ℕ) (x : ℝ) (hx : 0 < x) :
    paperKernelLogDerivative V j x =
      iteratedDeriv j (reflectedKernelLogProfile f) (Real.log (paperScale * x)) := by
  rw [paperKernelLogDerivative, mellinInv_eq_fourierInv 0 _ (mul_pos paperScale_pos hx)]
  simp only [Complex.ofReal_zero, neg_zero, Complex.cpow_zero, one_smul]
  rw [Real.fourierInv_eq_fourier_neg, neg_neg, reflectedKernelLogProfile_deriv]
  have he : (fun y : ℝ => mellinEulerData V j (0 + 2 * Real.pi * y * Complex.I)) =
      fun u : ℝ => (-2 * Real.pi * Complex.I * u) ^ j * kernelSpectralProfile f u := by
    funext u
    have hu : (0 + 2 * Real.pi * u * Complex.I : ℂ) =
        ((2 * Real.pi * u : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [hu, mellinEulerData, mellinData, mellin_imaginary_eq_logFourier V f hf]
    have hp : -(((2 * Real.pi * u : ℝ) : ℂ) * Complex.I) = -2 * Real.pi * Complex.I * u := by
      push_cast
      ring
    rw [hp]
    dsimp only [kernelSpectralProfile, cubicKernelAxisMultiplier]
    ring
  rw [he]

lemma iteratedDeriv_paperKernel_exp (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (R : ℝ) (hR : 0 < R) (j : ℕ) (u : ℝ) :
    iteratedDeriv j (fun v : ℝ => paperKernel V (R * Real.exp v)) u =
      paperKernelLogDerivative V j (R * Real.exp u) := by
  let f := kernelLogSource V a b ha hs hV
  have hf : ∀ v, f v = V (Real.exp v) := fun _ => rfl
  have he (v : ℝ) : Real.log (paperScale * (R * Real.exp v)) = Real.log (paperScale * R) + v := by
    rw [← mul_assoc, Real.log_mul (mul_pos paperScale_pos hR).ne' (Real.exp_pos v).ne', Real.log_exp]
  have hfun : (fun v : ℝ => paperKernel V (R * Real.exp v)) =
      fun v : ℝ => reflectedKernelLogProfile f (Real.log (paperScale * R) + v) := by
    funext v
    rw [paperKernel_eq_logFourier V f hf _ (mul_pos hR (Real.exp_pos v)), he]
  rw [hfun, iteratedDeriv_comp_const_add,
    paperKernelLogDerivative_eq V f hf j _ (mul_pos hR (Real.exp_pos u)), he]

lemma paperKernel_exp_smooth (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (R : ℝ) (hR : 0 < R) :
    ContDiff ℝ ∞ (fun u : ℝ => paperKernel V (R * Real.exp u)) := by
  let f := kernelLogSource V a b ha hs hV
  have he : (fun u : ℝ => paperKernel V (R * Real.exp u)) =
      fun u : ℝ => reflectedKernelLogProfile f (Real.log (paperScale * R) + u) := by
    funext u
    rw [paperKernel_eq_logFourier V f (fun _ => rfl) _ (mul_pos hR (Real.exp_pos u))]
    rw [← mul_assoc, Real.log_mul (mul_pos paperScale_pos hR).ne' (Real.exp_pos u).ne', Real.log_exp]
  rw [he]
  exact (reflectedKernelLogProfile_smooth f).comp (contDiff_const.add contDiff_id)

/-- Uniform bounds on compactly supported derivatives give uniform Fourier moments. -/
theorem compact_weighted_family_fourier_power_bound
    (F : ℝ → ℝ → ℂ) (P : ℝ → ℝ) (hP : ∀ R, 0 < R → 0 ≤ P R)
    (hF : ∀ R, 0 < R → ContDiff ℝ ∞ (F R))
    (K : Set ℝ) (hK : IsCompact K) (hs : ∀ R, 0 < R → Function.support (F R) ⊆ K)
    (hb : ∀ j : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ R, 0 < R → ∀ u,
      P R * ‖iteratedDeriv j (F R) u‖ ≤ C) (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ R, 0 < R → ∀ t : ℝ,
      P R * (|t| ^ j * ‖𝓕 (F R) t‖) ≤ C := by
  obtain ⟨C, hC, hCb⟩ := hb j
  refine ⟨C * (volume.real K + 1) / (2 * Real.pi) ^ j, by positivity, ?_⟩
  intro R hR t
  have hPR := hP R hR
  have hcompact (n : ℕ) : HasCompactSupport (iteratedDeriv n (F R)) := by
    apply HasCompactSupport.of_support_subset_isCompact hK
    exact (subset_tsupport _).trans ((tsupport_iteratedDeriv_subset _ n).trans
      (closure_minimal (hs R hR) hK.isClosed))
  have hi (n : ℕ) : Integrable (iteratedDeriv n (F R)) :=
    ((hF R hR).continuous_iteratedDeriv n
      (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))).integrable_of_hasCompactSupport (hcompact n)
  have hfour := Real.fourier_iteratedDeriv (N := (⊤ : ℕ∞)) (hF R hR)
    (fun n _ => hi n) (by simp : (j : ℕ∞) ≤ ⊤)
  have hid : (2 * Real.pi) ^ j * (|t| ^ j * ‖𝓕 (F R) t‖) =
      ‖𝓕 (iteratedDeriv j (F R)) t‖ := by
    rw [hfour]
    simp only [norm_smul, norm_pow, norm_mul, Complex.norm_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    norm_num
    ring
  have hsder : Function.support (iteratedDeriv j (F R)) ⊆ K :=
    (subset_tsupport _).trans ((tsupport_iteratedDeriv_subset _ j).trans
      (closure_minimal (hs R hR) hK.isClosed))
  have hzero : ∀ u, u ∉ K → P R * ‖iteratedDeriv j (F R) u‖ = 0 := by
    intro u hu
    have hz : iteratedDeriv j (F R) u = 0 := by
      by_contra hn
      exact hu (hsder hn)
    rw [hz, norm_zero, mul_zero]
  have hI := norm_setIntegral_le_of_norm_le_const («μ» := volume)
    (f := fun u => P R * ‖iteratedDeriv j (F R) u‖) hK.measure_lt_top
    (C := C) (fun u _ => by rw [Real.norm_of_nonneg (by positivity)]; exact hCb R hR u)
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzero,
    Real.norm_of_nonneg (integral_nonneg (fun _ => by positivity)), integral_const_mul] at hI
  have hFourier := mul_le_mul_of_nonneg_left
    (VectorFourier.norm_fourierIntegral_le_integral_norm Real.fourierChar volume (innerₗ ℝ)
      (iteratedDeriv j (F R)) t) (hP R hR)
  apply (le_div_iff₀ (by positivity : 0 < (2 * Real.pi) ^ j)).mpr
  calc
    _ = P R * ((2 * Real.pi) ^ j * (|t| ^ j * ‖𝓕 (F R) t‖)) := by ring
    _ = P R * ‖𝓕 (iteratedDeriv j (F R)) t‖ := by rw [hid]
    _ ≤ C * volume.real K := hFourier.trans hI
    _ ≤ C * (volume.real K + 1) := by nlinarith only [hC]

/-- The two extra Fourier powers furnish an integrable envelope. -/
lemma weighted_fourier_L1_bound (B : ℝ → ℂ) (hB : Continuous B)
    (P C : ℝ) (hP : 0 < P) (hC : 0 ≤ C) (J : ℕ)
    (hb : ∀ t : ℝ, P * (1 + |t|) ^ (J + 2) * ‖B t‖ ≤ C) :
    Integrable (fun t : ℝ => (1 + |t|) ^ J * ‖B t‖) ∧
      P * (∫ t : ℝ, (1 + |t|) ^ J * ‖B t‖) ≤
        C * ∫ t : ℝ, ((1 + |t|) ^ (2 : ℕ))⁻¹ := by
  have hw : Integrable (fun t : ℝ => ((1 + |t|) ^ (2 : ℕ))⁻¹) := by
    have h : Integrable (fun t : ℝ => (1 + ‖t‖) ^ (-(2 : ℝ))) :=
      integrable_one_add_norm (by norm_num)
    apply h.congr
    exact Eventually.of_forall (fun t => by
      dsimp only
      rw [Real.norm_eq_abs, Real.rpow_neg (by positivity), Real.rpow_two])
  have hdom (t : ℝ) : (1 + |t|) ^ J * ‖B t‖ ≤
      (C / P) * ((1 + |t|) ^ (2 : ℕ))⁻¹ := by
    rw [← div_eq_mul_inv]
    apply (le_div_iff₀ (by positivity : 0 < (1 + |t|) ^ (2 : ℕ))).mpr
    apply (le_div_iff₀ hP).mpr
    calc
      _ = P * (1 + |t|) ^ (J + 2) * ‖B t‖ := by rw [pow_add]; ring
      _ ≤ C := hb t
  have hi : Integrable (fun t : ℝ => (1 + |t|) ^ J * ‖B t‖) :=
    (hw.const_mul (C / P)).mono'
      (((continuous_const.add continuous_abs).pow J).mul hB.norm).aestronglyMeasurable
      (Eventually.of_forall (fun t => by rw [Real.norm_of_nonneg (by positivity)]; exact hdom t))
  refine ⟨hi, ?_⟩
  have hI := integral_mono hi (hw.const_mul (C / P)) hdom
  rw [integral_const_mul] at hI
  calc
    _ ≤ P * ((C / P) * ∫ t : ℝ, ((1 + |t|) ^ (2 : ℕ))⁻¹) :=
      mul_le_mul_of_nonneg_left hI hP.le
    _ = _ := by field_simp [hP.ne']

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
