import GaloisForLFunctions.RHTower.HardyTitchmarshEulerConcrete
import GaloisForLFunctions.RHTower.Suzuki.SuzukiLagariasMeromorphicInner
import GaloisForLFunctions.RHTower.Suzuki.SuzukiPositiveHalfLine

/-!
# Suzuki's canonical Hankel operator: the exact spectral unitary

This file constructs the operator-theoretic half of Suzuki (2012), Lemma 4.1.  The source Hilbert
space `L²((0,∞), dx)` is represented by the corpus's unitarily equivalent even real-line carrier.
The normalized shifted Fourier transform is the exact logarithmic half-density transform followed
by Plancherel, with spectral reflection inserted to match Suzuki's positive exponential convention.

If the literal shifted-Xi quotient `Theta_omega` is meromorphic inner, its boundary values are
unimodular.  Multiplication by this boundary function is therefore an actual unitary on `L²(R)`.
Conjugating `M_Theta R` by the shifted Fourier unitary gives an actual physical-space unitary and
proves, in the `Lp` quotient, the exact boundary relation

`F_{1/2}(H_omega f)(u) = Theta_omega(u) F_{1/2}(f)(-u)`.

No integral-kernel identification is asserted here.  That remaining bridge to the literal
`h_omega(xy)` integral is the second half of Suzuki's Lemma 4.1.
-/

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace RHTower

abbrev SuzukiSpectralL2 := Lp (α := ℝ) ℂ 2

/-! ## Unimodular multiplication on spectral `L²` -/

theorem memLp_unimodular_mul
    (theta : ℝ → ℂ) (hthetaMeas : AEStronglyMeasurable theta volume)
    (htheta : ∀ u, ‖theta u‖ = 1)
    (f : SuzukiSpectralL2) :
    MemLp (fun u => theta u * f u) 2 (volume : Measure ℝ) := by
  apply (Lp.memLp f).congr_norm
  · exact hthetaMeas.mul (Lp.aestronglyMeasurable f)
  · filter_upwards with u
    rw [norm_mul, htheta, one_mul]

def unimodularMulAux
    (theta : ℝ → ℂ) (hthetaMeas : AEStronglyMeasurable theta volume)
    (htheta : ∀ u, ‖theta u‖ = 1)
    (f : SuzukiSpectralL2) : SuzukiSpectralL2 :=
  (memLp_unimodular_mul theta hthetaMeas htheta f).toLp _

theorem unimodularMulAux_ae
    (theta : ℝ → ℂ) (hthetaMeas : AEStronglyMeasurable theta volume)
    (htheta : ∀ u, ‖theta u‖ = 1)
    (f : SuzukiSpectralL2) :
    unimodularMulAux theta hthetaMeas htheta f =ᵐ[volume] fun u => theta u * f u :=
  (memLp_unimodular_mul theta hthetaMeas htheta f).coeFn_toLp

def unimodularMulLinear
    (theta : ℝ → ℂ) (hthetaMeas : AEStronglyMeasurable theta volume)
    (htheta : ∀ u, ‖theta u‖ = 1) :
    SuzukiSpectralL2 →ₗ[ℂ] SuzukiSpectralL2 where
  toFun := unimodularMulAux theta hthetaMeas htheta
  map_add' f g := by
    apply Lp.ext
    filter_upwards [unimodularMulAux_ae theta hthetaMeas htheta (f + g),
      unimodularMulAux_ae theta hthetaMeas htheta f,
      unimodularMulAux_ae theta hthetaMeas htheta g,
      Lp.coeFn_add f g,
      Lp.coeFn_add (unimodularMulAux theta hthetaMeas htheta f)
        (unimodularMulAux theta hthetaMeas htheta g)] with u hout hf hg hfg hsum
    rw [hout, hfg, hsum]
    simp only [Pi.add_apply]
    rw [hf, hg]
    ring
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [unimodularMulAux_ae theta hthetaMeas htheta (c • f),
      unimodularMulAux_ae theta hthetaMeas htheta f,
      Lp.coeFn_smul c f,
      Lp.coeFn_smul c (unimodularMulAux theta hthetaMeas htheta f)] with u hout hf hcf hsmul
    rw [hout, hcf]
    simp only [RingHom.id_apply]
    rw [hsmul]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hf]
    ring

theorem norm_unimodularMulAux
    (theta : ℝ → ℂ) (hthetaMeas : AEStronglyMeasurable theta volume)
    (htheta : ∀ u, ‖theta u‖ = 1)
    (f : SuzukiSpectralL2) :
    ‖unimodularMulAux theta hthetaMeas htheta f‖ = ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def,
    eLpNorm_congr_ae (unimodularMulAux_ae theta hthetaMeas htheta f)]
  congr 1
  apply eLpNorm_congr_norm_ae
  filter_upwards with u
  rw [norm_mul, htheta, one_mul]

def unimodularMulIsometry
    (theta : ℝ → ℂ) (hthetaMeas : AEStronglyMeasurable theta volume)
    (htheta : ∀ u, ‖theta u‖ = 1) :
    SuzukiSpectralL2 →ₗᵢ[ℂ] SuzukiSpectralL2 where
  __ := unimodularMulLinear theta hthetaMeas htheta
  norm_map' := norm_unimodularMulAux theta hthetaMeas htheta

theorem unimodular_ne_zero
    (theta : ℝ → ℂ) (htheta : ∀ u, ‖theta u‖ = 1) (u : ℝ) :
    theta u ≠ 0 := by
  intro h
  simpa [h] using htheta u

def unimodularMulUnitary
    (theta : ℝ → ℂ) (hthetaMeas : AEStronglyMeasurable theta volume)
    (htheta : ∀ u, ‖theta u‖ = 1) :
    SuzukiSpectralL2 ≃ₗᵢ[ℂ] SuzukiSpectralL2 where
  __ := unimodularMulIsometry theta hthetaMeas htheta
  invFun := unimodularMulAux (fun u => (theta u)⁻¹) hthetaMeas.inv₀
    (fun u => by rw [norm_inv, htheta, inv_one])
  left_inv f := by
    change unimodularMulAux (fun u => (theta u)⁻¹) hthetaMeas.inv₀
      (fun u => by rw [norm_inv, htheta, inv_one])
      (unimodularMulAux theta hthetaMeas htheta f) = f
    apply Lp.ext
    filter_upwards [unimodularMulAux_ae theta hthetaMeas htheta f,
      unimodularMulAux_ae (fun u => (theta u)⁻¹)
        hthetaMeas.inv₀
        (fun u => by rw [norm_inv, htheta, inv_one])
        (unimodularMulAux theta hthetaMeas htheta f)] with u hf hout
    rw [hout, hf, ← mul_assoc,
      inv_mul_cancel₀ (unimodular_ne_zero theta htheta u), one_mul]
  right_inv f := by
    change unimodularMulAux theta hthetaMeas htheta
      (unimodularMulAux (fun u => (theta u)⁻¹) hthetaMeas.inv₀
        (fun u => by rw [norm_inv, htheta, inv_one]) f) = f
    apply Lp.ext
    filter_upwards [unimodularMulAux_ae (fun u => (theta u)⁻¹)
        hthetaMeas.inv₀
        (fun u => by rw [norm_inv, htheta, inv_one]) f,
      unimodularMulAux_ae theta hthetaMeas htheta
        (unimodularMulAux (fun u => (theta u)⁻¹)
          hthetaMeas.inv₀
          (fun u => by rw [norm_inv, htheta, inv_one]) f)] with u hf hout
    rw [hout, hf, ← mul_assoc,
      mul_inv_cancel₀ (unimodular_ne_zero theta htheta u), one_mul]

theorem unimodularMulUnitary_ae
    (theta : ℝ → ℂ) (hthetaMeas : AEStronglyMeasurable theta volume)
    (htheta : ∀ u, ‖theta u‖ = 1)
    (f : SuzukiSpectralL2) :
    unimodularMulUnitary theta hthetaMeas htheta f =ᵐ[volume]
      fun u => theta u * f u :=
  unimodularMulAux_ae theta hthetaMeas htheta f

/-! ## Spectral reflection and Suzuki's shifted transform -/

def spectralReflectionUnitary :
    SuzukiSpectralL2 ≃ₗᵢ[ℂ] SuzukiSpectralL2 where
  __ := l2ReflectionIsometry
  invFun := l2Reflection
  left_inv := l2Reflection_involutive
  right_inv := l2Reflection_involutive

theorem spectralReflectionUnitary_ae (f : SuzukiSpectralL2) :
    spectralReflectionUnitary f =ᵐ[volume] fun u => f (-u) :=
  l2Reflection_ae f

/-- Normalized version of Suzuki's `F_{1/2}`.  The logarithmic half-density map is followed by
the standard Mellin--Plancherel unitary and spectral reflection, so the phase has Suzuki's
`exp(+ i u log x)` sign.  Suzuki's unnormalized transform differs only by the constant
`sqrt(2*pi)`. -/
def suzukiShiftedFourierUnitary :
    evenSubspace ≃ₗᵢ[ℂ] SuzukiSpectralL2 :=
  archimedeanMellinUnitary.trans spectralReflectionUnitary

/-! ## The exact spectral Hankel unitary -/

def suzukiThetaBoundary (omega : ℝ) (u : ℝ) : ℂ :=
  suzukiCanonicalTheta omega (u : ℂ)

theorem norm_suzukiThetaBoundary
    {omega : ℝ} (hinner : SuzukiCanonicalThetaMeromorphicInner omega) (u : ℝ) :
    ‖suzukiThetaBoundary omega u‖ = 1 :=
  hinner.2.2.2 u

theorem suzukiCanonicalE_boundary_ne_zero
    {omega : ℝ} (hinner : SuzukiCanonicalThetaMeromorphicInner omega) (u : ℝ) :
    suzukiCanonicalE omega (u : ℂ) ≠ 0 := by
  intro hE
  have hzero : suzukiThetaBoundary omega u = 0 := by
    rw [suzukiThetaBoundary, suzukiCanonicalTheta_eq_ESharp_div_E, hE, div_zero]
  have hone := norm_suzukiThetaBoundary hinner u
  rw [hzero, norm_zero] at hone
  norm_num at hone

theorem differentiableAt_suzukiCanonicalTheta_boundary
    {omega : ℝ} (hinner : SuzukiCanonicalThetaMeromorphicInner omega) (u : ℝ) :
    DifferentiableAt ℂ (suzukiCanonicalTheta omega) (u : ℂ) := by
  rw [show suzukiCanonicalTheta omega = fun z =>
      suzukiCanonicalESharp omega z / suzukiCanonicalE omega z by
    funext z
    exact suzukiCanonicalTheta_eq_ESharp_div_E omega z]
  exact (differentiable_suzukiCanonicalESharp omega).differentiableAt.div
    (differentiable_suzukiCanonicalE omega).differentiableAt
    (suzukiCanonicalE_boundary_ne_zero hinner u)

theorem continuous_suzukiThetaBoundary
    {omega : ℝ} (hinner : SuzukiCanonicalThetaMeromorphicInner omega) :
    Continuous (suzukiThetaBoundary omega) := by
  rw [continuous_iff_continuousAt]
  intro u
  exact (differentiableAt_suzukiCanonicalTheta_boundary hinner u).continuousAt.comp
    Complex.continuous_ofReal.continuousAt

theorem measurable_suzukiThetaBoundary
    {omega : ℝ} (hinner : SuzukiCanonicalThetaMeromorphicInner omega) :
    Measurable (suzukiThetaBoundary omega) :=
  (continuous_suzukiThetaBoundary hinner).measurable

/-- Suzuki's unconditional range: if `omega > 1/2`, the classical zero-free half-plane
`Re(s) ≥ 1` makes the literal shifted-Xi quotient meromorphic inner. -/
theorem suzukiCanonicalTheta_meromorphicInner_of_half_lt
    {omega : ℝ} (homega : 1 / 2 < omega) :
    SuzukiCanonicalThetaMeromorphicInner omega := by
  have hzeta : SuzukiZetaZeroFreeRightOf (1 / 2) := by
    intro s hs _
    apply riemannZeta_ne_zero_of_one_le_re
    norm_num at hs ⊢
    exact hs.le
  exact suzukiZetaZeroFreeRightOf_implies_theta_meromorphicInner
    (by norm_num) hzeta omega homega

def suzukiThetaBoundaryMulUnitary
  (omega : ℝ) (hinner : SuzukiCanonicalThetaMeromorphicInner omega) :
    SuzukiSpectralL2 ≃ₗᵢ[ℂ] SuzukiSpectralL2 :=
  unimodularMulUnitary (suzukiThetaBoundary omega)
    (measurable_suzukiThetaBoundary hinner).aestronglyMeasurable
    (norm_suzukiThetaBoundary hinner)

theorem suzukiThetaBoundaryMulUnitary_ae
    (omega : ℝ) (hinner : SuzukiCanonicalThetaMeromorphicInner omega)
    (f : SuzukiSpectralL2) :
    suzukiThetaBoundaryMulUnitary omega hinner f =ᵐ[volume]
      fun u => suzukiCanonicalTheta omega (u : ℂ) * f u :=
  unimodularMulUnitary_ae _
    (measurable_suzukiThetaBoundary hinner).aestronglyMeasurable _ f

/-- Suzuki's canonical physical Hankel unitary, defined by the exact spectral action
`F_{1/2}^{-1} M_{Theta_omega} R F_{1/2}`. -/
def suzukiCanonicalHankelUnitary
    (omega : ℝ) (hinner : SuzukiCanonicalThetaMeromorphicInner omega) :
    evenSubspace ≃ₗᵢ[ℂ] evenSubspace :=
  suzukiShiftedFourierUnitary.trans
    (spectralReflectionUnitary.trans
      ((suzukiThetaBoundaryMulUnitary omega hinner).trans
        suzukiShiftedFourierUnitary.symm))

/-- **Suzuki (2012), equation (401), exact `L²` boundary identity.**  This is equality of
spectral `L²` classes, before choosing representatives. -/
theorem suzukiShiftedFourier_canonicalHankel
    (omega : ℝ) (hinner : SuzukiCanonicalThetaMeromorphicInner omega)
    (f : evenSubspace) :
    suzukiShiftedFourierUnitary
        (suzukiCanonicalHankelUnitary omega hinner f) =
      suzukiThetaBoundaryMulUnitary omega hinner
        (spectralReflectionUnitary (suzukiShiftedFourierUnitary f)) := by
  simp [suzukiCanonicalHankelUnitary]

/-- Pointwise-a.e. form of Suzuki's equation (401):
`F_{1/2}(H_omega f)(u) = Theta_omega(u) F_{1/2}(f)(-u)`. -/
theorem suzukiShiftedFourier_canonicalHankel_ae
    (omega : ℝ) (hinner : SuzukiCanonicalThetaMeromorphicInner omega)
    (f : evenSubspace) :
    (suzukiShiftedFourierUnitary
        (suzukiCanonicalHankelUnitary omega hinner f) : ℝ → ℂ)
      =ᵐ[volume]
        fun u => suzukiCanonicalTheta omega (u : ℂ) *
          (suzukiShiftedFourierUnitary f) (-u) := by
  rw [suzukiShiftedFourier_canonicalHankel]
  filter_upwards [spectralReflectionUnitary_ae (suzukiShiftedFourierUnitary f),
    suzukiThetaBoundaryMulUnitary_ae omega hinner
      (spectralReflectionUnitary (suzukiShiftedFourierUnitary f))] with u href hmul
  rw [hmul, href]

/-- The canonical Hankel extension in Suzuki's Lemma 4.1 is an isometry. -/
theorem norm_suzukiCanonicalHankelUnitary
    (omega : ℝ) (hinner : SuzukiCanonicalThetaMeromorphicInner omega)
    (f : evenSubspace) :
    ‖suzukiCanonicalHankelUnitary omega hinner f‖ = ‖f‖ :=
  (suzukiCanonicalHankelUnitary omega hinner).norm_map f

/-! ## Suzuki's literal positive-half-line carrier -/

/-- Normalized shifted Mellin transform on Suzuki's literal `L²((0,∞), dx)` carrier.  The
positive-half-line unitary is explicit, so this is no longer an identification by convention. -/
def suzukiPositiveShiftedFourierUnitary :
    SuzukiPositiveL2 ≃ₗᵢ[ℂ] SuzukiSpectralL2 :=
  suzukiPositiveHalfLineUnitary.symm.trans suzukiShiftedFourierUnitary

/-- Suzuki's canonical Hankel unitary on the literal positive-half-line carrier, defined by its
source spectral action `F_{1/2}^{-1} M_{Theta_omega} R F_{1/2}`. -/
def suzukiCanonicalPositiveHankelUnitary
    (omega : ℝ) (hinner : SuzukiCanonicalThetaMeromorphicInner omega) :
    SuzukiPositiveL2 ≃ₗᵢ[ℂ] SuzukiPositiveL2 :=
  suzukiPositiveShiftedFourierUnitary.trans
    (spectralReflectionUnitary.trans
      ((suzukiThetaBoundaryMulUnitary omega hinner).trans
        suzukiPositiveShiftedFourierUnitary.symm))

/-- **Suzuki (2012), equation (401), on the literal `L²((0,∞),dx)` carrier.** -/
theorem suzukiPositiveShiftedFourier_canonicalHankel
    (omega : ℝ) (hinner : SuzukiCanonicalThetaMeromorphicInner omega)
    (f : SuzukiPositiveL2) :
    suzukiPositiveShiftedFourierUnitary
        (suzukiCanonicalPositiveHankelUnitary omega hinner f) =
      suzukiThetaBoundaryMulUnitary omega hinner
        (spectralReflectionUnitary (suzukiPositiveShiftedFourierUnitary f)) := by
  simp [suzukiCanonicalPositiveHankelUnitary]

/-- Pointwise-a.e. source form of equation (401) on `L²((0,∞),dx)`. -/
theorem suzukiPositiveShiftedFourier_canonicalHankel_ae
    (omega : ℝ) (hinner : SuzukiCanonicalThetaMeromorphicInner omega)
    (f : SuzukiPositiveL2) :
    (suzukiPositiveShiftedFourierUnitary
        (suzukiCanonicalPositiveHankelUnitary omega hinner f) : ℝ → ℂ)
      =ᵐ[volume]
        fun u => suzukiCanonicalTheta omega (u : ℂ) *
          (suzukiPositiveShiftedFourierUnitary f) (-u) := by
  rw [suzukiPositiveShiftedFourier_canonicalHankel]
  filter_upwards [spectralReflectionUnitary_ae (suzukiPositiveShiftedFourierUnitary f),
    suzukiThetaBoundaryMulUnitary_ae omega hinner
      (spectralReflectionUnitary (suzukiPositiveShiftedFourierUnitary f))] with u href hmul
  rw [hmul, href]

/-- The source spectral Hankel extension is an isometry on literal `L²((0,∞),dx)`. -/
theorem norm_suzukiCanonicalPositiveHankelUnitary
    (omega : ℝ) (hinner : SuzukiCanonicalThetaMeromorphicInner omega)
    (f : SuzukiPositiveL2) :
    ‖suzukiCanonicalPositiveHankelUnitary omega hinner f‖ = ‖f‖ :=
  (suzukiCanonicalPositiveHankelUnitary omega hinner).norm_map f

end RHTower
