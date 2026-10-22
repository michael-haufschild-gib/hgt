import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingFZZParityComplexCharacterNonlocalRigidityNoGo
import GaloisForLFunctions.RHTower.Deninger.DeningerMobiusFourierCommutator
import GaloisForLFunctions.HTGeometry.SchwartzCompactSupport

/-!
# Tempered-distribution FZZ reflection has forced essential local response

Finite complex measures are not the final nonlocal class: a completion could be a genuine tempered
distribution.  Full imaginary-order Mellin covariance is distributional Fourier covariance on
logarithmic delay.  Fourier injectivity forces the dressed distribution to be the reciprocal Dirac
target even in `𝓢'(ℝ,ℂ)`.

Global division by the logarithmic Fermi multiplier is unnecessary.  A fixed compact bump translated
to the reciprocal delay has a compactly supported inverse-dressed probe, obtained by multiplying by
`exp(exp x)+1`.  One necessary local source-fidelity identity therefore exposes the exact undressed
Dirac coefficient.  Along reciprocal ultraviolet depth that response is the existing forced local
FZZ weight and grows beyond every polynomial.

Thus no locally polynomially tempered distributional completion can implement universal complex
FZZ reflection.  No positivity, measure representation, moment condition, support condition on the
kernel, or global inverse multiplier is used.

`[FZZ-P ROUTE KILL] [TEMPERED DISTRIBUTION] [LOCAL PROBE] [CANDIDATE NEW KNOWLEDGE]`
-/

open Filter Topology Asymptotics MeasureTheory SchwartzMap FourierTransform
open scoped ContDiff ENNReal

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

/-- Smooth compact unit-scale probe centered at logarithmic delay `y`. -/
def fzzCigarParityTemperedProbeFunction (y x : ℝ) : ℂ :=
  ((cutoffScaled 1 (x - y) : ℝ) : ℂ)

private theorem contDiff_fzzCigarParityTemperedProbeFunction (y : ℝ) :
    ContDiff ℝ ∞ (fzzCigarParityTemperedProbeFunction y) := by
  exact Complex.ofRealCLM.contDiff.comp
    ((contDiff_cutoffScaled 1).comp (contDiff_id.sub contDiff_const))

private theorem hasCompactSupport_fzzCigarParityTemperedProbeFunction (y : ℝ) :
    HasCompactSupport (fzzCigarParityTemperedProbeFunction y) := by
  have hreal : HasCompactSupport (fun x : ℝ => cutoffScaled 1 (x - y)) := by
    have h := (hasCompactSupport_cutoffScaled (by norm_num : (0 : ℝ) < 1)).comp_homeomorph
      (Homeomorph.subRight y)
    simpa [Function.comp_def] using h
  exact hreal.comp_left (by simp)

/-- Canonical source-predeclared unit-scale local probe. -/
def fzzCigarParityTemperedProbe (y : ℝ) : 𝓢(ℝ, ℂ) :=
  schwartzOfCompactSupport
    (contDiff_fzzCigarParityTemperedProbeFunction y)
    (hasCompactSupport_fzzCigarParityTemperedProbeFunction y)

@[simp] theorem fzzCigarParityTemperedProbe_apply (y x : ℝ) :
    fzzCigarParityTemperedProbe y x =
      ((cutoffScaled 1 (x - y) : ℝ) : ℂ) := rfl

@[simp] theorem fzzCigarParityTemperedProbe_center (y : ℝ) :
    fzzCigarParityTemperedProbe y y = 1 := by
  rw [fzzCigarParityTemperedProbe_apply]
  norm_num [cutoffScaled_eq_one]

/-- Reciprocal logarithmic Fermi factor. -/
def fzzCigarParityLogReciprocalFermi (x : ℝ) : ℂ :=
  ((Real.exp (Real.exp x) + 1 : ℝ) : ℂ)

private theorem contDiff_fzzCigarParityLogReciprocalFermi :
    ContDiff ℝ ∞ fzzCigarParityLogReciprocalFermi := by
  exact Complex.ofRealCLM.contDiff.comp
    ((Real.contDiff_exp.comp Real.contDiff_exp).add contDiff_const)

/-- Compact inverse-dressed probe.  Despite the superexponential reciprocal factor, compact support
makes this a Schwartz function. -/
def fzzCigarParityTemperedInverseProbeFunction (y x : ℝ) : ℂ :=
  fzzCigarParityLogReciprocalFermi x *
    fzzCigarParityTemperedProbeFunction y x

private theorem contDiff_fzzCigarParityTemperedInverseProbeFunction (y : ℝ) :
    ContDiff ℝ ∞ (fzzCigarParityTemperedInverseProbeFunction y) :=
  contDiff_fzzCigarParityLogReciprocalFermi.mul
    (contDiff_fzzCigarParityTemperedProbeFunction y)

private theorem hasCompactSupport_fzzCigarParityTemperedInverseProbeFunction (y : ℝ) :
    HasCompactSupport (fzzCigarParityTemperedInverseProbeFunction y) := by
  exact (hasCompactSupport_fzzCigarParityTemperedProbeFunction y).mul_left

/-- Canonical compact inverse-dressed local probe. -/
def fzzCigarParityTemperedInverseProbe (y : ℝ) : 𝓢(ℝ, ℂ) :=
  schwartzOfCompactSupport
    (contDiff_fzzCigarParityTemperedInverseProbeFunction y)
    (hasCompactSupport_fzzCigarParityTemperedInverseProbeFunction y)

@[simp] theorem fzzCigarParityTemperedInverseProbe_apply (y x : ℝ) :
    fzzCigarParityTemperedInverseProbe y x =
      fzzCigarParityLogReciprocalFermi x *
        fzzCigarParityTemperedProbeFunction y x := rfl

@[simp] theorem fzzCigarParityTemperedInverseProbe_center (y : ℝ) :
    fzzCigarParityTemperedInverseProbe y y =
      ((Real.exp (Real.exp y) + 1 : ℝ) : ℂ) := by
  rw [fzzCigarParityTemperedInverseProbe_apply,
    fzzCigarParityTemperedProbeFunction]
  rw [cutoffScaled_eq_one (by norm_num) (by simp)]
  simp [fzzCigarParityLogReciprocalFermi]

/-- Point evaluation as a tempered Dirac distribution. -/
def fzzCigarParityTemperedDirac (y : ℝ) : 𝓢'(ℝ, ℂ) :=
  (BoundedContinuousFunction.evalCLM ℂ y).comp
    (SchwartzMap.toBoundedContinuousFunctionCLM ℂ ℝ ℂ)

@[simp] theorem fzzCigarParityTemperedDirac_apply (y : ℝ) (φ : 𝓢(ℝ, ℂ)) :
    fzzCigarParityTemperedDirac y φ = φ y := rfl

/-- Dressed reciprocal-delay mass `a F(t)` at logarithmic center `log a`. -/
def fzzCigarParityTemperedDressedMass (t : FZZCigarPositiveDelay) : ℝ :=
  (t : ℝ)⁻¹ * fzzCigarPositiveDelayDensity t

private theorem fzzCigarParityTemperedDressedMass_pos (t : FZZCigarPositiveDelay) :
    0 < fzzCigarParityTemperedDressedMass t := by
  rw [fzzCigarParityTemperedDressedMass, fzzCigarPositiveDelayDensity,
    fzzCigarParityDelay_eq_fermi t.property]
  exact mul_pos (inv_pos.mpr t.property) (by positivity)

/-- Dressed reciprocal Dirac target in logarithmic delay. -/
def fzzCigarParityTemperedTarget (t : FZZCigarPositiveDelay) : 𝓢'(ℝ, ℂ) :=
  ((fzzCigarParityTemperedDressedMass t : ℝ) : ℂ) •
    fzzCigarParityTemperedDirac (Real.log (t : ℝ)⁻¹)

@[simp] theorem fzzCigarParityTemperedTarget_apply
    (t : FZZCigarPositiveDelay) (φ : 𝓢(ℝ, ℂ)) :
    fzzCigarParityTemperedTarget t φ =
      ((fzzCigarParityTemperedDressedMass t : ℝ) : ℂ) *
        φ (Real.log (t : ℝ)⁻¹) := by
  rfl

/-- Fourier transform is injective on tempered distributions, proved directly from inverse Fourier
tests. -/
theorem temperedDistribution_eq_of_fourier_eq
    {T U : 𝓢'(ℝ, ℂ)} (h : 𝓕 T = 𝓕 U) : T = U := by
  ext φ
  have hv := congrArg (fun V : 𝓢'(ℝ, ℂ) => V (𝓕⁻ φ)) h
  change T (𝓕 (𝓕⁻ φ)) = U (𝓕 (𝓕⁻ φ)) at hv
  simpa using hv

/-- A source-faithful tempered-distribution completion.  `local_source_fidelity` is only the one
canonical compact-probe consequence of global reciprocal-Fermi dressing; no global multiplication
operator is assumed. -/
structure FZZCigarParityTemperedDistributionFEReflectionData where
  undressedKernel : FZZCigarPositiveDelay → 𝓢'(ℝ, ℂ)
  dressedKernel : FZZCigarPositiveDelay → 𝓢'(ℝ, ℂ)
  local_source_fidelity : ∀ t,
    dressedKernel t
        (fzzCigarParityTemperedInverseProbe (Real.log (t : ℝ)⁻¹)) =
      undressedKernel t
        (fzzCigarParityTemperedProbe (Real.log (t : ℝ)⁻¹))
  full_fourier_covariance : ∀ t,
    𝓕 (dressedKernel t) = 𝓕 (fzzCigarParityTemperedTarget t)

/-- Full complex-order covariance classifies the dressed distribution exactly. -/
theorem FZZCigarParityTemperedDistributionFEReflectionData.dressedKernel_eq_target
    (D : FZZCigarParityTemperedDistributionFEReflectionData)
    (t : FZZCigarPositiveDelay) :
    D.dressedKernel t = fzzCigarParityTemperedTarget t :=
  temperedDistribution_eq_of_fourier_eq (D.full_fourier_covariance t)

/-- The canonical undressed local response is exactly the forced reciprocal-Fermi singular
weight. -/
theorem FZZCigarParityTemperedDistributionFEReflectionData.undressedProbe_eq
    (D : FZZCigarParityTemperedDistributionFEReflectionData)
    (t : FZZCigarPositiveDelay) :
    D.undressedKernel t
        (fzzCigarParityTemperedProbe (Real.log (t : ℝ)⁻¹)) =
      (((t : ℝ)⁻¹ * (Real.exp (t : ℝ)⁻¹ + 1) /
          (Real.exp (t : ℝ) + 1) : ℝ) : ℂ) := by
  rw [← D.local_source_fidelity t, D.dressedKernel_eq_target t,
    fzzCigarParityTemperedTarget_apply,
    fzzCigarParityTemperedInverseProbe_center]
  have ha : 0 < (t : ℝ)⁻¹ := inv_pos.mpr t.property
  rw [Real.exp_log ha]
  rw [fzzCigarParityTemperedDressedMass, fzzCigarPositiveDelayDensity,
    fzzCigarParityDelay_eq_fermi t.property]
  push_cast
  have hden : Real.exp (t : ℝ) + 1 ≠ 0 := by positivity
  field_simp [hden]

/-- Norm of the canonical local response. -/
def FZZCigarParityTemperedDistributionFEReflectionData.localProbeResponse
    (D : FZZCigarParityTemperedDistributionFEReflectionData)
    (t : FZZCigarPositiveDelay) : ℝ :=
  ‖D.undressedKernel t
    (fzzCigarParityTemperedProbe (Real.log (t : ℝ)⁻¹))‖

theorem FZZCigarParityTemperedDistributionFEReflectionData.localProbeResponse_eq
    (D : FZZCigarParityTemperedDistributionFEReflectionData)
    (t : FZZCigarPositiveDelay) :
    D.localProbeResponse t =
      (t : ℝ)⁻¹ * (Real.exp (t : ℝ)⁻¹ + 1) /
        (Real.exp (t : ℝ) + 1) := by
  rw [FZZCigarParityTemperedDistributionFEReflectionData.localProbeResponse,
    D.undressedProbe_eq, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_pos]
  exact div_pos
    (mul_pos (inv_pos.mpr t.property) (by positivity)) (by positivity)

/-- Canonical local-probe response on the reciprocal-depth ultraviolet ray. -/
def FZZCigarParityTemperedDistributionFEReflectionData.uvLocalProbeResponse
    (D : FZZCigarParityTemperedDistributionFEReflectionData) (n : ℕ) : ℝ :=
  D.localProbeResponse (fzzCigarParityPositiveNonlocalUVDelay n)

theorem FZZCigarParityTemperedDistributionFEReflectionData.uvLocalProbeResponse_eq_forced
    (D : FZZCigarParityTemperedDistributionFEReflectionData) (n : ℕ) :
    D.uvLocalProbeResponse n =
      fzzCigarParityForcedLocalFEReflectionData.uvWeight n := by
  rw [FZZCigarParityTemperedDistributionFEReflectionData.uvLocalProbeResponse,
    D.localProbeResponse_eq,
    fzzCigarParityForcedLocalFEReflectionData.uvWeight_eq]
  simp [fzzCigarParityPositiveNonlocalUVDelay]

/-- Weak local polynomial tempering: even the one source-predeclared unit-scale moving probe has
at most polynomial response.  Every uniform polynomial family bound implies this condition. -/
def FZZCigarParityTemperedDistributionFEReflectionData.LocallyPolynomiallyTempered
    (D : FZZCigarParityTemperedDistributionFEReflectionData) : Prop :=
  ∃ K : ℕ, D.uvLocalProbeResponse =O[atTop]
    (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ K)

/-- A universally covariant tempered completion already fails the weakest canonical local
polynomial-tempering test. -/
theorem FZZCigarParityTemperedDistributionFEReflectionData.not_locallyPolynomiallyTempered
    (D : FZZCigarParityTemperedDistributionFEReflectionData) :
    ¬ D.LocallyPolynomiallyTempered := by
  rintro ⟨K, hK⟩
  have heq : D.uvLocalProbeResponse =
      fzzCigarParityForcedLocalFEReflectionData.uvWeight := by
    funext n
    exact D.uvLocalProbeResponse_eq_forced n
  rw [heq] at hK
  exact fzzCigarParityForcedLocalFEReflectionData.not_polynomiallyTempered ⟨K, hK⟩

/-- **[FZZ-P TEMPERED-DISTRIBUTION ROUTE KILL].**  No locally polynomially tempered family of
tempered distributions can implement universal complex-order reflection with even one canonical
local reciprocal-Fermi source-fidelity identity. -/
theorem no_locallyPolynomiallyTempered_FZZCigarParityTemperedDistributionFEReflectionData :
    ¬ ∃ D : FZZCigarParityTemperedDistributionFEReflectionData,
      D.LocallyPolynomiallyTempered := by
  rintro ⟨D, hD⟩
  exact D.not_locallyPolynomiallyTempered hD

end

end RHTower
