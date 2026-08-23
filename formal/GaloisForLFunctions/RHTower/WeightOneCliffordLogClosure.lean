import GaloisForLFunctions.HTGeometry.LinearPMapUnitarySquareTransport
import GaloisForLFunctions.RHTower.L2WeakDerivativeUniqueness
import GaloisForLFunctions.RHTower.VectorL2FourierMultiplicationDerivative
import GaloisForLFunctions.RHTower.WeightOneCliffordSpectralClosure

/-!
# Closed weight-one Clifford--Dirac operator on the log line

Unitary Fourier transport of the closed spectral Dirac operator and its self-adjoint maximal
quadratic square, with exact natural-domain and composition identities.
-/

noncomputable section

set_option maxHeartbeats 1000000

open MeasureTheory Set Filter FourierTransform LineDeriv
open scoped ENNReal LinearPMap SchwartzMap LineDeriv

namespace RHTower

/-- Closed log-line realization of `∂ₓ + aR`, obtained by inverse Fourier transport. -/
def weightOneLogDirac (a : ℝ) : SoninL2 →ₗ.[ℂ] SoninL2 :=
  GaloisForLFunctions.HTGeometry.unitaryConjugateLinearPMap fourierUnitary
    (weightOneSpectralDirac a)

/-- Self-adjoint log-line square transported from the maximal real spectral multiplier. -/
def weightOneLogSquare (a : ℝ) : SoninL2 →ₗ.[ℂ] SoninL2 :=
  GaloisForLFunctions.HTGeometry.unitaryConjugateLinearPMap fourierUnitary
    (weightOneSpectralSquare a)

@[simp] theorem weightOneLogDirac_domain (a : ℝ) :
    (weightOneLogDirac a).domain =
      (weightOneSpectralDirac a).domain.comap
        fourierUnitary.toLinearEquiv.toLinearMap := rfl

@[simp] theorem weightOneLogSquare_domain (a : ℝ) :
    (weightOneLogSquare a).domain =
      (weightOneSpectralSquare a).domain.comap
        fourierUnitary.toLinearEquiv.toLinearMap := rfl

/-- The closed Dirac domain is exactly the standard Fourier realization of `H¹(ℝ)`. -/
theorem weightOneLogDirac_domain_eq_fourierL2H1 (a : ℝ) :
    (weightOneLogDirac a).domain = fourierL2H1 := by
  ext f
  change MemLp (fun ξ : ℝ => (ξ : ℂ) *
      (fourierUnitary f : ℝ → ℂ) ξ) 2 volume ↔
    MemLp (fun ξ : ℝ => ((ξ ^ 1 : ℝ) : ℂ) *
      (fourierUnitary f : ℝ → ℂ) ξ) 2 volume
  simp only [pow_one]

/-- The self-adjoint square domain is exactly the standard Fourier realization of `H²(ℝ)`. -/
theorem weightOneLogSquare_domain_eq_fourierL2H2 (a : ℝ) :
    (weightOneLogSquare a).domain = fourierL2H2 := by
  ext f
  exact weightOneSpectralSquare_domain_iff_squareCoordinate a (fourierUnitary f)

theorem weightOneLogDirac_isClosed (a : ℝ) : (weightOneLogDirac a).IsClosed :=
  GaloisForLFunctions.HTGeometry.LinearPMap.IsClosed.unitaryConjugate
    (weightOneSpectralDirac_isClosed a)

theorem weightOneLogSquare_isSelfAdjoint (a : ℝ) :
    IsSelfAdjoint (weightOneLogSquare a) :=
  GaloisForLFunctions.HTGeometry.IsSelfAdjoint.unitaryConjugate fourierUnitary
    (weightOneSpectralSquare_isSelfAdjoint a)

/-- Closed weak derivative on the log line, defined by the exact Fourier multiplier. -/
def weightOneLogDerivative : SoninL2 →ₗ.[ℂ] SoninL2 :=
  GaloisForLFunctions.HTGeometry.unitaryConjugateLinearPMap fourierUnitary
    weightOneSpectralDerivative

@[simp] theorem weightOneLogDerivative_domain :
    weightOneLogDerivative.domain =
      weightOneSpectralDerivative.domain.comap
        fourierUnitary.toLinearEquiv.toLinearMap := rfl

/-- The closed weak-derivative domain is exactly `H¹(ℝ)`. -/
theorem weightOneLogDerivative_domain_eq_fourierL2H1 :
    weightOneLogDerivative.domain = fourierL2H1 := by
  ext f
  change MemLp (fun ξ : ℝ => (ξ : ℂ) *
      (fourierUnitary f : ℝ → ℂ) ξ) 2 volume ↔
    MemLp (fun ξ : ℝ => ((ξ ^ 1 : ℝ) : ℂ) *
      (fourierUnitary f : ℝ → ℂ) ξ) 2 volume
  simp only [pow_one]

/-- The Fourier-multiplier derivative is the actual `L²` distributional derivative. -/
theorem weightOneLogDerivative_isWeakDerivative
    (f : weightOneLogDerivative.domain) :
    ∂_{(1 : ℝ)} (((f : SoninL2) : 𝓢'(ℝ, ℂ))) =
      ((weightOneLogDerivative f : SoninL2) : 𝓢'(ℝ, ℂ)) := by
  let F : SoninL2 := fourierUnitary (f : SoninL2)
  have hF : F ∈ weightOneSpectralCoordinate.domain := f.property
  let M : SoninL2 := weightOneSpectralCoordinate ⟨F, hF⟩
  have hM : (M : ℝ → ℂ) =ᵐ[volume]
      fun ξ : ℝ => (ξ : ℂ) • (F : ℝ → ℂ) ξ := by
    simpa only [M, weightOneSpectralCoordinate, smul_eq_mul, id_eq] using
      (GaloisForLFunctions.HTGeometry.maximalRealL2Mul_apply_ae volume id ⟨F, hF⟩)
  have hdistM : (M : 𝓢'(ℝ, ℂ)) =
      TemperedDistribution.smulLeftCLM ℂ (fun ξ : ℝ => inner ℝ ξ (1 : ℝ))
        (F : 𝓢'(ℝ, ℂ)) :=
    l2_smulLeft_toTemperedDistribution F M hM
  have hFg : fourierUnitary (weightOneLogDerivative f) =
      (2 * Real.pi * Complex.I : ℂ) • M := by
    simp only [weightOneLogDerivative,
      GaloisForLFunctions.HTGeometry.unitaryConjugateLinearPMap_apply,
      LinearIsometryEquiv.apply_symm_apply, weightOneSpectralDerivative,
      LinearPMap.smul_apply]
    rfl
  have hFourier :
      𝓕 (∂_{(1 : ℝ)} (((f : SoninL2) : 𝓢'(ℝ, ℂ)))) =
        𝓕 (((weightOneLogDerivative f : SoninL2) : 𝓢'(ℝ, ℂ))) := by
    rw [TemperedDistribution.fourier_lineDerivOp_eq,
      MeasureTheory.Lp.fourier_toTemperedDistribution_eq,
      MeasureTheory.Lp.fourier_toTemperedDistribution_eq]
    change (2 * Real.pi * Complex.I : ℂ) •
        TemperedDistribution.smulLeftCLM ℂ (fun ξ : ℝ => inner ℝ ξ (1 : ℝ))
          (F : 𝓢'(ℝ, ℂ)) =
      ((fourierUnitary (weightOneLogDerivative f) : SoninL2) : 𝓢'(ℝ, ℂ))
    rw [hFg]
    change _ = ((MeasureTheory.Lp.toTemperedDistributionCLM ℂ volume 2)
      ((2 * Real.pi * Complex.I : ℂ) • M))
    rw [map_smul]
    change _ = (2 * Real.pi * Complex.I : ℂ) • (M : 𝓢'(ℝ, ℂ))
    rw [hdistM]
  calc
    ∂_{(1 : ℝ)} (((f : SoninL2) : 𝓢'(ℝ, ℂ))) =
        𝓕⁻ (𝓕 (∂_{(1 : ℝ)} (((f : SoninL2) : 𝓢'(ℝ, ℂ))))) :=
      (fourierInv_fourier_eq _).symm
    _ = 𝓕⁻ (𝓕 (((weightOneLogDerivative f : SoninL2) : 𝓢'(ℝ, ℂ)))) := by
      rw [hFourier]
    _ = ((weightOneLogDerivative f : SoninL2) : 𝓢'(ℝ, ℂ)) :=
      fourierInv_fourier_eq _

/-- Exact weak-Sobolev characterization: `H¹(ℝ)` consists precisely of `L²` vectors having
an `L²` distributional derivative. -/
theorem mem_fourierL2H1_iff_exists_weakDerivative (f : SoninL2) :
    f ∈ fourierL2H1 ↔
      ∃ g : SoninL2, ∂_{(1 : ℝ)} (f : 𝓢'(ℝ, ℂ)) = (g : 𝓢'(ℝ, ℂ)) := by
  constructor
  · intro hf
    have hfD : f ∈ weightOneLogDerivative.domain := by
      rw [weightOneLogDerivative_domain_eq_fourierL2H1]
      exact hf
    exact ⟨weightOneLogDerivative ⟨f, hfD⟩,
      weightOneLogDerivative_isWeakDerivative ⟨f, hfD⟩⟩
  · rintro ⟨g, hweak⟩
    rw [← weightOneLogDerivative_domain_eq_fourierL2H1]
    change MemLp (fun ξ : ℝ => (ξ : ℂ) *
      (fourierUnitary f : ℝ → ℂ) ξ) 2 volume
    have hFourier := l2_fourier_weakDerivative_ae f g hweak
    change (fourierUnitary g : ℝ → ℂ) =ᵐ[volume]
      fun ξ : ℝ => (2 * Real.pi * Complex.I * ξ) •
        (fourierUnitary f : ℝ → ℂ) ξ at hFourier
    have hscaled : MemLp (fun ξ : ℝ =>
        (2 * Real.pi * Complex.I : ℂ)⁻¹ * (fourierUnitary g : ℝ → ℂ) ξ)
        2 volume :=
      (Lp.memLp (fourierUnitary g)).const_mul
        (2 * Real.pi * Complex.I : ℂ)⁻¹
    refine (memLp_congr_ae ?_).mpr hscaled
    filter_upwards [hFourier] with ξ hξ
    rw [hξ]
    change (ξ : ℂ) * (fourierUnitary f : ℝ → ℂ) ξ =
      (2 * Real.pi * Complex.I : ℂ)⁻¹ *
        ((2 * Real.pi * Complex.I : ℂ) * (ξ : ℂ) *
          (fourierUnitary f : ℝ → ℂ) ξ)
    have hc : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
      exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero))
        Complex.I_ne_zero
    field_simp

@[simp] theorem fourierUnitary_weightOneLogDirac_apply (a : ℝ)
    (f : (weightOneLogDirac a).domain) :
    fourierUnitary (weightOneLogDirac a f) =
      weightOneSpectralDirac a
        (GaloisForLFunctions.HTGeometry.unitaryConjugateDomainMap
          fourierUnitary (weightOneSpectralDirac a) f) := by
  simp only [weightOneLogDirac,
    GaloisForLFunctions.HTGeometry.unitaryConjugateLinearPMap_apply,
    LinearIsometryEquiv.apply_symm_apply]

/-- The transported Dirac operator is exactly `∂ₓ + aR` on its maximal first-order domain. -/
theorem weightOneLogDirac_apply_eq_derivative_add_reflection (a : ℝ)
    (f : (weightOneLogDirac a).domain) :
    let hfD : (f : SoninL2) ∈ weightOneLogDerivative.domain := f.property
    weightOneLogDirac a f =
      (a : ℂ) • l2Reflection (f : SoninL2) +
        weightOneLogDerivative ⟨(f : SoninL2), hfD⟩ := by
  dsimp only
  apply fourierUnitary.injective
  rw [fourierUnitary_weightOneLogDirac_apply]
  rw [map_add, map_smul, fourierUnitary_l2Reflection]
  simp only [weightOneLogDerivative,
    GaloisForLFunctions.HTGeometry.unitaryConjugateLinearPMap_apply,
    LinearIsometryEquiv.apply_symm_apply]
  rw [weightOneSpectralDirac_apply]
  congr 2

/-- At Clifford mass `a = 0`, the log-line Dirac operator is exactly the weak derivative. -/
theorem weightOneLogDirac_zero_apply
    (f : (weightOneLogDirac 0).domain) :
    weightOneLogDirac 0 f =
      weightOneLogDerivative ⟨(f : SoninL2), f.property⟩ := by
  simpa using (weightOneLogDirac_apply_eq_derivative_add_reflection 0 f)

theorem weightOneLogSquare_domain_le_dirac (a : ℝ) :
    (weightOneLogSquare a).domain ≤ (weightOneLogDirac a).domain := by
  exact GaloisForLFunctions.HTGeometry.unitaryConjugate_domain_le_of_domain_le
    fourierUnitary (weightOneSpectralSquare_domain_le_dirac a)

/-- Explicit natural-domain criterion. Once `f ∈ D(Q_a)` is fixed, membership in the square
domain is equivalent to `Q_a f ∈ D(Q_a)`. -/
theorem weightOneLogSquare_mem_iff_dirac_apply_mem (a : ℝ) (f : SoninL2)
    (hf : f ∈ (weightOneLogDirac a).domain) :
    f ∈ (weightOneLogSquare a).domain ↔
      weightOneLogDirac a ⟨f, hf⟩ ∈ (weightOneLogDirac a).domain := by
  exact GaloisForLFunctions.HTGeometry.unitaryConjugate_mem_iff_apply_mem
    fourierUnitary
    (fun x hx => weightOneSpectralSquare_mem_iff_dirac_apply_mem a x hx) f hf

/-- The log-line natural square is exactly the unitary transport of the maximal quadratic-energy
multiplier. -/
theorem weightOneLogDirac_sq_apply (a : ℝ)
    (f : (weightOneLogSquare a).domain)
    (hf : (f : SoninL2) ∈ (weightOneLogDirac a).domain)
    (hQ : weightOneLogDirac a ⟨(f : SoninL2), hf⟩ ∈
      (weightOneLogDirac a).domain) :
    weightOneLogDirac a ⟨weightOneLogDirac a ⟨(f : SoninL2), hf⟩, hQ⟩ =
      weightOneLogSquare a f := by
  exact GaloisForLFunctions.HTGeometry.unitaryConjugate_square_apply
    fourierUnitary
    (fun x hx hQ => weightOneSpectralDirac_sq_apply a x hx hQ) f hf hQ

/-- Exact second-order weak-Sobolev characterization: `H²(ℝ)` consists precisely of `L²`
vectors admitting two successive `L²` distributional derivatives. -/
theorem mem_fourierL2H2_iff_exists_two_weakDerivatives (f : SoninL2) :
    f ∈ fourierL2H2 ↔
      ∃ g₁ g₂ : SoninL2,
        ∂_{(1 : ℝ)} (f : 𝓢'(ℝ, ℂ)) = (g₁ : 𝓢'(ℝ, ℂ)) ∧
        ∂_{(1 : ℝ)} (g₁ : 𝓢'(ℝ, ℂ)) = (g₂ : 𝓢'(ℝ, ℂ)) := by
  constructor
  · intro hfH2
    have hfSquare : f ∈ (weightOneLogSquare 0).domain := by
      rw [weightOneLogSquare_domain_eq_fourierL2H2]
      exact hfH2
    have hfQ : f ∈ (weightOneLogDirac 0).domain :=
      weightOneLogSquare_domain_le_dirac 0 hfSquare
    have hQ : weightOneLogDirac 0 ⟨f, hfQ⟩ ∈
        (weightOneLogDirac 0).domain :=
      (weightOneLogSquare_mem_iff_dirac_apply_mem 0 f hfQ).1 hfSquare
    have hfD : f ∈ weightOneLogDerivative.domain := hfQ
    let g₁ : SoninL2 := weightOneLogDerivative ⟨f, hfD⟩
    have hQeq : weightOneLogDirac 0 ⟨f, hfQ⟩ = g₁ :=
      weightOneLogDirac_zero_apply ⟨f, hfQ⟩
    have hg₁D : g₁ ∈ weightOneLogDerivative.domain := by
      rw [← hQeq]
      exact hQ
    let g₂ : SoninL2 := weightOneLogDerivative ⟨g₁, hg₁D⟩
    exact ⟨g₁, g₂, weightOneLogDerivative_isWeakDerivative ⟨f, hfD⟩,
      weightOneLogDerivative_isWeakDerivative ⟨g₁, hg₁D⟩⟩
  · rintro ⟨g₁, g₂, h₁, h₂⟩
    have hfH1 : f ∈ fourierL2H1 :=
      (mem_fourierL2H1_iff_exists_weakDerivative f).2 ⟨g₁, h₁⟩
    have hg₁H1 : g₁ ∈ fourierL2H1 :=
      (mem_fourierL2H1_iff_exists_weakDerivative g₁).2 ⟨g₂, h₂⟩
    have hfD : f ∈ weightOneLogDerivative.domain := by
      rw [weightOneLogDerivative_domain_eq_fourierL2H1]
      exact hfH1
    have hg₁D : g₁ ∈ weightOneLogDerivative.domain := by
      rw [weightOneLogDerivative_domain_eq_fourierL2H1]
      exact hg₁H1
    have hDweak := weightOneLogDerivative_isWeakDerivative ⟨f, hfD⟩
    have hD_eq : weightOneLogDerivative ⟨f, hfD⟩ = g₁ :=
      l2_weakDerivative_unique f (weightOneLogDerivative ⟨f, hfD⟩) g₁ hDweak h₁
    have hfQ : f ∈ (weightOneLogDirac 0).domain := hfD
    have hQeq : weightOneLogDirac 0 ⟨f, hfQ⟩ =
        weightOneLogDerivative ⟨f, hfD⟩ :=
      weightOneLogDirac_zero_apply ⟨f, hfQ⟩
    have hQ : weightOneLogDirac 0 ⟨f, hfQ⟩ ∈
        (weightOneLogDirac 0).domain := by
      rw [hQeq, hD_eq]
      exact hg₁D
    rw [← weightOneLogSquare_domain_eq_fourierL2H2]
    exact (weightOneLogSquare_mem_iff_dirac_apply_mem 0 f hfQ).2 hQ

end RHTower
