import GaloisForLFunctions.RHTower.HardyTitchmarshEulerConcrete
import GaloisForLFunctions.RHTower.Suzuki.SuzukiPositiveHalfLine
import GaloisForLFunctions.HTGeometry.DilationSpectralType
import GaloisForLFunctions.HTGeometry.PullbackCompletion
import GaloisForLFunctions.HTGeometry.ResolventCompactness

/-!
# The dilation generator has no point spectrum

The logarithmic Jacobian identifies physical `L²` of the positive half line with even `L²` of the
line, and the Mellin--Fourier unitary sends that to `L²` of the spectral line.  In the spectral
coordinate the generator of dilations is multiplication by the spectral variable, whose level sets
are single points.  So the dilation generator is self-adjoint with no eigenvectors, it has no
compact resolvent, no bounded perturbation of it has one, and no operator that restricts it to a
pullback completion has an eigenvector.
-/

open MeasureTheory
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

/-- The physical-to-spectral unitary: the logarithmic Jacobian followed by Mellin--Fourier. -/
def physicalToSpectralUnitary : SuzukiPositiveL2 ≃ₗᵢ[ℂ] SpectralL2 :=
  suzukiPositiveHalfLineUnitary.symm.trans archimedeanMellinUnitary

/-- The spectral symbol of the dilation generator. -/
def dilationSymbol (c : ℝ) : ℝ → ℝ := fun s => c * s

theorem measurable_dilationSymbol (c : ℝ) : Measurable (dilationSymbol c) :=
  measurable_const.mul measurable_id

/-- The dilation generator on the physical half line, defined by its spectral diagonalization: in
the Mellin coordinate it is multiplication by a nonzero multiple of the spectral variable. -/
def dilationGenerator (c : ℝ) : SuzukiPositiveL2 →ₗ.[ℂ] SuzukiPositiveL2 :=
  unitaryConjugateLinearPMap physicalToSpectralUnitary
    (maximalRealL2Mul volume (dilationSymbol c))

/-- **The spectral diagonalization.**  In the Mellin coordinate the dilation generator is exactly
multiplication by the spectral variable: its spectral measure is Lebesgue measure on the line, so
its spectrum is the whole line and is purely absolutely continuous. -/
theorem dilationGenerator_eq_unitaryConjugate (c : ℝ) :
    dilationGenerator c =
      unitaryConjugateLinearPMap physicalToSpectralUnitary
        (maximalRealL2Mul volume (dilationSymbol c)) := rfl

/-- **The dilation generator is self-adjoint.** -/
theorem isSelfAdjoint_dilationGenerator (c : ℝ) : IsSelfAdjoint (dilationGenerator c) :=
  IsSelfAdjoint.unitaryConjugate physicalToSpectralUnitary
    (maximalRealL2Mul_isSelfAdjoint volume (measurable_dilationSymbol c))

/-- **`(12)`.**  The dilation generator has no eigenvectors at any complex parameter. -/
theorem hasNoEigenvector_dilationGenerator {c : ℝ} (hc : c ≠ 0) :
    HasNoEigenvector (dilationGenerator c) := by
  refine hasNoEigenvector_unitaryConjugate _ (hasNoEigenvector_maximalRealL2Mul fun lam => ?_)
  exact volume_realLinearSymbol_level_eq_zero hc lam

/-- **The dilation generator has no compact resolvent.** -/
theorem not_isCompactOperator_resolvent_dilationGenerator {c : ℝ} (hc : c ≠ 0)
    [Nontrivial SuzukiPositiveL2] {z w : ℂ} (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hzw : w = (starRingEnd ℂ) z) :
    ¬ IsCompactOperator (resolventCLM (isSelfAdjoint_dilationGenerator c) hz) :=
  not_isCompactOperator_resolventCLM (isSelfAdjoint_dilationGenerator c)
    (hasNoEigenvector_dilationGenerator hc) hz hw hzw

/-- **No bounded perturbation of the dilation generator has a compact resolvent.**  This is the
elementary form of the compact and trace-class exclusions. -/
theorem not_isCompactOperator_boundedPerturbation_dilationGenerator {c : ℝ} (hc : c ≠ 0)
    [Nontrivial SuzukiPositiveL2] {z w : ℂ} (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hzw : w = (starRingEnd ℂ) z) (K Q : SuzukiPositiveL2 →L[ℂ] SuzukiPositiveL2)
    (hQ : ∀ x : (dilationGenerator c).domain,
      Q (dilationGenerator c x - z • (x : SuzukiPositiveL2) + K (x : SuzukiPositiveL2)) =
        (x : SuzukiPositiveL2)) :
    ¬ IsCompactOperator Q :=
  not_isCompactOperator_of_boundedPerturbation (isSelfAdjoint_dilationGenerator c)
    (hasNoEigenvector_dilationGenerator hc) hz hw hzw K Q hQ

/-- **The BBM pullback verdict for the dilation generator.**  No operator on a pullback completion
that restricts the dilation generator has an eigenvector, so the boundary equation cannot produce
point spectrum in such a completion. -/
theorem pullbackCompletion_dilation_hasNoEigenvector {D : Type*} [AddCommGroup D] [Module ℂ D]
    {c : ℝ} (hc : c ≠ 0) (Δ : D →ₗ[ℂ] SuzukiPositiveL2)
    {B : (pullbackSpace Δ) →ₗ.[ℂ] (pullbackSpace Δ)}
    (hres : IsPMapRestriction (dilationGenerator c) (pullbackSpace Δ) B) :
    HasNoEigenvector B :=
  hasNoEigenvector_of_restriction hres (hasNoEigenvector_dilationGenerator hc)

/-- **The pullback completion reduces the dilation generator.** -/
theorem pullbackCompletion_dilation_resolvent_mem {D : Type*} [AddCommGroup D] [Module ℂ D]
    (c : ℝ) (Δ : D →ₗ[ℂ] SuzukiPositiveL2)
    {B : (pullbackSpace Δ) →ₗ.[ℂ] (pullbackSpace Δ)} (hB : IsSelfAdjoint B)
    (hres : IsPMapRestriction (dilationGenerator c) (pullbackSpace Δ) B) {z : ℂ}
    (hz : z.im ≠ 0) {y : SuzukiPositiveL2} (hy : y ∈ pullbackSpace Δ)
    {x : (dilationGenerator c).domain} (hx : shiftedMap (dilationGenerator c) z x = y) :
    (x : SuzukiPositiveL2) ∈ pullbackSpace Δ :=
  mem_of_shiftedMap_eq (isSelfAdjoint_dilationGenerator c) hB hres hz hy hx

end RHTower
