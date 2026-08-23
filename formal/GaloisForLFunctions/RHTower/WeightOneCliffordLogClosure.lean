import GaloisForLFunctions.RHTower.WeightOneCliffordSpectralClosure

/-!
# Closed weight-one Clifford--Dirac operator on the log line

Unitary Fourier transport of the closed spectral Dirac operator and its self-adjoint maximal
quadratic square, with exact natural-domain and composition identities.
-/

noncomputable section

set_option maxHeartbeats 1000000

open MeasureTheory Set Filter
open scoped ENNReal LinearPMap

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

theorem weightOneLogDirac_isClosed (a : ℝ) : (weightOneLogDirac a).IsClosed :=
  GaloisForLFunctions.HTGeometry.LinearPMap.IsClosed.unitaryConjugate
    (weightOneSpectralDirac_isClosed a)

theorem weightOneLogSquare_isSelfAdjoint (a : ℝ) :
    IsSelfAdjoint (weightOneLogSquare a) :=
  GaloisForLFunctions.HTGeometry.IsSelfAdjoint.unitaryConjugate fourierUnitary
    (weightOneSpectralSquare_isSelfAdjoint a)

@[simp] theorem fourierUnitary_weightOneLogDirac_apply (a : ℝ)
    (f : (weightOneLogDirac a).domain) :
    fourierUnitary (weightOneLogDirac a f) =
      weightOneSpectralDirac a
        (GaloisForLFunctions.HTGeometry.unitaryConjugateDomainMap
          fourierUnitary (weightOneSpectralDirac a) f) := by
  simp only [weightOneLogDirac,
    GaloisForLFunctions.HTGeometry.unitaryConjugateLinearPMap_apply,
    LinearIsometryEquiv.apply_symm_apply]

theorem weightOneLogSquare_domain_le_dirac (a : ℝ) :
    (weightOneLogSquare a).domain ≤ (weightOneLogDirac a).domain := by
  intro f hf
  exact weightOneSpectralSquare_domain_le_dirac a hf

/-- Explicit natural-domain criterion. Once `f ∈ D(Q_a)` is fixed, membership in the square
domain is equivalent to `Q_a f ∈ D(Q_a)`. -/
theorem weightOneLogSquare_mem_iff_dirac_apply_mem (a : ℝ) (f : SoninL2)
    (hf : f ∈ (weightOneLogDirac a).domain) :
    f ∈ (weightOneLogSquare a).domain ↔
      weightOneLogDirac a ⟨f, hf⟩ ∈ (weightOneLogDirac a).domain := by
  let fspec : (weightOneSpectralDirac a).domain :=
    GaloisForLFunctions.HTGeometry.unitaryConjugateDomainMap
      fourierUnitary (weightOneSpectralDirac a) ⟨f, hf⟩
  change fourierUnitary f ∈ (weightOneSpectralSquare a).domain ↔
    fourierUnitary (weightOneLogDirac a ⟨f, hf⟩) ∈
      (weightOneSpectralDirac a).domain
  rw [fourierUnitary_weightOneLogDirac_apply]
  exact weightOneSpectralSquare_mem_iff_dirac_apply_mem a (fourierUnitary f)
    fspec.property

/-- The log-line natural square is exactly the unitary transport of the maximal quadratic-energy
multiplier. -/
theorem weightOneLogDirac_sq_apply (a : ℝ)
    (f : (weightOneLogSquare a).domain)
    (hf : (f : SoninL2) ∈ (weightOneLogDirac a).domain)
    (hQ : weightOneLogDirac a ⟨(f : SoninL2), hf⟩ ∈
      (weightOneLogDirac a).domain) :
    weightOneLogDirac a ⟨weightOneLogDirac a ⟨(f : SoninL2), hf⟩, hQ⟩ =
      weightOneLogSquare a f := by
  let fsq : (weightOneSpectralSquare a).domain :=
    GaloisForLFunctions.HTGeometry.unitaryConjugateDomainMap
      fourierUnitary (weightOneSpectralSquare a) f
  let fspec : (weightOneSpectralDirac a).domain :=
    GaloisForLFunctions.HTGeometry.unitaryConjugateDomainMap
      fourierUnitary (weightOneSpectralDirac a) ⟨(f : SoninL2), hf⟩
  have hQspec : weightOneSpectralDirac a fspec ∈
      (weightOneSpectralDirac a).domain := by
    change fourierUnitary (weightOneLogDirac a ⟨(f : SoninL2), hf⟩) ∈
      (weightOneSpectralDirac a).domain at hQ
    rw [fourierUnitary_weightOneLogDirac_apply] at hQ
    exact hQ
  apply fourierUnitary.injective
  calc
    fourierUnitary
        (weightOneLogDirac a
          ⟨weightOneLogDirac a ⟨(f : SoninL2), hf⟩, hQ⟩) =
        weightOneSpectralDirac a
          ⟨weightOneSpectralDirac a fspec, hQspec⟩ := by
      rw [fourierUnitary_weightOneLogDirac_apply]
      congr 2
      apply Subtype.ext
      rw [fourierUnitary_weightOneLogDirac_apply]
    _ = weightOneSpectralSquare a fsq :=
      weightOneSpectralDirac_sq_apply a fsq fspec.property hQspec
    _ = fourierUnitary (weightOneLogSquare a f) := by
      simp only [weightOneLogSquare,
        GaloisForLFunctions.HTGeometry.unitaryConjugateLinearPMap_apply,
        LinearIsometryEquiv.apply_symm_apply]

end RHTower

