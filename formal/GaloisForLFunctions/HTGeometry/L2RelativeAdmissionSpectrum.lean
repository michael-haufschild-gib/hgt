import GaloisForLFunctions.HTGeometry.RelativeAdmissionSpectrumNaturalityLaw
import Mathlib.MeasureTheory.Function.LpSpace.Basic

open MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {α P : Type*} [MeasurableSpace α]

/-- Raw complex profiles whose square norm is integrable form the admitted sector of the identity
profile complex. -/
def memLpTwoSubmodule (μ : Measure α) : Submodule ℂ (α → ℂ) where
  carrier := {f | MemLp f 2 μ}
  zero_mem' := MemLp.zero
  add_mem' hf hg := hf.add hg
  smul_mem' c _ hf := hf.const_smul c

@[simp]
theorem mem_memLpTwoSubmodule (μ : Measure α) (f : α → ℂ) :
    f ∈ memLpTwoSubmodule μ ↔ MemLp f 2 μ :=
  Iff.rfl

/-- Every ordinary `L²` admission predicate is exactly a relative primitive spectrum for the
identity complex. -/
theorem relativeAdmissionSpectrum_id_eq_memLp
    (μ : Measure α) (x : P → α → ℂ) :
    relativeAdmissionSpectrum (memLpTwoSubmodule μ)
        (LinearMap.id : (α → ℂ) →ₗ[ℂ] (α → ℂ)) LinearMap.id x =
      {p | MemLp (x p) 2 μ} := by
  ext p
  change relativePrimitiveObstruction (memLpTwoSubmodule μ)
      (LinearMap.id : (α → ℂ) →ₗ[ℂ] (α → ℂ)) LinearMap.id (x p) = 0 ↔
    MemLp (x p) 2 μ
  simpa using
    (relativePrimitiveObstruction_eq_zero_iff_of_injective
      (memLpTwoSubmodule μ)
      (LinearMap.id : (α → ℂ) →ₗ[ℂ] (α → ℂ))
      LinearMap.id (x p) rfl Function.injective_id)

end

end GaloisForLFunctions.HTGeometry
