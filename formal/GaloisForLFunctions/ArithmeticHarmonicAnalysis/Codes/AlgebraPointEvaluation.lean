import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Pi

/-!
# Interpolation at distinct algebra points

Independent linear functionals evaluate onto a finite coordinate space:
a proper image would have a nonzero annihilator, contradicting their
independence. Dedekind independence applies this to distinct algebra
homomorphisms into the scalar field, giving interpolation on any finite
family of rational algebra points.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis.Codes

/-- A finite independent family of linear functionals admits arbitrary simultaneous values. -/
theorem independent_functionalEvaluation_surjective
    {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V] [Fintype ι]
    (ℓ : ι → V →ₗ[K] K) (hℓ : LinearIndependent K ℓ) :
    Function.Surjective (LinearMap.pi ℓ) := by
  classical
  rw [← LinearMap.range_eq_top]
  by_contra hne
  obtain ⟨f, hf0, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
  let c : ι → K := fun i => f (fun j => if i = j then 1 else 0)
  have hrel : (∑ i, c i • ℓ i) = 0 := by
    apply LinearMap.ext
    intro x
    have h := hle (LinearMap.mem_range_self (LinearMap.pi ℓ) x)
    rw [LinearMap.mem_ker, LinearMap.pi_apply_eq_sum_univ] at h
    simpa only [c, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.zero_apply,
      LinearMap.pi_apply, smul_eq_mul, mul_comm] using h
  have hc : ∀ i, c i = 0 := (Fintype.linearIndependent_iff.mp hℓ) c hrel
  apply hf0
  apply LinearMap.ext
  intro v
  rw [LinearMap.pi_apply_eq_sum_univ, LinearMap.zero_apply]
  apply Finset.sum_eq_zero
  intro i _
  rw [smul_eq_mul]
  change v i * c i = 0
  rw [hc i, mul_zero]

variable {K B ι : Type*} [Field K] [CommRing B] [Algebra K B]

/-- Simultaneous evaluation at a family of rational algebra points. -/
def algebraPointEvaluation (φ : ι → B →ₐ[K] K) : B →ₗ[K] (ι → K) :=
  LinearMap.pi (fun i => (φ i).toLinearMap)

/-- Distinct rational algebra points can be interpolated independently. -/
theorem algebraPointEvaluation_surjective [Fintype ι]
    (φ : ι → B →ₐ[K] K) (hφ : Function.Injective φ) :
    Function.Surjective (algebraPointEvaluation φ) :=
  independent_functionalEvaluation_surjective _
    ((linearIndependent_algHom_toLinearMap K B K).comp φ hφ)

end GaloisForLFunctions.ArithmeticHarmonicAnalysis.Codes
