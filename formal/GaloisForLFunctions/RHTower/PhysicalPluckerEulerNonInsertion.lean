import GaloisForLFunctions.RHTower.PhysicalPluckerIntegralNuclearDensity
import GaloisForLFunctions.HTGeometry.FredholmEulerGermRigidity

/-!
# The physical Plücker density cannot be an Euler multiplicity (POINH-B)

Replacing a local Euler factor `(1 - z)⁻¹` by `det(1 - zT)⁻¹` changes the logarithmic germ from
`∑ zᵏ/k` to `∑ Tr(Tᵏ) zᵏ/k`.  Equality of germs forces `Tr Tᵏ = 1` for every `k`
(**(POINH.14a)**); already the quadratic coefficient `(1 - Tr T²)/2` of `det(1 - zT)` is nonzero for
the physical-overlap density, whose purity is strictly below one (**(POINH.14b)**).  Only pure
states `|e⟩⟨e|` carry the scalar Euler factor, and the physical density is not pure.
-/

open Filter Topology
open scoped InnerProductSpace
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace RHTower.HedenmalmThetaSource

open GaloisForLFunctions.HTGeometry

variable {ι : Type*} [DecidableEq ι] (b : HilbertBasis ι ℂ GammaSewnCriticalPhysicalPluckerHilbert)

theorem isHilbertSchmidt_normalizedPhysicalPluckerOperator :
    IsHilbertSchmidt normalizedPhysicalPluckerOperator := by
  obtain ⟨A, B, hA, -, hfac⟩ := normalizedPhysicalPluckerOperator_memSchattenClass_one.one_isTraceClass
  rw [hfac]
  exact hA.comp_right B

/-- **(POINH.14b).**  The quadratic Taylor coefficient of `det(1 - zT)` is `(1 - Tr T²)/2 ≠ 0`. -/
theorem taylorCoeff_two_detOneSub_normalizedPhysicalPluckerOperator :
    taylorCoeff (detOneSub b normalizedPhysicalPluckerOperator) 2 = (1 - pluckerPurity) / 2 ∧
      (1 - pluckerPurity : ℂ) / 2 ≠ 0 := by
  refine ⟨?_, ?_⟩
  · rw [taylorCoeff_detOneSub_two b isHilbertSchmidt_normalizedPhysicalPluckerOperator,
      opTrace_normalizedPhysicalPluckerOperator, sq,
      show normalizedPhysicalPluckerOperator ^ 2 =
        normalizedPhysicalPluckerOperator ∘L normalizedPhysicalPluckerOperator from sq _,
      opTrace_normalizedPhysicalPluckerOperator_sq, mul_one]
    rfl
  · have h := pluckerPurity_lt_one
    have hne : (1 - pluckerPurity : ℝ) ≠ 0 := by linarith
    exact div_ne_zero (by exact_mod_cast hne) two_ne_zero

/-- **POINH-B.**  No Fredholm-determinant insertion of `T` reproduces the literal Euler factor:
`det(1 - zT) ≠ 1 - z` as germs at `0`. -/
theorem not_eventually_detOneSub_eq_euler :
    ¬ ∀ᶠ z in 𝓝 (0 : ℂ), detOneSub b normalizedPhysicalPluckerOperator z = 1 - z := by
  intro h
  have hn := (norm_normalizedPhysicalPluckerOperator_lt_one).2.le
  have h2 := opTrace_pow_eq_one_of_detOneSub_eq_euler b
    isHilbertSchmidt_normalizedPhysicalPluckerOperator hn h 2 (by norm_num)
  rw [show normalizedPhysicalPluckerOperator ^ 2 =
    normalizedPhysicalPluckerOperator ∘L normalizedPhysicalPluckerOperator from sq _,
    opTrace_normalizedPhysicalPluckerOperator_sq] at h2
  have := pluckerPurity_lt_one
  have h2' : pluckerPurity = 1 := by exact_mod_cast h2
  linarith

/-- **(POINH.14a).**  A germ equality would force every trace power to equal one. -/
theorem opTrace_pow_eq_one_of_detOneSub_normalized_eq_euler
    (h : ∀ᶠ z in 𝓝 (0 : ℂ), detOneSub b normalizedPhysicalPluckerOperator z = 1 - z) :
    ∀ k, 1 ≤ k → opTrace (normalizedPhysicalPluckerOperator ^ k) = 1 :=
  opTrace_pow_eq_one_of_detOneSub_eq_euler b isHilbertSchmidt_normalizedPhysicalPluckerOperator
    (norm_normalizedPhysicalPluckerOperator_lt_one).2.le h

/-- The physical density is not a pure state. -/
theorem normalizedPhysicalPluckerOperator_ne_rankOne (e : GammaSewnCriticalPhysicalPluckerHilbert) :
    normalizedPhysicalPluckerOperator ≠ rankOne ℂ e e := by
  intro h
  apply not_finiteDimensional_pluckerHilbert
  have hrange : ∀ x, normalizedPhysicalPluckerOperator x ∈ (ℂ ∙ e) := fun x => by
    rw [h, rankOne_apply]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self e)
  haveI : FiniteDimensional ℂ (ℂ ∙ e) := FiniteDimensional.span_singleton ℂ e
  exact Module.Finite.of_injective
    ((normalizedPhysicalPluckerOperator : _ →ₗ[ℂ] _).codRestrict (ℂ ∙ e) hrange)
    (fun x y hxy => normalizedPhysicalPluckerOperator_injective (by
      simpa using congrArg Subtype.val hxy))

end RHTower.HedenmalmThetaSource
