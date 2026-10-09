import GaloisForLFunctions.HTGeometry.CompactAlgebraicPointFiniteness
import GaloisForLFunctions.HTGeometry.OrderedCriticalValuePolynomial
import GaloisForLFunctions.HTGeometry.OrderedCriticalValueSurjectivity

/-!
# Finite critical-value fibers, including collisions

Every fiber of the actual critical-value map is a compact affine algebraic set in the
explicit polynomial coordinates. It is therefore finite. Surjectivity makes it nonempty.
-/

open Set Topology
namespace GaloisForLFunctions.HTGeometry.OrderedCriticalValueMap
noncomputable section

/-- Equations for the actual critical-value fiber in polynomial parameter coordinates. -/
def fiberIdeal {n : ℕ} (b : Fin (n + 1) → ℂ) : Ideal (CoordinatePolynomial n) :=
  Ideal.span (Set.range fun j => valuePolynomial n j - MvPolynomial.C (b j))

theorem zeroLocus_fiberIdeal {n : ℕ} (b : Fin (n + 1) → ℂ) :
    MvPolynomial.zeroLocus ℂ (fiberIdeal b) =
      {θ | valuesWithConstant (parameterOfCoordinates θ) = b} := by
  rw [fiberIdeal, MvPolynomial.zeroLocus_span]
  ext θ
  simp only [Set.mem_setOf_eq, Set.forall_mem_range, map_sub, MvPolynomial.aeval_C,
    Algebra.algebraMap_self, RingHom.id_apply, sub_eq_zero]
  have he (j : Fin (n + 1)) : MvPolynomial.aeval θ (valuePolynomial n j) =
      valuesWithConstant (parameterOfCoordinates θ) j := by
    change MvPolynomial.eval θ (valuePolynomial n j) = _
    exact eval_valuePolynomial θ j
  simp only [he, funext_iff]

theorem coordinateHomeomorph_image_fiber {n : ℕ} (b : Fin (n + 1) → ℂ) :
    coordinateHomeomorph n '' (valuesWithConstant ⁻¹' {b}) =
      MvPolynomial.zeroLocus ℂ (fiberIdeal b) := by
  rw [zeroLocus_fiberIdeal]
  ext θ
  constructor
  · rintro ⟨v, hv, rfl⟩
    change valuesWithConstant v = b at hv
    change valuesWithConstant (parameterOfCoordinates (parameterCoordinates v)) = b
    simpa only [parameterOfCoordinates_parameterCoordinates] using hv
  · intro hθ
    exact ⟨parameterOfCoordinates θ, hθ, parameterCoordinates_parameterOfCoordinates θ⟩

/-- Every actual critical-value fiber is finite, including all collisions of values and positions. -/
theorem finite_valuesWithConstant_fiber {n : ℕ} (b : Fin (n + 1) → ℂ) :
    (valuesWithConstant ⁻¹' {b}).Finite := by
  have hc : IsCompact (MvPolynomial.zeroLocus ℂ (fiberIdeal b)) := by
    rw [← coordinateHomeomorph_image_fiber]
    exact ((isProperMap_valuesWithConstant n).isCompact_preimage isCompact_singleton).image
      (coordinateHomeomorph n).continuous
  have hf := finite_zeroLocus_of_isCompact (fiberIdeal b) hc
  rw [← coordinateHomeomorph_image_fiber] at hf
  exact hf.of_finite_image (coordinateHomeomorph n).injective.injOn

/-- Each prescribed ordered critical-value tuple has a nonempty finite set of actual parameters. -/
theorem finite_nonempty_valuesWithConstant_fiber {n : ℕ} (b : Fin (n + 1) → ℂ) :
    (valuesWithConstant ⁻¹' {b}).Finite ∧ (valuesWithConstant ⁻¹' {b}).Nonempty :=
  ⟨finite_valuesWithConstant_fiber b, surjective_valuesWithConstant n b⟩

end
end GaloisForLFunctions.HTGeometry.OrderedCriticalValueMap
