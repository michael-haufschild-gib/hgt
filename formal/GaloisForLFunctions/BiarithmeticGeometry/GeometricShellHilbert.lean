import GaloisForLFunctions.HTGeometry.BoundedKernelReindexing
import GaloisForLFunctions.HTGeometry.DenseFeatureGramUnitary

/-!
# The geometric shell Gram completion is exactly one complex dimension

The canonical positive-kernel completion has scalar features `a^(-r)`.
Their zeroth feature is one, so equality of total feature Grams supplies
a unitary equivalence with the complex line. The norm-lattice shift is
the unique bounded extension of index addition on its canonical vectors.
-/

noncomputable section
open scoped InnerProductSpace
open GaloisForLFunctions.HTGeometry
namespace GaloisForLFunctions.BiarithmeticGeometry

/-- Scalar geometric features on the norm lattice. -/
def geometricShellFeature (a : ℝ) (r : ℕ) : ℂ := ((a ^ r)⁻¹ : ℝ)

theorem geometricShellFeature_zero (a : ℝ) : geometricShellFeature a 0 = 1 := by
  simp only [geometricShellFeature, pow_zero, inv_one, Complex.ofReal_one]

theorem geometricShellFeature_add (a : ℝ) (r s : ℕ) :
    geometricShellFeature a (r + s) = geometricShellFeature a r * geometricShellFeature a s := by
  simp only [geometricShellFeature, pow_add, mul_inv, Complex.ofReal_mul]

/-- The canonical geometric Gram kernel, with the corpus's inner-product orientation. -/
def geometricShellKernel (a : ℝ) (r s : ℕ) : ℂ :=
  inner ℂ (geometricShellFeature a s) (geometricShellFeature a r)

instance geometricShellKernel_positive (a : ℝ) : Fact (IsPSDKernel (geometricShellKernel a)) :=
  ⟨isPSDKernel_gram (geometricShellFeature a)⟩

/-- The canonical complex Gram is precisely the geometric real tangent table. -/
theorem geometricShellKernel_eq (a : ℝ) (r s : ℕ) :
    geometricShellKernel a r s = (((a ^ (r + s))⁻¹ : ℝ) : ℂ) := by
  simp only [geometricShellKernel, RCLike.inner_apply, geometricShellFeature,
    Complex.conj_ofReal, ← Complex.ofReal_mul, ← mul_inv, ← pow_add]

/-- The positive-kernel Hilbert completion of the geometric norm-lattice table. -/
abbrev GeometricShellTangentSpace (a : ℝ) := KernelHilbert (geometricShellKernel a)

private theorem geometricShellFeature_dense (a : ℝ) :
    Dense ((LinearMap.range (featureSynthesis (geometricShellFeature a)) : Submodule ℂ ℂ) : Set ℂ) := by
  have hrange : ((LinearMap.range (featureSynthesis (geometricShellFeature a)) :
      Submodule ℂ ℂ) : Set ℂ) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro z
    exact ⟨Finsupp.single 0 z, by rw [featureSynthesis_single, geometricShellFeature_zero, smul_eq_mul, mul_one]⟩
  rw [hrange]
  exact dense_univ

private theorem geometricShellVectors_dense (a : ℝ) :
    Dense ((LinearMap.range (featureSynthesis (KernelHilbert.vector (geometricShellKernel a))) :
      Submodule ℂ (GeometricShellTangentSpace a)) : Set (GeometricShellTangentSpace a)) := by
  rw [range_featureSynthesis_eq_span]
  exact KernelHilbert.dense_span_vectors (geometricShellKernel a)

/-- The actual Gram completion is isometrically the complex scalar line. -/
def geometricShellTangentIsometry (a : ℝ) : GeometricShellTangentSpace a ≃ₗᵢ[ℂ] ℂ :=
  denseFeatureGramUnitary
    (KernelHilbert.vector (geometricShellKernel a)) (geometricShellFeature a)
    (fun r s => KernelHilbert.inner_vector s r)
    (geometricShellVectors_dense a) (geometricShellFeature_dense a)

theorem geometricShellTangentIsometry_vector (a : ℝ) (r : ℕ) :
    geometricShellTangentIsometry a (KernelHilbert.vector (geometricShellKernel a) r) =
      geometricShellFeature a r :=
  denseFeatureGramUnitary_apply _ _ _ _ _ r

instance geometricShellTangent_finiteDimensional (a : ℝ) :
    FiniteDimensional ℂ (GeometricShellTangentSpace a) :=
  FiniteDimensional.of_injective (geometricShellTangentIsometry a).toLinearMap
    (geometricShellTangentIsometry a).injective

/-- The canonical completed geometric module has complex dimension exactly one. -/
theorem finrank_geometricShellTangentSpace (a : ℝ) :
    Module.finrank ℂ (GeometricShellTangentSpace a) = 1 := by
  simpa only [Module.finrank_self] using (geometricShellTangentIsometry a).toLinearEquiv.finrank_eq

/-- Bounded extension of a norm-lattice shift through the canonical Gram isometry. -/
def geometricShellTangentShift (a : ℝ) (r : ℕ) :
    GeometricShellTangentSpace a →L[ℂ] GeometricShellTangentSpace a :=
  (geometricShellTangentIsometry a).symm.toContinuousLinearMap.comp
    (geometricShellFeature a r • (geometricShellTangentIsometry a).toContinuousLinearMap)

theorem geometricShellTangentShift_apply (a : ℝ) (r : ℕ) (x : GeometricShellTangentSpace a) :
    geometricShellTangentShift a r x = geometricShellFeature a r • x := by
  change (geometricShellTangentIsometry a).symm
    (geometricShellFeature a r • geometricShellTangentIsometry a x) = _
  rw [map_smul, (geometricShellTangentIsometry a).symm_apply_apply]

/-- The completed operator acts on source-labelled vectors by exact index addition. -/
theorem geometricShellTangentShift_vector (a : ℝ) (r s : ℕ) :
    geometricShellTangentShift a r (KernelHilbert.vector (geometricShellKernel a) s) =
      KernelHilbert.vector (geometricShellKernel a) (r + s) := by
  apply (geometricShellTangentIsometry a).injective
  rw [geometricShellTangentShift_apply, map_smul, geometricShellTangentIsometry_vector,
    geometricShellTangentIsometry_vector, geometricShellFeature_add, smul_eq_mul]

/-- Every shift has its exact scalar norm on every completed vector. -/
theorem norm_geometricShellTangentShift (a : ℝ) (r : ℕ) (x : GeometricShellTangentSpace a) :
    ‖geometricShellTangentShift a r x‖ = |(a ^ r)⁻¹| * ‖x‖ := by
  rw [geometricShellTangentShift_apply, norm_smul, geometricShellFeature,
    Complex.norm_real, Real.norm_eq_abs]

/-- The completed shift action obeys the additive norm-lattice semigroup law. -/
theorem geometricShellTangentShift_comp (a : ℝ) (r s : ℕ) :
    (geometricShellTangentShift a r).comp (geometricShellTangentShift a s) =
      geometricShellTangentShift a (r + s) := by
  ext x
  simp only [ContinuousLinearMap.comp_apply, geometricShellTangentShift_apply,
    smul_smul, geometricShellFeature_add]

end GaloisForLFunctions.BiarithmeticGeometry

