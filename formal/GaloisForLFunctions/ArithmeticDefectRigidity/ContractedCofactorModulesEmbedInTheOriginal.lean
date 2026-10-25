import GaloisForLFunctions.HTGeometry.OneSidedFeatureGramIsometry
import GaloisForLFunctions.ArithmeticDefectRigidity.ContractingHorizonsProducesActualCofactorLimits
import GaloisForLFunctions.ArithmeticDefectRigidity.CofactorAnnihilatorsArePrincipalQuotients

/-!
# Contracted cofactor modules embed in the original module

Normalized cofactor vectors give an isometry from each actual contracted
module. Point-mass density extends dilation intertwining to every Wiener
operator, identifying the contracted annihilator and its character hull.
-/

noncomputable section
set_option autoImplicit false
open scoped InnerProductSpace ComplexConjugate
open GaloisForLFunctions.ArithmeticOrientationTheory
open GaloisForLFunctions.HTGeometry
open WienerAlgebraAt

namespace GaloisForLFunctions.ArithmeticDefectRigidity.ActualCofactorLimit

/-- The selected cyclic orbit normalized to unit receiver mass. -/
def contractedVector {ε : SubcriticalDamping} (L : ActualCofactorLimit ε)
    (p j : ℕ+) : Hilbert L :=
  ((Real.sqrt (L.kernel p p) : ℂ)⁻¹) • vector L (p * j)

/-- Exact contracted kernels induce an isometric embedding into the original module. -/
def contractedKernelIsometry {ε : SubcriticalDamping}
    (L M : ActualCofactorLimit ε) (p : ℕ+) (hp : 0 < L.kernel p p)
    (hK : ∀ j k, M.kernel j k = L.kernel (p * j) (p * k) / L.kernel p p) :
    Hilbert M →ₗᵢ[ℂ] Hilbert L :=
  denseSourceFeatureGramIsometry (vector M) (contractedVector L p)
    (fun j k => by
      rw [inner_vector, hK]
      simp only [contractedVector, inner_smul_left, inner_smul_right, inner_vector,
        map_inv₀, Complex.conj_ofReal]
      have hs : (Real.sqrt (L.kernel p p) : ℂ) ^ 2 = (L.kernel p p : ℂ) := by
        rw [← Complex.ofReal_pow, Real.sq_sqrt hp.le]
      rw [Complex.ofReal_div, ← hs]
      ring)
    (by rw [range_featureSynthesis_eq_span]; exact KernelHilbert.dense_span_vectors _)

theorem contractedKernelIsometry_vector {ε : SubcriticalDamping}
    (L M : ActualCofactorLimit ε) (p : ℕ+) (hp : 0 < L.kernel p p)
    (hK : ∀ j k, M.kernel j k = L.kernel (p * j) (p * k) / L.kernel p p)
    (j : ℕ+) :
    contractedKernelIsometry L M p hp hK (vector M j) = contractedVector L p j :=
  denseSourceFeatureGramIsometry_apply _ _ _ _ j

/-- The contracted isometry intertwines each dilation on the complete Hilbert space. -/
theorem contractedKernelIsometry_dilation {ε : SubcriticalDamping}
    (L M : ActualCofactorLimit ε) (p : ℕ+) (hp : 0 < L.kernel p p)
    (hK : ∀ j k, M.kernel j k = L.kernel (p * j) (p * k) / L.kernel p p)
    (q : ℕ+) (x : Hilbert M) :
    contractedKernelIsometry L M p hp hK (dilation M q x) =
      dilation L q (contractedKernelIsometry L M p hp hK x) := by
  let U := (contractedKernelIsometry L M p hp hK).toContinuousLinearMap
  have heq : U.comp (dilation M q) = (dilation L q).comp U := by
    apply KernelHilbert.ext_on_vectors (complexKernel M)
    intro j
    change contractedKernelIsometry L M p hp hK (dilation M q (vector M j)) =
      dilation L q (contractedKernelIsometry L M p hp hK (vector M j))
    rw [dilation_vector, contractedKernelIsometry_vector, contractedKernelIsometry_vector]
    simp only [contractedVector, map_smul, dilation_vector]
    rw [mul_left_comm p q j]
  exact congrArg (fun T : Hilbert M →L[ℂ] Hilbert L => T x) heq

/-- Point-mass density extends the intertwining identity to every Wiener operator. -/
theorem contractedKernelIsometry_wiener {ε : SubcriticalDamping}
    (L M : ActualCofactorLimit ε) (p : ℕ+) (hp : 0 < L.kernel p p)
    (hK : ∀ j k, M.kernel j k = L.kernel (p * j) (p * k) / L.kernel p p)
    (a : WienerAlgebraAt (1 / 2)) (x : Hilbert M) :
    contractedKernelIsometry L M p hp hK (wienerRepresentation M a x) =
      wienerRepresentation L a (contractedKernelIsometry L M p hp hK x) := by
  let U := (contractedKernelIsometry L M p hp hK).toContinuousLinearMap
  let F : WienerAlgebraAt (1 / 2) →L[ℂ] Hilbert L :=
    U.comp ((ContinuousLinearMap.apply ℂ (Hilbert M) x).comp (wienerLinear M))
  let G : WienerAlgebraAt (1 / 2) →L[ℂ] Hilbert L :=
    (ContinuousLinearMap.apply ℂ (Hilbert L) (U x)).comp (wienerLinear L)
  have hpoint (n : ℕ) : F (pointMass n) = G (pointMass n) := by
    change U (wienerRepresentation M (pointMass n) x) =
      wienerRepresentation L (pointMass n) (U x)
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [wienerRepresentation_eq_linear, wienerLinear, sequenceExtension_pointMass,
        naturalDilation_zero, zero_apply, map_zero,
        wienerRepresentation_eq_linear, wienerLinear, sequenceExtension_pointMass,
        naturalDilation_zero, zero_apply]
    · let q : ℕ+ := ⟨n, hn⟩
      change U (wienerRepresentation M (pointMass q) x) =
        wienerRepresentation L (pointMass q) (U x)
      rw [wienerRepresentation_pointMass, wienerRepresentation_pointMass]
      exact contractedKernelIsometry_dilation L M p hp hK q x
  have hF := F.hasSum (hasSum_pointMass a)
  have hG := G.hasSum (hasSum_pointMass a)
  exact (hF.congr_fun fun n => by simp only [map_smul, hpoint]).unique hG

/-- The complete Wiener cyclic orbit has the same normalization as its Gram generators. -/
theorem contractedKernelIsometry_wiener_vector {ε : SubcriticalDamping}
    (L M : ActualCofactorLimit ε) (p : ℕ+) (hp : 0 < L.kernel p p)
    (hK : ∀ j k, M.kernel j k = L.kernel (p * j) (p * k) / L.kernel p p)
    (a : WienerAlgebraAt (1 / 2)) :
    contractedKernelIsometry L M p hp hK (wienerRepresentation M a (vector M 1)) =
      ((Real.sqrt (L.kernel p p) : ℂ)⁻¹) • wienerRepresentation L a (vector L p) := by
  rw [contractedKernelIsometry_wiener, contractedKernelIsometry_vector]
  simp only [contractedVector, mul_one, map_smul]

/-- An actual contracted state's annihilator is the principal ideal quotient. -/
theorem annihilator_eq_cofactorAnnihilator_of_contracted_kernel {ε : SubcriticalDamping}
    (L M : ActualCofactorLimit ε) (p : ℕ+) (hp : 0 < L.kernel p p)
    (hK : ∀ j k, M.kernel j k = L.kernel (p * j) (p * k) / L.kernel p p) :
    annihilator M = cofactorAnnihilator L p := by
  ext a
  rw [mem_annihilator_iff, mem_cofactorAnnihilator_iff]
  let U := contractedKernelIsometry L M p hp hK
  have hc : (Real.sqrt (L.kernel p p) : ℂ)⁻¹ ≠ 0 :=
    inv_ne_zero (by exact_mod_cast (Real.sqrt_pos.2 hp).ne')
  constructor
  · intro h
    have hU := congrArg U h
    change contractedKernelIsometry L M p hp hK (wienerRepresentation M a (vector M 1)) =
      contractedKernelIsometry L M p hp hK 0 at hU
    rw [map_zero, contractedKernelIsometry_wiener_vector] at hU
    exact (smul_eq_zero.mp hU).resolve_left hc
  · intro h
    apply U.injective
    change contractedKernelIsometry L M p hp hK (wienerRepresentation M a (vector M 1)) =
      contractedKernelIsometry L M p hp hK 0
    rw [map_zero, contractedKernelIsometry_wiener_vector, h, smul_zero]

/-- Every positive cofactor has an actual contracted state with the exact quotient ideal. -/
theorem exists_actual_contracted_module {ε : SubcriticalDamping}
    (L : ActualCofactorLimit ε) (p : ℕ+) (hp : 0 < L.kernel p p) :
    ∃ M : ActualCofactorLimit ε,
      (∀ j k, M.kernel j k = L.kernel (p * j) (p * k) / L.kernel p p) ∧
      annihilator M = cofactorAnnihilator L p := by
  obtain ⟨M, hM⟩ := exists_actual_contracted_kernel L p hp
  exact ⟨M, hM, annihilator_eq_cofactorAnnihilator_of_contracted_kernel L M p hp hM⟩

/-- Contracted hulls agree off the vanishing-coordinate hyperplane. -/
theorem exists_actual_contracted_hull {ε : SubcriticalDamping}
    (L : ActualCofactorLimit ε) (p : ℕ+) (hp : 0 < L.kernel p p) :
    ∃ M : ActualCofactorLimit ε,
      (∀ j k, M.kernel j k = L.kernel (p * j) (p * k) / L.kernel p p) ∧
      {ω ∈ moduleHull L | ω.ω p ≠ 0} ⊆ moduleHull M ∧ moduleHull M ⊆ moduleHull L := by
  obtain ⟨M, hM, hI⟩ := exists_actual_contracted_module L p hp
  refine ⟨M, hM, ?_⟩
  simpa only [moduleHull, hI] using cofactor_hull_inclusions L p

end GaloisForLFunctions.ArithmeticDefectRigidity.ActualCofactorLimit

#print axioms GaloisForLFunctions.ArithmeticDefectRigidity.ActualCofactorLimit.exists_actual_contracted_module
#print axioms GaloisForLFunctions.ArithmeticDefectRigidity.ActualCofactorLimit.exists_actual_contracted_hull

#print axioms GaloisForLFunctions.ArithmeticDefectRigidity.ActualCofactorLimit.contractedKernelIsometry_wiener
end
