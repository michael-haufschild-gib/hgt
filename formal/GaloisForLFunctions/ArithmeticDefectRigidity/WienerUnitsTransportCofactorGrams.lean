import GaloisForLFunctions.ArithmeticOrientationTheory.TheOperatorHullOfAWienerAction
import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
import GaloisForLFunctions.ArithmeticDefectRigidity.TheCofactorLimitIsAWienerModule
import GaloisForLFunctions.HTGeometry.DenseFeatureGramUnitary

/-!
# Wiener units transport cofactor Gram spaces

An invertible Wiener action changes the cyclic receiver vector and preserves
its totality. Its Gram completion is unitarily equivalent to the original
cofactor Hilbert space. The unitary intertwines the full Wiener action,
preserving operator norms, the annihilator, the operator hull and algebraic dimension.
-/

noncomputable section
set_option autoImplicit false
open scoped InnerProductSpace
open GaloisForLFunctions.ArithmeticOrientationTheory
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.ArithmeticDefectRigidity.ActualCofactorLimit

/-- A Wiener unit acts as an invertible continuous operator on every actual module. -/
def unitOperatorEquiv {ε : SubcriticalDamping} (L : ActualCofactorLimit ε)
    (u : (WienerAlgebraAt (1 / 2))ˣ) : Hilbert L ≃L[ℂ] Hilbert L :=
  ContinuousLinearEquiv.unitsEquiv ℂ (Hilbert L)
    (Units.map (wienerRepresentation L).toMonoidHom u)

theorem unitOperatorEquiv_apply {ε : SubcriticalDamping} (L : ActualCofactorLimit ε)
    (u : (WienerAlgebraAt (1 / 2))ˣ) (x : Hilbert L) :
    unitOperatorEquiv L u x = wienerRepresentation L (u : WienerAlgebraAt (1 / 2)) x := rfl

/-- The old Gram generators after applying a Wiener unit. -/
def unitVector {ε : SubcriticalDamping} (L : ActualCofactorLimit ε)
    (u : (WienerAlgebraAt (1 / 2))ˣ) (j : ℕ+) : Hilbert L :=
  unitOperatorEquiv L u (vector L j)

theorem unitVector_one_ne_zero {ε : SubcriticalDamping} (L : ActualCofactorLimit ε)
    (u : (WienerAlgebraAt (1 / 2))ˣ) : unitVector L u 1 ≠ 0 := by
  intro h
  change unitOperatorEquiv L u (vector L 1) = 0 at h
  apply vector_one_ne_zero L
  apply (unitOperatorEquiv L u).injective
  simpa only [map_zero] using h

/-- Rescale a unit so that its new cyclic vector has unit norm. -/
def normalizedUnit {ε : SubcriticalDamping} (L : ActualCofactorLimit ε)
    (u : (WienerAlgebraAt (1 / 2))ˣ) : (WienerAlgebraAt (1 / 2))ˣ :=
  Units.map (algebraMap ℂ (WienerAlgebraAt (1 / 2))).toMonoidHom
    (Units.mk0 ((‖unitVector L u 1‖ : ℂ)⁻¹) (inv_ne_zero (by
      exact_mod_cast (norm_ne_zero_iff.mpr (unitVector_one_ne_zero L u))))) * u

theorem unitVector_normalizedUnit {ε : SubcriticalDamping} (L : ActualCofactorLimit ε)
    (u : (WienerAlgebraAt (1 / 2))ˣ) (j : ℕ+) :
    unitVector L (normalizedUnit L u) j =
      ((‖unitVector L u 1‖ : ℂ)⁻¹) • unitVector L u j := by
  change wienerRepresentation L
    (algebraMap ℂ (WienerAlgebraAt (1 / 2)) ((‖unitVector L u 1‖ : ℂ)⁻¹) *
      (u : WienerAlgebraAt (1 / 2))) (vector L j) = _
  rw [map_mul, (wienerRepresentation L).commutes, Algebra.algebraMap_eq_smul_one,
    smul_mul_assoc, one_mul]
  rfl

theorem norm_unitVector_normalizedUnit_one {ε : SubcriticalDamping}
    (L : ActualCofactorLimit ε) (u : (WienerAlgebraAt (1 / 2))ˣ) :
    ‖unitVector L (normalizedUnit L u) 1‖ = 1 := by
  rw [unitVector_normalizedUnit, norm_smul, norm_inv, Complex.norm_real, norm_norm,
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr (unitVector_one_ne_zero L u))]

/-- Commutativity leaves the integer dilation action unchanged after changing the cyclic vector. -/
theorem dilation_unitVector {ε : SubcriticalDamping} (L : ActualCofactorLimit ε)
    (u : (WienerAlgebraAt (1 / 2))ˣ) (p j : ℕ+) :
    dilation L p (unitVector L u j) = unitVector L u (p * j) := by
  have hcomm : dilation L p * wienerRepresentation L (u : WienerAlgebraAt (1 / 2)) =
      wienerRepresentation L (u : WienerAlgebraAt (1 / 2)) * dilation L p := by
    rw [← wienerRepresentation_pointMass, ← map_mul, ← map_mul, mul_comm]
  change dilation L p (wienerRepresentation L (u : WienerAlgebraAt (1 / 2)) (vector L j)) = _
  rw [← mul_apply_eq_comp, hcomm, mul_apply_eq_comp, dilation_vector]
  rfl

/-- Invertibility transports totality of the cofactor family. -/
theorem dense_span_unitVectors {ε : SubcriticalDamping} (L : ActualCofactorLimit ε)
    (u : (WienerAlgebraAt (1 / 2))ˣ) :
    Dense ((Submodule.span ℂ (Set.range (unitVector L u)) : Submodule ℂ (Hilbert L)) :
      Set (Hilbert L)) := by
  let e := unitOperatorEquiv L u
  have hd := e.surjective.denseRange.dense_image e.continuous
    (KernelHilbert.dense_span_vectors (complexKernel L))
  apply hd.mono
  rintro _ ⟨x, hx, rfl⟩
  have hm : (Submodule.span ℂ (Set.range (vector L))).map e.toLinearMap ≤
      Submodule.span ℂ (Set.range (unitVector L u)) := by
    rw [Submodule.map_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨y, ⟨j, rfl⟩, rfl⟩
    exact Submodule.subset_span ⟨j, rfl⟩
  exact hm ⟨x, hx, rfl⟩

/-- The Gram kernel after a unit changes the cyclic receiver vector. -/
def unitGram {ε : SubcriticalDamping} (L : ActualCofactorLimit ε)
    (u : (WienerAlgebraAt (1 / 2))ˣ) (j k : ℕ+) : ℂ :=
  ⟪unitVector L u k, unitVector L u j⟫_ℂ

theorem unitGram_normalizedUnit {ε : SubcriticalDamping} (L : ActualCofactorLimit ε)
    (u : (WienerAlgebraAt (1 / 2))ˣ) (j k : ℕ+) :
    unitGram L (normalizedUnit L u) j k =
      unitGram L u j k / ((‖unitVector L u 1‖ ^ 2 : ℝ) : ℂ) := by
  simp only [unitGram, unitVector_normalizedUnit, inner_smul_left, inner_smul_right,
    map_inv₀, Complex.conj_ofReal, Complex.ofReal_pow, div_eq_mul_inv]
  ring

instance unitGram_positive {ε : SubcriticalDamping} (L : ActualCofactorLimit ε)
    (u : (WienerAlgebraAt (1 / 2))ˣ) : Fact (IsPSDKernel (unitGram L u)) :=
  ⟨isPSDKernel_gram (unitVector L u)⟩

/-- The Gram realization of a unit-transformed receiver is the original Hilbert module. -/
def unitGramUnitary {ε : SubcriticalDamping} (L : ActualCofactorLimit ε)
    (u : (WienerAlgebraAt (1 / 2))ˣ) :
    KernelHilbert (unitGram L u) ≃ₗᵢ[ℂ] Hilbert L :=
  denseFeatureGramUnitary (KernelHilbert.vector (unitGram L u)) (unitVector L u)
    (fun j k => by rw [KernelHilbert.inner_vector]; rfl)
    (by rw [range_featureSynthesis_eq_span]; exact KernelHilbert.dense_span_vectors _)
    (by rw [range_featureSynthesis_eq_span]; exact dense_span_unitVectors L u)

theorem unitGramUnitary_vector {ε : SubcriticalDamping} (L : ActualCofactorLimit ε)
    (u : (WienerAlgebraAt (1 / 2))ˣ) (j : ℕ+) :
    unitGramUnitary L u (KernelHilbert.vector (unitGram L u) j) = unitVector L u j :=
  denseFeatureGramUnitary_apply _ _ _ _ _ j

end GaloisForLFunctions.ArithmeticDefectRigidity.ActualCofactorLimit

#print axioms GaloisForLFunctions.ArithmeticDefectRigidity.ActualCofactorLimit.unitGramUnitary
#print axioms GaloisForLFunctions.ArithmeticDefectRigidity.ActualCofactorLimit.dilation_unitVector


section

noncomputable section
set_option autoImplicit false
open GaloisForLFunctions.ArithmeticOrientationTheory
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.ArithmeticDefectRigidity.ActualCofactorLimit

/-- The complete Wiener action on the Gram realization after changing the receiver by a unit. -/
def unitGramRepresentation {ε : SubcriticalDamping} (L : ActualCofactorLimit ε)
    (u : (WienerAlgebraAt (1 / 2))ˣ) :
    WienerAlgebraAt (1 / 2) →ₐ[ℂ]
      (KernelHilbert (unitGram L u) →L[ℂ] KernelHilbert (unitGram L u)) :=
  ((unitGramUnitary L u).symm.toContinuousLinearEquiv.conjContinuousAlgEquiv).toAlgHom.comp
    (wienerRepresentation L)

theorem unitGramRepresentation_apply {ε : SubcriticalDamping} (L : ActualCofactorLimit ε)
    (u : (WienerAlgebraAt (1 / 2))ˣ) (a : WienerAlgebraAt (1 / 2))
    (x : KernelHilbert (unitGram L u)) :
    unitGramRepresentation L u a x = (unitGramUnitary L u).symm
      (wienerRepresentation L a (unitGramUnitary L u x)) := rfl

/-- The transported point masses act by the original integer reindexing of Gram vectors. -/
theorem unitGramRepresentation_pointMass_vector {ε : SubcriticalDamping}
    (L : ActualCofactorLimit ε) (u : (WienerAlgebraAt (1 / 2))ˣ) (p j : ℕ+) :
    unitGramRepresentation L u (WienerAlgebraAt.pointMass p)
      (KernelHilbert.vector (unitGram L u) j) =
        KernelHilbert.vector (unitGram L u) (p * j) := by
  apply (unitGramUnitary L u).injective
  rw [unitGramRepresentation_apply, LinearIsometryEquiv.apply_symm_apply,
    unitGramUnitary_vector, wienerRepresentation_pointMass, dilation_unitVector,
    unitGramUnitary_vector]

/-- The unitary comparison intertwines the entire Wiener algebra, including infinite kernels. -/
theorem unitGramUnitary_intertwines {ε : SubcriticalDamping} (L : ActualCofactorLimit ε)
    (u : (WienerAlgebraAt (1 / 2))ˣ) (a : WienerAlgebraAt (1 / 2))
    (x : KernelHilbert (unitGram L u)) :
    unitGramUnitary L u (unitGramRepresentation L u a x) =
      wienerRepresentation L a (unitGramUnitary L u x) := by
  rw [unitGramRepresentation_apply, LinearIsometryEquiv.apply_symm_apply]

/-- Changing a cyclic receiver by a Wiener unit preserves every represented operator norm. -/
theorem norm_unitGramRepresentation {ε : SubcriticalDamping} (L : ActualCofactorLimit ε)
    (u : (WienerAlgebraAt (1 / 2))ˣ) (a : WienerAlgebraAt (1 / 2)) :
    ‖unitGramRepresentation L u a‖ = ‖wienerRepresentation L a‖ := by
  apply le_antisymm
  · apply (unitGramRepresentation L u a).opNorm_le_bound (norm_nonneg _)
    intro x
    rw [unitGramRepresentation_apply, (unitGramUnitary L u).symm.norm_map]
    simpa only [(unitGramUnitary L u).norm_map] using
      (wienerRepresentation L a).le_opNorm (unitGramUnitary L u x)
  · apply (wienerRepresentation L a).opNorm_le_bound (norm_nonneg _)
    intro x
    have h := (unitGramRepresentation L u a).le_opNorm ((unitGramUnitary L u).symm x)
    change ‖(unitGramUnitary L u).symm
      (wienerRepresentation L a ((unitGramUnitary L u) ((unitGramUnitary L u).symm x)))‖ ≤
        ‖unitGramRepresentation L u a‖ * ‖(unitGramUnitary L u).symm x‖ at h
    rw [LinearIsometryEquiv.apply_symm_apply, (unitGramUnitary L u).symm.norm_map,
      (unitGramUnitary L u).symm.norm_map] at h
    exact h

/-- The full module annihilator is unchanged by unit transport. -/
theorem ker_unitGramRepresentation {ε : SubcriticalDamping} (L : ActualCofactorLimit ε)
    (u : (WienerAlgebraAt (1 / 2))ˣ) :
    RingHom.ker (unitGramRepresentation L u).toRingHom = annihilator L := by
  ext a
  change ((unitGramUnitary L u).symm.toContinuousLinearEquiv.conjContinuousAlgEquiv)
      (wienerRepresentation L a) = 0 ↔ wienerRepresentation L a = 0
  rw [← map_zero ((unitGramUnitary L u).symm.toContinuousLinearEquiv.conjContinuousAlgEquiv)]
  exact ((unitGramUnitary L u).symm.toContinuousLinearEquiv.conjContinuousAlgEquiv).injective.eq_iff

/-- Both the operator topology and all its bounded Bohr characters survive unit transport. -/
theorem operatorHull_unitGramRepresentation {ε : SubcriticalDamping} (L : ActualCofactorLimit ε)
    (u : (WienerAlgebraAt (1 / 2))ˣ) :
    ArithmeticOrientationTheory.operatorHull (unitGramRepresentation L u) =
      ArithmeticOrientationTheory.operatorHull (wienerRepresentation L) := by
  ext ω
  simp only [ArithmeticOrientationTheory.operatorHull, Set.mem_setOf_eq,
    norm_unitGramRepresentation]

/-- The algebraic dimension of the Hilbert realization is preserved by the unitary comparison. -/
theorem rank_unitGram {ε : SubcriticalDamping} (L : ActualCofactorLimit ε)
    (u : (WienerAlgebraAt (1 / 2))ˣ) :
    Module.rank ℂ (KernelHilbert (unitGram L u)) = Module.rank ℂ (Hilbert L) :=
  (unitGramUnitary L u).toLinearEquiv.rank_eq

theorem finrank_unitGram {ε : SubcriticalDamping} (L : ActualCofactorLimit ε)
    (u : (WienerAlgebraAt (1 / 2))ˣ) :
    Module.finrank ℂ (KernelHilbert (unitGram L u)) = Module.finrank ℂ (Hilbert L) :=
  (unitGramUnitary L u).toLinearEquiv.finrank_eq

end GaloisForLFunctions.ArithmeticDefectRigidity.ActualCofactorLimit

#print axioms GaloisForLFunctions.ArithmeticDefectRigidity.ActualCofactorLimit.ker_unitGramRepresentation
#print axioms GaloisForLFunctions.ArithmeticDefectRigidity.ActualCofactorLimit.operatorHull_unitGramRepresentation
end
end
