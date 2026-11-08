import GaloisForLFunctions.EffectiveScalingGeometry.PrimeHomologyCoefficientMap
import GaloisForLFunctions.EffectiveScalingGeometry.PrimeHomologyTensorCoordinates

/-!
# Canonical base change of prime homology persistence

The surviving-face tensor equivalence is the linear extension of the actual
homology coefficient map. A surviving face is represented by the boundary of
its prime-two cone, or by the empty chain in augmented degree zero. Canonical
chain extension preserves these representatives. It therefore preserves the
actual homology basis and identifies tensor extension with homology over every
commutative ring. The equivalences commute with every height inclusion.
-/

noncomputable section
open CategoryTheory RHTower
open DifferentialGeometry.Topology
namespace GaloisForLFunctions.EffectiveScalingGeometry
variable (R : Type*) [CommRing R]

/-- A surviving coordinate lifts to the actual cycle obtained by coning with two. -/
def primeCoefficientCycleLift : (k N : ℕ) →
    primeCriticalCoordinates R k N →ₗ[R] (primeCoefficientShortComplex R k N).g.hom.ker
  | 0,N => (primeZeroCycleOddEquiv R N).symm.toLinearMap.comp (primeCriticalLift R 0 N)
  | k+1,N => (primeRestrictedCycleEquiv R k N).symm.toLinearMap.comp
    ((primeCutoffCycleOddEquiv R k N).symm.toLinearMap.comp (primeCriticalLift R (k+1) N))

/-- The chosen cycle has exactly the prescribed surviving coefficients. -/
theorem primeCoefficientCycleLift_class (k N : ℕ) (x : primeCriticalCoordinates R k N) :
    ((primeCoefficientShortCriticalIso R k).app N).hom
      (moduleHomologyClass (primeCoefficientShortComplex R k N)
        (primeCoefficientCycleLift R k N x)) = x := by
  cases k with
  | zero =>
    change primeZeroShortHomologyEquiv R N
      (moduleHomologyClass (primeZeroShortComplex R N)
        ((primeZeroCycleOddEquiv R N).symm (primeCriticalLift R 0 N x))) = _
    rw [primeZeroShortHomologyEquiv_class]
    change primeCriticalProjection R 0 N
      (primeZeroCycleOddEquiv R N ((primeZeroCycleOddEquiv R N).symm (primeCriticalLift R 0 N x))) = _
    rw [LinearEquiv.apply_symm_apply]
    exact LinearMap.congr_fun (primeCriticalProjection_lift R 0 N) x
  | succ k =>
    change primeShortHomologyEquiv R k N
      (moduleHomologyClass (primeCutoffShortComplex R k N)
        ((primeRestrictedCycleEquiv R k N).symm
          ((primeCutoffCycleOddEquiv R k N).symm (primeCriticalLift R (k+1) N x)))) = _
    rw [primeShortHomologyEquiv_class]
    change primeCriticalProjection R (k+1) N
      (primeCutoffCycleOddEquiv R k N (primeRestrictedCycleEquiv R k N
        ((primeRestrictedCycleEquiv R k N).symm
          ((primeCutoffCycleOddEquiv R k N).symm (primeCriticalLift R (k+1) N x))))) = _
    rw [LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply]
    exact LinearMap.congr_fun (primeCriticalProjection_lift R (k+1) N) x

/-- The unit vector at a surviving face, before forgetting the support bound. -/
def primeCriticalUnit (k N : ℕ) (s : primeCriticalFaces k N) : primeCriticalCoordinates R k N :=
  (Finsupp.supportedEquivFinsupp (R := R) (primeCriticalFaces k N)).symm (Finsupp.single s 1)

theorem primeCriticalUnit_val (k N : ℕ) (s : primeCriticalFaces k N) :
    (primeCriticalUnit R k N s).val = Finsupp.single s.val 1 := by
  classical
  exact Finsupp.supportedEquivFinsupp_symm_single _ _ _

/-- The literal chain underlying the unit-coordinate lift is the corresponding prime face. -/
theorem primeCriticalLift_unit_val (k N : ℕ) (s : primeCriticalFaces k N) :
    (primeCriticalLift R k N (primeCriticalUnit R k N s)).val = primeChainBasis R k s.val := by
  change (primeChainBasis R k).repr.symm (primeCriticalUnit R k N s).val = _
  rw [primeCriticalUnit_val,Module.Basis.repr_symm_single,one_smul]

/-- A surviving basis class has its explicit actual cycle representative. -/
theorem primeActualHomologyClass_unit (k N : ℕ) (s : primeCriticalFaces k N) :
    primeActualHomologyClass R k N
      (primeCoefficientCycleLift R k N (primeCriticalUnit R k N s)) =
        primeHomologyCriticalBasis R k N s := by
  apply (primeHomologyCoordinateEquiv R k N).injective
  rw [primeHomologyCoordinateEquiv_basis]
  change (Finsupp.supportedEquivFinsupp (R := R) (primeCriticalFaces k N))
    (((primeHomologyCriticalIso R k).app N).hom
      (primeActualHomologyClass R k N (primeCoefficientCycleLift R k N (primeCriticalUnit R k N s)))) = _
  rw [primeHomologyCriticalIso_factor]
  change (Finsupp.supportedEquivFinsupp (R := R) (primeCriticalFaces k N))
    (((primeCoefficientShortCriticalIso R k).app N).hom
      (primeHomologyShortEquiv R k N ((primeHomologyShortEquiv R k N).symm
        (moduleHomologyClass (primeCoefficientShortComplex R k N)
          (primeCoefficientCycleLift R k N (primeCriticalUnit R k N s)))))) = _
  rw [LinearEquiv.apply_symm_apply,primeCoefficientCycleLift_class]
  exact LinearEquiv.apply_symm_apply _ _

/-- The canonical chain extension preserves the chosen cycle for every surviving face. -/
theorem primeIntegralShortCycleMap_unit (k N : ℕ) (s : primeCriticalFaces k N) :
    primeIntegralShortCycleMap R k N
      (primeCoefficientCycleLift ℤ k N (primeCriticalUnit ℤ k N s)) =
        primeCoefficientCycleLift R k N (primeCriticalUnit R k N s) := by
  cases k with
  | zero =>
    apply Subtype.ext
    apply Subtype.ext
    change primeIntegralChainMap R 0
      (primeCriticalLift ℤ 0 N (primeCriticalUnit ℤ 0 N s)).val =
        (primeCriticalLift R 0 N (primeCriticalUnit R 0 N s)).val
    rw [primeCriticalLift_unit_val,primeCriticalLift_unit_val,primeIntegralChainMap_basis]
  | succ k =>
    apply Subtype.ext
    apply Subtype.ext
    change primeIntegralChainMap R (k+1)
      (primeCycleProjector ℤ k (primeCriticalLift ℤ (k+1) N (primeCriticalUnit ℤ (k+1) N s)).val) =
      primeCycleProjector R k (primeCriticalLift R (k+1) N (primeCriticalUnit R (k+1) N s)).val
    rw [primeCriticalLift_unit_val,primeCriticalLift_unit_val]
    change primeIntegralChainMap R (k+1)
      (primeChainBoundary ℤ (k+1) (primeChainCone ℤ (k+1) primeTwoLabel (primeChainBasis ℤ (k+1) s.val))) =
      primeChainBoundary R (k+1) (primeChainCone R (k+1) primeTwoLabel (primeChainBasis R (k+1) s.val))
    have hb := LinearMap.congr_fun (primeIntegralChainMap_boundary R (k+1))
      (primeChainCone ℤ (k+1) primeTwoLabel (primeChainBasis ℤ (k+1) s.val))
    have hc := LinearMap.congr_fun (primeIntegralChainMap_cone R (k+1) primeTwoLabel)
      (primeChainBasis ℤ (k+1) s.val)
    simp only [LinearMap.comp_apply,LinearMap.restrictScalars_apply] at hb hc
    rw [← hb,hc,primeIntegralChainMap_basis]

/-- Canonical coefficient extension sends each actual integral homology basis vector to the same face. -/
theorem primeIntegralHomologyMap_basis (k N : ℕ) (s : primeCriticalFaces k N) :
    primeIntegralHomologyMap R k N (primeHomologyCriticalBasis ℤ k N s) =
      primeHomologyCriticalBasis R k N s := by
  rw [← primeActualHomologyClass_unit,primeIntegralHomologyMap_class,
    primeIntegralShortCycleMap_unit,primeActualHomologyClass_unit]

open scoped TensorProduct

/-- Tensoring an integral class with one gives its canonical coefficient extension. -/
theorem primeHomologyBaseChange_one_tmul (k N : ℕ)
    (x : (primeCutoffHomology ℤ (primeChainAugmentation ℤ) k).obj N) :
    primeHomologyCoordinateBaseChange R k N ((1 : R) ⊗ₜ[ℤ] x) =
      primeIntegralHomologyMap R k N x := by
  let f := ((primeHomologyCoordinateBaseChange R k N).toLinearMap.restrictScalars ℤ).comp
    (TensorProduct.mk ℤ R ((primeCutoffHomology ℤ (primeChainAugmentation ℤ) k).obj N) 1)
  have hf : f = primeIntegralHomologyMap R k N := by
    apply (primeHomologyCriticalBasis ℤ k N).ext
    intro s
    change primeHomologyCoordinateBaseChange R k N
      ((1 : R) ⊗ₜ[ℤ] primeHomologyCriticalBasis ℤ k N s) = _
    rw [primeHomologyCoordinateBaseChange_basis,primeIntegralHomologyMap_basis]
  exact LinearMap.congr_fun hf x

/-- The tensor comparison is the linear extension of the actual coefficient map. -/
theorem primeHomologyBaseChange_tmul (k N : ℕ) (r : R)
    (x : (primeCutoffHomology ℤ (primeChainAugmentation ℤ) k).obj N) :
    primeHomologyCoordinateBaseChange R k N (r ⊗ₜ[ℤ] x) =
      r • primeIntegralHomologyMap R k N x := by
  calc
    primeHomologyCoordinateBaseChange R k N (r ⊗ₜ[ℤ] x) =
        primeHomologyCoordinateBaseChange R k N (r • ((1 : R) ⊗ₜ[ℤ] x)) := by
      rw [TensorProduct.smul_tmul',smul_eq_mul,mul_one]
    _ = r • primeHomologyCoordinateBaseChange R k N ((1 : R) ⊗ₜ[ℤ] x) :=
      (primeHomologyCoordinateBaseChange R k N).map_smul r _
    _ = r • primeIntegralHomologyMap R k N x := by rw [primeHomologyBaseChange_one_tmul]

/-- The tensor comparison commutes with every actual height-persistence map. -/
theorem primeHomologyBaseChange_natural (k : ℕ) {N M : ℕ} (h : N ≤ M) :
    ((primeCutoffHomology R (primeChainAugmentation R) k).map (homOfLE h)).hom.comp
      (primeHomologyCoordinateBaseChange R k N).toLinearMap =
    (primeHomologyCoordinateBaseChange R k M).toLinearMap.comp
      (((primeCutoffHomology ℤ (primeChainAugmentation ℤ) k).map (homOfLE h)).hom.baseChange R) := by
  apply ((primeHomologyCriticalBasis ℤ k N).baseChange R).ext
  intro s
  change (primeCutoffHomology R (primeChainAugmentation R) k).map (homOfLE h)
    (primeHomologyCoordinateBaseChange R k N ((primeHomologyCriticalBasis ℤ k N).baseChange R s)) =
      primeHomologyCoordinateBaseChange R k M
        ((((primeCutoffHomology ℤ (primeChainAugmentation ℤ) k).map (homOfLE h)).hom.baseChange R)
          ((primeHomologyCriticalBasis ℤ k N).baseChange R s))
  simp only [Module.Basis.baseChange_apply,LinearMap.baseChange_tmul,
    primeHomologyBaseChange_one_tmul]
  exact primeIntegralHomologyMap_natural R k h (primeHomologyCriticalBasis ℤ k N s)

#print axioms primeIntegralHomologyMap_basis
#print axioms primeHomologyBaseChange_one_tmul
#print axioms primeHomologyBaseChange_tmul
#print axioms primeHomologyBaseChange_natural
end GaloisForLFunctions.EffectiveScalingGeometry
