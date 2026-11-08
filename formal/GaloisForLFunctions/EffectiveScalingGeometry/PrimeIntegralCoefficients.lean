import GaloisForLFunctions.EffectiveScalingGeometry.PrimeChainBasis
import GaloisForLFunctions.EffectiveScalingGeometry.PrimeCutoffComplex

/-!
# Canonical integral coefficient maps on prime chains

The exterior universal property extends the canonical prime-vertex map from
integers to any commutative coefficient ring. Every actual prime wedge maps to
the same wedge, so the maps commute with the alternating boundary, prime cones
and height inclusions. They preserve every prime-product cutoff and restrict
to the actual chain modules. These are the chain maps underlying coefficient
extension; the induced homology and tensor comparisons are further statements.
-/

noncomputable section
open RHTower
namespace GaloisForLFunctions.EffectiveScalingGeometry
attribute [local instance] primeLabelLinearOrder
variable (R : Type*) [CommRing R]

/-- Use the scalar action inherited from the integral exterior power. -/
local instance primeIntegerChainModule (k : ℕ) : Module ℤ (PrimeChainSpace ℤ k) :=
  (PrimeChainSpace ℤ k).module

/-- The canonical coefficient map on the free prime-vertex module. -/
def primeIntegralVertexMap : (Nat.Primes →₀ ℤ) →ₗ[ℤ] (Nat.Primes →₀ R) :=
  Finsupp.linearCombination ℤ (fun p => Finsupp.single p (1 : R))

theorem primeIntegralVertexMap_single (p : Nat.Primes) :
    primeIntegralVertexMap R (Finsupp.single p 1) = Finsupp.single p 1 := by
  simp only [primeIntegralVertexMap,Finsupp.linearCombination_single,one_smul]

/-- The coefficient-ring wedge is also alternating over the integers. -/
def primeIntegralWedge (k : ℕ) :
    (Nat.Primes →₀ R) [⋀^Fin k]→ₗ[ℤ] PrimeChainSpace R k :=
  { exteriorPower.ιMulti R k with
    toMultilinearMap := (exteriorPower.ιMulti R k).toMultilinearMap.restrictScalars ℤ }

/-- Extend integral coefficients on actual exterior chains by their universal property. -/
def primeIntegralChainMap (k : ℕ) : PrimeChainSpace ℤ k →ₗ[ℤ] PrimeChainSpace R k :=
  exteriorPower.alternatingMapLinearEquiv
    ((primeIntegralWedge R k).compLinearMap (primeIntegralVertexMap R))

theorem primeIntegralChainMap_atom {k : ℕ} (v : Fin k → Nat.Primes) :
    primeIntegralChainMap R k (primeChainAtom ℤ v) = primeChainAtom R v := by
  unfold primeIntegralChainMap primeChainAtom
  rw [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  change exteriorPower.ιMulti R k (fun i => primeIntegralVertexMap R (Finsupp.single (v i) 1)) = _
  congr 1
  funext i
  exact primeIntegralVertexMap_single R (v i)

/-- Every exterior basis face is the same face after extending coefficients. -/
theorem primeIntegralChainMap_basis (k : ℕ) (s : Set.powersetCard Nat.Primes k) :
    primeIntegralChainMap R k (primeChainBasis ℤ k s) = primeChainBasis R k s := by
  simp only [primeChainBasis_eq_atom,primeIntegralChainMap_atom]

/-- The actual integral boundary commutes with canonical coefficient extension. -/
theorem primeIntegralChainMap_boundary (k : ℕ) :
    ((primeChainBoundary R k).restrictScalars ℤ).comp (primeIntegralChainMap R (k+1)) =
      (primeIntegralChainMap R k).comp (primeChainBoundary ℤ k) := by
  apply (primeChainBasis ℤ (k+1)).ext
  intro s
  change primeChainBoundary R k (primeIntegralChainMap R (k+1) (primeChainBasis ℤ (k+1) s)) =
    primeIntegralChainMap R k (primeChainBoundary ℤ k (primeChainBasis ℤ (k+1) s))
  simp only [primeChainBasis_eq_atom,primeIntegralChainMap_atom,primeChainBoundary_atom,
    map_sum,map_smul]

/-- Adjoining a prime commutes with coefficient extension. -/
theorem primeIntegralChainMap_cone (k : ℕ) (p : Nat.Primes) :
    (primeIntegralChainMap R (k+1)).comp (primeChainCone ℤ k p) =
      ((primeChainCone R k p).restrictScalars ℤ).comp (primeIntegralChainMap R k) := by
  apply (primeChainBasis ℤ k).ext
  intro s
  change primeIntegralChainMap R (k+1) (primeChainCone ℤ k p (primeChainBasis ℤ k s)) =
    primeChainCone R k p (primeIntegralChainMap R k (primeChainBasis ℤ k s))
  simp only [primeChainBasis_eq_atom,primeChainCone_atom,primeIntegralChainMap_atom]

/-- The same prime support has the same product bound over every coefficient ring. -/
theorem primeIntegralChainMap_cutoff (k N : ℕ) :
    primeChainCutoff ℤ k N ≤ ((primeChainCutoff R k N).restrictScalars ℤ).comap
      (primeIntegralChainMap R k) := by
  apply Submodule.span_le.mpr
  rintro x ⟨v,hv,rfl⟩
  change primeIntegralChainMap R k (primeChainAtom ℤ v) ∈ primeChainCutoff R k N
  rw [primeIntegralChainMap_atom]
  exact Submodule.subset_span ⟨v,hv,rfl⟩

/-- The integral cutoff inherits its scalar action from the exterior chain module. -/
local instance primeIntegerCutoffModule (k N : ℕ) : Module ℤ (primeChainCutoff ℤ k N) :=
  (primeChainCutoff ℤ k N).module

/-- Canonical coefficient extension restricted to the actual cutoff modules. -/
def primeIntegralCutoffMap (k N : ℕ) :
    primeChainCutoff ℤ k N →ₗ[ℤ] primeChainCutoff R k N where
  toFun x := ⟨primeIntegralChainMap R k x.val,primeIntegralChainMap_cutoff R k N x.property⟩
  map_add' x y := Subtype.ext ((primeIntegralChainMap R k).map_add x.val y.val)
  map_smul' a x := Subtype.ext ((primeIntegralChainMap R k).map_smul a x.val)

/-- The restricted coefficient maps commute with the actual differentials. -/
theorem primeIntegralCutoffMap_boundary (k N : ℕ) (x : primeChainCutoff ℤ (k+1) N) :
    primeCutoffDifferential R (primeChainAugmentation R) k N (primeIntegralCutoffMap R (k+1) N x) =
      primeIntegralCutoffMap R k N (primeCutoffDifferential ℤ (primeChainAugmentation ℤ) k N x) :=
  Subtype.ext (LinearMap.congr_fun (primeIntegralChainMap_boundary R k) x.val)

/-- Coefficient extension commutes with every height inclusion. -/
theorem primeIntegralCutoffMap_natural (k : ℕ) {N M : ℕ} (h : N ≤ M) :
    ((Submodule.inclusion (primeChainCutoff_mono R k h)).restrictScalars ℤ).comp
      (primeIntegralCutoffMap R k N) =
        (primeIntegralCutoffMap R k M).comp (Submodule.inclusion (primeChainCutoff_mono ℤ k h)) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  rfl

#print axioms primeIntegralCutoffMap_boundary
#print axioms primeIntegralCutoffMap_natural

#print axioms primeIntegralChainMap_basis
#print axioms primeIntegralChainMap_boundary
#print axioms primeIntegralChainMap_cone
#print axioms primeIntegralChainMap_cutoff
end GaloisForLFunctions.EffectiveScalingGeometry
