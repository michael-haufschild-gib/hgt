import GaloisForLFunctions.EffectiveScalingGeometry.PrimeWeightedContraction
import GaloisForLFunctions.EffectiveScalingGeometry.PrimeBoundaryHeight

/-!
# Boundary saturation and exponent-two torsion

For the prime-valued boundary over the integers, a cycle has a bounding
nonzero multiple at height `N` exactly when it lies below `⌊N/2⌋`.
Coordinate cutoffs are saturated in the free exterior lattice, and every
boundary lowers height by at least two. Conversely, coning a half-height cycle
with prime two fills its double. Thus every torsion cycle class is killed by
two. The exact saturation law includes the empty augmented degree.
-/

noncomputable section
open RHTower
open GaloisForLFunctions.HTGeometry
namespace GaloisForLFunctions.EffectiveScalingGeometry

local instance primeSaturationIntegerChainModule (k : ℕ) : Module ℤ (PrimeChainSpace ℤ k) :=
  (PrimeChainSpace ℤ k).module

/-- Integer coordinate cutoffs are saturated in the full exterior lattice. -/
theorem primeIntegerCutoff_saturated (k N : ℕ) (a : ℤ) (ha : a ≠ 0) (x : PrimeChainSpace ℤ k) :
    a • x ∈ primeChainCutoff ℤ k N ↔ x ∈ primeChainCutoff ℤ k N := by
  constructor
  · intro h
    rw [primeChainCutoff_iff_repr_support] at h ⊢
    intro s hs
    apply h
    apply Finsupp.mem_support_iff.mpr
    rw [map_smul,Finsupp.smul_apply,smul_eq_mul]
    exact mul_ne_zero ha (Finsupp.mem_support_iff.mp hs)
  · exact fun h => Submodule.smul_mem _ a h

/-- Actual weighted boundary chains at a given height and exterior degree. -/
def primeValueBoundaries (k N : ℕ) : Submodule ℤ (PrimeChainSpace ℤ k) :=
  (primeChainCutoff ℤ (k+1) N).map (primeValueBoundary ℤ k)

/-- Every weighted boundary has half the height of its filling. -/
theorem primeValueBoundaries_le_half (k N : ℕ) :
    primeValueBoundaries k N ≤ primeChainCutoff ℤ k (N/2) := by
  rintro x ⟨y,hy,rfl⟩
  exact primeChainDifferential_half_cutoff ℤ (primeValueFunctional ℤ) k N hy

/-- Doubling a half-height weighted cycle gives a boundary within the original height. -/
theorem primeValueCycle_double_boundary (k N : ℕ)
    (x : ↥(primeChainCutoff ℤ (k+1) (N/2) ⊓ (primeValueBoundary ℤ k).ker)) :
    (2 : ℤ) • x.val ∈ primeValueBoundaries (k+1) N := by
  apply Submodule.mem_map.mpr
  refine ⟨primeChainCone ℤ (k+1) ⟨2,Nat.prime_two⟩ x.val,?_,?_⟩
  · exact primeChainCutoff_mono ℤ (k+2) (show 2*(N/2) ≤ N by omega)
      (primeChainCone_cutoff ℤ (k+1) (N/2) ⟨2,Nat.prime_two⟩ x.property.1)
  · have h := LinearMap.congr_fun (primeValueBoundary_cartan ℤ k ⟨2,Nat.prime_two⟩) x.val
    have hx : primeValueBoundary ℤ k x.val = 0 := x.property.2
    have he : primeValueBoundary ℤ (k+1)
        (primeChainCone ℤ (k+1) ⟨2,Nat.prime_two⟩ x.val) = x.val + x.val := by
      simpa only [LinearMap.add_apply,LinearMap.comp_apply,LinearMap.smul_apply,
        LinearMap.id_apply,Nat.cast_ofNat,hx,map_zero,add_zero,two_smul] using h
    exact he.trans (two_smul ℤ x.val).symm

/-- The double of every half-height empty chain is also a boundary. -/
theorem primeValueZero_double_boundary (N : ℕ) (x : primeChainCutoff ℤ 0 (N/2)) :
    (2 : ℤ) • x.val ∈ primeValueBoundaries 0 N := by
  apply Submodule.mem_map.mpr
  refine ⟨primeChainCone ℤ 0 ⟨2,Nat.prime_two⟩ x.val,?_,?_⟩
  · exact primeChainCutoff_mono ℤ 1 (show 2*(N/2) ≤ N by omega)
      (primeChainCone_cutoff ℤ 0 (N/2) ⟨2,Nat.prime_two⟩ x.property)
  · have h := LinearMap.congr_fun
      (koszul_cartan_zero_map (primeValueFunctional ℤ) (Finsupp.single ⟨2,Nat.prime_two⟩ 1)) x.val
    have he : primeValueBoundary ℤ 0
        (primeChainCone ℤ 0 ⟨2,Nat.prime_two⟩ x.val) = x.val + x.val := by
      simpa only [LinearMap.comp_apply,LinearMap.smul_apply,LinearMap.id_apply,
        primeValueFunctional_single,Nat.cast_ofNat,two_smul,LinearMap.add_apply] using h
    exact he.trans (two_smul ℤ x.val).symm

/-- A weighted cycle has a bounding nonzero multiple exactly when it has half height. -/
theorem primeValueCycle_saturation_iff (k N : ℕ) (x : (primeValueBoundary ℤ k).ker) :
    (∃ a : ℤ, a ≠ 0 ∧ a • x.val ∈ primeValueBoundaries (k+1) N) ↔
      x.val ∈ primeChainCutoff ℤ (k+1) (N/2) := by
  constructor
  · rintro ⟨a,ha,hb⟩
    exact (primeIntegerCutoff_saturated (k+1) (N/2) a ha x.val).mp
      (primeValueBoundaries_le_half (k+1) N hb)
  · intro hx
    exact ⟨2,by omega,primeValueCycle_double_boundary k N ⟨x.val,hx,x.property⟩⟩

/-- The exact boundary-saturation law includes the augmented empty degree. -/
theorem primeValueZero_saturation_iff (N : ℕ) (x : PrimeChainSpace ℤ 0) :
    (∃ a : ℤ, a ≠ 0 ∧ a • x ∈ primeValueBoundaries 0 N) ↔
      x ∈ primeChainCutoff ℤ 0 (N/2) := by
  constructor
  · rintro ⟨a,ha,hb⟩
    exact (primeIntegerCutoff_saturated 0 (N/2) a ha x).mp
      (primeValueBoundaries_le_half 0 N hb)
  · intro hx
    exact ⟨2,by omega,primeValueZero_double_boundary N ⟨x,hx⟩⟩

/-- Every torsion cycle class is killed by two; there is no other torsion exponent. -/
theorem primeValueCycle_torsion_iff_double_boundary (k N : ℕ) (x : (primeValueBoundary ℤ k).ker) :
    (∃ a : ℤ, a ≠ 0 ∧ a • x.val ∈ primeValueBoundaries (k+1) N) ↔
      (2 : ℤ) • x.val ∈ primeValueBoundaries (k+1) N := by
  constructor
  · intro h
    exact primeValueCycle_double_boundary k N
      ⟨x.val,(primeValueCycle_saturation_iff k N x).mp h,x.property⟩
  · intro h
    exact ⟨2,by omega,h⟩

/-- The same exponent-two torsion law holds for empty-chain classes. -/
theorem primeValueZero_torsion_iff_double_boundary (N : ℕ) (x : PrimeChainSpace ℤ 0) :
    (∃ a : ℤ, a ≠ 0 ∧ a • x ∈ primeValueBoundaries 0 N) ↔
      (2 : ℤ) • x ∈ primeValueBoundaries 0 N := by
  constructor
  · intro h
    exact primeValueZero_double_boundary N ⟨x,(primeValueZero_saturation_iff N x).mp h⟩
  · intro h
    exact ⟨2,by omega,h⟩

#print axioms primeValueCycle_saturation_iff
#print axioms primeValueZero_saturation_iff
#print axioms primeValueCycle_torsion_iff_double_boundary
#print axioms primeValueZero_torsion_iff_double_boundary
end GaloisForLFunctions.EffectiveScalingGeometry
