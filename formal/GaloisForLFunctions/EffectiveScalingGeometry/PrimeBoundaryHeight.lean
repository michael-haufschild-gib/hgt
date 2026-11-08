import GaloisForLFunctions.EffectiveScalingGeometry.PrimeCutoffComplex

/-!
# Exact height of the boundary submodule

Every prime deletion divides multiplicative height by at least two, for any
vertex functional. For the unweighted boundary the converse is exact: every
cycle below `N/2` fills at height `N` by adjoining prime two. Thus the boundary
image at `N` equals the cycle submodule at `N/2`, over any commutative ring.
The empty augmented degree satisfies the corresponding image identity.
-/

noncomputable section
open RHTower
open GaloisForLFunctions.HTGeometry
namespace GaloisForLFunctions.EffectiveScalingGeometry
variable (R : Type*) [CommRing R]

/-- Every prime deletion lowers multiplicative height by at least a factor of two. -/
theorem primeChainDifferential_half_cutoff
    (phi : (Nat.Primes →₀ R) →ₗ[R] R) (k N : ℕ) :
    primeChainCutoff R (k+1) N ≤
      (primeChainCutoff R k (N/2)).comap (physicalKoszulDifferential k phi) := by
  apply Submodule.span_le.mpr
  rintro x ⟨v,hv,rfl⟩
  change physicalKoszulDifferential k phi (primeChainAtom R v) ∈ primeChainCutoff R k (N/2)
  rw [primeChainAtom,physicalKoszulDifferential_ιMulti]
  apply Submodule.sum_mem
  intro i _
  apply (primeChainCutoff R k (N/2)).toAddSubgroup.zsmul_mem
  apply Submodule.smul_mem
  apply Submodule.subset_span
  refine ⟨fun j => v (i.succAbove j), ?_, rfl⟩
  have hh : 2 * ∏ j, (v (i.succAbove j) : ℕ) ≤ N := calc
    _ ≤ (v i : ℕ) * ∏ j, (v (i.succAbove j) : ℕ) :=
      Nat.mul_le_mul_right _ (v i).property.two_le
    _ = ∏ j, (v j : ℕ) := (Fin.prod_univ_succAbove (fun j => (v j : ℕ)) i).symm
    _ ≤ N := hv
  change (∏ j, (v (i.succAbove j) : ℕ)) ≤ N/2
  omega

/-- The unweighted boundary has the same height decrease. -/
theorem primeChainBoundary_half_mem (k N : ℕ) (x : PrimeChainSpace R (k+1))
    (hx : x ∈ primeChainCutoff R (k+1) N) :
    primeChainBoundary R k x ∈ primeChainCutoff R k (N/2) :=
  primeChainDifferential_half_cutoff R (primeChainAugmentation R) k N (x := x) hx

/-- Boundaries at height `N` are exactly cycles at height `N/2`. -/
theorem primeChainBoundary_image_eq_half_cycles (k N : ℕ) :
    (primeChainCutoff R ((k+1)+1) N).map (primeChainBoundary R (k+1)) =
      primeChainCutoff R (k+1) (N/2) ⊓ (primeChainBoundary R k).ker := by
  apply le_antisymm
  · intro x hx
    obtain ⟨y,hy,rfl⟩ := Submodule.mem_map.mp hx
    constructor
    · exact primeChainBoundary_half_mem R (k+1) N y hy
    · change primeChainBoundary R k (primeChainBoundary R (k+1) y) = 0
      exact LinearMap.congr_fun (primeChainBoundary_sq R k) y
  · intro x hx
    obtain ⟨y,hy⟩ := primeChainCutoff_cycle_bounds_in_double R k (N/2) ⟨x,hx⟩
    apply Submodule.mem_map.mpr
    refine ⟨y.val, ?_, hy⟩
    exact primeChainCutoff_mono R (k+2) (by omega : 2*(N/2) ≤ N) y.property

/-- The boundary-image law also includes the augmented empty-face degree. -/
theorem primeChainBoundary_zero_image_eq_half (N : ℕ) :
    (primeChainCutoff R 1 N).map (primeChainBoundary R 0) = primeChainCutoff R 0 (N/2) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨y,hy,rfl⟩ := Submodule.mem_map.mp hx
    exact primeChainDifferential_half_cutoff R (primeChainAugmentation R) 0 N hy
  · intro x hx
    obtain ⟨y,hy⟩ := primeChainCutoff_zero_bounds_in_double R (N/2) ⟨x,hx⟩
    apply Submodule.mem_map.mpr
    exact ⟨y.val,primeChainCutoff_mono R 1 (by omega : 2*(N/2) ≤ N) y.property,hy⟩

#print axioms primeChainDifferential_half_cutoff
#print axioms primeChainBoundary_image_eq_half_cycles
#print axioms primeChainBoundary_zero_image_eq_half
end GaloisForLFunctions.EffectiveScalingGeometry
