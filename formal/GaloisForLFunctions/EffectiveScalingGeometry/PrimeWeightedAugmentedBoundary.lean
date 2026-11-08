import GaloisForLFunctions.EffectiveScalingGeometry.PrimeWeightedBoundaryCoordinates

/-!
# The integral prime-weighted boundary lattice in augmented degree zero

The empty-degree boundary lattice has the same three-summand formula as the
positive degrees. Splitting a vertex chain separates its odd boundary from
twice its prime-two coordinate. The Bézout cone fills every low empty chain,
and the prime-two cone fills every doubled half-height chain. No nonzero empty
chain is annihilated by adjoining three: contraction recovers the chain.
-/

noncomputable section
open RHTower GaloisForLFunctions.HTGeometry
namespace GaloisForLFunctions.EffectiveScalingGeometry

/-- Contracting the chosen prime recovers every empty chain from its cone. -/
theorem primeCoordinateDeletion_zero_cone (R : Type*) [CommRing R] (p : Nat.Primes)
    (x : PrimeChainSpace R 0) :
    primeCoordinateDeletion R p 0 (primeChainCone R 0 p x) = x := by
  simpa only [LinearMap.comp_apply,LinearMap.smul_apply,LinearMap.id_apply,
    primeCoordinateFunctional_self,one_smul] using
    LinearMap.congr_fun
      (koszul_cartan_zero_map (primeCoordinateFunctional R p) (Finsupp.single p (1 : R))) x

/-- The boundary of a prime-two cone of an empty chain is its double. -/
theorem primeValueBoundary_zero_twoCone (x : PrimeChainSpace ℤ 0) :
    primeValueBoundary ℤ 0 (primeChainCone ℤ 0 primeTwoLabel x) = x+x := by
  simpa only [LinearMap.comp_apply,LinearMap.smul_apply,LinearMap.id_apply,
    primeValueFunctional_single,Nat.cast_ofNat,two_smul,LinearMap.add_apply] using
    LinearMap.congr_fun
      (koszul_cartan_zero_map (primeValueFunctional ℤ) (Finsupp.single primeTwoLabel (1 : ℤ))) x

/-- In empty degree, the odd and prime-two parts supply the two boundary terms. -/
theorem primeValueBoundary_zeroTwoSplit (y : PrimeChainSpace ℤ 1) :
    primeValueBoundary ℤ 0 y = primeValueBoundary ℤ 0 (oddChainProjection ℤ 1 y) +
      (primeTwoDeletion ℤ 0 y + primeTwoDeletion ℤ 0 y) := by
  have hs := LinearMap.congr_fun (oddProjection_add_cone_twoDeletion ℤ 0) y
  calc
    _ = primeValueBoundary ℤ 0 (oddChainProjection ℤ 1 y) +
        primeValueBoundary ℤ 0 (primeChainCone ℤ 0 primeTwoLabel (primeTwoDeletion ℤ 0 y)) :=
      (congrArg (primeValueBoundary ℤ 0) hs).symm.trans (map_add _ _ _)
    _ = _ := by rw [primeValueBoundary_zero_twoCone]

/-- The augmented empty-degree boundary lattice has the same arithmetic formula. -/
theorem primeValueZeroBoundary_eq_lattice (N : ℕ) :
    primeValueBoundaries 0 N = primeValueCoordinateLattice 0 N := by
  apply le_antisymm
  · rintro x ⟨y,hy,rfl⟩
    rw [primeValueBoundary_zeroTwoSplit]
    apply Submodule.add_mem
    · exact primeValueCoordinateLattice_low 0 N
        (primeOddDifferential_third_cutoff ℤ (primeValueFunctional ℤ) 0 N
          ⟨oddChainProjection_cutoff ℤ 1 N hy,⟨y,rfl⟩⟩)
    · exact primeValueCoordinateLattice_double 0 N (primeTwoDeletion_half_odd ℤ 0 N hy)
  · apply sup_le
    · apply sup_le
      · intro x hx
        apply Submodule.mem_map.mpr
        refine ⟨primeBezoutCone ℤ 0 x,?_,?_⟩
        · exact primeChainCutoff_mono ℤ 1 (show 3*(N/3) ≤ N by omega)
            (primeBezoutCone_cutoff ℤ 0 (N/3) hx.1)
        · exact LinearMap.congr_fun (primeBezoutCone_contracts_zero ℤ) x
      · rintro x ⟨y,hy,rfl⟩
        apply Submodule.mem_map.mpr
        refine ⟨primeChainCone ℤ 0 primeTwoLabel y,?_,primeValueBoundary_zero_twoCone y⟩
        exact primeChainCutoff_mono ℤ 1 (show 2*(N/2) ≤ N by omega)
          (primeChainCone_cutoff ℤ 0 (N/2) primeTwoLabel hy.1)
    · intro x hx
      have hz : primeChainCone ℤ 0 primeThreeLabel x = 0 := hx.2
      have he : x = 0 := by
        simpa only [hz,map_zero] using (primeCoordinateDeletion_zero_cone ℤ primeThreeLabel x).symm
      rw [he]
      exact Submodule.zero_mem _

#print axioms primeCoordinateDeletion_zero_cone
#print axioms primeValueZeroBoundary_eq_lattice
end GaloisForLFunctions.EffectiveScalingGeometry
