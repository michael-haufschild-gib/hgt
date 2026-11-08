import GaloisForLFunctions.EffectiveScalingGeometry.PrimeWeightedCycleCoordinates
import GaloisForLFunctions.EffectiveScalingGeometry.PrimeConeKernel

/-!
# Exact odd-coordinate boundary lattice for integral prime weights

Corrected odd coordinates send actual weighted boundaries at height `N` onto
three explicit summands: odd chains below `N/3`, doubled odd chains below
`N/2`, and odd chains below `N/2` annihilated by adjoining prime three.
Splitting a filling into its odd and two-cone parts proves one containment;
the Bézout cone and prime-two cone supply all reverse fillings. The cone
kernel consists exactly of faces containing three. These relations determine
the arithmetic coefficient ideals before passing to categorical homology.
-/

noncomputable section
open RHTower GaloisForLFunctions.HTGeometry
namespace GaloisForLFunctions.EffectiveScalingGeometry
local instance primeBoundaryIntegerChainModule (k : ℕ) : Module ℤ (PrimeChainSpace ℤ k) :=
  (PrimeChainSpace ℤ k).module

/-- Corrected odd coordinates of actual integral weighted boundaries. -/
def primeValueBoundaryCoordinates (k N : ℕ) : Submodule ℤ (PrimeChainSpace ℤ (k+1)) :=
  (primeValueBoundaries (k+1) N).map (primeValueOddCoordinates ℤ k)

/-- The three arithmetic sources of weighted boundaries in odd coordinates. -/
def primeValueCoordinateLattice (k N : ℕ) : Submodule ℤ (PrimeChainSpace ℤ k) :=
  (primeOddCutoff ℤ k (N/3) ⊔
    (primeOddCutoff ℤ k (N/2)).map (LinearMap.id + LinearMap.id)) ⊔
    (primeOddCutoff ℤ k (N/2) ⊓ (primeChainCone ℤ k primeThreeLabel).ker)

theorem primeValueCoordinateLattice_low (k N : ℕ) {x : PrimeChainSpace ℤ k}
    (hx : x ∈ primeOddCutoff ℤ k (N/3)) : x ∈ primeValueCoordinateLattice k N := by
  apply Submodule.mem_sup.mpr
  refine ⟨x,?_,0,Submodule.zero_mem _,add_zero x⟩
  exact Submodule.mem_sup.mpr ⟨x,hx,0,Submodule.zero_mem _,add_zero x⟩

theorem primeValueCoordinateLattice_double (k N : ℕ) {x : PrimeChainSpace ℤ k}
    (hx : x ∈ primeOddCutoff ℤ k (N/2)) : x+x ∈ primeValueCoordinateLattice k N := by
  apply Submodule.mem_sup.mpr
  refine ⟨x+x,?_,0,Submodule.zero_mem _,add_zero (x+x)⟩
  exact Submodule.mem_sup.mpr
    ⟨0,Submodule.zero_mem _,x+x,Submodule.mem_map.mpr ⟨x,hx,rfl⟩,zero_add (x+x)⟩

theorem primeValueCoordinateLattice_three (k N : ℕ) {x : PrimeChainSpace ℤ k}
    (hx : x ∈ primeOddCutoff ℤ k (N/2) ⊓ (primeChainCone ℤ k primeThreeLabel).ker) :
    x ∈ primeValueCoordinateLattice k N :=
  Submodule.mem_sup.mpr ⟨0,Submodule.zero_mem _,x,hx,zero_add x⟩

/-- Corrected coordinates act identically on already odd chains. -/
theorem primeValueOddCoordinates_on_odd (k N : ℕ) (x : primeOddCutoff ℤ (k+1) N) :
    primeValueOddCoordinates ℤ k x.val = x.val := by
  have ho := oddChainProjection_fixes_range ℤ (k+1) ⟨x.val,x.property.2⟩
  have hd := LinearMap.congr_fun (primeTwoDeletion_comp_oddProjection ℤ k) x.val
  have hz : primeTwoDeletion ℤ k x.val = 0 := by
    simpa only [LinearMap.comp_apply,ho,LinearMap.zero_apply] using hd
  change oddChainProjection ℤ (k+1) x.val + primeChainCone ℤ k primeThreeLabel (primeTwoDeletion ℤ k x.val) = x.val
  rw [ho,hz,map_zero,add_zero]

/-- In corrected coordinates, a two-cone of an odd chain becomes its three-cone. -/
theorem primeValueOddCoordinates_twoCone (k N : ℕ) (x : primeOddCutoff ℤ k N) :
    primeValueOddCoordinates ℤ k (primeChainCone ℤ k primeTwoLabel x.val) =
      primeChainCone ℤ k primeThreeLabel x.val := by
  have ho := LinearMap.congr_fun (oddChainProjection_comp_cone ℤ k) x.val
  have hd := (LinearMap.congr_fun (primeTwoDeletion_comp_cone ℤ k) x.val).trans
    (oddChainProjection_fixes_range ℤ k ⟨x.val,x.property.2⟩)
  change oddChainProjection ℤ (k+1) (primeChainCone ℤ k primeTwoLabel x.val) +
    primeChainCone ℤ k primeThreeLabel (primeTwoDeletion ℤ k (primeChainCone ℤ k primeTwoLabel x.val)) = _
  rw [show oddChainProjection ℤ (k+1) (primeChainCone ℤ k primeTwoLabel x.val) = 0 from ho,
    show primeTwoDeletion ℤ k (primeChainCone ℤ k primeTwoLabel x.val) = x.val from hd,zero_add]

/-- Every summand of the coordinate lattice has an explicit filling within the cutoff. -/
theorem primeValueCoordinateLattice_le_boundaries (k N : ℕ) :
    primeValueCoordinateLattice (k+1) N ≤ primeValueBoundaryCoordinates k N := by
  apply sup_le
  · apply sup_le
    · intro z hz
      apply Submodule.mem_map.mpr
      refine ⟨primeValueCycleProjector ℤ k z,?_,primeValueCoordinates_projector ℤ k (N/3) ⟨z,hz⟩⟩
      apply Submodule.mem_map.mpr
      refine ⟨primeBezoutCone ℤ (k+1) (primeValueCycleProjector ℤ k z),?_,?_⟩
      · exact primeChainCutoff_mono ℤ (k+2) (show 3*(N/3) ≤ N by omega)
          (primeBezoutCone_cutoff ℤ (k+1) (N/3) (primeValueCycleProjector_odd_cutoff ℤ k (N/3) hz))
      · exact primeValueCycleProjector_fixes ℤ k
          ⟨primeValueCycleProjector ℤ k z,primeValueCycleProjector_cycle ℤ k z⟩
    · rintro z ⟨w,hw,rfl⟩
      apply Submodule.mem_map.mpr
      refine ⟨primeValueCycleProjector ℤ k w + primeValueCycleProjector ℤ k w,?_,?_⟩
      · apply Submodule.mem_map.mpr
        refine ⟨primeChainCone ℤ (k+1) primeTwoLabel (primeValueCycleProjector ℤ k w),?_,?_⟩
        · exact primeChainCutoff_mono ℤ (k+2) (show 2*(N/2) ≤ N by omega)
            (primeChainCone_cutoff ℤ (k+1) (N/2) primeTwoLabel
              (primeValueCycleProjector_odd_cutoff ℤ k (N/2) hw))
        · have h := LinearMap.congr_fun (primeValueBoundary_cartan ℤ k primeTwoLabel)
            (primeValueCycleProjector ℤ k w)
          simpa only [LinearMap.add_apply,LinearMap.comp_apply,LinearMap.smul_apply,
            LinearMap.id_apply,Nat.cast_ofNat,primeValueCycleProjector_cycle,map_zero,add_zero,two_smul] using h
      · change primeValueOddCoordinates ℤ k
          (primeValueCycleProjector ℤ k w + primeValueCycleProjector ℤ k w) = w+w
        rw [map_add,primeValueCoordinates_projector ℤ k (N/2) ⟨w,hw⟩]
  · intro z hz
    apply Submodule.mem_map.mpr
    refine ⟨primeValueCycleProjector ℤ k z,?_,primeValueCoordinates_projector ℤ k (N/2) ⟨z,hz.1⟩⟩
    apply Submodule.mem_map.mpr
    refine ⟨-primeChainCone ℤ (k+1) primeTwoLabel z,?_,?_⟩
    · exact Submodule.neg_mem _ (primeChainCutoff_mono ℤ (k+2) (show 2*(N/2) ≤ N by omega)
        (primeChainCone_cutoff ℤ (k+1) (N/2) primeTwoLabel hz.1.1))
    · have h3 : primeChainCone ℤ (k+1) primeThreeLabel z = 0 := hz.2
      change primeValueBoundary ℤ (k+1) (-primeChainCone ℤ (k+1) primeTwoLabel z) =
        primeValueBoundary ℤ (k+1)
          (primeChainCone ℤ (k+1) primeThreeLabel z - primeChainCone ℤ (k+1) primeTwoLabel z)
      rw [h3,zero_sub]

/-- Cartan's identity after splitting a chain into its odd and two-cone parts. -/
theorem primeValueBoundary_twoSplit (k : ℕ) (y : PrimeChainSpace ℤ (k+2)) :
    primeValueBoundary ℤ (k+1) y =
      primeValueBoundary ℤ (k+1) (oddChainProjection ℤ (k+2) y) +
      (primeTwoDeletion ℤ (k+1) y + primeTwoDeletion ℤ (k+1) y) -
      primeChainCone ℤ k primeTwoLabel (primeValueBoundary ℤ k (primeTwoDeletion ℤ (k+1) y)) := by
  have hs := LinearMap.congr_fun (oddProjection_add_cone_twoDeletion ℤ (k+1)) y
  have hc : primeValueBoundary ℤ (k+1) (primeChainCone ℤ (k+1) primeTwoLabel (primeTwoDeletion ℤ (k+1) y)) +
      primeChainCone ℤ k primeTwoLabel (primeValueBoundary ℤ k (primeTwoDeletion ℤ (k+1) y)) =
      primeTwoDeletion ℤ (k+1) y + primeTwoDeletion ℤ (k+1) y := by
    simpa only [LinearMap.add_apply,LinearMap.comp_apply,LinearMap.smul_apply,
      LinearMap.id_apply,Nat.cast_ofNat,two_smul] using
      LinearMap.congr_fun (primeValueBoundary_cartan ℤ k primeTwoLabel) (primeTwoDeletion ℤ (k+1) y)
  calc
    _ = primeValueBoundary ℤ (k+1) (oddChainProjection ℤ (k+2) y) +
        primeValueBoundary ℤ (k+1) (primeChainCone ℤ (k+1) primeTwoLabel (primeTwoDeletion ℤ (k+1) y)) :=
      (congrArg (primeValueBoundary ℤ (k+1)) hs).symm.trans (map_add _ _ _)
    _ = _ := by rw [← hc]; abel

/-- The three-cone of the boundary of an odd half-height chain stays at half-height. -/
theorem primeValueBoundary_threeCone_half (k N : ℕ)
    (v : primeOddCutoff ℤ (k+1) (N/2)) :
    primeChainCone ℤ k primeThreeLabel (primeValueBoundary ℤ k v.val) ∈
      primeOddCutoff ℤ (k+1) (N/2) ⊓ (primeChainCone ℤ (k+1) primeThreeLabel).ker := by
  constructor
  · have hp : primeThreeLabel ≠ primeTwoLabel := by
      intro h
      have hh := congrArg Subtype.val h
      change (3 : ℕ) = 2 at hh
      omega
    exact primeOddCutoff_mono ℤ (k+1) (show 3*((N/2)/3) ≤ N/2 by omega)
      (primeOddCone_cutoff ℤ k ((N/2)/3) primeThreeLabel hp
        (primeOddDifferential_third_cutoff ℤ (primeValueFunctional ℤ) k (N/2) v.property))
  · exact LinearMap.congr_fun (primeChainCone_sq ℤ primeThreeLabel k) (primeValueBoundary ℤ k v.val)

/-- Corrected coordinates of a boundary are the sum of its three arithmetic parts. -/
theorem primeValueBoundaryCoordinates_formula (k N : ℕ)
    (y : primeChainCutoff ℤ (k+2) N) :
    primeValueOddCoordinates ℤ k (primeValueBoundary ℤ (k+1) y.val) =
      primeValueBoundary ℤ (k+1) (oddChainProjection ℤ (k+2) y.val) +
      (primeTwoDeletion ℤ (k+1) y.val + primeTwoDeletion ℤ (k+1) y.val) -
      primeChainCone ℤ k primeThreeLabel (primeValueBoundary ℤ k (primeTwoDeletion ℤ (k+1) y.val)) := by
  have ho : oddChainProjection ℤ (k+2) y.val ∈ primeOddCutoff ℤ (k+2) N :=
    ⟨oddChainProjection_cutoff ℤ (k+2) N y.property,⟨y.val,rfl⟩⟩
  have hv := primeTwoDeletion_half_odd ℤ (k+1) N y.property
  have hdo := primeOddDifferential_third_cutoff ℤ (primeValueFunctional ℤ) (k+1) N ho
  have hdv := primeOddDifferential_third_cutoff ℤ (primeValueFunctional ℤ) k (N/2) hv
  rw [primeValueBoundary_twoSplit,map_sub,map_add,map_add,
    primeValueOddCoordinates_on_odd k (N/3) ⟨_,hdo⟩,
    primeValueOddCoordinates_on_odd k (N/2) ⟨_,hv⟩,
    primeValueOddCoordinates_twoCone k ((N/2)/3) ⟨_,hdv⟩]

/-- A bounded filling has its corrected boundary in the coordinate lattice. -/
theorem primeValueBoundaryCoordinates_mem_lattice (k N : ℕ)
    (y : primeChainCutoff ℤ (k+2) N) :
    primeValueOddCoordinates ℤ k (primeValueBoundary ℤ (k+1) y.val) ∈
      primeValueCoordinateLattice (k+1) N := by
  have ho : oddChainProjection ℤ (k+2) y.val ∈ primeOddCutoff ℤ (k+2) N :=
    ⟨oddChainProjection_cutoff ℤ (k+2) N y.property,⟨y.val,rfl⟩⟩
  have hv : primeTwoDeletion ℤ (k+1) y.val ∈ primeOddCutoff ℤ (k+1) (N/2) :=
    @primeTwoDeletion_half_odd ℤ _ (k+1) N y.val y.property
  have h₁ : primeValueBoundary ℤ (k+1) (oddChainProjection ℤ (k+2) y.val) ∈
      primeValueCoordinateLattice (k+1) N :=
    primeValueCoordinateLattice_low (k+1) N
      (x := primeValueBoundary ℤ (k+1) (oddChainProjection ℤ (k+2) y.val))
      (@primeOddDifferential_third_cutoff ℤ _ (primeValueFunctional ℤ) (k+1) N
        (oddChainProjection ℤ (k+2) y.val) ho)
  have h₂ : primeTwoDeletion ℤ (k+1) y.val + primeTwoDeletion ℤ (k+1) y.val ∈
      primeValueCoordinateLattice (k+1) N := primeValueCoordinateLattice_double (k+1) N hv
  have h₃ : primeChainCone ℤ k primeThreeLabel
      (primeValueBoundary ℤ k (primeTwoDeletion ℤ (k+1) y.val)) ∈
      primeValueCoordinateLattice (k+1) N :=
    primeValueCoordinateLattice_three (k+1) N (primeValueBoundary_threeCone_half k N ⟨_,hv⟩)
  have hsum := (primeValueCoordinateLattice (k+1) N).sub_mem
    ((primeValueCoordinateLattice (k+1) N).add_mem h₁ h₂) h₃
  exact (congrArg (fun z : PrimeChainSpace ℤ (k+1) =>
    z ∈ primeValueCoordinateLattice (k+1) N)
      (primeValueBoundaryCoordinates_formula k N y)).mpr hsum

/-- Splitting a filling gives the three coordinate components of its boundary. -/
theorem primeValueBoundaryCoordinates_le_lattice (k N : ℕ) :
    primeValueBoundaryCoordinates k N ≤ primeValueCoordinateLattice (k+1) N := by
  rintro z ⟨b,⟨y,hy,rfl⟩,rfl⟩
  exact primeValueBoundaryCoordinates_mem_lattice k N ⟨y,hy⟩

/-- The boundary lattice is exactly low odd chains, doubled half chains, and half chains containing three. -/
theorem primeValueBoundaryCoordinates_eq_lattice (k N : ℕ) :
    primeValueBoundaryCoordinates k N = primeValueCoordinateLattice (k+1) N :=
  le_antisymm (primeValueBoundaryCoordinates_le_lattice k N) (primeValueCoordinateLattice_le_boundaries k N)

#print axioms primeValueCoordinateLattice_le_boundaries
#print axioms primeValueBoundaryCoordinates_le_lattice
#print axioms primeValueBoundaryCoordinates_eq_lattice
end GaloisForLFunctions.EffectiveScalingGeometry
