import GaloisForLFunctions.EffectiveScalingGeometry.PrimeTwoChainSplitting
import GaloisForLFunctions.EffectiveScalingGeometry.PrimeOddCutoffComplex
import GaloisForLFunctions.EffectiveScalingGeometry.PrimeWeightedBoundarySaturation

/-!
# The sharper height of weighted cycle components

For an integral prime-weighted cycle, deleting prime two lowers product height
by at least three. The odd part of its boundary gives
`d(Ox)+2δ₂x=0`; odd deletion already has this factor-three decrease.
Saturation of the integer cutoff lattice removes the factor two.
-/

noncomputable section
open RHTower GaloisForLFunctions.HTGeometry
namespace GaloisForLFunctions.EffectiveScalingGeometry
variable (R : Type*) [CommRing R]

/-- The odd part of a weighted two-cone boundary is twice its odd input. -/
theorem primeOddProjection_valueBoundary_cone (k : ℕ) (x : PrimeChainSpace R k) :
    oddChainProjection R k (primeValueBoundary R k (primeChainCone R k primeTwoLabel x)) =
      (2 : R) • oddChainProjection R k x := by
  cases k with
  | zero =>
    rw [oddChainProjection_zero]
    simp only [LinearMap.id_apply]
    simpa only [LinearMap.comp_apply,LinearMap.smul_apply,LinearMap.id_apply,
      primeValueFunctional_single,Nat.cast_ofNat] using
      LinearMap.congr_fun
        (koszul_cartan_zero_map (primeValueFunctional R) (Finsupp.single primeTwoLabel (1 : R))) x
  | succ k =>
    have h := congrArg (oddChainProjection R (k+1))
      (LinearMap.congr_fun (primeValueBoundary_cartan R k primeTwoLabel) x)
    have hz : oddChainProjection R (k+1)
        (primeChainCone R k primeTwoLabel (primeValueBoundary R k x)) = 0 :=
      LinearMap.congr_fun (oddChainProjection_comp_cone R k) (primeValueBoundary R k x)
    simpa only [LinearMap.add_apply,LinearMap.comp_apply,LinearMap.smul_apply,
      LinearMap.id_apply,Nat.cast_ofNat,map_add,map_smul,hz,add_zero] using h

/-- In an integral weighted cycle, deleting two lowers height by at least three. -/
theorem primeValueCycle_twoDeletion_third (k N : ℕ)
    (x : ↥(primeChainCutoff ℤ (k+1) N ⊓ (primeValueBoundary ℤ k).ker)) :
    primeTwoDeletion ℤ k x.val ∈ primeOddCutoff ℤ k (N/3) := by
  let o : primeOddCutoff ℤ (k+1) N :=
    ⟨oddChainProjection ℤ (k+1) x.val,
      oddChainProjection_cutoff ℤ (k+1) N x.property.1,⟨x.val,rfl⟩⟩
  have hdmem : primeValueBoundary ℤ k o.val ∈ primeOddCutoff ℤ k (N/3) :=
    primeOddDifferential_third_cutoff ℤ (primeValueFunctional ℤ) k N o.property
  have hdfix : oddChainProjection ℤ k (primeValueBoundary ℤ k o.val) =
      primeValueBoundary ℤ k o.val :=
    oddChainProjection_fixes_range ℤ k ⟨_,hdmem.2⟩
  have hvfix : oddChainProjection ℤ k (primeTwoDeletion ℤ k x.val) = primeTwoDeletion ℤ k x.val :=
    LinearMap.congr_fun (oddProjection_comp_twoDeletion ℤ k) x.val
  have hx : primeValueBoundary ℤ k x.val = 0 := x.property.2
  have he := congrArg (fun z => oddChainProjection ℤ k (primeValueBoundary ℤ k z))
    (LinearMap.congr_fun (oddProjection_add_cone_twoDeletion ℤ k) x.val)
  change oddChainProjection ℤ k (primeValueBoundary ℤ k (oddChainProjection ℤ (k+1) x.val)) =
    primeValueBoundary ℤ k (oddChainProjection ℤ (k+1) x.val) at hdfix
  have h : primeValueBoundary ℤ k o.val +
      (primeTwoDeletion ℤ k x.val + primeTwoDeletion ℤ k x.val) = 0 := by
    change primeValueBoundary ℤ k (oddChainProjection ℤ (k+1) x.val) +
      (primeTwoDeletion ℤ k x.val + primeTwoDeletion ℤ k x.val) = 0
    simpa only [LinearMap.add_apply,LinearMap.comp_apply,LinearMap.id_apply,
      map_add,hdfix,primeOddProjection_valueBoundary_cone,hvfix,two_smul,hx,map_zero] using he
  have hm : (2 : ℤ) • primeTwoDeletion ℤ k x.val ∈ primeChainCutoff ℤ k (N/3) := by
    have he2 : (2 : ℤ) • primeTwoDeletion ℤ k x.val = -primeValueBoundary ℤ k o.val := by
      calc
        (2 : ℤ) • primeTwoDeletion ℤ k x.val =
            primeTwoDeletion ℤ k x.val + primeTwoDeletion ℤ k x.val := two_smul ℤ _
        _ = (primeValueBoundary ℤ k o.val +
              (primeTwoDeletion ℤ k x.val + primeTwoDeletion ℤ k x.val)) -
                primeValueBoundary ℤ k o.val := by abel
        _ = -primeValueBoundary ℤ k o.val := by rw [h,zero_sub]
    rw [he2]
    exact Submodule.neg_mem _ hdmem.1
  exact ⟨(primeIntegerCutoff_saturated k (N/3) 2 (by omega) _).mp hm,
    ⟨primeTwoDeletion ℤ k x.val,hvfix⟩⟩

#print axioms primeOddProjection_valueBoundary_cone
#print axioms primeValueCycle_twoDeletion_third
end GaloisForLFunctions.EffectiveScalingGeometry
