import GaloisForLFunctions.EffectiveScalingGeometry.PrimeWeightedCycleHeight

/-!
# Natural integral coordinates for prime-weighted cycles

The Bézout cone gives the cycle projection `d((e₃−e₂)∧·)`.
Its inverse on odd chains is odd projection corrected by `e₃∧δ₂`.
Both maps preserve the original cutoff over the integers: odd boundaries
and the two-deletion of integral weighted cycles have one-third height.
The resulting equivalence is natural in height and supplies an actual
integral cycle basis indexed by bounded odd prime faces.
-/

noncomputable section
open RHTower GaloisForLFunctions.HTGeometry
namespace GaloisForLFunctions.EffectiveScalingGeometry
attribute [local instance] primeLabelLinearOrder
variable (R : Type*) [CommRing R]

private theorem primeWedgeLeft_sub (k : ℕ) (e f : Nat.Primes →₀ R) :
    wedgeLeft (R := R) k (e-f) = wedgeLeft (R := R) k e - wedgeLeft (R := R) k f := by
  unfold wedgeLeft
  rw [map_sub,map_sub]

/-- The prime-three label. -/
abbrev primeThreeLabel : Nat.Primes := ⟨3,Nat.prime_three⟩

private theorem primeThreeLabel_ne_two : primeThreeLabel ≠ primeTwoLabel := by
  intro h
  have he := congrArg Subtype.val h
  change (3 : ℕ) = 2 at he
  omega

/-- The integral vertex vector with prime-valued boundary one. -/
def primeBezoutVertex : Nat.Primes →₀ R :=
  Finsupp.single primeThreeLabel 1 - Finsupp.single primeTwoLabel 1

theorem primeBezoutCone_eq_wedge (k : ℕ) :
    primeBezoutCone R k = wedgeLeft (R := R) k (primeBezoutVertex R) := by
  rw [primeBezoutVertex,primeWedgeLeft_sub]
  rfl

/-- Adjoining the same Bézout vector twice vanishes. -/
theorem primeBezoutCone_sq (k : ℕ) :
    (primeBezoutCone R (k+1)).comp (primeBezoutCone R k) = 0 := by
  rw [primeBezoutCone_eq_wedge,primeBezoutCone_eq_wedge]
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  simp only [LinearMap.compAlternatingMap_apply,LinearMap.comp_apply,
    LinearMap.zero_apply,wedgeLeft_ιMulti]
  apply AlternatingMap.map_eq_zero_of_eq _ _ (i := 0) (j := (0 : Fin (k+1)).succ)
  · simp only [Fin.cons_zero,Fin.cons_succ]
  · exact (Fin.succ_ne_zero _).symm

/-- Projection to prime-weighted cycles using the integral Bézout cone. -/
def primeValueCycleProjector (k : ℕ) :
    PrimeChainSpace R (k+1) →ₗ[R] PrimeChainSpace R (k+1) :=
  (primeValueBoundary R (k+1)).comp (primeBezoutCone R (k+1))

theorem primeValueCycleProjector_cycle (k : ℕ) (x : PrimeChainSpace R (k+1)) :
    primeValueBoundary R k (primeValueCycleProjector R k x) = 0 :=
  LinearMap.congr_fun (physicalKoszulDifferential_sq k (primeValueFunctional R))
    (primeBezoutCone R (k+1) x)

theorem primeValueCycleProjector_add (k : ℕ) (x : PrimeChainSpace R (k+1)) :
    primeValueCycleProjector R k x + primeBezoutCone R k (primeValueBoundary R k x) = x :=
  LinearMap.congr_fun (primeBezoutCone_contracts R k) x

theorem primeValueCycleProjector_eq_sub (k : ℕ) (x : PrimeChainSpace R (k+1)) :
    primeValueCycleProjector R k x = x - primeBezoutCone R k (primeValueBoundary R k x) := by
  calc
    _ = (primeValueCycleProjector R k x + primeBezoutCone R k (primeValueBoundary R k x)) -
        primeBezoutCone R k (primeValueBoundary R k x) := by abel
    _ = _ := by rw [primeValueCycleProjector_add]

theorem primeValueCycleProjector_fixes (k : ℕ) (x : (primeValueBoundary R k).ker) :
    primeValueCycleProjector R k x.val = x.val := by
  rw [primeValueCycleProjector_eq_sub,x.property,map_zero,sub_zero]

theorem primeValueCycleProjector_cone (k : ℕ) (x : PrimeChainSpace R k) :
    primeValueCycleProjector R k (primeBezoutCone R k x) = 0 := by
  change primeValueBoundary R (k+1)
    (primeBezoutCone R (k+1) (primeBezoutCone R k x)) = 0
  rw [show primeBezoutCone R (k+1) (primeBezoutCone R k x) = 0 from
    LinearMap.congr_fun (primeBezoutCone_sq R k) x,map_zero]

/-- Adjoining an odd prime preserves odd support and has its usual product cost. -/
theorem primeOddCone_cutoff (k N : ℕ) (p : Nat.Primes) (hp : p ≠ primeTwoLabel) :
    primeOddCutoff R k N ≤ (primeOddCutoff R (k+1) (p*N)).comap (primeChainCone R k p) := by
  rw [primeOddCutoff_eq_span_basis]
  apply Submodule.span_le.mpr
  rintro x ⟨s,hs,rfl⟩
  let v : Fin k → Nat.Primes := Set.powersetCard.ofFinEmbEquiv.symm s
  have ho : ∀ i, v i ≠ primeTwoLabel := by
    intro i hi
    exact hs.2 ((Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem s primeTwoLabel).mp ⟨i,hi⟩)
  change primeChainCone R k p (primeChainBasis R k s) ∈ primeOddCutoff R (k+1) (p*N)
  rw [primeChainBasis_eq_atom,primeChainCone_atom]
  apply primeOddChainAtom_mem_cutoff
  · have hv : (∏ i, (v i : ℕ)) ≤ N := (primeFaceProduct_eq_prod_enum s) ▸ hs.1
    simpa only [Fin.prod_univ_succ,Fin.cons_zero,Fin.cons_succ] using Nat.mul_le_mul_left (p : ℕ) hv
  · intro i
    exact Fin.cases hp (fun j => ho j) i

/-- The Bézout cycle projection preserves the original height on odd chains. -/
theorem primeValueCycleProjector_odd_cutoff (k N : ℕ) :
    primeOddCutoff R (k+1) N ≤ (primeChainCutoff R (k+1) N).comap (primeValueCycleProjector R k) := by
  intro x hx
  have hd := primeOddDifferential_third_cutoff R (primeValueFunctional R) k N hx
  change primeValueCycleProjector R k x ∈ primeChainCutoff R (k+1) N
  rw [primeValueCycleProjector_eq_sub]
  exact Submodule.sub_mem _ hx.1
    (primeChainCutoff_mono R (k+1) (show 3*(N/3) ≤ N by omega)
      (primeBezoutCone_cutoff R k (N/3) hd.1))

/-- Actual weighted cycles at a product cutoff. -/
def primeValueCutoffCycles (k N : ℕ) : Submodule R (PrimeChainSpace R (k+1)) :=
  primeChainCutoff R (k+1) N ⊓ (primeValueBoundary R k).ker

/-- Odd chains have canonical integral weighted cycle representatives at the same height. -/
def primeOddToValueCycle (k N : ℕ) :
    primeOddCutoff R (k+1) N →ₗ[R] primeValueCutoffCycles R k N :=
  (primeValueCycleProjector R k).restrict (fun x hx =>
    ⟨primeValueCycleProjector_odd_cutoff R k N hx,primeValueCycleProjector_cycle R k x⟩)

/-- Odd coordinates correct the two-deletion by adjoining three. -/
def primeValueOddCoordinates (k : ℕ) :
    PrimeChainSpace R (k+1) →ₗ[R] PrimeChainSpace R (k+1) :=
  oddChainProjection R (k+1) + (primeChainCone R k primeThreeLabel).comp (primeTwoDeletion R k)

theorem primeValueOddCoordinates_eq (k : ℕ) (x : PrimeChainSpace R (k+1)) :
    primeValueOddCoordinates R k x = x + primeBezoutCone R k (primeTwoDeletion R k x) := by
  have h := LinearMap.congr_fun (oddProjection_add_cone_twoDeletion R k) x
  change oddChainProjection R (k+1) x + primeChainCone R k primeTwoLabel (primeTwoDeletion R k x) = x at h
  change oddChainProjection R (k+1) x + primeChainCone R k primeThreeLabel (primeTwoDeletion R k x) =
    x + (primeChainCone R k primeThreeLabel (primeTwoDeletion R k x) -
      primeChainCone R k primeTwoLabel (primeTwoDeletion R k x))
  calc
    _ = (oddChainProjection R (k+1) x +
        primeChainCone R k primeTwoLabel (primeTwoDeletion R k x)) +
        (primeChainCone R k primeThreeLabel (primeTwoDeletion R k x) -
          primeChainCone R k primeTwoLabel (primeTwoDeletion R k x)) := by abel
    _ = _ := by rw [h]

/-- The correction has the original height for integral weighted cycles. -/
theorem primeValueOddCoordinates_cutoff (k N : ℕ) :
    primeValueCutoffCycles ℤ k N ≤ (primeOddCutoff ℤ (k+1) N).comap (primeValueOddCoordinates ℤ k) := by
  intro x hx
  change oddChainProjection ℤ (k+1) x + primeChainCone ℤ k primeThreeLabel (primeTwoDeletion ℤ k x) ∈
    primeOddCutoff ℤ (k+1) N
  apply Submodule.add_mem
  · exact ⟨oddChainProjection_cutoff ℤ (k+1) N hx.1,⟨x,rfl⟩⟩
  · exact primeOddCutoff_mono ℤ (k+1) (show 3*(N/3) ≤ N by omega)
      (primeOddCone_cutoff ℤ k (N/3) primeThreeLabel primeThreeLabel_ne_two
        (primeValueCycle_twoDeletion_third k N ⟨x,hx⟩))

/-- Actual integral weighted cycles map to odd chains without increasing height. -/
def primeValueCycleToOdd (k N : ℕ) :
    primeValueCutoffCycles ℤ k N →ₗ[ℤ] primeOddCutoff ℤ (k+1) N :=
  (primeValueOddCoordinates ℤ k).restrict (fun _ hx => primeValueOddCoordinates_cutoff k N hx)

/-- The cycle projection is a left inverse on weighted cycles. -/
theorem primeValueProjector_coordinates (k : ℕ) (x : (primeValueBoundary R k).ker) :
    primeValueCycleProjector R k (primeValueOddCoordinates R k x.val) = x.val := by
  rw [primeValueOddCoordinates_eq,map_add,primeValueCycleProjector_fixes R k x,
    primeValueCycleProjector_cone,add_zero]

private theorem primeTwoDeletion_odd_zero (k : ℕ) (x : (oddChainProjection R (k+1)).range) :
    primeTwoDeletion R k x.val = 0 := by
  obtain ⟨y,hy⟩ := x.property
  rw [← hy]
  exact LinearMap.congr_fun (primeTwoDeletion_comp_oddProjection R k) y

/-- Taking corrected odd coordinates recovers the original odd chain. -/
theorem primeValueCoordinates_projector (k N : ℕ) (y : primeOddCutoff R (k+1) N) :
    primeValueOddCoordinates R k (primeValueCycleProjector R k y.val) = y.val := by
  have hd := primeOddDifferential_third_cutoff R (primeValueFunctional R) k N y.property
  have h3 := primeOddCone_cutoff R k (N/3) primeThreeLabel primeThreeLabel_ne_two hd
  have hyfix := oddChainProjection_fixes_range R (k+1) ⟨y.val,y.property.2⟩
  have h3fix := oddChainProjection_fixes_range R (k+1)
    ⟨primeChainCone R k primeThreeLabel (primeValueBoundary R k y.val),h3.2⟩
  have h2zero := LinearMap.congr_fun (oddChainProjection_comp_cone R k) (primeValueBoundary R k y.val)
  have hydel := primeTwoDeletion_odd_zero R k ⟨y.val,y.property.2⟩
  have h3del := primeTwoDeletion_odd_zero R k
    ⟨primeChainCone R k primeThreeLabel (primeValueBoundary R k y.val),h3.2⟩
  have h2del := (LinearMap.congr_fun (primeTwoDeletion_comp_cone R k) (primeValueBoundary R k y.val)).trans
    (oddChainProjection_fixes_range R k ⟨_,hd.2⟩)
  rw [primeValueCycleProjector_eq_sub]
  change oddChainProjection R (k+1)
      (y.val - (primeChainCone R k primeThreeLabel (primeValueBoundary R k y.val) -
        primeChainCone R k primeTwoLabel (primeValueBoundary R k y.val))) +
    primeChainCone R k primeThreeLabel (primeTwoDeletion R k
      (y.val - (primeChainCone R k primeThreeLabel (primeValueBoundary R k y.val) -
        primeChainCone R k primeTwoLabel (primeValueBoundary R k y.val)))) = y.val
  simp only [map_sub,hyfix,h3fix,show oddChainProjection R (k+1)
      (primeChainCone R k primeTwoLabel (primeValueBoundary R k y.val)) = 0 from h2zero,
    hydel,h3del,show primeTwoDeletion R k (primeChainCone R k primeTwoLabel
      (primeValueBoundary R k y.val)) = primeValueBoundary R k y.val from h2del,
    sub_zero,zero_sub,neg_neg]
  abel

/-- Integral weighted cycles have exactly the bounded odd-face coordinate lattice. -/
def primeValueCycleOddEquiv (k N : ℕ) :
    primeValueCutoffCycles ℤ k N ≃ₗ[ℤ] primeOddCutoff ℤ (k+1) N :=
  LinearEquiv.ofLinear (primeValueCycleToOdd k N) (primeOddToValueCycle ℤ k N)
    (by
      apply LinearMap.ext
      intro y
      apply Subtype.ext
      exact primeValueCoordinates_projector ℤ k N y)
    (by
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      exact primeValueProjector_coordinates ℤ k ⟨x.val,x.property.2⟩)

theorem primeValueCutoffCycles_mono (k : ℕ) {N M : ℕ} (h : N ≤ M) :
    primeValueCutoffCycles R k N ≤ primeValueCutoffCycles R k M :=
  inf_le_inf (primeChainCutoff_mono R (k+1) h) le_rfl

/-- Corrected odd coordinates commute with actual height inclusions. -/
theorem primeValueCycleToOdd_natural (k : ℕ) {N M : ℕ} (h : N ≤ M) :
    (primeValueCycleToOdd k M).comp (Submodule.inclusion (primeValueCutoffCycles_mono ℤ k h)) =
      (Submodule.inclusion (primeOddCutoff_mono ℤ (k+1) h)).comp (primeValueCycleToOdd k N) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  rfl

/-- The chosen weighted cycle representatives also commute with height inclusions. -/
theorem primeOddToValueCycle_natural (k : ℕ) {N M : ℕ} (h : N ≤ M) :
    (primeOddToValueCycle R k M).comp (Submodule.inclusion (primeOddCutoff_mono R (k+1) h)) =
      (Submodule.inclusion (primeValueCutoffCycles_mono R k h)).comp (primeOddToValueCycle R k N) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  rfl

/-- Bounded odd prime faces form an actual integral basis of weighted cycles. -/
def primeValueCutoffCycleBasis (k N : ℕ) :
    Module.Basis (OddPrimeFace (k+1) N) ℤ (primeValueCutoffCycles ℤ k N) :=
  (oddPrimeCutoffBasis ℤ (k+1) N).map (primeValueCycleOddEquiv k N).symm

/-- A weighted basis cycle is the boundary of its integral Bézout cone. -/
theorem primeValueCutoffCycleBasis_val (k N : ℕ) (s : OddPrimeFace (k+1) N) :
    (primeValueCutoffCycleBasis k N s).val =
      primeValueCycleProjector ℤ k (primeChainBasis ℤ (k+1) s.val) := by
  rw [primeValueCutoffCycleBasis,Module.Basis.map_apply]
  change primeValueCycleProjector ℤ k (oddPrimeCutoffBasis ℤ (k+1) N s).val = _
  rw [oddPrimeCutoffBasis_val]

#print axioms primeValueCycleProjector_odd_cutoff
#print axioms primeValueCycleOddEquiv
#print axioms primeValueCycleToOdd_natural
#print axioms primeValueCutoffCycleBasis_val
end GaloisForLFunctions.EffectiveScalingGeometry
