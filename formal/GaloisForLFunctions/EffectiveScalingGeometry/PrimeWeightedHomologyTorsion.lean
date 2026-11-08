import GaloisForLFunctions.EffectiveScalingGeometry.PrimeWeightedBoundarySaturation
import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.ModuleHomologyClasses

/-!
# Sharp torsion exponent of actual prime-weighted homology

Every integral torsion class is killed by two. Representing a class by an
actual cutoff cycle reduces this to boundary saturation: a bounding nonzero
multiple forces half height, and the prime-two cone then fills the double.
The empty-face class at height two is nonzero and has order two.
-/

noncomputable section
open CategoryTheory RHTower
open DifferentialGeometry.Topology
namespace GaloisForLFunctions.EffectiveScalingGeometry

/-- The actual adjacent degrees of the prime-valued cutoff complex. -/
abbrev primeValueShortComplex (k N : ℕ) :=
  (primeCutoffComplex ℤ (primeValueFunctional ℤ) N).sc' (k+1) k (k-1)

theorem primeValueShort_f (k N : ℕ) :
    (primeValueShortComplex k N).f =
      ModuleCat.ofHom (primeCutoffDifferential ℤ (primeValueFunctional ℤ) k N) := by
  change (primeCutoffComplex ℤ (primeValueFunctional ℤ) N).d (k+1) k = _
  simp only [primeCutoffComplex,ChainComplex.of_d]

theorem primeValueShort_g_succ (k N : ℕ) :
    (primeValueShortComplex (k+1) N).g =
      ModuleCat.ofHom (primeCutoffDifferential ℤ (primeValueFunctional ℤ) k N) := by
  change (primeCutoffComplex ℤ (primeValueFunctional ℤ) N).d (k+1) k = _
  simp only [primeCutoffComplex,ChainComplex.of_d]
  rfl

/-- Torsion in the actual boundary quotient is exactly its two-torsion. -/
theorem primeValueShortHomology_torsion_iff (k N : ℕ) (x : (primeValueShortComplex k N).homology) :
    (∃ a : ℤ, a ≠ 0 ∧ a • x = 0) ↔ (2 : ℤ) • x = 0 := by
  constructor
  · rintro ⟨a,ha,hx⟩
    obtain ⟨c,rfl⟩ := moduleHomologyClass_surjective (primeValueShortComplex k N) x
    have hc : moduleHomologyClass (primeValueShortComplex k N) (a • c) = 0 := by
      rw [map_zsmul]
      exact hx
    obtain ⟨y,hy⟩ := (moduleHomologyClass_eq_zero_iff _ _).mp hc
    rw [primeValueShort_f] at hy
    have hb : a • c.val.val ∈ primeValueBoundaries k N :=
      Submodule.mem_map.mpr ⟨y.val,y.property,congrArg Subtype.val hy⟩
    have h2 : (2 : ℤ) • c.val.val ∈ primeValueBoundaries k N := by
      cases k with
      | zero => exact (primeValueZero_torsion_iff_double_boundary N c.val.val).mp ⟨a,ha,hb⟩
      | succ k =>
        have hc0 : (primeValueShortComplex (k+1) N).g c.val = 0 := c.property
        have hh := congrArg (fun f => f c.val) (primeValueShort_g_succ k N)
        have hc' : primeValueBoundary ℤ k c.val.val = 0 := congrArg Subtype.val (hh.symm.trans hc0)
        exact (primeValueCycle_torsion_iff_double_boundary k N ⟨c.val.val,hc'⟩).mp ⟨a,ha,hb⟩
    obtain ⟨z,hz,he⟩ := Submodule.mem_map.mp h2
    rw [← map_zsmul]
    apply (moduleHomologyClass_eq_zero_iff _ _).mpr
    refine ⟨⟨z,hz⟩,?_⟩
    rw [primeValueShort_f]
    exact Subtype.ext he
  · intro h
    exact ⟨2,by omega,h⟩

/-- The original homology object and the actual adjacent-complex homology agree. -/
def primeValueHomologyShortIso (k N : ℕ) :
    (primeCutoffHomology ℤ (primeValueFunctional ℤ) k).obj N ≅ (primeValueShortComplex k N).homology :=
  (HomologicalComplex.homologyFunctorIso' (ModuleCat ℤ) (ComplexShape.down ℕ)
    (k+1) k (k-1) (by simp) (by cases k <;> simp)).app
      (primeCutoffComplex ℤ (primeValueFunctional ℤ) N)

/-- Every torsion class of actual integral prime-weighted homology is killed by two. -/
theorem primeValueHomology_torsion_iff (k N : ℕ)
    (x : (primeCutoffHomology ℤ (primeValueFunctional ℤ) k).obj N) :
    (∃ a : ℤ, a ≠ 0 ∧ a • x = 0) ↔ (2 : ℤ) • x = 0 := by
  let e := (primeValueHomologyShortIso k N).toLinearEquiv
  constructor
  · rintro ⟨a,ha,hx⟩
    have he : ∃ a : ℤ, a ≠ 0 ∧ a • e x = 0 := by
      refine ⟨a,ha,?_⟩
      rw [← map_zsmul e,hx,map_zero]
    apply e.injective
    rw [map_zsmul,map_zero]
    exact (primeValueShortHomology_torsion_iff k N (e x)).mp he
  · intro h
    exact ⟨2,by omega,h⟩

/-- The exponent-two bound is attained by the actual empty-face homology at height two. -/
theorem primeValueShortHomology_two_torsion_nontrivial :
    ∃ x : (primeValueShortComplex 0 2).homology, x ≠ 0 ∧ (2 : ℤ) • x = 0 := by
  obtain ⟨x,hx⟩ := primeValueEmpty_not_filled_at_two
  let c : (primeValueShortComplex 0 2).g.hom.ker :=
    ⟨⟨x.val,primeChainCutoff_mono ℤ 0 (show 1 ≤ 2 by omega) x.property⟩,rfl⟩
  refine ⟨moduleHomologyClass (primeValueShortComplex 0 2) c,?_,?_⟩
  · intro h
    obtain ⟨y,hy⟩ := (moduleHomologyClass_eq_zero_iff _ _).mp h
    rw [primeValueShort_f] at hy
    exact hx y (congrArg Subtype.val hy)
  · have hb := primeValueZero_double_boundary 2 x
    obtain ⟨y,hy,he⟩ := Submodule.mem_map.mp hb
    rw [← map_zsmul]
    apply (moduleHomologyClass_eq_zero_iff _ _).mpr
    refine ⟨⟨y,hy⟩,?_⟩
    rw [primeValueShort_f]
    exact Subtype.ext he

/-- Actual augmented prime-weighted homology contains nonzero two-torsion. -/
theorem primeValueHomology_two_torsion_nontrivial :
    ∃ x : (primeCutoffHomology ℤ (primeValueFunctional ℤ) 0).obj 2,
      x ≠ 0 ∧ (2 : ℤ) • x = 0 := by
  obtain ⟨y,hy,h2⟩ := primeValueShortHomology_two_torsion_nontrivial
  let e := (primeValueHomologyShortIso 0 2).toLinearEquiv
  refine ⟨e.symm y,?_,?_⟩
  · intro h
    apply hy
    have hh := congrArg e h
    simpa only [LinearEquiv.apply_symm_apply,map_zero] using hh
  · rw [← map_zsmul e.symm,h2,map_zero]

#print axioms primeValueShortHomology_torsion_iff
#print axioms primeValueHomology_torsion_iff
#print axioms primeValueHomology_two_torsion_nontrivial
end GaloisForLFunctions.EffectiveScalingGeometry
