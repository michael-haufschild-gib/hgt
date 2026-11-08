import GaloisForLFunctions.EffectiveScalingGeometry.PrimeTwoPrimeBlockRetractions
import GaloisForLFunctions.EffectiveScalingGeometry.PrimeTwoPrimeHomologyCoreSum

/-! A large-prime core contributes actual homology only in its bottom and middle
degrees. Other chain degrees have no matching tags, and top cycles vanish
because the integral column (-3,2) stays injective over every coefficient ring. -/

noncomputable section
open scoped Classical
open CategoryTheory RHTower DifferentialGeometry.Topology
namespace GaloisForLFunctions.EffectiveScalingGeometry
variable (R : Type*) [CommRing R]

/-- A core has no chains below its number of large-prime factors. -/
theorem twoPrimeCoreCutoffProjection_below (k N : ℕ) (c : TwoPrimeCoreFace)
    (hk : k < c.val.card) : twoPrimeCoreCutoffProjection R k N c = 0 := by
  apply (twoPrimeBlockBasis R k N).ext
  intro ct
  apply Subtype.ext
  rw [twoPrimeCoreCutoffProjection_basis]
  have hn : ct.val.1 ≠ c := by
    intro he
    have hd := ct.property.1
    rw [he] at hd
    omega
  rw [if_neg hn]
  rfl

/-- A fixed core occurs in precisely the three possible chain degrees. -/
theorem twoPrimeCoreCutoffProjection_other (k N : ℕ) (c : TwoPrimeCoreFace)
    (h₀ : k ≠ c.val.card) (h₁ : k ≠ c.val.card+1) (h₂ : k ≠ c.val.card+2) :
    twoPrimeCoreCutoffProjection R k N c = 0 := by
  apply (twoPrimeBlockBasis R k N).ext
  intro ct
  apply Subtype.ext
  rw [twoPrimeCoreCutoffProjection_basis]
  have hn : ct.val.1 ≠ c := by
    intro he
    have hd := ct.property.1
    rw [he] at hd
    cases ht : ct.val.2 <;> simp only [ht,TwoPrimeFaceTag.degree] at hd <;> omega
  rw [if_neg hn]
  rfl

/-- Birth truncation preserves injectivity of the top column. -/
theorem twoPrimeBlockCutoffTop_injective (m N : ℕ) :
    Function.Injective (twoPrimeBlockCutoffTop R m N) := by
  intro x y h
  apply Subtype.ext
  exact twoPrimeBlockTop_injective R (congrArg Subtype.val h)

/-- A top-degree cycle has zero coefficient on its own core. -/
theorem twoPrimeCoreCycleProjection_top (c : TwoPrimeCoreFace) (N : ℕ)
    (z : ((primeCutoffComplex R (primeValueFunctional R) N).sc (c.val.card+2)).g.hom.ker) :
    twoPrimeCoreCycleProjection R (c.val.card+2) N c z = 0 := by
  have hz : primeCutoffDifferential R (primeValueFunctional R) (c.val.card+1) N z.val = 0 := by
    have hw := (moduleCycleMap
      ((primeCutoffComplex R (primeValueFunctional R) N).isoSc'
        (c.val.card+3) (c.val.card+2) (c.val.card+1) (by simp) (by simp)).hom z).property
    change ((primeCutoffComplex R (primeValueFunctional R) N).d
      ((c.val.card+1)+1) (c.val.card+1)).hom z.val = 0 at hw
    simp only [primeCutoffComplex,ChainComplex.of_d] at hw
    exact hw
  have ha : twoPrimeBlockScalarExtraction R c .both N z.val = 0 := by
    apply twoPrimeBlockCutoffTop_injective R (twoPrimeCoreHeight c) N
    have he := LinearMap.congr_fun (twoPrimeBlockTopExtraction_boundary R c N) z.val
    change twoPrimeBlockCutoffTop R (twoPrimeCoreHeight c) N
      (twoPrimeBlockScalarExtraction R c .both N z.val) =
      twoPrimeBlockMiddleExtraction R c N
        (primeCutoffDifferential R (primeValueFunctional R) (c.val.card+1) N z.val) at he
    rw [hz,map_zero] at he
    exact he.trans (map_zero _).symm
  apply Subtype.ext
  change twoPrimeCoreCutoffProjection R (c.val.card+2) N c z.val = 0
  exact (LinearMap.congr_fun (twoPrimeTop_realization_extraction R c N) z.val).symm.trans
    ((congrArg (twoPrimeBlockScalarRealization R c .both N) ha).trans (map_zero _))

/-- No top-degree homology survives in the core, over any commutative coefficient ring. -/
theorem twoPrimeCoreHomologyProjection_top (c : TwoPrimeCoreFace) (N : ℕ) :
    twoPrimeCoreHomologyProjection R (c.val.card+2) N c = 0 := by
  apply LinearMap.ext
  intro x
  obtain ⟨z,rfl⟩ := moduleHomologyClass_surjective
    ((primeCutoffComplex R (primeValueFunctional R) N).sc (c.val.card+2)) x
  rw [twoPrimeCoreHomologyProjection_class,twoPrimeCoreCycleProjection_top,map_zero]
  rfl

/-- Degrees outside the three tagged chain degrees have zero core homology. -/
theorem twoPrimeCoreHomologyProjection_other (k N : ℕ) (c : TwoPrimeCoreFace)
    (h₀ : k ≠ c.val.card) (h₁ : k ≠ c.val.card+1) (h₂ : k ≠ c.val.card+2) :
    twoPrimeCoreHomologyProjection R k N c = 0 := by
  apply LinearMap.ext
  intro x
  obtain ⟨z,rfl⟩ := moduleHomologyClass_surjective
    ((primeCutoffComplex R (primeValueFunctional R) N).sc k) x
  rw [twoPrimeCoreHomologyProjection_class]
  have hz : twoPrimeCoreCycleProjection R k N c z = 0 := by
    apply Subtype.ext
    exact LinearMap.congr_fun (twoPrimeCoreCutoffProjection_other R k N c h₀ h₁ h₂) z.val
  rw [hz,map_zero]
  rfl

/-- Each core contributes actual homology only in its bottom and middle degrees. -/
theorem twoPrimeCoreHomologyProjection_supported (k N : ℕ) (c : TwoPrimeCoreFace)
    (h₀ : k ≠ c.val.card) (h₁ : k ≠ c.val.card+1) :
    twoPrimeCoreHomologyProjection R k N c = 0 := by
  by_cases h₂ : k=c.val.card+2
  · subst k
    exact twoPrimeCoreHomologyProjection_top R c N
  · exact twoPrimeCoreHomologyProjection_other R k N c h₀ h₁ h₂

#print axioms twoPrimeCoreCutoffProjection_below
#print axioms twoPrimeCoreCycleProjection_top
#print axioms twoPrimeCoreHomologyProjection_supported
end GaloisForLFunctions.EffectiveScalingGeometry
