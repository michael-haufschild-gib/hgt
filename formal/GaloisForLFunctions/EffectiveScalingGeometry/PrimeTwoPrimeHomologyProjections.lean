import GaloisForLFunctions.EffectiveScalingGeometry.PrimeTwoPrimeCoreProjections
import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.ModuleHomologyMaps

/-!
# Core projections on actual augmented arithmetic homology

The chain core projections induce natural orthogonal idempotents on the
original categorical homology in every augmented degree. Each projected
class is represented by the same projected cycle, and every class is a
finite sum of its core contributions. These identities retain the original
height maps and do not assume a direct-sum or quotient comparison.
-/

noncomputable section
open scoped Classical
open CategoryTheory RHTower DifferentialGeometry.Topology
namespace GaloisForLFunctions.EffectiveScalingGeometry
variable (R : Type*) [CommRing R]

/-- Project an original concrete cycle onto one large-prime core. -/
def twoPrimeCoreCycleProjection (k N : ℕ) (c : TwoPrimeCoreFace) :
    ((primeCutoffComplex R (primeValueFunctional R) N).sc k).g.hom.ker →ₗ[R]
      ((primeCutoffComplex R (primeValueFunctional R) N).sc k).g.hom.ker :=
  moduleCycleMap ((HomologicalComplex.shortComplexFunctor (ModuleCat R) (ComplexShape.down ℕ) k).map
    (twoPrimeCoreChainProjection R c N))

theorem twoPrimeCoreCycleProjection_val (k N : ℕ) (c : TwoPrimeCoreFace)
    (x : ((primeCutoffComplex R (primeValueFunctional R) N).sc k).g.hom.ker) :
    (twoPrimeCoreCycleProjection R k N c x).val.val =
      twoPrimeCoreProjection R k c x.val.val := rfl

/-- Project the original homology onto the contribution of one large-prime core. -/
def twoPrimeCoreHomologyProjection (k N : ℕ) (c : TwoPrimeCoreFace) :
    (primeCutoffComplex R (primeValueFunctional R) N).homology k →ₗ[R]
      (primeCutoffComplex R (primeValueFunctional R) N).homology k :=
  (HomologicalComplex.homologyMap (twoPrimeCoreChainProjection R c N) k).hom

/-- The original homology projection takes the class of the same projected cycle. -/
theorem twoPrimeCoreHomologyProjection_class (k N : ℕ) (c : TwoPrimeCoreFace)
    (x : ((primeCutoffComplex R (primeValueFunctional R) N).sc k).g.hom.ker) :
    twoPrimeCoreHomologyProjection R k N c
      (moduleHomologyClass ((primeCutoffComplex R (primeValueFunctional R) N).sc k) x) =
    moduleHomologyClass ((primeCutoffComplex R (primeValueFunctional R) N).sc k)
      (twoPrimeCoreCycleProjection R k N c x) :=
  moduleHomologyClass_map _ x

/-- The finite core decomposition restricts to the original cutoff module. -/
theorem twoPrimeCoreCutoffProjection_sum (k N : ℕ) (x : primeChainCutoff R k N) :
    ∑ c ∈ twoPrimeCoreSupport R k x.val, twoPrimeCoreCutoffProjection R k N c x = x := by
  apply Subtype.ext
  rw [Submodule.coe_sum]
  exact twoPrimeCoreProjection_sum R k x.val

/-- Every original cycle is the finite sum of its projected cycles. -/
theorem twoPrimeCoreCycleProjection_sum (k N : ℕ)
    (x : ((primeCutoffComplex R (primeValueFunctional R) N).sc k).g.hom.ker) :
    ∑ c ∈ twoPrimeCoreSupport R k x.val.val, twoPrimeCoreCycleProjection R k N c x = x := by
  apply Subtype.ext
  simp only [Submodule.coe_sum]
  exact twoPrimeCoreCutoffProjection_sum R k N x.val

/-- Every original homology class is a finite sum of its core contributions. -/
theorem twoPrimeCoreHomologyProjection_finite_sum (k N : ℕ)
    (x : (primeCutoffComplex R (primeValueFunctional R) N).homology k) :
    ∃ S : Finset TwoPrimeCoreFace, ∑ c ∈ S, twoPrimeCoreHomologyProjection R k N c x = x := by
  obtain ⟨z,rfl⟩ := moduleHomologyClass_surjective
    ((primeCutoffComplex R (primeValueFunctional R) N).sc k) x
  refine ⟨twoPrimeCoreSupport R k z.val.val,?_⟩
  simp only [twoPrimeCoreHomologyProjection_class]
  calc
    _ = moduleHomologyClass ((primeCutoffComplex R (primeValueFunctional R) N).sc k)
        (∑ c ∈ twoPrimeCoreSupport R k z.val.val, twoPrimeCoreCycleProjection R k N c z) :=
      (map_sum (moduleHomologyClass ((primeCutoffComplex R (primeValueFunctional R) N).sc k))
        (fun c => twoPrimeCoreCycleProjection R k N c z) (twoPrimeCoreSupport R k z.val.val)).symm
    _ = _ := congrArg (moduleHomologyClass ((primeCutoffComplex R (primeValueFunctional R) N).sc k))
      (twoPrimeCoreCycleProjection_sum R k N z)

/-- Core projection acts naturally on the original arithmetic homology persistence. -/
def twoPrimeCoreHomologyProjectionNat (k : ℕ) (c : TwoPrimeCoreFace) :
    primeCutoffHomology R (primeValueFunctional R) k ⟶
      primeCutoffHomology R (primeValueFunctional R) k :=
  Functor.whiskerRight (twoPrimeCoreChainProjectionNat R c)
    (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.down ℕ) k)

/-- Each original homology projection is idempotent. -/
theorem twoPrimeCoreHomologyProjection_idempotent (k N : ℕ) (c : TwoPrimeCoreFace) :
    (twoPrimeCoreHomologyProjection R k N c).comp (twoPrimeCoreHomologyProjection R k N c) =
      twoPrimeCoreHomologyProjection R k N c := by
  have he := congrArg (fun f =>
    (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.down ℕ) k).map f)
    (twoPrimeCoreChainProjection_idempotent R c N)
  rw [Functor.map_comp] at he
  exact congrArg ModuleCat.Hom.hom he

/-- Different core contributions are orthogonal in original homology. -/
theorem twoPrimeCoreHomologyProjection_orthogonal (k N : ℕ) (c d : TwoPrimeCoreFace) (h : c ≠ d) :
    (twoPrimeCoreHomologyProjection R k N c).comp (twoPrimeCoreHomologyProjection R k N d) = 0 := by
  have he := congrArg (fun f =>
    (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.down ℕ) k).map f)
    (twoPrimeCoreChainProjection_orthogonal R d c (Ne.symm h) N)
  rw [Functor.map_comp,Functor.map_zero] at he
  exact congrArg ModuleCat.Hom.hom he

#print axioms twoPrimeCoreHomologyProjectionNat
#print axioms twoPrimeCoreHomologyProjection_idempotent
#print axioms twoPrimeCoreHomologyProjection_orthogonal
#print axioms twoPrimeCoreHomologyProjection_class
#print axioms twoPrimeCoreCycleProjection_sum
#print axioms twoPrimeCoreHomologyProjection_finite_sum
end GaloisForLFunctions.EffectiveScalingGeometry
