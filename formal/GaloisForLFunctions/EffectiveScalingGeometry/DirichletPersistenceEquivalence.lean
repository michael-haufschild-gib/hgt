import GaloisForLFunctions.EffectiveScalingGeometry.DirichletChainGauge
import GaloisForLFunctions.EffectiveScalingGeometry.PrimeCutoffComplex
import Mathlib.CategoryTheory.Whiskering

/-!
# Dirichlet weighting preserves prime-product homology persistence

The face gauge gives an isomorphism of the actual augmented chain complexes
at each cutoff. These isomorphisms commute with height inclusions, hence induce
an isomorphism of homology persistence functors in every degree. No condition
on the real part of the complex parameter is needed for finite chains.
-/

noncomputable section
open CategoryTheory RHTower
namespace GaloisForLFunctions.EffectiveScalingGeometry

/-- The Dirichlet gauge is a chain isomorphism at exactly the same height. -/
def dirichletCutoffComplexIso (s : ℂ) (N : ℕ) :
    primeCutoffComplex ℂ (primeChainAugmentation ℂ) N ≅
      primeCutoffComplex ℂ (dirichletPrimeChainFunctional s) N :=
  HomologicalComplex.Hom.isoOfComponents
    (fun k => (dirichletCutoffGaugeEquiv s k N).toModuleIso)
    (fun i j hij => by
      change j + 1 = i at hij
      subst i
      simp only [primeCutoffComplex, ChainComplex.of_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      exact LinearMap.congr_fun (dirichletChainGauge_boundary s j) x.val)

/-- The conjugacy is natural under every height inclusion. -/
def dirichletPersistenceIso (s : ℂ) :
    primeCutoffPersistence ℂ (primeChainAugmentation ℂ) ≅
      primeCutoffPersistence ℂ (dirichletPrimeChainFunctional s) :=
  NatIso.ofComponents (dirichletCutoffComplexIso s) (fun h => by
    apply HomologicalComplex.Hom.ext
    funext k
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    rfl)

/-- Finite Dirichlet weighting changes no algebraic persistent homology group or map. -/
def dirichletHomologyPersistenceIso (s : ℂ) (k : ℕ) :
    primeCutoffHomology ℂ (primeChainAugmentation ℂ) k ≅
      primeCutoffHomology ℂ (dirichletPrimeChainFunctional s) k :=
  Functor.isoWhiskerRight (dirichletPersistenceIso s)
    (HomologicalComplex.homologyFunctor (ModuleCat ℂ) (ComplexShape.down ℕ) k)

#print axioms dirichletCutoffComplexIso
#print axioms dirichletPersistenceIso
#print axioms dirichletHomologyPersistenceIso
end GaloisForLFunctions.EffectiveScalingGeometry
