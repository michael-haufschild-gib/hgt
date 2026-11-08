import GaloisForLFunctions.EffectiveScalingGeometry.PrimeTwoPrimeBlockHomology
import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.ModuleHomologyMaps

/-!
# Natural homology persistence of arithmetic two-prime blocks

Height maps retain each scalar coefficient while enlarging the allowed
chains and boundary relations. The original homology maps act by these
literal coefficient maps under the explicit upper and lower quotient
comparisons. These comparisons form natural isomorphisms of persistence
functors, retaining the nontrivial transitions between birth windows.
-/

noncomputable section
open CategoryTheory DifferentialGeometry.Topology
namespace GaloisForLFunctions.EffectiveScalingGeometry
variable (R : Type*) [CommRing R]

/-- Raising height only adds possible lower relations. -/
theorem twoPrimeLowerIdeal_mono (m : ℕ) {N M : ℕ} (h : N ≤ M) :
    twoPrimeLowerIdeal R m N ≤ twoPrimeLowerIdeal R m M := by
  intro c hc
  obtain ⟨x,hx⟩ := (twoPrimeLowerIdeal_mem_iff R m N c).mp hc
  apply (twoPrimeLowerIdeal_mem_iff R m M c).mpr
  exact ⟨Submodule.inclusion (twoPrimeBlockMiddle_mono R m h) x,hx⟩

/-- Upper persistence keeps the coefficient and quotients by newly born top faces. -/
def twoPrimeUpperHomologyMap (m : ℕ) {N M : ℕ} (h : N ≤ M) :
    TwoPrimeUpperHomology R m N →ₗ[R] TwoPrimeUpperHomology R m M :=
  Submodule.mapQ (twoPrimeUpperRelations R m N) (twoPrimeUpperRelations R m M)
    (Submodule.inclusion (twoPrimeUpperCoefficients_mono R m h)) (by
      intro c hc
      exact twoPrimeBlockScalar_mono R (6*m) h hc)

/-- Lower persistence keeps the coefficient and passes to its larger relation ideal. -/
def twoPrimeLowerHomologyMap (m : ℕ) {N M : ℕ} (h : N ≤ M) :
    TwoPrimeLowerHomology R m N →ₗ[R] TwoPrimeLowerHomology R m M :=
  Submodule.mapQ (twoPrimeLowerRelations R m N) (twoPrimeLowerRelations R m M)
    (Submodule.inclusion (twoPrimeBlockScalar_mono R m h)) (by
      intro c hc
      exact twoPrimeLowerIdeal_mono R m h hc)

/-- The actual upper cycle inclusion retains its scalar coordinate. -/
theorem twoPrimeUpperProjection_natural (m : ℕ) {N M : ℕ} (h : N ≤ M)
    (x : (twoPrimeUpperBlock R m N).g.hom.ker) :
    twoPrimeUpperProjection R m M (moduleCycleMap (twoPrimeUpperBlockInclusion R m h) x) =
      twoPrimeUpperHomologyMap R m h (twoPrimeUpperProjection R m N x) := rfl

/-- The actual lower cycle inclusion retains its scalar coordinate. -/
theorem twoPrimeLowerProjection_natural (m : ℕ) {N M : ℕ} (h : N ≤ M)
    (x : (twoPrimeLowerBlock R m N).g.hom.ker) :
    twoPrimeLowerProjection R m M (moduleCycleMap (twoPrimeLowerBlockInclusion R m h) x) =
      twoPrimeLowerHomologyMap R m h (twoPrimeLowerProjection R m N x) := rfl

/-- The original upper homology map induces precisely the explicit coefficient map. -/
theorem twoPrimeUpperHomologyEquiv_natural (m : ℕ) {N M : ℕ} (h : N ≤ M)
    (x : (twoPrimeUpperBlock R m N).homology) :
    twoPrimeUpperHomologyEquiv R m M (ShortComplex.homologyMap (twoPrimeUpperBlockInclusion R m h) x) =
      twoPrimeUpperHomologyMap R m h (twoPrimeUpperHomologyEquiv R m N x) := by
  obtain ⟨c,rfl⟩ := moduleHomologyClass_surjective (twoPrimeUpperBlock R m N) x
  rw [moduleHomologyClass_map,twoPrimeUpperHomologyEquiv_class,twoPrimeUpperHomologyEquiv_class]
  exact twoPrimeUpperProjection_natural R m h c

/-- The original lower homology map induces precisely the explicit coefficient map. -/
theorem twoPrimeLowerHomologyEquiv_natural (m : ℕ) {N M : ℕ} (h : N ≤ M)
    (x : (twoPrimeLowerBlock R m N).homology) :
    twoPrimeLowerHomologyEquiv R m M (ShortComplex.homologyMap (twoPrimeLowerBlockInclusion R m h) x) =
      twoPrimeLowerHomologyMap R m h (twoPrimeLowerHomologyEquiv R m N x) := by
  obtain ⟨c,rfl⟩ := moduleHomologyClass_surjective (twoPrimeLowerBlock R m N) x
  rw [moduleHomologyClass_map,twoPrimeLowerHomologyEquiv_class,twoPrimeLowerHomologyEquiv_class]
  exact twoPrimeLowerProjection_natural R m h c

/-- Upper coefficient quotients form the homology persistence of one block. -/
def twoPrimeUpperCoefficientPersistence (m : ℕ) : ℕ ⥤ ModuleCat R where
  obj N := ModuleCat.of R (TwoPrimeUpperHomology R m N)
  map h := ModuleCat.ofHom (twoPrimeUpperHomologyMap R m h.le)
  map_id N := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    obtain ⟨c,rfl⟩ := Submodule.mkQ_surjective (twoPrimeUpperRelations R m N) x
    rfl
  map_comp h g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    obtain ⟨c,rfl⟩ := Submodule.mkQ_surjective (twoPrimeUpperRelations R m _) x
    rfl

/-- Lower coefficient quotients form the homology persistence of one block. -/
def twoPrimeLowerCoefficientPersistence (m : ℕ) : ℕ ⥤ ModuleCat R where
  obj N := ModuleCat.of R (TwoPrimeLowerHomology R m N)
  map h := ModuleCat.ofHom (twoPrimeLowerHomologyMap R m h.le)
  map_id N := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    obtain ⟨c,rfl⟩ := Submodule.mkQ_surjective (twoPrimeLowerRelations R m N) x
    rfl
  map_comp h g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    obtain ⟨c,rfl⟩ := Submodule.mkQ_surjective (twoPrimeLowerRelations R m _) x
    rfl

/-- Natural identification of actual upper homology with the coefficient persistence. -/
def twoPrimeUpperHomologyPersistenceIso (m : ℕ) :
    twoPrimeUpperBlockPersistence R m ⋙ ShortComplex.homologyFunctor (ModuleCat R) ≅
      twoPrimeUpperCoefficientPersistence R m :=
  NatIso.ofComponents (fun N => (twoPrimeUpperHomologyEquiv R m N).toModuleIso)
    (fun h => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      exact twoPrimeUpperHomologyEquiv_natural R m h.le x)

/-- Natural identification of actual lower homology with the coefficient persistence. -/
def twoPrimeLowerHomologyPersistenceIso (m : ℕ) :
    twoPrimeLowerBlockPersistence R m ⋙ ShortComplex.homologyFunctor (ModuleCat R) ≅
      twoPrimeLowerCoefficientPersistence R m :=
  NatIso.ofComponents (fun N => (twoPrimeLowerHomologyEquiv R m N).toModuleIso)
    (fun h => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      exact twoPrimeLowerHomologyEquiv_natural R m h.le x)

#print axioms twoPrimeUpperHomologyPersistenceIso
#print axioms twoPrimeLowerHomologyPersistenceIso
#print axioms twoPrimeUpperHomologyEquiv_natural
#print axioms twoPrimeLowerHomologyEquiv_natural
#print axioms twoPrimeUpperCoefficientPersistence
#print axioms twoPrimeLowerCoefficientPersistence
end GaloisForLFunctions.EffectiveScalingGeometry
