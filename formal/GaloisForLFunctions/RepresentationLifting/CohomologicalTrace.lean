import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence
import Mathlib.LinearAlgebra.Trace
import Mathlib.Algebra.Homology.Linear

/-!
# Trace on group cohomology

Conjugation makes the trace on endomorphisms an equivariant linear map. For an
equivariant endomorphism `T`, sending a scalar class to its multiple of `T` and
then taking trace multiplies the original class by `trace T`, in every degree.
This is the trace calculation in Scavia's Lemma 6.1.

The cohomology here is ordinary group cohomology. The scalar compatibility of
the cohomology functor is proved through cycles and the homology quotient.
-/

noncomputable section

open CategoryTheory

namespace GaloisForLFunctions.RepresentationLifting

universe u

section Homology

variable {R ι : Type*} [CommRing R] {c : ComplexShape ι}
  {C D : HomologicalComplex (ModuleCat R) c}

/-- Passing a chain map to cycles preserves scalar multiplication. -/
theorem moduleCyclesMap_smul (a : R) (f : C ⟶ D) (i : ι) :
    HomologicalComplex.cyclesMap (a • f) i = a • HomologicalComplex.cyclesMap f i := by
  apply (cancel_mono (D.iCycles i)).mp
  simp only [HomologicalComplex.cyclesMap_i, HomologicalComplex.smul_f_apply,
    Linear.comp_smul, Linear.smul_comp]

/-- Passing a chain map to homology preserves scalar multiplication. -/
theorem moduleHomologyMap_smul (a : R) (f : C ⟶ D) (i : ι) :
    HomologicalComplex.homologyMap (a • f) i = a • HomologicalComplex.homologyMap f i := by
  apply (cancel_epi (C.homologyπ i)).mp
  simp only [HomologicalComplex.homologyπ_naturality, moduleCyclesMap_smul,
    Linear.comp_smul, Linear.smul_comp]

end Homology

variable {k G : Type u} [CommRing k] [Group G]

/-- Ordinary group cohomology is linear in coefficient morphisms. -/
instance groupCohomologyFunctor_linear (n : ℕ) :
    Functor.Linear k (groupCohomology.functor k G n) where
  map_smul f a := by
    have hc : groupCohomology.cochainsMap (MonoidHom.id G) (a • f) =
        a • groupCohomology.cochainsMap (MonoidHom.id G) f := by
      apply HomologicalComplex.Hom.ext
      funext i
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro v
      funext g
      rfl
    change HomologicalComplex.homologyMap
        (groupCohomology.cochainsMap (MonoidHom.id G) (a • f)) n =
      a • HomologicalComplex.homologyMap (groupCohomology.cochainsMap (MonoidHom.id G) f) n
    rw [hc, moduleHomologyMap_smul]

/-- Trace is invariant under the conjugation action on endomorphisms. -/
def endomorphismTrace (V : Rep k G) :
    (Rep.ihom V).obj V ⟶ Rep.trivial k G k :=
  Rep.ofHom ⟨LinearMap.trace k V, fun g => by
    apply LinearMap.ext
    intro T
    change LinearMap.trace k V (V.ρ g ∘ₗ T ∘ₗ V.ρ g⁻¹) = LinearMap.trace k V T
    change LinearMap.trace k V (V.ρ g * T * V.ρ g⁻¹) = LinearMap.trace k V T
    rw [LinearMap.trace_mul_cycle]
    simp only [← map_mul, inv_mul_cancel, map_one, one_mul]⟩

/-- An equivariant map determines an invariant line in the internal Hom. -/
def scalarHom {V W : Rep k G} (T : V ⟶ W) :
    Rep.trivial k G k ⟶ (Rep.ihom V).obj W :=
  Rep.ofHom ⟨(LinearMap.id : k →ₗ[k] k).smulRight T.hom.toLinearMap, fun g => by
    apply LinearMap.ext
    intro a
    have hT : Representation.linHom V.ρ W.ρ g T.hom.toLinearMap = T.hom.toLinearMap := by
      apply LinearMap.ext
      intro v
      change W.ρ g (T.hom (V.ρ g⁻¹ v)) = T.hom v
      rw [← Rep.hom_comm_apply]
      simp
    change a • T.hom.toLinearMap = Representation.linHom V.ρ W.ρ g (a • T.hom.toLinearMap)
    rw [map_smul, hT]⟩

/-- The scalar line attached to `T` has trace `a ↦ a * trace T`. -/
theorem scalarHom_trace {V : Rep k G} (T : V ⟶ V) :
    scalarHom T ≫ endomorphismTrace V =
      LinearMap.trace k V T.hom.toLinearMap • 𝟙 (Rep.trivial k G k) := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro a
  change LinearMap.trace k V (a • T.hom.toLinearMap) = LinearMap.trace k V T.hom.toLinearMap • a
  rw [map_smul]
  exact mul_comm _ _

/-- The scalar-to-endomorphism map followed by trace acts by `trace T` on cohomology. -/
theorem scalarHom_trace_cohomology {V : Rep k G} (T : V ⟶ V) (n : ℕ) :
    (groupCohomology.functor k G n).map (scalarHom T) ≫
        (groupCohomology.functor k G n).map (endomorphismTrace V) =
      LinearMap.trace k V T.hom.toLinearMap •
        𝟙 (groupCohomology (Rep.trivial k G k) n) := by
  rw [← CategoryTheory.Functor.map_comp, scalarHom_trace,
    CategoryTheory.Functor.map_smul, CategoryTheory.Functor.map_id]
  rfl

/-- The scalar-line construction commutes with postcomposition. -/
theorem scalarHom_comp {U V W : Rep k G} (f : U ⟶ V) (g : V ⟶ W) :
    scalarHom f ≫ (Rep.ihom U).map g = scalarHom (f ≫ g) := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro a
  apply LinearMap.ext
  intro v
  exact map_smul g.hom a (f.hom v)

/-- Element form of the trace formula in every cohomological degree. -/
theorem scalarHom_trace_cohomology_apply {V : Rep k G} (T : V ⟶ V) (n : ℕ)
    (b : groupCohomology (Rep.trivial k G k) n) :
    ((groupCohomology.functor k G n).map (endomorphismTrace V)).hom
        (((groupCohomology.functor k G n).map (scalarHom T)).hom b) =
      LinearMap.trace k V T.hom.toLinearMap • b := by
  exact congrArg (fun f : groupCohomology (Rep.trivial k G k) n ⟶
    groupCohomology (Rep.trivial k G k) n => f.hom b) (scalarHom_trace_cohomology T n)

end GaloisForLFunctions.RepresentationLifting

#print axioms GaloisForLFunctions.RepresentationLifting.scalarHom_trace_cohomology
