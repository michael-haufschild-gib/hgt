import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.SphereHomologyVanishing
import DifferentialGeometry.Topology.Homology.HurewiczLowDegrees
import DifferentialGeometry.Topology.FundamentalGroup.Sphere

/-!
# Low-degree Hurewicz maps and sphere homotopy groups

The actual degree-two and degree-three Hurewicz maps are bundled as additive
homomorphisms for any topological space and basepoint. Simple connectedness
makes the degree-two map an equivalence; trivial π₂ makes degree three an
equivalence as well. Vanishing H₂ supplies that π₂ premise through degree two.

For the standard spheres this gives π₂(S²) ≃ ℤ and π₃(S³) ≃ ℤ, using the
upstream chosen sphere generators. The S³ π₂ premise follows from its proved
vanishing degree-two integral singular homology.
-/

noncomputable section
universe u
namespace HTGeometry.GeometricHurewicz
open DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]

def hurewiczTwoHom (x : X) :
    Additive (HomotopyGroup (Fin 2) X x) →+ integralSingularHomology 2 X where
  toFun a := sphereHurewicz 1 x (integralLiftedSphereGenerator 1) a.toMul
  map_zero' := sphereHurewicz_one 1 x (integralLiftedSphereGenerator 1)
  map_add' a b :=
    sphereHurewicz_two_mul x (integralLiftedSphereGenerator 1) a.toMul b.toMul

def hurewiczTwoEquiv [SimplyConnectedSpace X] (x : X) :
    Additive (HomotopyGroup (Fin 2) X x) ≃+ integralSingularHomology 2 X :=
  AddEquiv.ofBijective (hurewiczTwoHom x)
    (hurewicz_two_isomorphism x _ (integralLiftedSphereGenerator_isGenerator 1)).1

def hurewiczThreeHom (x : X) :
    Additive (HomotopyGroup (Fin 3) X x) →+ integralSingularHomology 3 X where
  toFun a := sphereHurewicz 2 x (integralLiftedSphereGenerator 2) a.toMul
  map_zero' := sphereHurewicz_one 2 x (integralLiftedSphereGenerator 2)
  map_add' a b :=
    sphereHurewicz_three_mul x (integralLiftedSphereGenerator 2) a.toMul b.toMul

def hurewiczThreeEquiv [SimplyConnectedSpace X] (x : X) [Subsingleton (HomotopyGroup (Fin 2) X x)] :
    Additive (HomotopyGroup (Fin 3) X x) ≃+ integralSingularHomology 3 X :=
  AddEquiv.ofBijective (hurewiczThreeHom x)
    (hurewicz_three_isomorphism x inferInstance _ (integralLiftedSphereGenerator_isGenerator 2)).1

def sphereTwoDegreeEquiv (x : SphereTwo) :
    Additive (HomotopyGroup (Fin 2) SphereTwo x) ≃+ ℤ :=
  (hurewiczTwoEquiv x).trans
    (integralSphereTopHomologyEquiv 1 (EuclideanSpace ℝ (Fin 3)) (by simp)).toAddEquiv

theorem homotopyTwo_subsingleton_of_homology [SimplyConnectedSpace X] (x : X)
    [Subsingleton (integralSingularHomology 2 X)] :
    Subsingleton (HomotopyGroup (Fin 2) X x) := by
  refine ⟨fun a b => ?_⟩
  have h : Additive.ofMul a = Additive.ofMul b :=
    (hurewiczTwoEquiv x).injective (Subsingleton.elim _ _)
  exact congrArg Additive.toMul h

/-- Vanishing degree-two homology supplies the connectivity premise for degree three. -/
def hurewiczThreeEquiv_of_homologyTwo [SimplyConnectedSpace X] (x : X)
    [Subsingleton (integralSingularHomology 2 X)] :
    Additive (HomotopyGroup (Fin 3) X x) ≃+ integralSingularHomology 3 X := by
  letI := homotopyTwo_subsingleton_of_homology x
  exact hurewiczThreeEquiv x

theorem sphereThree_homotopyTwo_subsingleton (x : SphereThree) :
    Subsingleton (HomotopyGroup (Fin 2) SphereThree x) := by
  letI := integralSphereHomology_subsingleton 3 2 (EuclideanSpace ℝ (Fin 4))
    (by simp) (by decide) (by decide)
  exact homotopyTwo_subsingleton_of_homology x

def sphereThreeDegreeEquiv (x : SphereThree) :
    Additive (HomotopyGroup (Fin 3) SphereThree x) ≃+ ℤ := by
  letI := sphereThree_homotopyTwo_subsingleton x
  exact (hurewiczThreeEquiv x).trans
    (integralSphereTopHomologyEquiv 2 (EuclideanSpace ℝ (Fin 4)) (by simp)).toAddEquiv

end HTGeometry.GeometricHurewicz
