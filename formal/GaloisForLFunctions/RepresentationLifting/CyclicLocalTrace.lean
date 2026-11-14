import GaloisForLFunctions.RepresentationLifting.CyclicGraphFreeness
import GaloisForLFunctions.RepresentationLifting.CyclicSelfExtension
import GaloisForLFunctions.RepresentationLifting.RegularPairTrace
import GaloisForLFunctions.RepresentationLifting.CyclicInfinityTrace

/-!
# Local splitting and incompatible traces of the cyclic self-extension

Graph restrictions are regular pairs, hence projective. Their endomorphisms have
zero scalar trace when the group order vanishes in the coefficient field.
The additive-axis restriction instead gives trace two for every retraction.
Consequently, away from characteristic two the extension cannot split globally,
even though it splits on every additive graph and on the additive axis.
-/

noncomputable section
open CategoryTheory
namespace GaloisForLFunctions.RepresentationLifting
universe u
variable (k G : Type u) [Field k] [CommGroup G] [Fintype G] [IsCyclic G]


/-- Projectivity of the regular pair splits the extension over every additive graph. -/
theorem cyclicSelfExtension_graph_splits (h2 : (2 : k) ≠ 0) (χ : G →* Multiplicative k) :
    ∃ r : Rep.res (cyclicGraphHom k G χ) (Rep.of (cyclicExtensionRepresentation k G)) ⟶
        Rep.res (cyclicGraphHom k G χ) (Rep.of (cyclicProductRepresentation k G)),
      (Rep.resFunctor (cyclicGraphHom k G χ)).map (cyclicSelfExtensionInclusion k G) ≫ r = 𝟙 _ := by
  let S := (cyclicSelfExtension k G).map (Rep.resFunctor (cyclicGraphHom k G χ))
  have hS : S.ShortExact := (Rep.shortExact_res (cyclicGraphHom k G χ)).mpr
    (cyclicSelfExtension_shortExact k G)
  haveI : Projective S.X₃ := Projective.of_iso (cyclicGraphIso k G h2 χ)
    (cyclicRegularPair_projective k G)
  exact ⟨hS.splittingOfProjective.r, hS.splittingOfProjective.f_r⟩

/-- Conjugacy transports modular regular trace vanishing to every graph restriction. -/
theorem cyclicGraph_endomorphism_trace (h2 : (2 : k) ≠ 0)
    (hcard : (Fintype.card G : k) = 0) (χ : G →* Multiplicative k)
    (T : Rep.res (cyclicGraphHom k G χ) (Rep.of (cyclicProductRepresentation k G)) ⟶
      Rep.res (cyclicGraphHom k G χ) (Rep.of (cyclicProductRepresentation k G))) :
    LinearMap.trace k (CyclicDetector k G) T.hom.toLinearMap = 0 := by
  let e := cyclicGraphIso k G h2 χ
  have h := cyclicRegularPair_endomorphism_trace k G hcard (e.hom ≫ T ≫ e.inv)
  have hc : LinearMap.trace k (CyclicDetector k G) ((e.hom ≫ T ≫ e.inv).hom.toLinearMap) =
      LinearMap.trace k (CyclicDetector k G) T.hom.toLinearMap := by
    change LinearMap.trace k (CyclicDetector k G)
      (e.inv.hom.toLinearMap.comp (T.hom.toLinearMap.comp e.hom.hom.toLinearMap)) = _
    rw [LinearMap.trace_comp_comm']
    have he : e.hom.hom.toLinearMap.comp e.inv.hom.toLinearMap = LinearMap.id :=
      congrArg (fun m => m.hom.toLinearMap) e.inv_hom_id
    rw [LinearMap.comp_assoc, he, LinearMap.comp_id]
  exact hc.symm.trans h

/-- Every equivariant map back from the graph-restricted extension gives trace zero after the lift. -/
theorem cyclicSelfExtension_graph_trace (h2 : (2 : k) ≠ 0)
    (hcard : (Fintype.card G : k) = 0) (χ : G →* Multiplicative k)
    (r : Rep.res (cyclicGraphHom k G χ) (Rep.of (cyclicExtensionRepresentation k G)) ⟶
      Rep.res (cyclicGraphHom k G χ) (Rep.of (cyclicProductRepresentation k G))) :
    LinearMap.trace k (CyclicDetector k G)
      (((Rep.resFunctor (cyclicGraphHom k G χ)).map
        (cyclicSelfExtensionLift k G) ≫ r).hom.toLinearMap) = 0 :=
  cyclicGraph_endomorphism_trace k G h2 hcard χ _

/-- The incompatible graph and additive-axis traces exclude any global equivariant retraction. -/
theorem cyclicSelfExtension_not_split (h2 : (2 : k) ≠ 0)
    (hcard : (Fintype.card G : k) = 0) :
    ¬ ∃ r : Rep.of (cyclicExtensionRepresentation k G) ⟶ Rep.of (cyclicProductRepresentation k G),
      cyclicSelfExtensionInclusion k G ≫ r = 𝟙 _ := by
  rintro ⟨r, hr⟩
  let j₀ := cyclicGraphHom k G (1 : G →* Multiplicative k)
  let jInfinity := MonoidHom.inr G (Multiplicative k)
  have hzero := cyclicSelfExtension_graph_trace k G h2 hcard (1 : G →* Multiplicative k)
    ((Rep.resFunctor j₀).map r)
  have hrInfinity : (Rep.resFunctor jInfinity).map (cyclicSelfExtensionInclusion k G) ≫
      (Rep.resFunctor jInfinity).map r = 𝟙 _ := by
    rw [← CategoryTheory.Functor.map_comp, hr, CategoryTheory.Functor.map_id]
  have htwo := cyclicSelfExtension_infinity_trace k G ((Rep.resFunctor jInfinity).map r) hrInfinity
  change LinearMap.trace k (CyclicDetector k G)
    (r.hom.toLinearMap.comp (cyclicSelfExtensionLift k G).hom.toLinearMap) = 0 at hzero
  change LinearMap.trace k (CyclicDetector k G)
    (r.hom.toLinearMap.comp (cyclicSelfExtensionLift k G).hom.toLinearMap) = 2 at htwo
  exact h2 (htwo.symm.trans hzero)

end GaloisForLFunctions.RepresentationLifting

#print axioms GaloisForLFunctions.RepresentationLifting.cyclicSelfExtension_graph_splits
#print axioms GaloisForLFunctions.RepresentationLifting.cyclicSelfExtension_graph_trace
#print axioms GaloisForLFunctions.RepresentationLifting.cyclicSelfExtension_not_split
