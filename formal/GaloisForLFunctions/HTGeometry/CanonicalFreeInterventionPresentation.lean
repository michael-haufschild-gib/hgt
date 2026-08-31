import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Quotient.Defs
import Mathlib.Tactic

/-!
# Canonical free intervention presentations

A linear intervention grammar consists of primitive intervention generators, declared legal
rewrite boundaries, and an observer assignment neutral on every declared rewrite. Its canonical
history space is the free module on interventions modulo the span of rewrite boundaries.

The main theorem gives an exact flat-readout criterion: an assignment of intervention generators
into a boundaryless linear target extends to a unique representation of presented histories if and
only if it annihilates every declared rewrite. This classifies observers and scalar readouts. A
general chain-level route may instead carry a rewrite to a nonzero target rewrite and is not
classified by this quotient theorem. The induced observer is the canonical example.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe uk ui ur uo uw

/-- A source grammar of primitive interventions, legal rewrite relations, and observer reports. -/
structure LinearInterventionGrammar
    (k : Type uk) (I : Type ui) (R : Type ur) (O : Type uo)
    [Field k] [AddCommGroup O] [Module k O] where
  /-- The finitely supported history changed by one primitive legal rewrite. -/
  relation : R → (I →₀ k)
  /-- Observer report attached to one primitive intervention. -/
  generatorObserver : I → O
  /-- Every declared legal rewrite is information-neutral for the observer. -/
  relation_neutral : ∀ r,
    Finsupp.linearCombination k generatorObserver (relation r) = 0

namespace LinearInterventionGrammar

variable {k : Type uk} {I : Type ui} {R : Type ur} {O : Type uo}
    [Field k] [AddCommGroup O] [Module k O]

/-- Free finitely supported histories on primitive interventions. -/
abbrev History (_G : LinearInterventionGrammar k I R O) := I →₀ k

/-- Free finitely supported chains of primitive legal rewrites. -/
abbrev Faces (_G : LinearInterventionGrammar k I R O) := R →₀ k

/-- Linear extension of primitive rewrite boundaries. -/
def boundary (G : LinearInterventionGrammar k I R O) : G.Faces →ₗ[k] G.History :=
  Finsupp.linearCombination k G.relation

/-- Linear extension of primitive observer reports. -/
def observer (G : LinearInterventionGrammar k I R O) : G.History →ₗ[k] O :=
  Finsupp.linearCombination k G.generatorObserver

/-- Boundary of one weighted primitive rewrite. -/
theorem boundary_single (G : LinearInterventionGrammar k I R O) (r : R) (c : k) :
    G.boundary (Finsupp.single r c) = c • G.relation r := by
  simp [boundary]

/-- Observer value of one weighted primitive intervention. -/
theorem observer_single (G : LinearInterventionGrammar k I R O) (i : I) (c : k) :
    G.observer (Finsupp.single i c) = c • G.generatorObserver i := by
  simp [observer]

/-- The observer kills each primitive legal relation. -/
theorem observer_relation (G : LinearInterventionGrammar k I R O) (r : R) :
    G.observer (G.relation r) = 0 :=
  G.relation_neutral r

/-- **Information-neutrality.** The observer kills every finite legal rewrite chain. -/
theorem observer_boundary (G : LinearInterventionGrammar k I R O) :
    G.observer.comp G.boundary = 0 := by
  apply Finsupp.lhom_ext'
  intro r
  apply LinearMap.ext
  intro c
  simp [boundary, observer, G.relation_neutral]

/-- Canonical histories modulo exactly the span of declared legal rewrites. -/
abbrev PresentedHistory (G : LinearInterventionGrammar k I R O) :=
  G.History ⧸ LinearMap.range G.boundary

/-- Quotient a free history by legal rewrite boundaries. -/
def classOf (G : LinearInterventionGrammar k I R O) :
    G.History →ₗ[k] G.PresentedHistory :=
  (LinearMap.range G.boundary).mkQ

/-- Class of one primitive intervention in the canonical presentation. -/
def generatorClass (G : LinearInterventionGrammar k I R O) (i : I) : G.PresentedHistory :=
  G.classOf (Finsupp.single i 1)

/-- Linear extension of a proposed flat readout's values on primitive interventions. -/
def routeLinear {W : Type uw} [AddCommGroup W] [Module k W]
    (G : LinearInterventionGrammar k I R O) (φ : I → W) : G.History →ₗ[k] W :=
  Finsupp.linearCombination k φ

/-- A proposed flat readout is source-admissible when it kills every declared legal rewrite. -/
def RouteAnnihilatesRelations {W : Type uw} [AddCommGroup W] [Module k W]
    (G : LinearInterventionGrammar k I R O) (φ : I → W) : Prop :=
  ∀ r, G.routeLinear φ (G.relation r) = 0

/-- Flat-readout value of one weighted primitive intervention. -/
theorem routeLinear_single {W : Type uw} [AddCommGroup W] [Module k W]
    (G : LinearInterventionGrammar k I R O) (φ : I → W) (i : I) (c : k) :
    G.routeLinear φ (Finsupp.single i c) = c • φ i := by
  simp [routeLinear]

/-- A source-admissible flat readout kills every finite legal rewrite chain. -/
theorem routeLinear_boundary_eq_zero {W : Type uw} [AddCommGroup W] [Module k W]
    (G : LinearInterventionGrammar k I R O) (φ : I → W)
    (hφ : G.RouteAnnihilatesRelations φ) (a : G.Faces) :
    G.routeLinear φ (G.boundary a) = 0 := by
  induction a using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single r c =>
      rw [G.boundary_single, map_smul, hφ r, smul_zero]

/-- The legal-rewrite span lies in the kernel of every source-admissible flat readout. -/
theorem range_boundary_le_routeLinear_ker {W : Type uw}
    [AddCommGroup W] [Module k W]
    (G : LinearInterventionGrammar k I R O) (φ : I → W)
    (hφ : G.RouteAnnihilatesRelations φ) :
    LinearMap.range G.boundary ≤ LinearMap.ker (G.routeLinear φ) := by
  rintro _ ⟨a, rfl⟩
  exact LinearMap.mem_ker.mpr (G.routeLinear_boundary_eq_zero φ hφ a)

/-- Canonical flat-readout representation obtained by quotienting the free linear extension. -/
def routeQuotientLift {W : Type uw} [AddCommGroup W] [Module k W]
    (G : LinearInterventionGrammar k I R O) (φ : I → W)
    (hφ : G.RouteAnnihilatesRelations φ) : G.PresentedHistory →ₗ[k] W :=
  Submodule.liftQ (LinearMap.range G.boundary) (G.routeLinear φ)
    (G.range_boundary_le_routeLinear_ker φ hφ)

/-- The canonical quotient representation recovers the free readout map on every history. -/
theorem routeQuotientLift_classOf {W : Type uw} [AddCommGroup W] [Module k W]
    (G : LinearInterventionGrammar k I R O) (φ : I → W)
    (hφ : G.RouteAnnihilatesRelations φ) (x : G.History) :
    G.routeQuotientLift φ hφ (G.classOf x) = G.routeLinear φ x := by
  rfl

/-- The canonical quotient representation has the prescribed primitive generator values. -/
theorem routeQuotientLift_generatorClass {W : Type uw}
    [AddCommGroup W] [Module k W]
    (G : LinearInterventionGrammar k I R O) (φ : I → W)
    (hφ : G.RouteAnnihilatesRelations φ) (i : I) :
    G.routeQuotientLift φ hφ (G.generatorClass i) = φ i := by
  simp [generatorClass, routeQuotientLift_classOf, routeLinear]

/-- Any representation with the prescribed generator values agrees with the free route map after
the quotient projection. -/
theorem apply_classOf_eq_routeLinear_of_generator {W : Type uw}
    [AddCommGroup W] [Module k W]
    (G : LinearInterventionGrammar k I R O) (φ : I → W)
    (F : G.PresentedHistory →ₗ[k] W)
    (hF : ∀ i, F (G.generatorClass i) = φ i) (x : G.History) :
    F (G.classOf x) = G.routeLinear φ x := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single i c =>
      have hs : Finsupp.single i c = c • Finsupp.single i (1 : k) := by
        ext j
        simp
      rw [hs]
      simp only [map_smul]
      change c • F (G.generatorClass i) =
        c • G.routeLinear φ (Finsupp.single i 1)
      rw [hF i, G.routeLinear_single]
      simp

/-- Existence of a presented representation forces the primitive relation test. -/
theorem routeAnnihilatesRelations_of_representation {W : Type uw}
    [AddCommGroup W] [Module k W]
    (G : LinearInterventionGrammar k I R O) (φ : I → W)
    (F : G.PresentedHistory →ₗ[k] W)
    (hF : ∀ i, F (G.generatorClass i) = φ i) :
    G.RouteAnnihilatesRelations φ := by
  intro r
  rw [← G.apply_classOf_eq_routeLinear_of_generator φ F hF]
  have hrange : G.relation r ∈ LinearMap.range G.boundary := by
    refine ⟨Finsupp.single r 1, ?_⟩
    simp [boundary_single]
  have hzero : G.classOf (G.relation r) = 0 := by
    exact (Submodule.Quotient.mk_eq_zero _).mpr hrange
  rw [hzero, map_zero]

/-- **Universal flat-readout law.** A primitive assignment into a boundaryless target extends
uniquely through the canonical flat quotient if and only if it annihilates every legal rewrite. -/
theorem existsUnique_routeRepresentation_iff {W : Type uw}
    [AddCommGroup W] [Module k W]
    (G : LinearInterventionGrammar k I R O) (φ : I → W) :
    (∃! F : G.PresentedHistory →ₗ[k] W,
        ∀ i, F (G.generatorClass i) = φ i) ↔
      G.RouteAnnihilatesRelations φ := by
  constructor
  · rintro ⟨F, hF, _⟩
    exact G.routeAnnihilatesRelations_of_representation φ F hF
  · intro hφ
    refine ⟨G.routeQuotientLift φ hφ,
      G.routeQuotientLift_generatorClass φ hφ, ?_⟩
    intro F hF
    apply LinearMap.ext
    intro q
    induction q using Submodule.Quotient.induction_on with
    | _ x =>
      change F (G.classOf x) = G.routeQuotientLift φ hφ (G.classOf x)
      rw [G.apply_classOf_eq_routeLinear_of_generator φ F hF]
      exact (G.routeQuotientLift_classOf φ hφ x).symm

/-- The source observer assignment satisfies the universal flat-readout test. -/
theorem generatorObserver_annihilatesRelations (G : LinearInterventionGrammar k I R O) :
    G.RouteAnnihilatesRelations G.generatorObserver :=
  G.relation_neutral

/-- Canonical observer on histories modulo legal rewrites. -/
def presentedObserver (G : LinearInterventionGrammar k I R O) :
    G.PresentedHistory →ₗ[k] O :=
  G.routeQuotientLift G.generatorObserver G.generatorObserver_annihilatesRelations

/-- The presented observer recovers the free observer on every history. -/
theorem presentedObserver_classOf (G : LinearInterventionGrammar k I R O) (x : G.History) :
    G.presentedObserver (G.classOf x) = G.observer x := by
  rfl

/-- The presented observer has the declared primitive observer values. -/
theorem presentedObserver_generatorClass (G : LinearInterventionGrammar k I R O) (i : I) :
    G.presentedObserver (G.generatorClass i) = G.generatorObserver i := by
  exact G.routeQuotientLift_generatorClass G.generatorObserver
    G.generatorObserver_annihilatesRelations i

/-- Certified capstone: flat-readout extension is equivalent to the primitive relation test,
and the source observer is the canonical representation of its generator reports. -/
theorem canonicalFreeInterventionPresentation_capstone {W : Type uw}
    [AddCommGroup W] [Module k W]
    (G : LinearInterventionGrammar k I R O) (φ : I → W) :
    ((∃! F : G.PresentedHistory →ₗ[k] W,
        ∀ i, F (G.generatorClass i) = φ i) ↔
      ∀ r, G.routeLinear φ (G.relation r) = 0) ∧
    (∀ x, G.presentedObserver (G.classOf x) = G.observer x) := by
  exact ⟨G.existsUnique_routeRepresentation_iff φ,
    G.presentedObserver_classOf⟩

end LinearInterventionGrammar

end

end GaloisForLFunctions.HTGeometry
