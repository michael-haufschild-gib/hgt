import GaloisForLFunctions.HTGeometry.StokesEnhancedTranslationAction
import GaloisForLFunctions.HTGeometry.StokesClosedSupportSheaf

/-!
# Compactified enhanced exponential objects

A continuous real phase on a compact base defines a closed epigraph in the extended-real enhanced
direction. The constant integral sheaf on that epigraph gives compact-support, ind-sheaf, derived,
and generated enhanced-quotient realizations in both bounded and unbounded settings.
-/

open CategoryTheory CategoryTheory.Limits Topology

namespace GaloisForLFunctions.IrregularStokes.EnhancedExponential

open CompactIndSheaf CompactIndEmbedding EnhancedIndPullback Bordered
open OrdinaryConvolution ClosedSupportSheaf

/-- Closed epigraph of a real phase in the compactified enhanced direction. -/
def compactifiedExponentialEpigraph {X : Type*} (φ : X → ℝ) : Set (X × EReal) :=
  {p | (φ p.1 : EReal) ≤ p.2}

/-- A continuous phase has closed compactified epigraph. -/
theorem isClosed_compactifiedExponentialEpigraph {X : Type*} [TopologicalSpace X]
    {φ : X → ℝ} (hφ : Continuous φ) :
    IsClosed (compactifiedExponentialEpigraph φ) :=
  isClosed_le (continuous_coe_real_ereal.comp (hφ.comp continuous_fst)) continuous_snd

@[simp]
theorem compactifiedExponentialEpigraph_top {X : Type*} (φ : X → ℝ) (x : X) :
    compactifiedExponentialEpigraph φ (x, ⊤) := by
  change (φ x : EReal) ≤ ⊤
  exact le_top

@[simp]
theorem compactifiedExponentialEpigraph_bot {X : Type*} (φ : X → ℝ) (x : X) :
    ¬ compactifiedExponentialEpigraph φ (x, ⊥) := by
  change ¬(φ x : EReal) ≤ ⊥
  simp

@[simp]
theorem compactifiedExponentialEpigraph_coe {X : Type*} (φ : X → ℝ) (x : X) (t : ℝ) :
    compactifiedExponentialEpigraph φ (x, (t : EReal)) ↔ φ x ≤ t := by
  change (φ x : EReal) ≤ (t : EReal) ↔ φ x ≤ t
  simp

/-- Pulling a compactified epigraph back by translation subtracts that translation from its
phase. -/
theorem enhancedTranslation_preimage_compactifiedExponentialEpigraph
    (X : TopCat.{0}) (φ : X → ℝ) (c : ℝ) :
    enhancedTranslation X c ⁻¹' compactifiedExponentialEpigraph φ =
      compactifiedExponentialEpigraph (fun x => φ x - c) := by
  ext p
  change (φ p.1 : EReal) ≤ p.2 + (c : EReal) ↔
    ((φ p.1 - c : ℝ) : EReal) ≤ p.2
  induction p.2 <;> simp [sub_eq_add_neg, ← EReal.coe_add]

/-- Integral sheaf carried by the compactified exponential epigraph. -/
noncomputable def compactifiedExponentialSheaf (X : TopCat.{0})
    (φ : X → ℝ) (_hφ : Continuous φ) : Sh (EnhancedCompactification X) :=
  (TopCat.Sheaf.pushforward IntModuleCat
    (subtypeInclusion (compactifiedExponentialEpigraph φ))).obj
      (constantIntModuleSheaf (TopCat.of (compactifiedExponentialEpigraph φ))
        (ModuleCat.of ℤ ℤ))

/-- Every sheaf on a compact space satisfies the stalkwise compact-support predicate. -/
theorem hasCompactSupport_of_compactSpace (Y : TopCat.{0}) [CompactSpace Y]
    (F : Sh Y) : HasCompactSupport Y F :=
  ⟨Set.univ, isCompact_univ, fun x hx => (hx (Set.mem_univ x)).elim⟩

/-- Compact-support realization of a compactified exponential sheaf on a compact base. -/
noncomputable def compactifiedExponentialCompactSheaf (X : TopCat.{0})
    [CompactSpace X] (φ : X → ℝ) (hφ : Continuous φ) :
    CompactlySupportedSheaf (EnhancedCompactification X) :=
  ⟨compactifiedExponentialSheaf X φ hφ,
    hasCompactSupport_of_compactSpace _ _⟩

/-- Ind-sheaf realization of a compactified exponential sheaf. -/
noncomputable def compactifiedExponentialIndSheaf (X : TopCat.{0})
    [CompactSpace X] (φ : X → ℝ) (hφ : Continuous φ) :
    IndSheaf (EnhancedCompactification X) :=
  (compactSheafToIndSheaf _).obj (compactifiedExponentialCompactSheaf X φ hφ)

/-- Degree-zero unbounded-derived realization of a compactified exponential ind-sheaf. -/
noncomputable def compactifiedExponentialDerivedObject (X : TopCat.{0})
    [CompactSpace X] (φ : X → ℝ) (hφ : Continuous φ) :
    DerivedIndSheaf (EnhancedCompactification X) :=
  (DerivedCategory.singleFunctor (IndSheaf (EnhancedCompactification X)) 0).obj
    (compactifiedExponentialIndSheaf X φ hφ)

/-- Degree-zero bounded-derived realization of a compactified exponential ind-sheaf. -/
noncomputable def compactifiedExponentialBoundedDerivedObject (X : TopCat.{0})
    [CompactSpace X] (φ : X → ℝ) (hφ : Continuous φ) :
    BoundedDerivedIndSheaf (EnhancedCompactification X) :=
  ⟨compactifiedExponentialDerivedObject X φ hφ, by
    change DerivedCategory.TStructure.t.bounded
      ((DerivedCategory.singleFunctor (IndSheaf (EnhancedCompactification X)) 0).obj
        (compactifiedExponentialIndSheaf X φ hφ))
    exact ⟨⟨0, by infer_instance⟩, ⟨0, by infer_instance⟩⟩⟩

/-- Compactified exponential object in the unbounded generated enhanced quotient. -/
noncomputable def compactifiedExponentialEnhancedObject (X : TopCat.{0})
    [CompactSpace X] (φ : X → ℝ) (hφ : Continuous φ) :
    GeneratedEnhancedQuotient X :=
  (generatedQuotientFunctor X).obj (compactifiedExponentialDerivedObject X φ hφ)

/-- Compactified exponential object in the bounded generated enhanced quotient. -/
noncomputable def compactifiedExponentialBoundedEnhancedObject (X : TopCat.{0})
    [CompactSpace X] (φ : X → ℝ) (hφ : Continuous φ) :
    BoundedGeneratedEnhancedQuotient X :=
  (boundedGeneratedQuotientFunctor X).obj
    (compactifiedExponentialBoundedDerivedObject X φ hφ)

end GaloisForLFunctions.IrregularStokes.EnhancedExponential
