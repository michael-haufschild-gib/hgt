import GaloisForLFunctions.HTGeometry.ContinuumChronometricGravity

/-!
# Sharpness of branch-safe chronometric rigidity

The rigidity theorem says an injective observation encoding turns equality of branch-safe solution
graphs into equality of arbitrary nonlinear laws. Two hypotheses carry it, and this file shows both
are load-bearing rather than technical.

* **Injectivity of the encoding is necessary, not only sufficient.** If two geometries share an
  observation, two laws separating them have identical graphs. Rigidity therefore holds exactly
  when the encoding is injective. A clock-dark sector — a factor of the geometry that the encoding
  ignores — is the canonical way this fails.
* **Source labels must be fixed independently of the theory.** Relabelling the calibrated source
  set by a bijection changes the law but only transports its graph, so a theory free to choose its
  own labelling always matches.
-/

namespace GaloisForLFunctions.HTGeometry

universe u v w

section Sharpness

variable {Geometry : Type u} {Observation : Type w}

/-- **Non-injective encodings defeat rigidity.** Two geometries sharing an observation are
separated by two laws with identical branch-safe solution graphs. -/
theorem exists_ne_law_graph_eq_of_not_injective
    {encode : Geometry → Observation} (hnot : ¬ Function.Injective encode) :
    ∃ law₁ law₂ : Geometry → Prop,
      chronometricSolutionGraph encode law₁ = chronometricSolutionGraph encode law₂ ∧
        law₁ ≠ law₂ := by
  obtain ⟨g₁, g₂, henc, hne⟩ := Function.not_injective_iff.mp hnot
  have hkey : ∀ a b : Geometry, encode a = encode b → a ≠ b →
      chronometricSolutionGraph encode (fun g => g = a) ⊆
        chronometricSolutionGraph encode (fun g => g = b) := by
    intro a b hab hab' p hp
    obtain ⟨g, rfl⟩ := hp
    by_cases hga : g = a
    · subst hga
      refine ⟨b, Prod.ext ?_ ?_⟩
      · exact propext ⟨fun _ => rfl, fun _ => rfl⟩
      · exact hab.symm
    · by_cases hgb : g = b
      · subst hgb
        refine ⟨a, Prod.ext ?_ ?_⟩
        · exact propext ⟨fun h => absurd h hab', fun h => absurd h hga⟩
        · exact hab
      · refine ⟨g, Prod.ext ?_ ?_⟩
        · exact propext ⟨fun h => absurd h hgb, fun h => absurd h hga⟩
        · rfl
  refine ⟨fun g => g = g₁, fun g => g = g₂, ?_, ?_⟩
  · exact Set.Subset.antisymm (hkey g₁ g₂ henc hne) (hkey g₂ g₁ henc.symm (Ne.symm hne))
  · intro hlaw
    have hpt : (g₁ = g₁) ↔ (g₁ = g₂) := by
      rw [← eq_iff_iff]
      exact congrFun hlaw g₁
    exact hne (hpt.mp rfl)

/-- **Rigidity holds exactly when the observation encoding is injective.** -/
theorem chronometricSolutionGraph_rigid_iff_injective (encode : Geometry → Observation) :
    (∀ law₁ law₂ : Geometry → Prop,
        chronometricSolutionGraph encode law₁ = chronometricSolutionGraph encode law₂ →
          law₁ = law₂) ↔
      Function.Injective encode := by
  constructor
  · intro hrigid
    by_contra hnot
    obtain ⟨law₁, law₂, hgraph, hne⟩ := exists_ne_law_graph_eq_of_not_injective hnot
    exact hne (hrigid law₁ law₂ hgraph)
  · intro hinj law₁ law₂ hgraph
    exact (chronometricSolutionGraph_eq_iff_of_injective hinj law₁ law₂).1 hgraph

end Sharpness

/-! ## Clock-dark sectors -/

section HiddenSector

variable {Geometry : Type u} {Hidden : Type u} {Observation : Type w}

/-- An encoding that ignores a factor of the geometry is not injective as soon as that factor has
two distinct states. -/
theorem not_injective_hiddenSector [Nonempty Geometry]
    (encode : Geometry → Observation) {h₀ h₁ : Hidden} (hne : h₀ ≠ h₁) :
    ¬ Function.Injective fun p : Geometry × Hidden => encode p.1 := by
  intro hinj
  obtain ⟨g⟩ := ‹Nonempty Geometry›
  have := hinj (a₁ := (g, h₀)) (a₂ := (g, h₁)) rfl
  exact hne (congrArg Prod.snd this)

/-- **A clock-dark sector defeats rigidity.** If the geometry carries a factor absent from every
observation channel, two laws separating that factor have identical branch-safe graphs. -/
theorem exists_ne_law_graph_eq_of_hiddenSector [Nonempty Geometry]
    (encode : Geometry → Observation) {h₀ h₁ : Hidden} (hne : h₀ ≠ h₁) :
    ∃ law₁ law₂ : Geometry × Hidden → Prop,
      chronometricSolutionGraph (fun p : Geometry × Hidden => encode p.1) law₁ =
          chronometricSolutionGraph (fun p : Geometry × Hidden => encode p.1) law₂ ∧
        law₁ ≠ law₂ :=
  exists_ne_law_graph_eq_of_not_injective (not_injective_hiddenSector encode hne)

end HiddenSector

/-- **A clock-dark sector defeats continuum chronometric rigidity.** Squared clock intervals are
injective on metric fields, but a hidden companion field they do not see restores the ambiguity. -/
theorem exists_ne_law_graph_eq_of_hiddenSector_chronometric
    {Event : Type u} {Tangent : Type u}
    [AddCommGroup Tangent] [Module ℝ Tangent] {Hidden : Type u}
    {h₀ h₁ : Hidden} (hne : h₀ ≠ h₁) :
    ∃ law₁ law₂ : ChronometricMetricField Event Tangent × Hidden → Prop,
      chronometricSolutionGraph
            (fun p : ChronometricMetricField Event Tangent × Hidden =>
              ChronometricMetricField.squaredInterval p.1) law₁ =
          chronometricSolutionGraph
            (fun p : ChronometricMetricField Event Tangent × Hidden =>
              ChronometricMetricField.squaredInterval p.1) law₂ ∧
        law₁ ≠ law₂ := by
  haveI : Nonempty (ChronometricMetricField Event Tangent) :=
    ⟨{ form := fun _ => 0
       symmetric := fun _ _ _ => rfl }⟩
  exact exists_ne_law_graph_eq_of_hiddenSector ChronometricMetricField.squaredInterval hne

/-! ## Theory-dependent source labelling -/

section Relabelling

variable {Geometry : Type u} {Source : Type v} {Observation : Type w}

/-- Relabelling the calibrated source set transports the branch-safe graph. -/
theorem chronometricSolutionGraph_relabel (encode : Geometry → Observation)
    (law : Geometry → Source) (sigma : Source ≃ Source) :
    chronometricSolutionGraph encode (fun g => sigma (law g)) =
      (fun p : Source × Observation => (sigma p.1, p.2)) ''
        chronometricSolutionGraph encode law := by
  simp only [chronometricSolutionGraph]
  rw [← Set.range_comp]
  rfl

/-- **Source labels must be fixed independently of the theory.** A theory allowed to relabel the
calibrated source set produces a genuinely different operator whose graph is nevertheless the
transported image of the original graph, so graph comparison up to relabelling carries no
information about the operator. -/
theorem exists_ne_law_with_transported_graph (encode : Geometry → Observation)
    (law : Geometry → Source) (sigma : Source ≃ Source)
    (hmove : ∃ g, sigma (law g) ≠ law g) :
    (fun g => sigma (law g)) ≠ law ∧
      chronometricSolutionGraph encode (fun g => sigma (law g)) =
        (fun p : Source × Observation => (sigma p.1, p.2)) ''
          chronometricSolutionGraph encode law := by
  refine ⟨?_, chronometricSolutionGraph_relabel encode law sigma⟩
  obtain ⟨g, hg⟩ := hmove
  intro hEq
  exact hg (congrFun hEq g)

end Relabelling

end GaloisForLFunctions.HTGeometry
