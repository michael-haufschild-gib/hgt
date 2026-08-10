import GaloisForLFunctions.HTGeometry.InfiniteTorusEquidistribution
import GaloisForLFunctions.HTGeometry.InfiniteTorusKroneckerDensity

/-!
# The recurrence torus of a component-factorized spectrum

Relative to a reference label in every component, the phase of a total energy is the sum of the
component gap phases.  The resulting embedding of the gap torus into the space of phase functions on
the joint label set is an injective continuous homomorphism, so the closure of the phase orbit is
exactly its image, a torus of dimension `∑ (D_r - 1)`.  Unique ergodicity of the Kronecker flow then
computes every completed time average as a Haar integral over that torus.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {C : Type*} [Fintype C] [DecidableEq C]
variable {J : C → Type*} [∀ r, Fintype (J r)] [∀ r, DecidableEq (J r)]

/-- The gap index set: one coordinate for every non-reference label of every component. -/
abbrev ComponentGapIndex (J : C → Type*) [∀ r, DecidableEq (J r)] (a₀ : ∀ r, J r) : Type _ :=
  Σ r : C, {a : J r // a ≠ a₀ r}

/-- The component gap frequencies of `(1)`. -/
def componentGapFrequency (energy : ∀ r, J r → ℝ) (a₀ : ∀ r, J r) :
    ComponentGapIndex J a₀ → ℝ :=
  fun i => energy i.1 i.2.1 - energy i.1 (a₀ i.1)

omit [Fintype C] [DecidableEq C] in
theorem card_componentGap (a₀ : ∀ r, J r) (r : C) :
    Fintype.card {a : J r // a ≠ a₀ r} = Fintype.card (J r) - 1 := by
  classical
  rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]

/-- The phase coordinate of a label: the reference label carries no phase. -/
def gapPhase (a₀ : ∀ r, J r) (z : ComponentGapIndex J a₀ → AddCircle (1 : ℝ)) (r : C)
    (a : J r) : AddCircle (1 : ℝ) :=
  if h : a = a₀ r then 0 else z ⟨r, ⟨a, h⟩⟩

/-- **The recurrence torus embedding `(2)`.**  A gap phase vector becomes a phase function on the
joint label set by summing its component coordinates. -/
def phaseEmbed (a₀ : ∀ r, J r) (z : ComponentGapIndex J a₀ → AddCircle (1 : ℝ)) :
    (∀ r, J r) → AddCircle (1 : ℝ) :=
  fun x => ∑ r, gapPhase a₀ z r (x r)

omit [DecidableEq C] [∀ r, Fintype (J r)] in
theorem phaseEmbed_add (a₀ : ∀ r, J r) (z w : ComponentGapIndex J a₀ → AddCircle (1 : ℝ)) :
    phaseEmbed a₀ (z + w) = phaseEmbed a₀ z + phaseEmbed a₀ w := by
  funext x
  simp only [phaseEmbed, Pi.add_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [gapPhase, gapPhase, gapPhase]
  split_ifs with h
  · rw [add_zero]
  · rfl

omit [DecidableEq C] [∀ r, Fintype (J r)] in
theorem phaseEmbed_reference (a₀ : ∀ r, J r) (z : ComponentGapIndex J a₀ → AddCircle (1 : ℝ)) :
    phaseEmbed a₀ z a₀ = 0 := by
  rw [phaseEmbed]
  refine Finset.sum_eq_zero fun r _ => ?_
  rw [gapPhase, dif_pos rfl]

omit [∀ r, Fintype (J r)] in
theorem phaseEmbed_update (a₀ : ∀ r, J r) (z : ComponentGapIndex J a₀ → AddCircle (1 : ℝ))
    (r : C) (a : J r) (ha : a ≠ a₀ r) :
    phaseEmbed a₀ z (Function.update a₀ r a) = z ⟨r, ⟨a, ha⟩⟩ := by
  classical
  rw [phaseEmbed, Finset.sum_eq_single r]
  · rw [Function.update_self, gapPhase, dif_neg ha]
  · intro b _ hbr
    rw [Function.update_of_ne hbr, gapPhase, dif_pos rfl]
  · intro h
    exact absurd (Finset.mem_univ r) h

omit [∀ r, Fintype (J r)] in
/-- **The embedding is injective `(1)`.**  Comparing with the all-reference coordinate isolates
every component phase. -/
theorem phaseEmbed_injective (a₀ : ∀ r, J r) :
    Function.Injective (phaseEmbed (J := J) a₀) := by
  intro z w hzw
  funext i
  obtain ⟨r, a, ha⟩ := i
  rw [← phaseEmbed_update a₀ z r a ha, ← phaseEmbed_update a₀ w r a ha, hzw]

omit [DecidableEq C] [∀ r, Fintype (J r)] in
theorem continuous_phaseEmbed (a₀ : ∀ r, J r) :
    Continuous (phaseEmbed (J := J) a₀) := by
  classical
  refine continuous_pi fun x => continuous_finsetSum _ fun r _ => ?_
  simp only [gapPhase]
  by_cases h : x r = a₀ r
  · simp only [dif_pos h]
    exact continuous_const
  · simp only [dif_neg h]
    exact continuous_apply _

/-- The recurrence torus embedding as a continuous map. -/
def phaseEmbedMap (a₀ : ∀ r, J r) :
    C(ComponentGapIndex J a₀ → AddCircle (1 : ℝ), (∀ r, J r) → AddCircle (1 : ℝ)) where
  toFun := phaseEmbed a₀
  continuous_toFun := continuous_phaseEmbed a₀

/-! ## The orbit is the embedded flow -/

/-- The total energy of a joint label. -/
def componentTotalEnergy (energy : ∀ r, J r → ℝ) (x : ∀ r, J r) : ℝ :=
  ∑ r, energy r (x r)

omit [DecidableEq C] [∀ r, Fintype (J r)] in
theorem phaseEmbed_clockPhasePoint (energy : ∀ r, J r → ℝ) (a₀ : ∀ r, J r) (t : ℝ)
    (x : ∀ r, J r) :
    phaseEmbed a₀ (clockPhasePoint (componentGapFrequency energy a₀) t) x
      = ((t * (componentTotalEnergy energy x - componentTotalEnergy energy a₀)
            / (2 * Real.pi) : ℝ) : AddCircle (1 : ℝ)) := by
  classical
  have hterm : ∀ r : C, gapPhase a₀ (clockPhasePoint (componentGapFrequency energy a₀) t) r (x r)
      = ((t * (energy r (x r) - energy r (a₀ r)) / (2 * Real.pi) : ℝ) : AddCircle (1 : ℝ)) := by
    intro r
    rw [gapPhase]
    by_cases h : x r = a₀ r
    · rw [dif_pos h, h]
      simp
    · rw [dif_neg h, clockPhasePoint, componentGapFrequency]
  rw [phaseEmbed, Finset.sum_congr rfl fun r _ => hterm r]
  rw [componentTotalEnergy, componentTotalEnergy]
  have hsum : ∑ r : C, (t * (energy r (x r) - energy r (a₀ r)) / (2 * Real.pi))
      = t * ((∑ r, energy r (x r)) - ∑ r, energy r (a₀ r)) / (2 * Real.pi) := by
    rw [← Finset.sum_div, ← Finset.mul_sum, ← Finset.sum_sub_distrib]
  rw [← hsum]
  exact (map_sum (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))) _ _).symm

/-! ## Orbit closure -/

omit [DecidableEq C] [∀ r, Fintype (J r)] in
/-- **The completed orbit closure `(1)`–`(3)`.**  The closure of the projective phase orbit is
exactly the image of the gap torus. -/
theorem closure_range_phaseEmbed_clockPhasePoint (energy : ∀ r, J r → ℝ) (a₀ : ∀ r, J r)
    (h : RationallyIndependentSequence (componentGapFrequency energy a₀)) :
    closure (Set.range fun t : ℝ =>
        phaseEmbed a₀ (clockPhasePoint (componentGapFrequency energy a₀) t))
      = Set.range (phaseEmbed (J := J) a₀) := by
  classical
  have hcont := continuous_phaseEmbed (J := J) a₀
  have hclosed : IsClosed (Set.range (phaseEmbed (J := J) a₀)) :=
    (isCompact_range hcont).isClosed
  refine Set.Subset.antisymm (closure_minimal ?_ hclosed) ?_
  · rintro _ ⟨t, rfl⟩
    exact ⟨_, rfl⟩
  · have hdense := dense_range_clockPhasePoint (componentGapFrequency energy a₀) h
    calc Set.range (phaseEmbed (J := J) a₀)
        = phaseEmbed a₀ '' closure (Set.range (clockPhasePoint (componentGapFrequency energy a₀)))
          := by rw [hdense.closure_eq, Set.image_univ]
      _ ⊆ closure (phaseEmbed a₀ ''
            Set.range (clockPhasePoint (componentGapFrequency energy a₀))) :=
          image_closure_subset_closure_image hcont
      _ = closure (Set.range fun t : ℝ =>
            phaseEmbed a₀ (clockPhasePoint (componentGapFrequency energy a₀) t)) := by
          rw [← Set.range_comp]
          rfl

/-! ## The completed time average -/

/-- **The completed Haar law `(4)`.**  Under rational independence of the component gaps the
symmetric time average of every continuous function of the projective phase converges to its Haar
mean over the recurrence torus. -/
theorem hasHaarTimeAverage_comp_phaseEmbed (energy : ∀ r, J r → ℝ) (a₀ : ∀ r, J r)
    (h : RationallyIndependentSequence (componentGapFrequency energy a₀))
    (f : C((∀ r, J r) → AddCircle (1 : ℝ), ℂ)) :
    HasHaarTimeAverage (componentGapFrequency energy a₀) (f.comp (phaseEmbedMap a₀)) :=
  hasHaarTimeAverage_of_continuous h _

end

end GaloisForLFunctions.HTGeometry
