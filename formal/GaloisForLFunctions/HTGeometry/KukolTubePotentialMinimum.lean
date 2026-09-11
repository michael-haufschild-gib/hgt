import GaloisForLFunctions.HTGeometry.KukolTubePotentialStrictConvexity

/-!
# Canonical minima for arbitrary real linear subgroup orbits

Application of Kukol, *Extended Future Tube Conjecture for Unipotent Subgroups*,
arXiv:2609.10214, Sections 4–5. These results use the native imaginary orbit
action and its reciprocal-margin exhaustion on the full strict-state domain.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry
open scoped BigOperators
open Set
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype ι]

/-- Admissible imaginary parameters restricted to an arbitrary real linear subgroup. -/
def kukolConstrainedTubeDomain (W : Submodule ℝ E) (v : ι → KukolLightCone E)
    (r s : ι → ℝ) (z : ι → E) : Set E := kukolTubeDomain v r s z ∩ (W : Set E)

/-- Every subgroup-restricted strict family has a unique minimizing imaginary parameter. -/
theorem kukolTubePotential_exists_unique_minimum (W : Submodule ℝ E)
    (v : ι → KukolLightCone E) (r s : ι → ℝ) (z : ι → E) (anchor : ι) :
    ∃! u : E,u ∈ kukolConstrainedTubeDomain W v r s z ∧
      IsMinOn (kukolTubePotential v r s z) (kukolConstrainedTubeDomain W v r s z) u := by
  let t := kukolTubePotential v r s z 0
  let K := kukolTubeSublevel v r s z t ∩ (W : Set E)
  have ht : t ≤ Real.exp t := by linarith [Real.add_one_le_exp t]
  have hzero : (0 : E) ∈ K := ⟨⟨kukolTubeDomain_zero v r s z,ht⟩,W.zero_mem⟩
  have hK : IsCompact K :=
    (isCompact_kukolTubeSublevel v r s z t anchor).inter_right W.closed_of_finiteDimensional
  have hKD : K ⊆ kukolConstrainedTubeDomain W v r s z := fun u hu => ⟨hu.1.1,hu.2⟩
  have hcont : ContinuousOn (kukolTubePotential v r s z) K :=
    (continuousOn_kukolTubePotential v r s z).mono (fun u hu => hu.1.1)
  obtain ⟨u,hu,hmin⟩ := hK.exists_isMinOn ⟨0,hzero⟩ hcont
  have hminD : IsMinOn (kukolTubePotential v r s z) (kukolConstrainedTubeDomain W v r s z) u := by
    intro w hw
    by_cases hle : kukolTubePotential v r s z w ≤ Real.exp t
    · exact hmin ⟨⟨hw.1,hle⟩,hw.2⟩
    · exact (hmin hzero).trans (ht.trans (le_of_lt (lt_of_not_ge hle)))
  refine ⟨u,⟨hKD hu,hminD⟩,?_⟩
  rintro w ⟨hw,hwmin⟩
  have hc : StrictConvexOn ℝ (kukolConstrainedTubeDomain W v r s z) (kukolTubePotential v r s z) :=
    (strictConvexOn_kukolTubePotential v r s z anchor).subset Set.inter_subset_left
      ((convex_kukolTubeDomain v r s z).inter W.convex)
  exact hc.eq_of_isMinOn hwmin hminD hw (hKD hu)

/-- The unique canonical imaginary parameter selected by the paper's orbit potential. -/
def kukolTubeMinimizer (W : Submodule ℝ E) (v : ι → KukolLightCone E)
    (r s : ι → ℝ) (z : ι → E) (anchor : ι) : E :=
  (kukolTubePotential_exists_unique_minimum W v r s z anchor).exists.choose

/-- The selected point lies in the subgroup and the strict domain and globally minimizes the potential there. -/
theorem kukolTubeMinimizer_spec (W : Submodule ℝ E) (v : ι → KukolLightCone E)
    (r s : ι → ℝ) (z : ι → E) (anchor : ι) :
    kukolTubeMinimizer W v r s z anchor ∈ kukolConstrainedTubeDomain W v r s z ∧
      IsMinOn (kukolTubePotential v r s z) (kukolConstrainedTubeDomain W v r s z)
        (kukolTubeMinimizer W v r s z anchor) :=
  (kukolTubePotential_exists_unique_minimum W v r s z anchor).exists.choose_spec

/-- The characterization is exact; there are no additional minimizing representatives. -/
theorem kukolTubeMinimizer_eq_iff (W : Submodule ℝ E) (v : ι → KukolLightCone E)
    (r s : ι → ℝ) (z : ι → E) (anchor : ι) (u : E) :
    u=kukolTubeMinimizer W v r s z anchor ↔
      u ∈ kukolConstrainedTubeDomain W v r s z ∧
        IsMinOn (kukolTubePotential v r s z) (kukolConstrainedTubeDomain W v r s z) u := by
  constructor
  · rintro rfl
    exact kukolTubeMinimizer_spec W v r s z anchor
  · intro hu
    exact (kukolTubePotential_exists_unique_minimum W v r s z anchor).unique hu
      (kukolTubeMinimizer_spec W v r s z anchor)

/-- The construction is independent of the anchor used to witness nonemptiness of the finite family. -/
theorem kukolTubeMinimizer_anchor_independent (W : Submodule ℝ E) (v : ι → KukolLightCone E)
    (r s : ι → ℝ) (z : ι → E) (anchor other : ι) :
    kukolTubeMinimizer W v r s z anchor=kukolTubeMinimizer W v r s z other :=
  (kukolTubeMinimizer_eq_iff W v r s z other _).mpr (kukolTubeMinimizer_spec W v r s z anchor)

/-- The positive canonical value of the orbit potential on a real linear subgroup. -/
def kukolTubeMinimumValue (W : Submodule ℝ E) (v : ι → KukolLightCone E)
    (r s : ι → ℝ) (z : ι → E) (anchor : ι) : ℝ :=
  kukolTubePotential v r s z (kukolTubeMinimizer W v r s z anchor)

theorem kukolTubeMinimumValue_pos (W : Submodule ℝ E) (v : ι → KukolLightCone E)
    (r s : ι → ℝ) (z : ι → E) (anchor : ι) : 0 < kukolTubeMinimumValue W v r s z anchor :=
  kukolTubePotential_mapsTo_pos v r s z anchor (kukolTubeMinimizer_spec W v r s z anchor).1.1

end GaloisForLFunctions.HTGeometry
