import GaloisForLFunctions.HTGeometry.KukolImaginaryOrbitBalls

/-!
# Compact sublevels of the unipotent orbit potential

Kukol, arXiv:2609.10214, Proposition 4.1 uses the sum of reciprocal Lorentz
margins to exhaust an imaginary group orbit. For the constructed strict future
states, every potential sublevel has a positive uniform margin floor. Clamping
denominators at that floor gives a globally continuous description, proving
closedness in the ambient parameter space. The explicit orbit ball gives
boundedness, and finite-dimensional Heine--Borel gives compactness. This closes
the parameter-space exhaustion mechanism without a quotient or Stein premise.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry
open scoped BigOperators
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fintype ι]

/-- The Lorentz margin along an imaginary group orbit. -/
def kukolTubeMargin (v : KukolLightCone E) (r s : ℝ) (z u : E) : ℝ :=
  kukolQuadratic (kukolImaginaryAction u v (kukolStrictState r s z))

/-- The reciprocal Lorentz margins form the orbit exhaustion potential. -/
def kukolTubePotential (v : ι → KukolLightCone E) (r s : ι → ℝ) (z : ι → E) (u : E) : ℝ :=
  ∑ i, 1/kukolTubeMargin (v i) (r i) (s i) (z i) u

/-- An actual sublevel inside the future-tube orbit domain. -/
def kukolTubeSublevel (v : ι → KukolLightCone E) (r s : ι → ℝ) (z : ι → E) (t : ℝ) : Set E :=
  {u | (∀ i, 0 < kukolTubeMargin (v i) (r i) (s i) (z i) u) ∧
    kukolTubePotential v r s z u ≤ Real.exp t}

omit [Fintype ι] in
theorem continuous_kukolTubeMargin (v : KukolLightCone E) (r s : ℝ) (z : E) :
    Continuous (kukolTubeMargin v r s z) := by
  unfold kukolTubeMargin
  simp_rw [kukolQuadratic_imaginaryAction, kukolQuadratic_strictState]
  fun_prop

/-- Every point of a potential sublevel stays uniformly away from every null boundary. -/
theorem kukolTubeSublevel_margin_floor (v : ι → KukolLightCone E) (r s : ι → ℝ)
    (z : ι → E) (t : ℝ) :
    kukolTubeSublevel v r s z t ⊆
      {u | ∀ i, 1/Real.exp t ≤ kukolTubeMargin (v i) (r i) (s i) (z i) u} := by
  intro u hu i
  have hterm : 1/kukolTubeMargin (v i) (r i) (s i) (z i) u ≤ kukolTubePotential v r s z u :=
    Finset.single_le_sum (fun j _ => (one_div_pos.mpr (hu.1 j)).le) (Finset.mem_univ i)
  exact (one_div_le (hu.1 i) (Real.exp_pos t)).mp (hterm.trans hu.2)

/-- Clamping reciprocal denominators gives a globally continuous sublevel representation. -/
theorem kukolTubeSublevel_clamped (v : ι → KukolLightCone E) (r s : ι → ℝ)
    (z : ι → E) (t : ℝ) :
    kukolTubeSublevel v r s z t =
      {u | (∀ i, 1/Real.exp t ≤ kukolTubeMargin (v i) (r i) (s i) (z i) u) ∧
        (∑ i, 1/max (1/Real.exp t) (kukolTubeMargin (v i) (r i) (s i) (z i) u)) ≤ Real.exp t} := by
  ext u
  constructor
  · intro hu
    have hf := kukolTubeSublevel_margin_floor v r s z t hu
    refine ⟨hf, ?_⟩
    simpa only [kukolTubePotential, max_eq_right (hf _)] using hu.2
  · rintro ⟨hf,hp⟩
    refine ⟨fun i => (one_div_pos.mpr (Real.exp_pos t)).trans_le (hf i), ?_⟩
    simpa only [kukolTubePotential, max_eq_right (hf _)] using hp

/-- Potential sublevels are closed in the whole parameter space, not only within the tube. -/
theorem isClosed_kukolTubeSublevel (v : ι → KukolLightCone E) (r s : ι → ℝ)
    (z : ι → E) (t : ℝ) : IsClosed (kukolTubeSublevel v r s z t) := by
  rw [kukolTubeSublevel_clamped]
  have hclosed : IsClosed {u : E | ∀ i, 1/Real.exp t ≤
      kukolTubeMargin (v i) (r i) (s i) (z i) u} := by
    simpa only [Set.setOf_forall] using isClosed_iInter (fun i =>
      isClosed_le continuous_const (continuous_kukolTubeMargin (v i) (r i) (s i) (z i)))
  have hcont : Continuous (fun u : E => ∑ i,
      1/max (1/Real.exp t) (kukolTubeMargin (v i) (r i) (s i) (z i) u)) := by
    apply continuous_finsetSum
    intro i _
    apply continuous_const.div (continuous_const.max
      (continuous_kukolTubeMargin (v i) (r i) (s i) (z i)))
    intro u
    exact ne_of_gt ((one_div_pos.mpr (Real.exp_pos t)).trans_le (le_max_left _ _))
  exact hclosed.inter (isClosed_le hcont continuous_const)

/-- A single tube component bounds every simultaneous potential sublevel. -/
theorem isBounded_kukolTubeSublevel (v : ι → KukolLightCone E) (r s : ι → ℝ)
    (z : ι → E) (t : ℝ) (i₀ : ι) : Bornology.IsBounded (kukolTubeSublevel v r s z t) := by
  apply (kukolImaginaryAction_bounded (v i₀).1 (v i₀).2.1 (r i₀) (s i₀)
    (v i₀).2.2 (z i₀)).subset
  intro u hu
  exact ⟨Real.exp_pos (r i₀), hu.1 i₀⟩

/-- The reciprocal-margin potential has compact sublevels on every finite-dimensional orbit. -/
theorem isCompact_kukolTubeSublevel [FiniteDimensional ℝ E]
    (v : ι → KukolLightCone E) (r s : ι → ℝ) (z : ι → E) (t : ℝ) (i₀ : ι) :
    IsCompact (kukolTubeSublevel v r s z t) :=
  Metric.isCompact_iff_isClosed_bounded.mpr
    ⟨isClosed_kukolTubeSublevel v r s z t, isBounded_kukolTubeSublevel v r s z t i₀⟩

end GaloisForLFunctions.HTGeometry
