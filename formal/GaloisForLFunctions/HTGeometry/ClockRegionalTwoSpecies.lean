import GaloisForLFunctions.HTGeometry.ChronometricCausalDiamond
import GaloisForLFunctions.HTGeometry.KleinGordonConformalSpacetime

/-!
# The two-species scale law inside a causal diamond

A laboratory performs its experiments in a bounded region. The determination theorems of the
two-species programme quantify over *all* open regions, which is more than any laboratory supplies.

Restricting both the probes and the experiments to an open region costs nothing: the determination
argument is pointwise in the event, so probes posed inside the region determine the potential inside
the region. Taking the region to be the chronological diamond between two events — an open set, and
one that the clock's own worldline traverses — gives the two-species conformal scale law from
experiments performed only inside the diamond, with the probes of the massive species constructed
rather than assumed.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped ContDiff

/-! ## Probes and experiments confined to a region -/

section Regional

variable {Y : Type*} [TopologicalSpace Y]

/-- Clock probes confined to a region: at every event of the region there is an open neighbourhood
*inside the region* carrying a solution that is nonvanishing throughout it. -/
def OpenProbesOn (wave : (Y → ℝ) → (Y → ℝ)) (potential : Y → ℝ) (region : Set Y) : Prop :=
  ∀ x ∈ region, ∃ W : Set Y, IsOpen W ∧ x ∈ W ∧ W ⊆ region ∧ ∃ u : Y → ℝ,
    SolvesPotentialWaveOn wave potential u W ∧ ∀ y ∈ W, u y ≠ 0

/-- Probes everywhere restrict to probes inside any open region. -/
theorem openProbesOn_of_openProbes {wave : (Y → ℝ) → (Y → ℝ)} {potential : Y → ℝ}
    {region : Set Y} (hregion : IsOpen region) (h : OpenProbes wave potential) :
    OpenProbesOn wave potential region := by
  intro x hx
  obtain ⟨W, hWopen, hxW, u, hu, hune⟩ := h x
  exact ⟨W ∩ region, hWopen.inter hregion, ⟨hxW, hx⟩, Set.inter_subset_right, u,
    fun y hy => hu y hy.1, fun y hy => hune y hy.1⟩

/-- **Experiments inside a region determine the potential inside that region.** Only solutions on
open subsets of the region are used, so nothing outside the laboratory is assumed observable. -/
theorem potential_eqOn_of_openProbesOn {wave : (Y → ℝ) → (Y → ℝ)} {potential other : Y → ℝ}
    {region : Set Y} (hopen : OpenProbesOn wave potential region)
    (h : ∀ (u : Y → ℝ) (W : Set Y), IsOpen W → W ⊆ region →
      SolvesPotentialWaveOn wave potential u W → SolvesPotentialWaveOn wave other u W) :
    Set.EqOn other potential region := by
  intro x hx
  obtain ⟨W, hWopen, hxW, hWsub, u, hu, hune⟩ := hopen x hx
  exact potential_eqOn_of_solvesOn hu (h u W hWopen hWsub hu) hune hxW

end Regional

/-! ## The scale law on a region -/

section RegionalScale

variable {d : ℕ}

/-- **The two-species scale law from experiments confined to a region.** -/
theorem scale_reconstruction_on_region (M : SmoothMetricChart d) (a : ℝ)
    {σ : (Fin d → ℝ) → ℝ} (hσ : ContDiff ℝ ∞ σ) {massSq : ℝ} (hmass : massSq ≠ 0)
    {region : Set (Fin d → ℝ)} (hregion : IsOpen region)
    (hop₁ : OpenProbesOn M.dalembert (M.conformalPotential a massSq σ) region)
    {other₁ other₂ : (Fin d → ℝ) → ℝ}
    (h₁ : ∀ (u : (Fin d → ℝ) → ℝ) (W : Set (Fin d → ℝ)), IsOpen W → W ⊆ region →
      SolvesPotentialWaveOn M.dalembert (M.conformalPotential a massSq σ) u W →
        SolvesPotentialWaveOn M.dalembert other₁ u W)
    (h₂ : ∀ (u : (Fin d → ℝ) → ℝ) (W : Set (Fin d → ℝ)), IsOpen W → W ⊆ region →
      SolvesPotentialWaveOn M.dalembert (M.conformalPotential a 0 σ) u W →
        SolvesPotentialWaveOn M.dalembert other₂ u W)
    {x : Fin d → ℝ} (hx : x ∈ region) :
    (other₁ x - other₂ x) / massSq = Real.exp (2 * σ x) := by
  have e₁ : other₁ x = M.conformalPotential a massSq σ x :=
    potential_eqOn_of_openProbesOn hop₁ h₁ hx
  have hop₂ : OpenProbesOn M.dalembert (M.conformalPotential a 0 σ) region :=
    openProbesOn_of_openProbes hregion
      (openProbes_of_solves (solvesPotentialWave_masslessProbe M a hσ)
        (masslessProbe_ne_zero a σ))
  have e₂ : other₂ x = M.conformalPotential a 0 σ x :=
    potential_eqOn_of_openProbesOn hop₂ h₂ hx
  rw [e₁, e₂, M.conformalPotential_difference a massSq 0 σ x, sub_zero]
  field_simp

end RegionalScale

/-! ## The diamond of the Klein--Gordon chart -/

section Diamond

variable {d : ℕ}

/-- The metric whose cone is the causal structure of the probe construction. -/
noncomputable def kgMetric (d : ℕ) : SmoothPseudoMetric (d + 1) :=
  SmoothPseudoMetric.ofSignature (kgEps d) (kgEps_ne_zero d)

theorem kgChart_eq_chart (d : ℕ) : kgChart d = (kgMetric d).chart := rfl

/-- The signature of the Klein--Gordon construction is the Minkowski signature, so its cones are the
Minkowski cones. -/
theorem kgMetric_eq_minkowski (d : ℕ) : kgMetric d = SmoothPseudoMetric.minkowski (d + 1) := by
  refine SmoothPseudoMetric.ext' ?_
  funext x
  have heps : kgEps d = fun i : Fin (d + 1) => if (i : ℕ) = 0 then (-1 : ℝ) else 1 := by
    funext i
    rw [kgEps]
    by_cases hi : i = 0
    · simp [hi]
    · have hival : (i : ℕ) ≠ 0 := fun h => hi (Fin.ext h)
      simp [hi, hival]
  simp only [kgMetric, SmoothPseudoMetric.ofSignature, SmoothPseudoMetric.minkowski, heps]

/-- The chronological diamond of the probe construction between two events. -/
noncomputable def kgDiamond (d : ℕ) (p q : Fin (d + 1) → ℝ) : Set (Fin (d + 1) → ℝ) :=
  SmoothPseudoMetric.chronoDiamond (kgMetric d) p q

theorem isOpen_kgDiamond (d : ℕ) (p q : Fin (d + 1) → ℝ) : IsOpen (kgDiamond d p q) :=
  SmoothPseudoMetric.isOpen_chronoDiamond _ p q

/-- **The diamond is not empty**: the interior of the clock's own worldline segment lies in it. -/
theorem mem_kgDiamond_segment (p : Fin (d + 1) → ℝ) {T t : ℝ} (ht0 : 0 < t) (htT : t < T) :
    p + t • SmoothPseudoMetric.timeAxis d ∈
      kgDiamond d p (p + T • SmoothPseudoMetric.timeAxis d) := by
  rw [kgDiamond, kgMetric_eq_minkowski]
  exact SmoothPseudoMetric.mem_chronoDiamond_segment p ht0 htT

/-- **The two-species conformal clock scale law inside a causal diamond.** For an arbitrary smooth
conformal factor on spacetime, experiments performed only inside the chronological diamond of two
events reconstruct the conformal scale at every event of that diamond. The probes of the massive
species are constructed, not assumed. -/
theorem twoSpecies_scale_reconstruction_diamond {N : ℕ}
    (hN : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) + 2 < N)
    {σ : ℝ × EuclideanSpace ℝ (Fin d) → ℝ} (hσ : ContDiff ℝ ∞ σ) {massSq : ℝ} (hmass : massSq ≠ 0)
    (p q : Fin (d + 1) → ℝ)
    {other₁ other₂ : (Fin (d + 1) → ℝ) → ℝ}
    (h₁ : ∀ (u : (Fin (d + 1) → ℝ) → ℝ) (W : Set (Fin (d + 1) → ℝ)), IsOpen W →
      W ⊆ kgDiamond d p q →
      SolvesPotentialWaveOn (kgChart d).dalembert
        ((kgChart d).conformalPotential 0 massSq fun y => σ (y 0, kgSpatial d y)) u W →
        SolvesPotentialWaveOn (kgChart d).dalembert other₁ u W)
    (h₂ : ∀ (u : (Fin (d + 1) → ℝ) → ℝ) (W : Set (Fin (d + 1) → ℝ)), IsOpen W →
      W ⊆ kgDiamond d p q →
      SolvesPotentialWaveOn (kgChart d).dalembert
        ((kgChart d).conformalPotential 0 0 fun y => σ (y 0, kgSpatial d y)) u W →
        SolvesPotentialWaveOn (kgChart d).dalembert other₂ u W)
    {x : Fin (d + 1) → ℝ} (hx : x ∈ kgDiamond d p q) :
    (other₁ x - other₂ x) / massSq = Real.exp (2 * σ (x 0, kgSpatial d x)) :=
  scale_reconstruction_on_region (kgChart d) 0 (contDiff_comp_kgEvent hσ) hmass
    (isOpen_kgDiamond d p q)
    (openProbesOn_of_openProbes (isOpen_kgDiamond d p q)
      (openProbes_conformalPotential (N := N) hN hσ massSq))
    h₁ h₂ hx

end Diamond

end GaloisForLFunctions.HTGeometry
