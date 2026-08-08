import GaloisForLFunctions.HTGeometry.ClosedSubgroupLineStructure
import GaloisForLFunctions.HTGeometry.PeriodSubgroupCyclic

/-!
# Full-period extraction

The full period group of a function on a finite-dimensional space,

`translationPeriods G = {h | forall z, G (z + h) = G z}`,

is a closed additive subgroup whenever `G` is continuous, so the line-direction structure theorem
applies to it verbatim: `G` has a linear space of directions along which it is constant, and modulo
that space its periods are separated.

When `G` is entire on a complex space the linear part is automatically a **complex** subspace, not
merely a real one.  A real line of periods through a direction `x` makes the entire one-variable
restriction `w -> G (z + w • x)` constant on the real axis, and the identity theorem then makes it
constant on all of `C`.  This is exactly the classical statement that the identity component of the
period group of a holomorphic function is complex-linear.
-/

open Filter Topology Set

namespace GaloisForLFunctions.HTGeometry

variable {V : Type*} {W : Type*}

/-- The full group of translation periods of a function. -/
def translationPeriods [AddCommGroup V] (G : V → W) : AddSubgroup V where
  carrier := {h | Function.Periodic G h}
  zero_mem' := by intro z; simp
  add_mem' := fun ha hb => Function.Periodic.add_period ha hb
  neg_mem' := fun ha => Function.Periodic.neg ha

@[simp]
theorem mem_translationPeriods [AddCommGroup V] {G : V → W} {h : V} :
    h ∈ translationPeriods G ↔ ∀ z, G (z + h) = G z := Iff.rfl

/-- In one complex variable this is the corpus period subgroup. -/
theorem translationPeriods_eq_periodSubgroup (f : ℂ → ℂ) :
    translationPeriods f = periodSubgroup f := rfl

/-- **The full period group of a continuous function is closed.** -/
theorem isClosed_translationPeriods [AddCommGroup V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [TopologicalSpace W] [T2Space W]
    {G : V → W} (hG : Continuous G) :
    IsClosed ((translationPeriods G : AddSubgroup V) : Set V) := by
  have hset : ((translationPeriods G : AddSubgroup V) : Set V)
      = ⋂ z : V, {h : V | G (z + h) = G z} := by
    ext h
    simp only [SetLike.mem_coe, mem_translationPeriods, Set.mem_iInter, Set.mem_setOf_eq]
  rw [hset]
  refine isClosed_iInter fun z => ?_
  have hcont : Continuous fun h : V => G (z + h) := hG.comp (continuous_const.add continuous_id)
  exact isClosed_eq hcont continuous_const

section Complex

variable [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- **The linear period directions of an entire function are complex.**  A real line of periods in
direction `x` restricts `G` to a constant on the real axis of the complex line through `x`, and the
identity theorem propagates that to the whole line. -/
theorem complex_smul_mem_lineDirections_translationPeriods
    {G : V → ℂ} (hG : AnalyticOnNhd ℂ G Set.univ) {x : V}
    (hx : x ∈ lineDirections (translationPeriods G)) (w : ℂ) :
    w • x ∈ lineDirections (translationPeriods G) := by
  -- It suffices to show every complex multiple of `x` is a period.
  have key : ∀ v : ℂ, ∀ z : V, G (z + v • x) = G z := by
    intro v z
    set L : ℂ →L[ℂ] V := (ContinuousLinearMap.id ℂ ℂ).smulRight x with hL
    have hLapply : ∀ u : ℂ, L u = u • x := by
      intro u
      rw [hL]
      simp
    set f : ℂ → ℂ := fun u => G (z + L u) - G z with hf
    have hfa : AnalyticOnNhd ℂ f Set.univ := by
      have haff : AnalyticOnNhd ℂ (fun u : ℂ => z + L u) Set.univ :=
        analyticOnNhd_const.add (L.analyticOnNhd Set.univ)
      have hcomp : AnalyticOnNhd ℂ (fun u : ℂ => G (z + L u)) Set.univ :=
        (hG.comp haff) fun u _ => Set.mem_univ _
      exact hcomp.sub analyticOnNhd_const
    have hcast : ∀ (r : ℝ) (y : V), ((r : ℂ)) • y = r • y := by
      intro r y
      rw [← Complex.coe_algebraMap, algebraMap_smul]
    have hreal : ∀ t : ℝ, f (t : ℂ) = 0 := by
      intro t
      have hper : G (z + (t : ℝ) • x) = G z := hx t z
      rw [hf]
      simp only [hLapply, hcast, hper, sub_self]
    have hfreq : ∃ᶠ u in 𝓝[≠] (0 : ℂ), f u = 0 := by
      have htend : Tendsto (fun n : ℕ => ((1 / (n + 1 : ℝ) : ℝ) : ℂ)) atTop (𝓝[≠] (0 : ℂ)) := by
        refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
        · have h : Tendsto (fun n : ℕ => (1 / (n + 1 : ℝ))) atTop (𝓝 (0 : ℝ)) :=
            tendsto_one_div_add_atTop_nhds_zero_nat
          have h2 : Tendsto (fun n : ℕ => ((1 / (n + 1 : ℝ) : ℝ) : ℂ)) atTop
              (𝓝 (((0 : ℝ) : ℂ))) := (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp h
          rwa [Complex.ofReal_zero] at h2
        · filter_upwards with n
          simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
          have hpos : (0 : ℝ) < 1 / (n + 1 : ℝ) := by positivity
          exact Complex.ofReal_ne_zero.mpr hpos.ne'
      exact htend.frequently (Frequently.of_forall fun n => hreal _)
    have hzero : Set.EqOn f 0 Set.univ :=
      hfa.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ
        (Set.mem_univ _) hfreq
    have hv := hzero (Set.mem_univ v)
    rw [hf] at hv
    simp only [hLapply, Pi.zero_apply, sub_eq_zero] at hv
    exact hv
  intro t z
  have hcast : ((t : ℂ)) • (w • x) = (t : ℝ) • (w • x) := by
    rw [← Complex.coe_algebraMap, algebraMap_smul]
  have hstep : (t : ℝ) • (w • x) = ((t : ℂ) * w) • x := by
    rw [← hcast, smul_smul]
  rw [hstep]
  exact key _ z

end Complex

/-- **Full-period extraction.**  For a continuous function on a finite-dimensional real space the
period group is closed, its constancy directions form a linear subspace of periods, and the periods
are separated modulo that subspace. -/
theorem exists_pos_forall_mem_lineDirections_translationPeriods
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [TopologicalSpace W] [T2Space W] {G : V → W} (hG : Continuous G) :
    ∃ ε > 0, ∀ h ∈ translationPeriods G, ‖h‖ < ε →
      h ∈ lineDirections (translationPeriods G) :=
  exists_pos_forall_mem_lineDirections (isClosed_translationPeriods hG)

/-- **Full-period extraction for an entire function on a finite-dimensional complex space.**  The
period group is closed; its line directions form a complex subspace consisting of periods; and
modulo that subspace the periods are separated. -/
theorem analytic_full_period_extraction
    [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    {G : V → ℂ} (hG : AnalyticOnNhd ℂ G Set.univ) :
    IsClosed ((translationPeriods G : AddSubgroup V) : Set V) ∧
    (∀ x ∈ lineDirections (translationPeriods G), ∀ w : ℂ,
        w • x ∈ lineDirections (translationPeriods G)) ∧
    (∀ x ∈ lineDirections (translationPeriods G), x ∈ translationPeriods G) ∧
    ∃ ε > 0, ∀ h ∈ translationPeriods G, ‖h‖ < ε →
      h ∈ lineDirections (translationPeriods G) := by
  haveI : FiniteDimensional ℝ V := Module.Finite.trans ℂ V
  have hcont : Continuous G := by
    rw [← continuousOn_univ]
    exact hG.continuousOn
  refine ⟨isClosed_translationPeriods hcont, ?_, ?_,
    exists_pos_forall_mem_lineDirections_translationPeriods hcont⟩
  · intro x hx w
    exact complex_smul_mem_lineDirections_translationPeriods hG hx w
  · intro x hx
    exact lineDirections_le _ hx

end GaloisForLFunctions.HTGeometry
