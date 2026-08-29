import GaloisForLFunctions.HTGeometry.RungeDensity
import GaloisForLFunctions.HTGeometry.DifferentialAlgebraicCompactOpenMeagre

/-!
# The differentially algebraic locus is compact-open dense

Runge approximation on each member of an explicit compact exhaustion of `Ω` produces a sequence of
differentially algebraic holomorphic functions converging locally uniformly to any prescribed
holomorphic function.  Hence the differentially algebraic locus is dense in the compact-open
Fréchet space `O(Ω)`.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Set Filter Topology

noncomputable section

variable {Ω : Set ℂ}

/-! ## An explicit compact exhaustion of an open set -/

/-- The `j`-th member of the canonical compact exhaustion of `Ω`. -/
def rungeExhaustion (Ω : Set ℂ) (j : ℕ) : Set ℂ :=
  Metric.closedBall (0 : ℂ) j ∩ {z | ∀ w ∉ Ω, (1 : ℝ) / (j + 1) ≤ dist z w}

theorem isCompact_rungeExhaustion (Ω : Set ℂ) (j : ℕ) : IsCompact (rungeExhaustion Ω j) := by
  refine (isCompact_closedBall (0 : ℂ) j).inter_right ?_
  have hrw : {z : ℂ | ∀ w ∉ Ω, (1 : ℝ) / (j + 1) ≤ dist z w}
      = ⋂ w ∈ (Ωᶜ : Set ℂ), {z : ℂ | (1 : ℝ) / (j + 1) ≤ dist z w} := by
    ext z
    simp [Set.mem_iInter]
  rw [hrw]
  refine isClosed_biInter fun w _ => ?_
  exact isClosed_le continuous_const (by fun_prop)

theorem rungeExhaustion_subset (Ω : Set ℂ) (j : ℕ) : rungeExhaustion Ω j ⊆ Ω := by
  intro z hz
  by_contra hzΩ
  have := hz.2 z hzΩ
  simp at this
  have hpos : (0:ℝ) < 1 / ((j : ℝ) + 1) := by positivity
  linarith

theorem rungeExhaustion_mono (Ω : Set ℂ) {i j : ℕ} (hij : i ≤ j) :
    rungeExhaustion Ω i ⊆ rungeExhaustion Ω j := by
  intro z hz
  refine ⟨?_, ?_⟩
  · have h1 := hz.1
    rw [Metric.mem_closedBall] at h1 ⊢
    have : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
    linarith
  · intro w hw
    have h2 := hz.2 w hw
    have hle : (1:ℝ) / ((j : ℝ) + 1) ≤ 1 / ((i : ℝ) + 1) := by
      have hi : (0:ℝ) < (i : ℝ) + 1 := by positivity
      have : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
      apply div_le_div_of_nonneg_left (by norm_num) hi
      linarith
    linarith

theorem exists_rungeExhaustion_superset (hΩ : IsOpen Ω) {K : Set ℂ} (hK : IsCompact K)
    (hKΩ : K ⊆ Ω) : ∃ j : ℕ, K ⊆ rungeExhaustion Ω j := by
  obtain ⟨δ, hδ, hthick⟩ := hK.exists_thickening_subset_open hΩ hKΩ
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
  obtain ⟨j, hj⟩ := exists_nat_gt (max R (1 / δ))
  refine ⟨j, fun z hz => ?_⟩
  have hjR : R < (j : ℝ) := lt_of_le_of_lt (le_max_left _ _) hj
  have hjδ : 1 / δ < (j : ℝ) := lt_of_le_of_lt (le_max_right _ _) hj
  refine ⟨?_, ?_⟩
  · have := hR hz
    rw [Metric.mem_closedBall] at this ⊢
    linarith
  · intro w hw
    by_contra hcon
    push Not at hcon
    have hdw : dist w z < δ := by
      have hle : (1:ℝ) / ((j : ℝ) + 1) ≤ δ := by
        rw [div_le_iff₀ (by positivity)]
        rw [div_lt_iff₀ hδ] at hjδ
        nlinarith [hδ]
      rw [dist_comm]
      linarith
    exact hw (hthick (Metric.mem_thickening_iff.2 ⟨z, hz, hdw⟩))


/-! ## Compact-open density of the differentially algebraic locus -/

/-- An analytic function on `Ω` as a member of the compact-open holomorphic space. -/
def toHoloCO {G : ℂ → ℂ} (hG : AnalyticOnNhd ℂ G Ω) : HoloCO Ω := by
  refine ⟨⟨fun z : ↥Ω => G (z : ℂ), ?_⟩, ?_⟩
  · exact ContinuousOn.restrict (fun z hz => (hG z hz).continuousAt.continuousWithinAt)
  · show DifferentiableOn ℂ (holoExtend Ω (fun z : ↥Ω => G (z : ℂ))) Ω
    have heq : Set.EqOn (holoExtend Ω (fun z : ↥Ω => G (z : ℂ))) G Ω := fun z hz =>
      holoExtend_of_mem _ hz
    exact DifferentiableOn.congr hG.differentiableOn (fun z hz => heq hz)

theorem holoCOFun_toHoloCO {G : ℂ → ℂ} (hG : AnalyticOnNhd ℂ G Ω) :
    Set.EqOn (holoCOFun (toHoloCO hG)) G Ω := fun _ hz => holoExtend_of_mem _ hz

theorem infinite_of_isOpen_nonempty (hΩ : IsOpen Ω) (hΩne : Ω.Nonempty) : Ω.Infinite := by
  obtain ⟨z₀, hz₀⟩ := hΩne
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hΩ z₀ hz₀
  refine Set.infinite_of_injective_forall_mem (f := fun k : ℕ => domainSampleNode z₀ ε k) ?_ ?_
  · exact domainSampleNode_injective z₀ hε
  · intro k
    exact hball (domainSampleNode_mem_ball z₀ hε k)

/-- **The differentially algebraic locus is compact-open dense.** -/
theorem dense_daCompactOpenLocus (hΩ : IsOpen Ω) (hΩc : IsPreconnected Ω) (hΩne : Ω.Nonempty) :
    Dense (daCompactOpenLocus Ω) := by
  classical
  haveI := hΩ.locallyCompactSpace
  have hΩinf : Ω.Infinite := infinite_of_isOpen_nonempty hΩ hΩne
  intro F
  have hf : AnalyticOnNhd ℂ (holoCOFun F) Ω := analyticOnNhd_holoCOFun hΩ F
  have hchoice : ∀ j : ℕ, ∃ G : ℂ → ℂ, G ∈ RungeDA Ω ∧
      ∀ z ∈ rungeExhaustion Ω j, ‖holoCOFun F z - G z‖ ≤ 1 / ((j : ℝ) + 1) := by
    intro j
    exact approxOn_rungeDA_of_analyticOnNhd hΩ hΩc hΩne hΩinf hf
      (isCompact_rungeExhaustion Ω j) (rungeExhaustion_subset Ω j) (1 / ((j : ℝ) + 1))
      (by positivity)
  choose G hGmem hGbound using hchoice
  set g : ℕ → HoloCO Ω := fun j => toHoloCO (hGmem j).1 with hgdef
  have hgmem : ∀ j, g j ∈ daCompactOpenLocus Ω := by
    intro j
    exact differentiallyAlgebraicOn_of_eqOn hΩ (holoCOFun_toHoloCO (hGmem j).1).symm
      (hGmem j).2
  have hloc : TendstoLocallyUniformlyOn (fun j z => G j z) (holoCOFun F) atTop Ω := by
    rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hΩ]
    intro K hKsub hK
    obtain ⟨j₀, hj₀⟩ := exists_rungeExhaustion_superset hΩ hK hKsub
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
    filter_upwards [eventually_ge_atTop (max j₀ N)] with j hj z hz
    have h1 : z ∈ rungeExhaustion Ω j :=
      rungeExhaustion_mono Ω (le_trans (le_max_left _ _) hj) (hj₀ hz)
    have h2 := hGbound j z h1
    have hjN : (N : ℝ) ≤ (j : ℝ) := by
      exact_mod_cast le_trans (le_max_right j₀ N) hj
    have hsmall : 1 / ((j : ℝ) + 1) < ε := by
      rw [div_lt_iff₀ (by positivity)]
      rw [div_lt_iff₀ hε] at hN
      nlinarith [hε]
    rw [Complex.dist_eq]
    linarith
  rw [tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe] at hloc
  have hC : Tendsto (fun j => ((g j : HoloCO Ω) : C(↥Ω, ℂ))) atTop
      (𝓝 ((F : HoloCO Ω) : C(↥Ω, ℂ))) := by
    rw [ContinuousMap.tendsto_iff_tendstoLocallyUniformly]
    refine (hloc.congr (fun j x => ?_)).congr_right (fun x => ?_)
    · rfl
    · simp [holoCOFun, Function.comp]
  exact mem_closure_of_tendsto (tendsto_subtype_rng.2 hC) (Eventually.of_forall hgmem)


/-! ## The compact-open interlacing law -/

/-- **DA/HT topological interlacing in the compact-open topology.**  On every domain the
differentially algebraic functions are dense and meagre, and the hypertranscendental functions are a
dense comeagre `Gδ`.  In particular every nonempty compact-open neighbourhood contains functions of
both phases. -/
theorem compactOpen_interlacing (hΩ : IsOpen Ω) (hΩc : IsPreconnected Ω) (hΩne : Ω.Nonempty) :
    Dense (daCompactOpenLocus Ω) ∧ IsMeagre (daCompactOpenLocus Ω) ∧
      Dense ((daCompactOpenLocus Ω)ᶜ) ∧ IsGδ ((daCompactOpenLocus Ω)ᶜ) :=
  ⟨dense_daCompactOpenLocus hΩ hΩc hΩne,
    isMeagre_daCompactOpenLocus hΩ hΩc hΩne,
    dense_htCompactOpenLocus hΩ hΩc hΩne,
    isGδ_htCompactOpenLocus hΩ hΩc hΩne⟩

/-- Every nonempty compact-open neighbourhood contains both a differentially algebraic and a
hypertranscendental function. -/
theorem exists_mem_both_of_isOpen (hΩ : IsOpen Ω) (hΩc : IsPreconnected Ω) (hΩne : Ω.Nonempty)
    {U : Set (HoloCO Ω)} (hU : IsOpen U) (hUne : U.Nonempty) :
    (U ∩ daCompactOpenLocus Ω).Nonempty ∧ (U ∩ (daCompactOpenLocus Ω)ᶜ).Nonempty :=
  ⟨(dense_daCompactOpenLocus hΩ hΩc hΩne).inter_open_nonempty U hU hUne,
    (dense_htCompactOpenLocus hΩ hΩc hΩne).inter_open_nonempty U hU hUne⟩

/-- **The compact-open phase-selector collapse.**  No continuous map into a Hausdorff space which
is constant on each differential phase can be nonconstant. -/
theorem compactOpen_phase_selector_collapse {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    (hΩ : IsOpen Ω) (hΩc : IsPreconnected Ω) (hΩne : Ω.Nonempty)
    {Φ : HoloCO Ω → Y} (hΦ : Continuous Φ) {p q : Y}
    (hDA : ∀ F ∈ daCompactOpenLocus Ω, Φ F = p)
    (hHT : ∀ F ∈ (daCompactOpenLocus Ω)ᶜ, Φ F = q) :
    p = q ∧ Φ = fun _ => p := by
  have hdense := dense_daCompactOpenLocus hΩ hΩc hΩne
  have hdenseHT := dense_htCompactOpenLocus hΩ hΩc hΩne
  have hpq : p = q :=
    const_eq_const_of_continuous_of_dense hdense hΦ hDA hHT hdenseHT.nonempty
  exact ⟨hpq, eq_const_of_continuous_of_dense_eqOn hdense hΦ hDA⟩

end

end GaloisForLFunctions.HTGeometry
