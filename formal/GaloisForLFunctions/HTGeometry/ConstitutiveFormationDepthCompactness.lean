import GaloisForLFunctions.HTGeometry.ConstitutiveFormationDepthProperness
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Semicontinuity.Basic

/-!
# Compact formation-depth graph sublevels

This module closes the topological clause of the source-depth properness law.  It realizes the
graph domain of the depth generator inside `ℓ¹(ℕ, ℂ)`, proves the generator graph closed, proves
lower semicontinuity of the formation gauge, and proves every gauge sublevel compact in the
ambient `ℓ¹` topology.
-/

open scoped BigOperators lp
open Complex

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Ambient source space for the formation-depth graph law. -/
abbrev FormationL1 := ℓ¹(ℕ, ℂ)

/-- The graph domain `D₁`: `ℓ¹` source histories whose depth formation is also summable. -/
abbrev FormationDepthDomain :=
  {x : FormationL1 // Summable (formationDepthSequence (x : ℕ → ℂ))}

/-- Formation gauge on the ambient representative of the graph domain. -/
def formationLpGauge (x : FormationL1) : ℝ :=
  formationGauge (x : ℕ → ℂ)

/-- Formation gauge on `D₁` with its topology induced from `ℓ¹`. -/
def formationDepthDomainGauge (x : FormationDepthDomain) : ℝ :=
  formationLpGauge x.1

/-- Exact ambient realization of a graph-gauge sublevel. -/
def formationLpGaugeSublevel (C : ℝ) : Set FormationL1 :=
  {x | Summable (formationDepthSequence (x : ℕ → ℂ)) ∧ formationLpGauge x ≤ C}

/-- Every `ℓ¹` source history is absolutely summable. -/
theorem formationL1_summable (x : FormationL1) : Summable (x : ℕ → ℂ) := by
  apply Summable.of_norm
  simpa using (lp.memℓp x).summable (by simp : 0 < (1 : ENNReal).toReal)

/-- The `ℓ¹` norm is the sum of coordinate norms. -/
theorem formationL1_norm_eq_tsum_norm (x : FormationL1) :
    ‖x‖ = ∑' n, ‖x n‖ := by
  rw [lp.norm_eq_tsum_rpow (by simp : 0 < (1 : ENNReal).toReal)]
  simp

/-! ## Closed graph -/

/-- Literal graph of the depth generator in `ℓ¹ × ℓ¹`. -/
def formationDepthGraph : Set (FormationL1 × FormationL1) :=
  {p | ∀ n, p.2 n = formationDepthSequence (p.1 : ℕ → ℂ) n}

/-- The depth generator is a closed operator on its natural `ℓ¹` graph domain. -/
theorem isClosed_formationDepthGraph : IsClosed formationDepthGraph := by
  rw [show formationDepthGraph =
      ⋂ n : ℕ, {p : FormationL1 × FormationL1 |
        p.2 n = formationDepthSequence (p.1 : ℕ → ℂ) n} by
    ext p
    simp [formationDepthGraph]]
  apply isClosed_iInter
  intro n
  apply isClosed_eq
  · exact (lp.evalCLM ℂ (fun _ : ℕ => ℂ) 1 n).continuous.comp continuous_snd
  · have hcoord : Continuous (fun p : FormationL1 × FormationL1 => p.1 n) :=
      (lp.evalCLM ℂ (fun _ : ℕ => ℂ) 1 n).continuous.comp continuous_fst
    change Continuous (fun p : FormationL1 × FormationL1 => (n : ℂ) * p.1 n)
    exact continuous_const.mul hcoord

/-! ## Lower semicontinuity through finite graph work -/

/-- Work seen through the first `N` formation depths. -/
def formationDepthPartialWork (N : ℕ) (x : FormationL1) : ℝ :=
  ∑ n ∈ Finset.range N, ‖formationDepthSequence (x : ℕ → ℂ) n‖

/-- Finite-aperture approximation to the formation gauge. -/
def formationFiniteGauge (N : ℕ) (x : FormationL1) : ℝ :=
  ‖formationMass (x : ℕ → ℂ)‖ + 2 * formationDepthPartialWork N x

theorem continuous_formationMass_l1 :
    Continuous (fun x : FormationL1 => formationMass (x : ℕ → ℂ)) := by
  change Continuous (fun x : FormationL1 => ∑' n, x n)
  exact (lp.tsumCLM ℂ ℕ ℂ).continuous

theorem continuous_formationDepthPartialWork (N : ℕ) :
    Continuous (formationDepthPartialWork N) := by
  unfold formationDepthPartialWork
  apply continuous_finsetSum
  intro n _
  have hcoord : Continuous (fun x : FormationL1 => x n) :=
    (lp.evalCLM ℂ (fun _ : ℕ => ℂ) 1 n).continuous
  change Continuous (fun x : FormationL1 => ‖(n : ℂ) * x n‖)
  exact (continuous_const.mul hcoord).norm

theorem continuous_formationFiniteGauge (N : ℕ) :
    Continuous (formationFiniteGauge N) := by
  unfold formationFiniteGauge
  exact continuous_formationMass_l1.norm.add
    (continuous_const.mul (continuous_formationDepthPartialWork N))

/-- Membership in the graph-gauge sublevel is exactly boundedness of every finite gauge. -/
theorem mem_formationLpGaugeSublevel_iff_forall_finiteGauge
    {C : ℝ} {x : FormationL1} :
    x ∈ formationLpGaugeSublevel C ↔ ∀ N, formationFiniteGauge N x ≤ C := by
  constructor
  · rintro ⟨hDx, hgauge⟩ N
    have hpartial :
        formationDepthPartialWork N x ≤
          formationDepthWork (x : ℕ → ℂ) := by
      exact hDx.norm.sum_le_tsum (Finset.range N) (fun _ _ => norm_nonneg _)
    change ‖formationMass (x : ℕ → ℂ)‖ +
      2 * formationDepthPartialWork N x ≤ C
    change ‖formationMass (x : ℕ → ℂ)‖ +
      2 * formationDepthWork (x : ℕ → ℂ) ≤ C at hgauge
    linarith
  · intro hfinite
    let B : ℝ := (C - ‖formationMass (x : ℕ → ℂ)‖) / 2
    have hpartial : ∀ N, formationDepthPartialWork N x ≤ B := by
      intro N
      have hN := hfinite N
      dsimp [formationFiniteGauge, B] at hN ⊢
      linarith
    have hnormSummable :
        Summable (fun n => ‖formationDepthSequence (x : ℕ → ℂ) n‖) := by
      apply summable_of_sum_range_le (fun n => norm_nonneg _)
      simpa [formationDepthPartialWork] using hpartial
    have hDx : Summable (formationDepthSequence (x : ℕ → ℂ)) :=
      Summable.of_norm hnormSummable
    have hwork : formationDepthWork (x : ℕ → ℂ) ≤ B := by
      unfold formationDepthWork
      apply Real.tsum_le_of_sum_range_le (fun n => norm_nonneg _)
      simpa [formationDepthPartialWork] using hpartial
    refine ⟨hDx, ?_⟩
    unfold formationLpGauge formationGauge
    dsimp [B] at hwork
    linarith

/-- Exact intersection representation by continuous finite gauges. -/
theorem formationLpGaugeSublevel_eq_iInter (C : ℝ) :
    formationLpGaugeSublevel C =
      ⋂ N : ℕ, {x : FormationL1 | formationFiniteGauge N x ≤ C} := by
  ext x
  simp only [Set.mem_iInter, Set.mem_setOf_eq]
  exact mem_formationLpGaugeSublevel_iff_forall_finiteGauge

/-- The gauge is lower semicontinuous in its exact extended-domain sense. -/
theorem isClosed_formationLpGaugeSublevel (C : ℝ) :
    IsClosed (formationLpGaugeSublevel C) := by
  rw [formationLpGaugeSublevel_eq_iInter]
  exact isClosed_iInter fun N =>
    isClosed_le (continuous_formationFiniteGauge N) continuous_const

/-- The domain gauge is lower semicontinuous for the topology induced from ambient `ℓ¹`. -/
theorem lowerSemicontinuous_formationDepthDomainGauge :
    LowerSemicontinuous formationDepthDomainGauge := by
  rw [lowerSemicontinuous_iff_isClosed_preimage]
  intro C
  rw [isClosed_induced_iff]
  refine ⟨formationLpGaugeSublevel C, isClosed_formationLpGaugeSublevel C, ?_⟩
  ext x
  change (Summable (formationDepthSequence (x.1 : ℕ → ℂ)) ∧
      formationLpGauge x.1 ≤ C) ↔ formationDepthDomainGauge x ≤ C
  exact ⟨fun h => h.2, fun h => ⟨x.property, h⟩⟩

/-! ## Finite heads and uniform tail approximation -/

/-- Coordinate truncation at formation depth `N`. -/
def formationTruncation (N : ℕ) (x : FormationL1) : FormationL1 :=
  ∑ n ∈ Finset.range N, lp.single 1 n (x n)

/-- Synthesis of an `N`-coordinate head into ambient `ℓ¹`. -/
def formationHead (N : ℕ) (v : Fin N → ℂ) : FormationL1 :=
  ∑ i : Fin N, lp.single 1 (i : ℕ) (v i)

theorem continuous_formationHead (N : ℕ) : Continuous (formationHead N) := by
  unfold formationHead
  apply continuous_finsetSum
  intro i _
  exact (lp.singleContinuousLinearMap ℂ (fun _ : ℕ => ℂ) 1 (i : ℕ)).continuous.comp
    (continuous_apply i)

theorem formationHead_coordinates_eq_truncation (N : ℕ) (x : FormationL1) :
    formationHead N (fun i => x i) = formationTruncation N x := by
  unfold formationHead formationTruncation
  exact Fin.sum_univ_eq_sum_range (fun n => lp.single 1 n (x n)) N

/-- Truncation error is exactly the cofinal `ℓ¹` tail. -/
theorem norm_sub_formationTruncation_eq_tail (N : ℕ) (x : FormationL1) :
    ‖x - formationTruncation N x‖ = formationTail (x : ℕ → ℂ) N := by
  have hcompl := lp.norm_compl_sum_single
    (by simp : 0 < (1 : ENNReal).toReal) x (Finset.range N)
  simp only [ENNReal.toReal_one, Real.rpow_one] at hcompl
  rw [formationTruncation, hcompl, formationL1_norm_eq_tsum_norm]
  have hsplit := (formationL1_summable x).norm.sum_add_tsum_nat_add N
  unfold formationTail
  linarith

/-- A gauge sublevel is uniformly bounded in ambient `ℓ¹`. -/
theorem norm_le_of_mem_formationLpGaugeSublevel
    {C : ℝ} {x : FormationL1} (hx : x ∈ formationLpGaugeSublevel C) :
    ‖x‖ ≤ C := by
  have hcoercive := tsum_norm_le_formationGauge (x : ℕ → ℂ)
    (formationL1_summable x) hx.1
  rw [← formationL1_norm_eq_tsum_norm] at hcoercive
  exact hcoercive.trans hx.2

/-- A gauge sublevel has the uniform sharp cofinal tail bound inherited from depth work. -/
theorem formationTail_le_of_mem_formationLpGaugeSublevel
    {C : ℝ} {x : FormationL1} (hx : x ∈ formationLpGaugeSublevel C)
    {N : ℕ} (hN : 0 < N) :
    formationTail (x : ℕ → ℂ) N ≤ C / (2 * N) := by
  have htail := formationTail_le_depthWork_div (x : ℕ → ℂ)
    (formationL1_summable x) hx.1 hN
  have hwork : formationDepthWork (x : ℕ → ℂ) ≤ C / 2 := by
    dsimp [formationLpGaugeSublevel, formationLpGauge, formationGauge] at hx
    have := norm_nonneg (formationMass (x : ℕ → ℂ))
    linarith
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  calc
    formationTail (x : ℕ → ℂ) N
        ≤ formationDepthWork (x : ℕ → ℂ) / N := htail
    _ ≤ (C / 2) / N := div_le_div_of_nonneg_right hwork hNreal.le
    _ = C / (2 * N) := by field_simp

/-! ## Compact graph-gauge sublevels -/

/-- Every graph-gauge sublevel is totally bounded in ambient `ℓ¹`. -/
theorem totallyBounded_formationLpGaugeSublevel (C : ℝ) :
    TotallyBounded (formationLpGaugeSublevel C) := by
  by_cases hnonempty : (formationLpGaugeSublevel C).Nonempty
  · obtain ⟨x₀, hx₀⟩ := hnonempty
    have hC : 0 ≤ C := (norm_nonneg x₀).trans (norm_le_of_mem_formationLpGaugeSublevel hx₀)
    rw [Metric.totallyBounded_iff]
    intro ε hε
    obtain ⟨N, hNlarge⟩ := exists_nat_gt (C / ε)
    have hNreal : (0 : ℝ) < N := by
      have hnonneg : 0 ≤ C / ε := div_nonneg hC hε.le
      linarith
    have hN : 0 < N := by exact_mod_cast hNreal
    let K : Set FormationL1 :=
      formationHead N '' Metric.closedBall (0 : Fin N → ℂ) C
    have hKcompact : IsCompact K :=
      (isCompact_closedBall (0 : Fin N → ℂ) C).image (continuous_formationHead N)
    obtain ⟨centers, hcentersFinite, hcover⟩ :=
      Metric.totallyBounded_iff.mp hKcompact.totallyBounded (ε / 2) (by positivity)
    refine ⟨centers, hcentersFinite, ?_⟩
    intro x hx
    have hxnorm : ‖x‖ ≤ C := norm_le_of_mem_formationLpGaugeSublevel hx
    have hvnorm : ‖fun i : Fin N => x i‖ ≤ ‖x‖ := by
      rw [pi_norm_le_iff_of_nonneg (norm_nonneg x)]
      intro i
      exact lp.norm_apply_le_norm (by simp : (1 : ENNReal) ≠ 0) x i
    have hvball : (fun i : Fin N => x i) ∈ Metric.closedBall (0 : Fin N → ℂ) C := by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact hvnorm.trans hxnorm
    have htruncK : formationTruncation N x ∈ K := by
      refine ⟨(fun i : Fin N => x i), hvball, ?_⟩
      exact formationHead_coordinates_eq_truncation N x
    have htruncCovered := hcover htruncK
    rcases Set.mem_iUnion.mp htruncCovered with ⟨c, hc⟩
    rcases Set.mem_iUnion.mp hc with ⟨hcCenter, htruncBall⟩
    refine Set.mem_iUnion.mpr ⟨c, Set.mem_iUnion.mpr ⟨hcCenter, ?_⟩⟩
    rw [Metric.mem_ball] at htruncBall ⊢
    have htailBound := formationTail_le_of_mem_formationLpGaugeSublevel hx hN
    have hCN : C < ε * (N : ℝ) := by
      have := (div_lt_iff₀ hε).mp hNlarge
      simpa [mul_comm] using this
    have htailSmall : formationTail (x : ℕ → ℂ) N < ε / 2 := by
      have hdenom : (0 : ℝ) < 2 * N := mul_pos (by positivity) hNreal
      have hfrac : C / (2 * (N : ℝ)) < ε / 2 := by
        apply (div_lt_iff₀ hdenom).2
        nlinarith
      exact htailBound.trans_lt hfrac
    have happrox : dist x (formationTruncation N x) < ε / 2 := by
      rw [dist_eq_norm, norm_sub_formationTruncation_eq_tail]
      exact htailSmall
    exact (dist_triangle x (formationTruncation N x) c).trans_lt (by linarith)
  · rw [Set.not_nonempty_iff_eq_empty.mp hnonempty]
    exact totallyBounded_empty

/-- Every exact formation-gauge sublevel is compact in ambient `ℓ¹`. -/
theorem isCompact_formationLpGaugeSublevel (C : ℝ) :
    IsCompact (formationLpGaugeSublevel C) :=
  (totallyBounded_formationLpGaugeSublevel C).isCompact_of_isClosed
    (isClosed_formationLpGaugeSublevel C)

/-- The same compact-sublevel law on the graph-domain subtype. -/
theorem isCompact_formationDepthDomainGaugeSublevel (C : ℝ) :
    IsCompact {x : FormationDepthDomain | formationDepthDomainGauge x ≤ C} := by
  rw [Subtype.isCompact_iff]
  convert isCompact_formationLpGaugeSublevel C using 1
  ext x
  simp [formationLpGaugeSublevel, formationDepthDomainGauge, and_comm]

/-- Natural-number gauge sublevels exhaust the entire graph domain. -/
theorem iUnion_formationDepthDomainGaugeSublevel :
    (⋃ N : ℕ, {x : FormationDepthDomain | formationDepthDomainGauge x ≤ N}) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨N, hN⟩ := exists_nat_gt (formationDepthDomainGauge x)
  exact Set.mem_iUnion.mpr ⟨N, hN.le⟩

/-- Bundled closed-graph, lower-semicontinuity, compact-sublevel, and exhaustion theorem. -/
theorem formationDepthCompactProperness_capstone :
    IsClosed formationDepthGraph ∧
      LowerSemicontinuous formationDepthDomainGauge ∧
      (∀ C : ℝ, IsCompact (formationLpGaugeSublevel C)) ∧
      (∀ C : ℝ,
        IsCompact {x : FormationDepthDomain | formationDepthDomainGauge x ≤ C}) ∧
      (⋃ N : ℕ, {x : FormationDepthDomain | formationDepthDomainGauge x ≤ N}) = Set.univ := by
  exact ⟨isClosed_formationDepthGraph, lowerSemicontinuous_formationDepthDomainGauge,
    isCompact_formationLpGaugeSublevel, isCompact_formationDepthDomainGaugeSublevel,
    iUnion_formationDepthDomainGaugeSublevel⟩

end

end GaloisForLFunctions.HTGeometry
