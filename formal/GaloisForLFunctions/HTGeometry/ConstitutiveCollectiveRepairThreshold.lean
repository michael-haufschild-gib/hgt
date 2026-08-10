import Mathlib

/-!
# Collective repair spectral threshold

Two conservative repairs are individually nonviable for every positive coupling, yet jointly cross
a sharp threshold.  Below the swap spectral radius, a strict progress certificate excludes every
nonnegative closed history.  At threshold a repair-only circulation appears; above threshold it
has full support.  The same threshold is singular for symmetric inverse response, while the visible
repair interaction remains period two.

Paper source:
`docs/drafts/pipeline/2-fully-proven/universal-law-field/autopoietic-law-mechanics/
collective-repair-spectral-threshold-and-open-history-law.md`.
-/

namespace GaloisForLFunctions.HTGeometry

/-- Two semantic resource directions. -/
abbrev CollectiveRepairResource := ℝ × ℝ

/-- Old-rule multiplicities followed by two repair multiplicities. -/
abbrev CollectiveRepairFlux := CollectiveRepairResource × CollectiveRepairResource

/-- Semantic boundary for old rules `e₁,e₂` and repairs `(-α,1),(1,-α)`. -/
def collectiveRepairBoundary (α : ℝ) :
    CollectiveRepairFlux →ₗ[ℝ] CollectiveRepairResource where
  toFun h :=
    (h.1.1 - α * h.2.1 + h.2.2,
      h.1.2 + h.2.1 - α * h.2.2)
  map_add' x y := by
    ext <;> simp <;> ring
  map_smul' a x := by
    ext <;> simp <;> ring

/-- Semantic reach is unchanged because the two old basis rules remain available. -/
theorem collectiveRepairBoundary_surjective (α : ℝ) :
    Function.Surjective (collectiveRepairBoundary α) := by
  intro y
  exact ⟨(y, (0, 0)), by ext <;> simp [collectiveRepairBoundary]⟩

/-- Exact graph presentation of every zero-boundary repair history. -/
theorem collectiveRepairBoundary_eq_zero_iff (α : ℝ) (h : CollectiveRepairFlux) :
    collectiveRepairBoundary α h = 0 ↔
      h.1.1 = α * h.2.1 - h.2.2 ∧
        h.1.2 = α * h.2.2 - h.2.1 := by
  constructor
  · intro hh
    have h₁ := congrArg Prod.fst hh
    have h₂ := congrArg Prod.snd hh
    simp [collectiveRepairBoundary] at h₁ h₂
    constructor <;> linarith
  · rintro ⟨h₁, h₂⟩
    ext <;> simp [collectiveRepairBoundary, h₁, h₂]

/-- Coordinatewise nonnegative execution. -/
def CollectiveRepairFeasible (h : CollectiveRepairFlux) : Prop :=
  0 ≤ h.1.1 ∧ 0 ≤ h.1.2 ∧ 0 ≤ h.2.1 ∧ 0 ≤ h.2.2

/-- The first repair cannot form a feasible circulation without the second repair. -/
theorem collectiveRepair_left_alone_nonviable (α : ℝ) (h : CollectiveRepairFlux)
    (hfeas : CollectiveRepairFeasible h)
    (hker : collectiveRepairBoundary α h = 0) (hright : h.2.2 = 0) :
    h = 0 := by
  have hk := (collectiveRepairBoundary_eq_zero_iff α h).mp hker
  rcases h with ⟨⟨x₁, x₂⟩, ⟨t₁, t₂⟩⟩
  simp only at hright hk ⊢
  simp only [CollectiveRepairFeasible] at hfeas
  have ht₁ : t₁ = 0 := by
    rw [hright] at hk
    nlinarith [hk.2, hfeas.2.1, hfeas.2.2.1]
  have hx₂ : x₂ = 0 := by rw [hk.2, hright, ht₁]; ring
  have hx₁ : x₁ = 0 := by rw [hk.1, hright, ht₁]; ring
  simp [hx₁, hx₂, ht₁, hright]

/-- The second repair cannot form a feasible circulation without the first repair. -/
theorem collectiveRepair_right_alone_nonviable (α : ℝ) (h : CollectiveRepairFlux)
    (hfeas : CollectiveRepairFeasible h)
    (hker : collectiveRepairBoundary α h = 0) (hleft : h.2.1 = 0) :
    h = 0 := by
  have hk := (collectiveRepairBoundary_eq_zero_iff α h).mp hker
  rcases h with ⟨⟨x₁, x₂⟩, ⟨t₁, t₂⟩⟩
  simp only at hleft hk ⊢
  simp only [CollectiveRepairFeasible] at hfeas
  have ht₂ : t₂ = 0 := by
    rw [hleft] at hk
    nlinarith [hk.1, hfeas.1, hfeas.2.2.2]
  have hx₁ : x₁ = 0 := by rw [hk.1, hleft, ht₂]; ring
  have hx₂ : x₂ = 0 := by rw [hk.2, hleft, ht₂]; ring
  simp [hx₁, hx₂, hleft, ht₂]

/-! ## Subcritical progress -/

/-- Below threshold, no nonzero nonnegative closed history exists. -/
theorem collectiveRepair_subcritical_no_feasible_cycle {α : ℝ}
    (_hα0 : 0 < α) (hα1 : α < 1) (h : CollectiveRepairFlux)
    (hfeas : CollectiveRepairFeasible h)
    (hker : collectiveRepairBoundary α h = 0) :
    h = 0 := by
  have hk := (collectiveRepairBoundary_eq_zero_iff α h).mp hker
  rcases h with ⟨⟨x₁, x₂⟩, ⟨t₁, t₂⟩⟩
  simp only at hk ⊢
  simp only [CollectiveRepairFeasible] at hfeas
  ext <;> simp <;> nlinarith

/-- First old rule vector. -/
def collectiveOldRuleOne : CollectiveRepairResource := (1, 0)

/-- Second old rule vector. -/
def collectiveOldRuleTwo : CollectiveRepairResource := (0, 1)

/-- First interacting repair. -/
def collectiveRepairRuleOne (α : ℝ) : CollectiveRepairResource := (-α, 1)

/-- Second interacting repair. -/
def collectiveRepairRuleTwo (α : ℝ) : CollectiveRepairResource := (1, -α)

/-- Coordinate-sum progress certificate. -/
def collectiveProgressPotential : CollectiveRepairResource →ₗ[ℝ] ℝ where
  toFun z := z.1 + z.2
  map_add' _ _ := by simp; ring
  map_smul' _ _ := by simp; ring

/-- Below threshold, one source-fixed functional is strictly positive on every admitted rule. -/
theorem collectiveRepair_subcritical_strict_progress {α : ℝ} (hα : α < 1) :
    0 < collectiveProgressPotential collectiveOldRuleOne ∧
      0 < collectiveProgressPotential collectiveOldRuleTwo ∧
      0 < collectiveProgressPotential (collectiveRepairRuleOne α) ∧
      0 < collectiveProgressPotential (collectiveRepairRuleTwo α) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [collectiveProgressPotential, collectiveOldRuleOne]
  · simp [collectiveProgressPotential, collectiveOldRuleTwo]
  · simp [collectiveProgressPotential, collectiveRepairRuleOne]
    linarith
  · simp [collectiveProgressPotential, collectiveRepairRuleTwo]
    linarith

/-! ## Critical and supercritical carrier birth -/

/-- At threshold the whole feasible kernel is one repair-only ray. -/
theorem collectiveRepair_critical_feasible_kernel_ray (h : CollectiveRepairFlux) :
    CollectiveRepairFeasible h ∧ collectiveRepairBoundary 1 h = 0 ↔
      ∃ t : ℝ, 0 ≤ t ∧ h = ((0, 0), (t, t)) := by
  constructor
  · rintro ⟨hfeas, hker⟩
    have hk := (collectiveRepairBoundary_eq_zero_iff 1 h).mp hker
    rcases h with ⟨⟨x₁, x₂⟩, ⟨t₁, t₂⟩⟩
    simp only at hk ⊢
    simp only [CollectiveRepairFeasible] at hfeas
    refine ⟨t₁, hfeas.2.2.1, ?_⟩
    ext <;> simp <;> nlinarith
  · rintro ⟨t, ht, rfl⟩
    constructor
    · exact ⟨le_rfl, le_rfl, ht, ht⟩
    · ext <;> simp [collectiveRepairBoundary]

/-- Canonical symmetric circulation born at and above threshold. -/
def collectiveRepairCarrier (α : ℝ) : CollectiveRepairFlux :=
  ((α - 1, α - 1), (1, 1))

theorem collectiveRepairCarrier_boundary_zero (α : ℝ) :
    collectiveRepairBoundary α (collectiveRepairCarrier α) = 0 := by
  ext <;> simp [collectiveRepairBoundary, collectiveRepairCarrier]

theorem collectiveRepairCarrier_feasible {α : ℝ} (hα : 1 ≤ α) :
    CollectiveRepairFeasible (collectiveRepairCarrier α) := by
  simp only [CollectiveRepairFeasible, collectiveRepairCarrier]
  exact ⟨sub_nonneg.mpr hα, sub_nonneg.mpr hα, zero_le_one, zero_le_one⟩

/-- Above threshold the canonical collective carrier uses every old and repair rule strictly. -/
theorem collectiveRepairCarrier_full_support {α : ℝ} (hα : 1 < α) :
    0 < (collectiveRepairCarrier α).1.1 ∧
      0 < (collectiveRepairCarrier α).1.2 ∧
      0 < (collectiveRepairCarrier α).2.1 ∧
      0 < (collectiveRepairCarrier α).2.2 := by
  simp only [collectiveRepairCarrier]
  exact ⟨sub_pos.mpr hα, sub_pos.mpr hα, zero_lt_one, zero_lt_one⟩

/-- At and above threshold, the collective circulation excludes every strict scalar progress
certificate on the same directed support. -/
theorem collectiveRepair_no_strict_progress {α : ℝ} (hα : 1 ≤ α) :
    ¬ ∃ ell : CollectiveRepairResource →ₗ[ℝ] ℝ,
      0 < ell collectiveOldRuleOne ∧
        0 < ell collectiveOldRuleTwo ∧
        0 < ell (collectiveRepairRuleOne α) ∧
        0 < ell (collectiveRepairRuleTwo α) := by
  rintro ⟨ell, h₁, h₂, hr₁, hr₂⟩
  have hvec :
      (α - 1) • collectiveOldRuleOne +
          (α - 1) • collectiveOldRuleTwo +
          collectiveRepairRuleOne α + collectiveRepairRuleTwo α = 0 := by
    ext <;> simp [collectiveOldRuleOne, collectiveOldRuleTwo,
      collectiveRepairRuleOne, collectiveRepairRuleTwo]
    ring
  have himg := congrArg ell hvec
  simp only [map_add, map_smul, map_zero, smul_eq_mul] at himg
  nlinarith

/-! ## Singular symmetric response -/

/-- Repair-interaction matrix `αI-J`. -/
def collectiveRepairInteraction (α : ℝ) :
    CollectiveRepairResource →ₗ[ℝ] CollectiveRepairResource where
  toFun t := (α * t.1 - t.2, α * t.2 - t.1)
  map_add' x y := by ext <;> simp <;> ring
  map_smul' a x := by ext <;> simp <;> ring

/-- The symmetric mode has exact eigenvalue `α-1`. -/
theorem collectiveRepairInteraction_symmetric (α : ℝ) :
    collectiveRepairInteraction α (1, 1) = (α - 1) • (1, 1) := by
  ext <;> simp [collectiveRepairInteraction]

/-- Exact inverse amplification on the symmetric mode. -/
theorem collectiveRepair_symmetric_amplification {ε : ℝ} (hε : 0 < ε) :
    collectiveRepairInteraction (1 + ε) (1 / ε, 1 / ε) = (1, 1) ∧
      (1 / ε + 1 / ε) = 2 / ε := by
  constructor
  · ext <;> simp [collectiveRepairInteraction]
    all_goals
      field_simp [hε.ne']
      ring
  · ring

/-- The amplified symmetric preimage is unique inside the symmetric line. -/
theorem collectiveRepair_symmetric_amplification_unique {ε u : ℝ} (hε : 0 < ε)
    (hu : collectiveRepairInteraction (1 + ε) (u, u) = (1, 1)) :
    u = 1 / ε := by
  have hfirst := congrArg Prod.fst hu
  simp [collectiveRepairInteraction] at hfirst
  have hmul : ε * u = 1 := by
    nlinarith
  apply mul_left_cancel₀ hε.ne'
  calc
    ε * u = 1 := hmul
    _ = ε * (1 / ε) := by field_simp [hε.ne']

/-! ## Recurrent interaction and open history -/

/-- Visible repair interaction: swap the two repair channels. -/
def collectiveRepairSwap : CollectiveRepairResource →ₗ[ℝ] CollectiveRepairResource where
  toFun t := (t.2, t.1)
  map_add' _ _ := by ext <;> simp
  map_smul' _ _ := by ext <;> simp

theorem collectiveRepairSwap_period_two (t : CollectiveRepairResource) :
    collectiveRepairSwap (collectiveRepairSwap t) = t := by
  rfl

theorem collectiveRepairSwap_not_period_one :
    collectiveRepairSwap (1, 0) ≠ (1, 0) := by
  intro h
  have hfirst := congrArg Prod.fst h
  simp [collectiveRepairSwap] at hfirst

/-- Repetition of the collective carrier. -/
def collectiveRepairHistory (α : ℝ) (n : ℕ) : CollectiveRepairFlux :=
  (n : ℝ) • collectiveRepairCarrier α

/-- Positive unit execution size. -/
def collectiveRepairExecutionSize (h : CollectiveRepairFlux) : ℝ :=
  h.1.1 + h.1.2 + h.2.1 + h.2.2

theorem collectiveRepairHistory_boundary_zero (α : ℝ) (n : ℕ) :
    collectiveRepairBoundary α (collectiveRepairHistory α n) = 0 := by
  rw [collectiveRepairHistory, map_smul, collectiveRepairCarrier_boundary_zero]
  simp

theorem collectiveRepairHistory_size (α : ℝ) (n : ℕ) :
    collectiveRepairExecutionSize (collectiveRepairHistory α n) = 2 * α * n := by
  simp [collectiveRepairExecutionSize, collectiveRepairHistory, collectiveRepairCarrier]
  ring

/-- At and above threshold, semantic endpoint stays fixed while execution history is unbounded. -/
theorem collectiveRepairHistory_unbounded {α : ℝ} (hα : 1 ≤ α) (N : ℕ) :
    (N : ℝ) < collectiveRepairExecutionSize (collectiveRepairHistory α (N + 1)) := by
  rw [collectiveRepairHistory_size]
  push_cast
  have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  nlinarith

/-- Positive execution cost cannot descend to a potential of semantic endpoints. -/
theorem collectiveRepairUnitCost_not_endpoint_integrable {α : ℝ} (hα : 1 ≤ α) :
    ∀ Phi : CollectiveRepairResource → ℝ,
      collectiveRepairExecutionSize (collectiveRepairHistory α 1) ≠
        Phi (collectiveRepairBoundary α (collectiveRepairHistory α 1)) - Phi 0 := by
  intro Phi heq
  rw [collectiveRepairHistory_boundary_zero] at heq
  simp only [sub_self] at heq
  rw [collectiveRepairHistory_size] at heq
  simp only [Nat.cast_one, mul_one] at heq
  nlinarith

/-- Closed unconditional package: individual repair nonviability, collective spectral transition,
coercivity loss, recurrent interaction, and open positive-cost history coexist in one law cell. -/
theorem collectiveRepairThresholdMechanism_unconditional :
    (∀ α : ℝ, Function.Surjective (collectiveRepairBoundary α)) ∧
    (∀ (α : ℝ) (h : CollectiveRepairFlux),
      CollectiveRepairFeasible h → collectiveRepairBoundary α h = 0 → h.2.2 = 0 → h = 0) ∧
    (∀ (α : ℝ) (h : CollectiveRepairFlux),
      CollectiveRepairFeasible h → collectiveRepairBoundary α h = 0 → h.2.1 = 0 → h = 0) ∧
    (∀ (α : ℝ), 0 < α → α < 1 → ∀ h : CollectiveRepairFlux,
      CollectiveRepairFeasible h → collectiveRepairBoundary α h = 0 → h = 0) ∧
    (∀ α : ℝ, α < 1 →
      0 < collectiveProgressPotential collectiveOldRuleOne ∧
        0 < collectiveProgressPotential collectiveOldRuleTwo ∧
        0 < collectiveProgressPotential (collectiveRepairRuleOne α) ∧
        0 < collectiveProgressPotential (collectiveRepairRuleTwo α)) ∧
    (∀ h : CollectiveRepairFlux,
      CollectiveRepairFeasible h ∧ collectiveRepairBoundary 1 h = 0 ↔
        ∃ t : ℝ, 0 ≤ t ∧ h = ((0, 0), (t, t))) ∧
    (∀ α : ℝ, 1 < α →
      collectiveRepairBoundary α (collectiveRepairCarrier α) = 0 ∧
        0 < (collectiveRepairCarrier α).1.1 ∧
        0 < (collectiveRepairCarrier α).1.2 ∧
        0 < (collectiveRepairCarrier α).2.1 ∧
        0 < (collectiveRepairCarrier α).2.2) ∧
    (∀ α : ℝ, 1 ≤ α →
      ¬ ∃ ell : CollectiveRepairResource →ₗ[ℝ] ℝ,
        0 < ell collectiveOldRuleOne ∧
          0 < ell collectiveOldRuleTwo ∧
          0 < ell (collectiveRepairRuleOne α) ∧
          0 < ell (collectiveRepairRuleTwo α)) ∧
    (∀ t : CollectiveRepairResource,
      collectiveRepairSwap (collectiveRepairSwap t) = t) ∧
    (∀ (α : ℝ), 1 ≤ α → ∀ N : ℕ,
      (N : ℝ) < collectiveRepairExecutionSize (collectiveRepairHistory α (N + 1))) := by
  exact ⟨collectiveRepairBoundary_surjective,
    collectiveRepair_left_alone_nonviable,
    collectiveRepair_right_alone_nonviable,
    (fun α hα0 hα1 h hfeas hker ↦
      collectiveRepair_subcritical_no_feasible_cycle hα0 hα1 h hfeas hker),
    (fun _α hα ↦ collectiveRepair_subcritical_strict_progress hα),
    collectiveRepair_critical_feasible_kernel_ray,
    fun α hα ↦ ⟨collectiveRepairCarrier_boundary_zero α,
      collectiveRepairCarrier_full_support hα⟩,
    (fun _α hα ↦ collectiveRepair_no_strict_progress hα),
    collectiveRepairSwap_period_two,
    (fun α hα N ↦ collectiveRepairHistory_unbounded hα N)⟩

end GaloisForLFunctions.HTGeometry
