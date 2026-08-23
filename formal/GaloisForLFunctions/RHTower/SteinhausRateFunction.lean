import GaloisForLFunctions.RHTower.SteinhausBesselIdentity

/-!
# The rate function of the regular-variation Steinhaus model

`I_α(q) = sup_{λ ≥ 0}(λq − Λ_α(λ))`.  The linear lower bound `Λ_α(λ) ≥ cλ + log μ_c`, valid for
every `c < 1`, makes the supremum finite for every `q < 1`; the supremum is nonnegative, vanishes
at `q = 0`, and is monotone.
-/

open MeasureTheory Set

namespace HTGeometry

noncomputable section

/-- The set whose supremum is the rate function. -/
def rvLegendreSet (α q : ℝ) : Set ℝ :=
  {y : ℝ | ∃ lam : ℝ, 0 ≤ lam ∧ y = lam * q - rvCumulant α lam}

/-- The rate function. -/
def rvRate (α q : ℝ) : ℝ := sSup (rvLegendreSet α q)

theorem zero_mem_rvLegendreSet (α q : ℝ) : (0 : ℝ) ∈ rvLegendreSet α q :=
  ⟨0, le_rfl, by rw [rvCumulant_zero]; ring⟩

theorem rvLegendreSet_nonempty (α q : ℝ) : (rvLegendreSet α q).Nonempty :=
  ⟨0, zero_mem_rvLegendreSet α q⟩

/-- **The supremum is finite below `q = 1`.** -/
theorem bddAbove_rvLegendreSet {α : ℝ} (hα : α < 1) {q : ℝ} (hq : q < 1) :
    BddAbove (rvLegendreSet α q) := by
  obtain ⟨c, hqc, hc1⟩ := exists_between hq
  refine ⟨-Real.log (arcMass c), ?_⟩
  rintro y ⟨lam, hlam, rfl⟩
  have hlow := le_rvCumulant hα hc1 hlam
  nlinarith [hlow, hlam, hqc]

theorem rvRate_nonneg {α : ℝ} (hα : α < 1) {q : ℝ} (hq : q < 1) : 0 ≤ rvRate α q :=
  le_csSup (bddAbove_rvLegendreSet hα hq) (zero_mem_rvLegendreSet α q)

/-- **Every tilt gives a lower bound for the rate.** -/
theorem le_rvRate {α : ℝ} (hα : α < 1) {q : ℝ} (hq : q < 1) {lam : ℝ} (hlam : 0 ≤ lam) :
    lam * q - rvCumulant α lam ≤ rvRate α q :=
  le_csSup (bddAbove_rvLegendreSet hα hq) ⟨lam, hlam, rfl⟩

/-- **The rate vanishes at the origin.** -/
theorem rvRate_zero {α : ℝ} (hα : α < 1) : rvRate α 0 = 0 := by
  refine le_antisymm ?_ (rvRate_nonneg hα (by norm_num))
  refine csSup_le (rvLegendreSet_nonempty α 0) ?_
  rintro y ⟨lam, hlam, rfl⟩
  have := rvCumulant_nonneg α lam
  nlinarith

/-- **The rate is monotone.** -/
theorem rvRate_mono {α : ℝ} (hα : α < 1) {q₁ q₂ : ℝ} (h : q₁ ≤ q₂) (hq₂ : q₂ < 1) :
    rvRate α q₁ ≤ rvRate α q₂ := by
  refine csSup_le (rvLegendreSet_nonempty α q₁) ?_
  rintro y ⟨lam, hlam, rfl⟩
  refine le_trans ?_ (le_rvRate hα hq₂ hlam)
  nlinarith [hlam, h]

end

end HTGeometry
