/-
The eligibility criterion for a covering architecture, and the cost curve of the `A`-process.

A pair contributes to a covering architecture whose restricted source begins at length `T^(x₁)`
exactly when its demand there meets the target:

    **μ(κ, λ) - θ  ≤  d(κ, λ) · (1/2 - x₁).**

This is the operational form of the whole displacement framework: it filters candidate pairs by a
single inequality, and the quantity on the right is the *budget* the handoff length provides.  At the
published handoff `x₁ = 17/42` the budget is `2d/21`.

Applied to the `A`-image of a pair on the line of symmetry, `P = (κ, κ + 1/2)`, the displacement cost
against a fixed target `θ` has a closed form:

    **ρ_A(κ, θ) = (4κ + 1)/2 - 4θ(κ + 1),**

linear in `κ` with slope `2 - 4θ > 0`.  So the cost falls as the record improves, and against the
current record it takes the values

    Weyl `1/6` → **1/9**,  Bombieri–Iwaniec `9/56` → **121/1176**,
    Huxley `32/205` → **277/2870**,  Bourgain `13/84` → **167/1764**,

strictly decreasing.  The cost reaches zero — the threshold reaching the critical length itself — at
`κ = (8θ - 1)/(4 - 8θ)`, which for `θ = 13/84` is `5/58`, some forty-four percent below the record.
-/
import GaloisForLFunctions.HTGeometry.NewPairsDisplacementTest

namespace HTGeometry

/-! ### The eligibility criterion -/

/-- The excess budget a handoff at length `x₁` provides to a pair of displacement `d`. -/
def eligibilityBudget (d x₁ : ℚ) : ℚ := d * (1 / 2 - x₁)

/-- **A pair meets a target at the handoff length exactly when its excess fits the budget.** -/
theorem eligible_iff_excess_within_budget (κ lam θ x₁ : ℚ) :
    covDemandOfPair x₁ κ lam ≤ θ ↔
      epMu κ lam - θ ≤ eligibilityBudget (epDisplacement κ lam) x₁ := by
  rw [covDemand_factorisation]
  unfold eligibilityBudget
  constructor <;> intro h <;> nlinarith

/-- At the published handoff the budget is `2d/21`. -/
theorem budget_at_decouplingStart (d : ℚ) :
    eligibilityBudget d decouplingStart = 2 * d / 21 := by
  unfold eligibilityBudget decouplingStart; ring

/-- **The `A`-image of the record pair passes, with margin `1/8148`.** -/
theorem procA_bourgain_eligible :
    eligibilityBudget (epDisplacement (procA_fst bourgainKappa)
        (procA_snd bourgainKappa bourgainLambda)) decouplingStart
      - (epMu (procA_fst bourgainKappa) (procA_snd bourgainKappa bourgainLambda) - bourgainTheta)
      = 1 / 8148 := by
  rw [budget_at_decouplingStart, procA_bourgain_displacement, procA_bourgain_excess]
  norm_num

/-- **Both recent pairs fail**, by margins exceeding `1/100`. -/
theorem tty_pairs_ineligible :
    epMu ttyPair1Kappa ttyPair1Lambda - bourgainTheta
        - eligibilityBudget (epDisplacement ttyPair1Kappa ttyPair1Lambda) decouplingStart
      > 1 / 100 ∧
    epMu ttyPair2Kappa ttyPair2Lambda - bourgainTheta
        - eligibilityBudget (epDisplacement ttyPair2Kappa ttyPair2Lambda) decouplingStart
      > 1 / 100 := by
  rw [budget_at_decouplingStart, budget_at_decouplingStart, ttyPair1_mu, ttyPair1_displacement,
    ttyPair2_mu, ttyPair2_displacement]
  unfold bourgainTheta
  constructor <;> norm_num

/-! ### The cost curve of the `A`-process against a fixed target -/

/-- The displacement cost of the `A`-image of a line pair, against a fixed target. -/
def procACost (κ θ : ℚ) : ℚ := (4 * κ + 1) / 2 - 4 * θ * (κ + 1)

/-- **The closed form of the cost.** -/
theorem procACost_eq {κ : ℚ} (h : κ + 1 ≠ 0) (θ : ℚ) :
    displacementCost (procA_fst κ) (procA_snd κ (κ + 1 / 2)) θ = procACost κ θ := by
  have h4 : 4 * κ + 4 ≠ 0 := by intro hc; apply h; linarith
  have h8 : 8 * κ + 8 ≠ 0 := by intro hc; apply h; linarith
  unfold displacementCost procACost
  rw [procA_line_displacement h, procA_line_mu h]
  field_simp
  ring

/-- **The cost is linear in the record with positive slope**, so it falls as the record improves. -/
theorem procACost_strictMono {κ κ' θ : ℚ} (hθ : θ < 1 / 2) (h : κ < κ') :
    procACost κ θ < procACost κ' θ := by
  unfold procACost; nlinarith

/-- The cost against the current record, at each landmark. -/
@[simp] theorem procACost_weyl : procACost weylKappa bourgainTheta = 1 / 9 := by
  unfold procACost weylKappa bourgainTheta; norm_num

@[simp] theorem procACost_bi : procACost biKappa bourgainTheta = 121 / 1176 := by
  unfold procACost biKappa bourgainTheta; norm_num

@[simp] theorem procACost_huxley : procACost huxleyPairKappa bourgainTheta = 277 / 2870 := by
  unfold procACost huxleyPairKappa bourgainTheta; norm_num

@[simp] theorem procACost_bourgain : procACost bourgainKappa bourgainTheta = 167 / 1764 := by
  unfold procACost bourgainKappa bourgainTheta; norm_num

/-- **The cost of buying displacement falls strictly along the record sequence.** -/
theorem procACost_decreasing :
    procACost bourgainKappa bourgainTheta < procACost huxleyPairKappa bourgainTheta ∧
      procACost huxleyPairKappa bourgainTheta < procACost biKappa bourgainTheta ∧
      procACost biKappa bourgainTheta < procACost weylKappa bourgainTheta := by
  rw [procACost_bourgain, procACost_huxley, procACost_bi, procACost_weyl]
  refine ⟨by norm_num, by norm_num, by norm_num⟩

/-! ### Where the cost would vanish -/

/-- The record at which the `A`-process would become productive at the critical length itself. -/
def freeDisplacementKappa (θ : ℚ) : ℚ := (8 * θ - 1) / (4 - 8 * θ)

/-- **The cost vanishes exactly at that record.** -/
theorem procACost_eq_zero_iff {κ θ : ℚ} (hθ : 4 - 8 * θ ≠ 0) :
    procACost κ θ = 0 ↔ κ = freeDisplacementKappa θ := by
  unfold procACost freeDisplacementKappa
  rw [eq_div_iff hθ]
  constructor <;> intro h <;> nlinarith

/-- **Against the current record the vanishing point is `5/58`.** -/
@[simp] theorem freeDisplacementKappa_bourgain : freeDisplacementKappa bourgainTheta = 5 / 58 := by
  unfold freeDisplacementKappa bourgainTheta; norm_num

/-- **The record is well above it**: `13/84 ≈ 0.1548` against `5/58 ≈ 0.0862`. -/
theorem record_above_free_displacement :
    freeDisplacementKappa bourgainTheta < bourgainKappa ∧
      bourgainKappa - freeDisplacementKappa bourgainTheta = 167 / 2436 := by
  rw [freeDisplacementKappa_bourgain]
  constructor <;> (unfold bourgainKappa; norm_num)

/-- **The cost is positive at the record, so the productive range stops short of the critical
length** — the quantitative form of Theorem 142's vertex condition. -/
theorem procACost_pos_at_record : 0 < procACost bourgainKappa bourgainTheta := by
  rw [procACost_bourgain]; norm_num

/-- **Summary.**  The productive threshold is `1/2` minus the cost, so it reaches the critical length
only at a record already far beyond anything known. -/
theorem productivity_needs_far_better_record :
    efficiencyThreshold (procA_fst bourgainKappa) (procA_snd bourgainKappa bourgainLambda)
        bourgainTheta = 1 / 2 - procACost bourgainKappa bourgainTheta ∧
      procACost (freeDisplacementKappa bourgainTheta) bourgainTheta = 0 := by
  constructor
  · rw [threshold_eq_half_sub_cost, procA_bourgain_cost, procACost_bourgain]
  · rw [freeDisplacementKappa_bourgain]
    unfold procACost bourgainTheta; norm_num

end HTGeometry
