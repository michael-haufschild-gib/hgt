/-
The van der Corput process destroys its own leverage as the record improves.

For a pair on the line of symmetry, `P = (κ, κ + 1/2)` with `μ(P) = κ`, the `A`-process produces

    A(P) = (κ/(2κ+2), (2κ + 3/2)/(2κ+2)),
    displacement  d(A(P)) = 1/(4κ + 4),
    exponent      μ(A(P)) = (4κ + 1)/(8κ + 8),
    excess        μ(A(P)) - κ = (1 - 4κ - 8κ²)/(8κ + 8).

So its efficiency against the pair's own exponent is

    **η(κ) = d / excess = 2 / (1 - 4κ - 8κ²),**

and by the efficiency law its productivity threshold — the largest length at which `A(P)` still beats
`P` — is

    **T(κ) = 1/2 - 1/η(κ) = 2κ(1 + 2κ).**

Three consequences.

* `T` is strictly increasing with `T(0) = 0`, and `T(κ) = 1/2` exactly at the positive root of
  `8κ² + 4κ - 1`, which is the stationarity threshold of the `A`-process for the pointwise exponent.
  The two thresholds recorded separately are one formula.

* Along the record sequence Weyl, Bombieri–Iwaniec, Huxley, Bourgain the thresholds are
  `4/9`, `333/784`, `17216/42025`, `715/1764` — strictly decreasing.  **Improving the record shrinks
  the range over which the process is productive, at rate `T'(κ) = 2 + 8κ`.**  At the Lindelöf value
  `κ = 0` the productive range is empty.

* The published handoff length `17/42` is crossed at `κ* = (√1155 - 21)/84`.  Since `1155 = 34² - 1`,
  `κ* < 13/84` by the single unit `1156 - 1155 = 1`; and `κ*` exceeds the covering floor `277/1792`.
  So the very next improvement of the record would push the productive range below the length at which
  the published proof hands off.
-/
import GaloisForLFunctions.HTGeometry.EfficiencyThresholdLaw

namespace HTGeometry

/-! ### The `A`-image of a line pair -/

/-- The displacement of the `A`-image of a pair on the line of symmetry. -/
theorem procA_line_displacement {κ : ℚ} (h : κ + 1 ≠ 0) :
    epDisplacement (procA_fst κ) (procA_snd κ (κ + 1 / 2)) = 1 / (4 * κ + 4) := by
  have h2 : 2 * κ + 2 ≠ 0 := by intro hc; apply h; linarith
  unfold epDisplacement procA_fst procA_snd
  field_simp
  ring

/-- The pointwise exponent of the `A`-image of a pair on the line of symmetry. -/
theorem procA_line_mu {κ : ℚ} (h : κ + 1 ≠ 0) :
    epMu (procA_fst κ) (procA_snd κ (κ + 1 / 2)) = (4 * κ + 1) / (8 * κ + 8) := by
  have h2 : 2 * κ + 2 ≠ 0 := by intro hc; apply h; linarith
  unfold epMu procA_fst procA_snd
  field_simp
  ring

/-- Its excess over the pair's own exponent. -/
theorem procA_line_excess {κ : ℚ} (h : κ + 1 ≠ 0) :
    epMu (procA_fst κ) (procA_snd κ (κ + 1 / 2)) - κ
      = (1 - 4 * κ - 8 * κ ^ (2 : ℕ)) / (8 * κ + 8) := by
  have h2 : 8 * κ + 8 ≠ 0 := by intro hc; apply h; linarith
  rw [procA_line_mu h]
  field_simp
  ring

/-! ### Efficiency and productivity threshold -/

/-- The self-efficiency of the `A`-process at a line pair. -/
def lineSelfEfficiency (κ : ℚ) : ℚ := 2 / (1 - 4 * κ - 8 * κ ^ (2 : ℕ))

/-- The productivity threshold of the `A`-process at a line pair. -/
def aProductivityThreshold (κ : ℚ) : ℚ := 2 * κ * (1 + 2 * κ)

/-- **The self-efficiency is `2/(1 - 4κ - 8κ²)`.** -/
theorem lineSelfEfficiency_eq {κ : ℚ} (h : κ + 1 ≠ 0) :
    epEfficiency (procA_fst κ) (procA_snd κ (κ + 1 / 2)) κ = lineSelfEfficiency κ := by
  have h8 : 8 * κ + 8 ≠ 0 := by intro hc; apply h; linarith
  have h4 : 4 * κ + 4 ≠ 0 := by intro hc; apply h; linarith
  unfold epEfficiency lineSelfEfficiency
  rw [procA_line_displacement h, procA_line_excess h]
  field_simp
  ring

/-- **The productivity threshold is `2κ(1 + 2κ)`.** -/
theorem aProductivityThreshold_eq {κ : ℚ} (h : κ + 1 ≠ 0) :
    efficiencyThreshold (procA_fst κ) (procA_snd κ (κ + 1 / 2)) κ = aProductivityThreshold κ := by
  have h4 : 4 * κ + 4 ≠ 0 := by intro hc; apply h; linarith
  have h8 : 8 * κ + 8 ≠ 0 := by intro hc; apply h; linarith
  unfold efficiencyThreshold aProductivityThreshold
  rw [procA_line_displacement h, procA_line_excess h]
  field_simp
  ring

/-- The threshold vanishes at the Lindelöf value. -/
@[simp] theorem aProductivityThreshold_zero : aProductivityThreshold 0 = 0 := by
  unfold aProductivityThreshold; ring

/-- **The threshold is strictly increasing on the nonnegative axis.** -/
theorem aProductivityThreshold_strictMono {κ κ' : ℚ} (h0 : 0 ≤ κ) (h : κ < κ') :
    aProductivityThreshold κ < aProductivityThreshold κ' := by
  unfold aProductivityThreshold; nlinarith

/-- **The threshold reaches the critical length exactly at the stationarity threshold of the
`A`-process for the pointwise exponent.** -/
theorem threshold_reaches_critical_iff (κ : ℚ) :
    aProductivityThreshold κ = 1 / 2 ↔ 8 * κ ^ (2 : ℕ) + 4 * κ - 1 = 0 := by
  unfold aProductivityThreshold
  constructor <;> intro h <;> nlinarith

/-! ### The record sequence -/

@[simp] theorem aThreshold_weyl : aProductivityThreshold weylKappa = 4 / 9 := by
  unfold aProductivityThreshold weylKappa; norm_num

@[simp] theorem aThreshold_bi : aProductivityThreshold biKappa = 333 / 784 := by
  unfold aProductivityThreshold biKappa; norm_num

@[simp] theorem aThreshold_huxley : aProductivityThreshold huxleyPairKappa = 17216 / 42025 := by
  unfold aProductivityThreshold huxleyPairKappa; norm_num

@[simp] theorem aThreshold_bourgain : aProductivityThreshold bourgainKappa = 715 / 1764 := by
  unfold aProductivityThreshold bourgainKappa; norm_num

/-- **The productive range shrinks monotonically along the record sequence.** -/
theorem thresholds_decreasing :
    aProductivityThreshold bourgainKappa < aProductivityThreshold huxleyPairKappa ∧
      aProductivityThreshold huxleyPairKappa < aProductivityThreshold biKappa ∧
      aProductivityThreshold biKappa < aProductivityThreshold weylKappa := by
  rw [aThreshold_bourgain, aThreshold_huxley, aThreshold_bi, aThreshold_weyl]
  refine ⟨by norm_num, by norm_num, by norm_num⟩

/-- **The self-defeating law.**  Each unit of progress in the pointwise exponent costs at least two
units of productive range: the threshold's increments dominate twice the exponent's. -/
theorem self_defeating_rate {κ κ' : ℚ} (h0 : 0 ≤ κ) (h : κ < κ') :
    2 * (κ' - κ) < aProductivityThreshold κ' - aProductivityThreshold κ := by
  unfold aProductivityThreshold; nlinarith

/-! ### Where the productive range falls below the published handoff -/

/-- The record value at which the productive range would drop to the handoff length. -/
def handoffCrossingSq : ℚ := 1155

/-- **The crossing point satisfies `(84κ + 21)² = 1155`.**  Equivalently `κ = (√1155 - 21)/84`. -/
theorem handoff_crossing_equation (κ : ℚ) :
    aProductivityThreshold κ = decouplingStart ↔ (84 * κ + 21) ^ (2 : ℕ) = handoffCrossingSq := by
  unfold aProductivityThreshold decouplingStart handoffCrossingSq
  constructor <;> intro h <;> nlinarith

/-- **`1155 = 34² - 1`**, so the crossing point is strictly below the record `13/84`. -/
theorem crossing_below_record : handoffCrossingSq = 34 ^ (2 : ℕ) - 1 := by
  unfold handoffCrossingSq; norm_num

/-- The record's own value of `(84κ + 21)²` is `34² = 1156`, one more than the crossing value. -/
theorem record_exceeds_crossing :
    (84 * bourgainKappa + 21) ^ (2 : ℕ) = handoffCrossingSq + 1 := by
  unfold bourgainKappa handoffCrossingSq; norm_num

/-- **The covering floor's value of `(84κ + 21)²` is below the crossing value**, so the crossing point
lies strictly between the covering floor and the record. -/
theorem covering_floor_below_crossing :
    (84 * (277 / 1792 : ℚ) + 21) ^ (2 : ℕ) < handoffCrossingSq := by
  unfold handoffCrossingSq; norm_num

/-- **The productive range at the record still exceeds the handoff length, by `1/1764`; at the
covering floor it would not.** -/
theorem productivity_vs_handoff :
    decouplingStart < aProductivityThreshold bourgainKappa ∧
      aProductivityThreshold bourgainKappa - decouplingStart = 1 / 1764 ∧
      aProductivityThreshold (277 / 1792) < decouplingStart := by
  rw [aThreshold_bourgain]
  refine ⟨by unfold decouplingStart; norm_num, by unfold decouplingStart; norm_num, ?_⟩
  unfold aProductivityThreshold decouplingStart; norm_num

/-- **The prediction.**  Any record strictly below `13/84` whose `(84κ+21)²` falls under `1155` leaves
the exponent-pair machinery unproductive on the whole covered range: the architecture would have to be
rebuilt, not merely re-tuned. -/
theorem next_improvement_breaks_architecture {κ : ℚ}
    (h : (84 * κ + 21) ^ (2 : ℕ) < handoffCrossingSq) :
    aProductivityThreshold κ < decouplingStart := by
  unfold aProductivityThreshold decouplingStart
  unfold handoffCrossingSq at h
  nlinarith

end HTGeometry
