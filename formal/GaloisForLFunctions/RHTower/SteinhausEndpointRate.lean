import GaloisForLFunctions.RHTower.SteinhausEndpointCumulant
import GaloisForLFunctions.HTGeometry.IntegralLogCesaro

/-!
# The high-coherence endpoint of the rate function

The card's `(8)`.  With `Λ_α(λ) = λ − ½log(2πλ) − c_α + o(1)` and `c_α = ½log(1−α) + α/2`, the
tilted functional at `q = 1 − ε` is

`λ(1−ε) − Λ_α(λ) = −λε + ½log(2πλ) + c_α − o(1)`,

whose exact maximum over `λ > 0` is at `λ = 1/(2ε)` with value `−½ + ½log(π/ε)`.  The optimality is
`log z ≤ z − 1` at `z = 2λε`.  Hence

`I_α(1−ε) = ½log(1/ε) + ½log(π(1−α)) − (1−α)/2 + o(1)`.

Small tilts need no asymptotic at all: they contribute at most `λ₀`, while the target diverges.
-/

open Filter Topology Set

namespace HTGeometry

noncomputable section

/-- The card's high-coherence value. -/
def endpointTarget (α ε : ℝ) : ℝ :=
  (1 / 2) * Real.log (1 / ε) + (1 / 2) * Real.log (Real.pi * (1 - α)) - (1 - α) / 2

/-- The exactly optimal endpoint tilt. -/
def endpointTilt (ε : ℝ) : ℝ := 1 / (2 * ε)

/-- **Optimality of the endpoint tilt**, from `log z ≤ z − 1`. -/
theorem endpoint_tilt_value_le {ε lam : ℝ} (hε : 0 < ε) (hlam : 0 < lam) :
    -(lam * ε) + (1 / 2) * Real.log (2 * Real.pi * lam)
      ≤ -(1 / 2) + (1 / 2) * Real.log (Real.pi / ε) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hz : (0 : ℝ) < 2 * lam * ε := by positivity
  have hlog := Real.log_le_sub_one_of_pos hz
  have hid : Real.log (2 * lam * ε)
      = Real.log (2 * Real.pi * lam) - Real.log (Real.pi / ε) := by
    rw [← Real.log_div (by positivity) (by positivity)]
    congr 1
    field_simp
  rw [hid] at hlog
  linarith

/-- The value at the optimal tilt. -/
theorem endpoint_tilt_value_eq {ε : ℝ} (hε : 0 < ε) :
    -(endpointTilt ε * ε) + (1 / 2) * Real.log (2 * Real.pi * endpointTilt ε)
      = -(1 / 2) + (1 / 2) * Real.log (Real.pi / ε) := by
  have h1 : endpointTilt ε * ε = 1 / 2 := by
    rw [endpointTilt]; field_simp
  have h2 : 2 * Real.pi * endpointTilt ε = Real.pi / ε := by
    rw [endpointTilt]; field_simp
  rw [h1, h2]

/-- The target, decomposed into the optimal tilt value and the profile constant. -/
theorem endpointTarget_eq {α ε : ℝ} (hα : α < 1) (hε : 0 < ε) :
    endpointTarget α ε
      = (-(1 / 2) + (1 / 2) * Real.log (Real.pi / ε))
        + ((1 / 2) * Real.log (1 - α) + α / 2) := by
  have hα1 : (0 : ℝ) < 1 - α := by linarith
  rw [endpointTarget, Real.log_div Real.pi_ne_zero hε.ne',
    Real.log_mul Real.pi_ne_zero hα1.ne', one_div ε, Real.log_inv]
  ring

theorem tendsto_endpointTarget_atTop (α : ℝ) :
    Tendsto (endpointTarget α) (𝓝[>] (0 : ℝ)) atTop := by
  have hbase : Tendsto (fun ε : ℝ => (1 / 2) * Real.log (1 / ε)) (𝓝[>] (0 : ℝ)) atTop :=
    Filter.Tendsto.const_mul_atTop (by norm_num) tendsto_logInv_atTop
  have := hbase.atTop_add
    (tendsto_const_nhds (x := (1 / 2) * Real.log (Real.pi * (1 - α)) - (1 - α) / 2)
      (f := 𝓝[>] (0 : ℝ)))
  refine this.congr fun ε => ?_
  rw [endpointTarget]
  ring


/-- **The high-coherence endpoint law**, the card's `(8)`:
`I_α(1−ε) = ½log(1/ε) + ½log(π(1−α)) − (1−α)/2 + o(1)`. -/
theorem tendsto_rvRate_endpoint {α : ℝ} (hα0 : 0 ≤ α) (hα : α < 1) :
    Tendsto (fun ε : ℝ => rvRate α (1 - ε) - endpointTarget α ε) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hα1 : (0 : ℝ) < 1 - α := by linarith
  rw [Metric.tendsto_nhds]
  intro δ hδ
  obtain ⟨lamBase, hlamBase⟩ :=
    Metric.tendsto_atTop.1 (tendsto_rvCumulant_deficit hα0 hα) (δ / 2) (by linarith)
  set L : ℝ := max 1 lamBase with hL
  have hL1 : (1 : ℝ) ≤ L := le_max_left _ _
  have hL0 : (0 : ℝ) < L := lt_of_lt_of_le one_pos hL1
  have hdef : ∀ lam : ℝ, L ≤ lam →
      |rvCumulant α lam - (lam - (1 / 2) * Real.log (2 * Real.pi * lam)
        - (1 / 2) * Real.log (1 - α) - α / 2)| < δ / 2 := by
    intro lam hlam
    have := hlamBase lam (le_trans (le_max_right _ _) hlam)
    rwa [Real.dist_eq, sub_zero] at this
  have hev1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < 1 :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
  have hev2 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), L ≤ endpointTarget α ε :=
    (tendsto_endpointTarget_atTop α).eventually_ge_atTop L
  have hev3 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < 1 / (2 * L) :=
    (eventually_lt_nhds (by positivity : (0 : ℝ) < 1 / (2 * L))).filter_mono nhdsWithin_le_nhds
  filter_upwards [hev1, hev2, hev3, self_mem_nhdsWithin] with ε hε1 hεT hε3 hε
  have hε0 : (0 : ℝ) < ε := hε
  have hεL : L ≤ endpointTilt ε := by
    rw [endpointTilt, le_div_iff₀ (by positivity)]
    rw [lt_div_iff₀ (by positivity)] at hε3
    nlinarith [hε3]
  have hq1 : (1 : ℝ) - ε < 1 := by linarith
  have hTeq := endpointTarget_eq hα hε0
  -- upper bound
  have hupper : rvRate α (1 - ε) ≤ endpointTarget α ε + δ / 2 := by
    refine csSup_le (rvLegendreSet_nonempty α (1 - ε)) ?_
    rintro y ⟨lam, hlam, rfl⟩
    rcases le_or_gt L lam with hbig | hsmall
    · have hlam0 : (0 : ℝ) < lam := lt_of_lt_of_le hL0 hbig
      have hd := hdef lam hbig
      rw [abs_lt] at hd
      have hopt := endpoint_tilt_value_le hε0 hlam0
      have hstep : lam * (1 - ε) - rvCumulant α lam
          ≤ (-(lam * ε) + (1 / 2) * Real.log (2 * Real.pi * lam))
            + ((1 / 2) * Real.log (1 - α) + α / 2) + δ / 2 := by
        nlinarith [hd.1, hd.2]
      rw [hTeq]
      linarith [hstep, hopt]
    · have hcum := rvCumulant_nonneg α lam
      have hval : lam * (1 - ε) - rvCumulant α lam ≤ L := by
        nlinarith [hlam, hε0.le, hcum, hsmall.le]
      linarith [hval, hεT, hδ]
  -- lower bound
  have hlower : endpointTarget α ε - δ / 2 ≤ rvRate α (1 - ε) := by
    have hlam0 : (0 : ℝ) < endpointTilt ε := lt_of_lt_of_le hL0 hεL
    have hd := hdef _ hεL
    rw [abs_lt] at hd
    have hle := le_rvRate hα hq1 hlam0.le
    have hopt := endpoint_tilt_value_eq hε0
    have hstep : endpointTarget α ε - δ / 2
        ≤ endpointTilt ε * (1 - ε) - rvCumulant α (endpointTilt ε) := by
      rw [hTeq, ← hopt]
      nlinarith [hd.1, hd.2]
    linarith [hstep, hle]
  rw [Real.dist_eq, sub_zero, abs_lt]
  constructor
  · linarith [hlower, hδ]
  · linarith [hupper, hδ]

end

end HTGeometry
