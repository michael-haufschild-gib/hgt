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
    ring
  rw [hid] at hlog
  linarith

/-- The value at the optimal tilt. -/
theorem endpoint_tilt_value_eq {ε : ℝ} (hε : 0 < ε) :
    -(endpointTilt ε * ε) + (1 / 2) * Real.log (2 * Real.pi * endpointTilt ε)
      = -(1 / 2) + (1 / 2) * Real.log (Real.pi / ε) := by
  have h1 : endpointTilt ε * ε = 1 / 2 := by
    rw [endpointTilt]; field_simp
  have h2 : 2 * Real.pi * endpointTilt ε = Real.pi / ε := by
    rw [endpointTilt]; field_simp; ring
  rw [h1, h2]

/-- The target, decomposed into the optimal tilt value and the profile constant. -/
theorem endpointTarget_eq {α ε : ℝ} (hα : α < 1) (hε : 0 < ε) :
    endpointTarget α ε
      = (-(1 / 2) + (1 / 2) * Real.log (Real.pi / ε))
        + ((1 / 2) * Real.log (1 - α) + α / 2) := by
  have hα1 : (0 : ℝ) < 1 - α := by linarith
  rw [endpointTarget, Real.log_div Real.pi_ne_zero hε.ne',
    Real.log_mul Real.pi_ne_zero hα1.ne', one_div, Real.log_inv]
  ring

theorem tendsto_endpointTarget_atTop {α : ℝ} (hα : α < 1) :
    Tendsto (endpointTarget α) (𝓝[>] (0 : ℝ)) atTop := by
  have hbase : Tendsto (fun ε : ℝ => (1 / 2) * Real.log (1 / ε)) (𝓝[>] (0 : ℝ)) atTop :=
    Filter.Tendsto.const_mul_atTop (by norm_num) tendsto_logInv_atTop
  have := hbase.atTop_add
    (tendsto_const_nhds (x := (1 / 2) * Real.log (Real.pi * (1 - α)) - (1 - α) / 2)
      (f := 𝓝[>] (0 : ℝ)))
  refine this.congr fun ε => ?_
  rw [endpointTarget]
  ring

end

end HTGeometry
