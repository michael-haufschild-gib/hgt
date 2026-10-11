import GaloisForLFunctions.RHTower.XiGaussianHeatZeroFreeHalfPlane
import GaloisForLFunctions.RHTower.XiResolventMassBudget

/-!
# Heat duality of one Euler factor and the critical parabola

In heat coordinates `w = z²` (`z = (ρ − ½)/i`), the critical strip `|Re ρ − ½| < ½` becomes the
interior of the parabola

`Π = {w : Re w > (Im w)² − ¼}`, with vertex `−¼` (the pole of `ζ`).

* Every zero frequency `w_q` lies strictly inside `Π` (`heatParabolaDefect_xiHeatFrequency_pos`).
  RH says they all lie on the focal ray `[0, ∞)`.
* **Euler-factor duality** (`tsum_eulerFactor_heat_eq`).  For `L > 0` (`L = log p`) and
  `Re τ > 0`, Poisson summation over the prime powers gives

  `Σ_{k∈ℤ} e^{−k²L²/(4τ) − kL/2} = a^{−½} Σ_{m∈ℤ} e^{−τ w_m},  a = L²/(4πτ),`

  with local heat spectrum `w_m = (2πm/L − i/2)²`.  At real time `t > 0` this reads
  `L (π/t)^{½} Σ_k … = 2π Σ_m e^{−t w_m}` (`eulerFactor_heat_duality_real`).
* Every local frequency lies **on** `∂Π`, and the vertex `m = 0` is the pole `−¼`
  (`heatParabolaDefect_eulerLocalHeatFrequency`, `eulerLocalHeatFrequency_zero`).

The terms `k ≥ 1` of the left side, times `L`, are the contribution of `p` to the Gaussian prime
chirp `Σ Λ(n) n^{−½} e^{−(log n)²/(4τ)}`.  So in heat coordinates each Euler factor is a heat trace
over a spectrum on the boundary of the parabola, while the zeros live strictly inside it.
-/

open Complex

namespace RHTower

noncomputable section

/-- The defect `Re w − ((Im w)² − ¼)`: positive inside the critical parabola, zero on it. -/
def heatParabolaDefect (w : ℂ) : ℝ := w.re - (w.im ^ 2 - 1 / 4)

/-- The local heat spectrum `w_m = (2πm/L − i/2)²` of an Euler factor with logarithm `L`. -/
def eulerLocalHeatFrequency (L : ℝ) (m : ℤ) : ℂ := (2 * (Real.pi : ℂ) * m / L - I / 2) ^ 2

theorem heatParabolaDefect_eulerLocalHeatFrequency (L : ℝ) (m : ℤ) :
    heatParabolaDefect (eulerLocalHeatFrequency L m) = 0 := by
  have h : (2 * (Real.pi : ℂ) * m / L - I / 2) = ((2 * Real.pi * m / L : ℝ) : ℂ) - I / 2 := by
    push_cast; ring
  simp only [heatParabolaDefect, eulerLocalHeatFrequency, h, sq, mul_re, mul_im, sub_re, sub_im,
    ofReal_re, ofReal_im, div_re, div_im, I_re, I_im, normSq_ofNat]
  norm_num
  ring

theorem eulerLocalHeatFrequency_zero (L : ℝ) : eulerLocalHeatFrequency L 0 = -1 / 4 := by
  simp only [eulerLocalHeatFrequency, Int.cast_zero, mul_zero, zero_div, zero_sub]
  rw [neg_sq, div_pow, I_sq]
  norm_num

/-- Every zero frequency lies strictly inside the critical parabola:
`Re w − (Im w)² + ¼ = (4γ² + 1)(¼ − δ²) > 0`. -/
theorem heatParabolaDefect_xiHeatFrequency_pos (q : XiZeroCopy) :
    0 < heatParabolaDefect (xiHeatFrequency q) := by
  have h := xiSpectralPoint_im_sq_lt_quarter q
  set γ := (xiSpectralPoint q).re
  set δ := (xiSpectralPoint q).im
  have hre : (xiHeatFrequency q).re = γ ^ 2 - δ ^ 2 := by
    simp only [xiHeatFrequency, sq, mul_re, γ, δ]
  have him : (xiHeatFrequency q).im = 2 * γ * δ := by
    simp only [xiHeatFrequency, sq, mul_im, γ, δ]; ring
  rw [heatParabolaDefect, hre, him]
  have : γ ^ 2 - δ ^ 2 - ((2 * γ * δ) ^ 2 - 1 / 4) = (4 * γ ^ 2 + 1) * (1 / 4 - δ ^ 2) := by ring
  rw [this]
  exact mul_pos (by positivity) (by linarith)

/-- **Euler-factor heat duality.**  Poisson summation over the powers of one prime. -/
theorem tsum_eulerFactor_heat_eq {L : ℝ} (hL : 0 < L) {τ : ℂ} (hτ : 0 < τ.re) :
    ∑' k : ℤ, Complex.exp (-(k : ℂ) ^ 2 * (L : ℂ) ^ 2 / (4 * τ) - k * L / 2) =
      1 / ((L : ℂ) ^ 2 / (4 * Real.pi * τ)) ^ (1 / 2 : ℂ) *
        ∑' m : ℤ, Complex.exp (-τ * eulerLocalHeatFrequency L m) := by
  have hτ0 : τ ≠ 0 := fun h => by rw [h, zero_re] at hτ; exact lt_irrefl 0 hτ
  have hπ : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  have hL0 : (L : ℂ) ≠ 0 := ofReal_ne_zero.2 hL.ne'
  set a : ℂ := (L : ℂ) ^ 2 / (4 * Real.pi * τ) with ha
  have hare : 0 < a.re := by
    have e : a = ((L ^ 2 / (4 * Real.pi) : ℝ) : ℂ) * τ⁻¹ := by
      rw [ha]; push_cast; field_simp
    rw [e, re_ofReal_mul, inv_re]
    exact mul_pos (by positivity) (div_pos hτ (normSq_pos.2 hτ0))
  have hP := Complex.tsum_exp_neg_quadratic hare (-(L : ℂ) / (4 * Real.pi))
  have hlhs : ∀ k : ℤ, -(k : ℂ) ^ 2 * (L : ℂ) ^ 2 / (4 * τ) - k * L / 2 =
      -(Real.pi : ℂ) * a * k ^ 2 + 2 * Real.pi * (-(L : ℂ) / (4 * Real.pi)) * k := by
    intro k; rw [ha]; field_simp; ring
  have hrhs : ∀ m : ℤ, -(Real.pi : ℂ) / a * (m + I * (-(L : ℂ) / (4 * Real.pi))) ^ 2 =
      -τ * eulerLocalHeatFrequency L m := by
    intro m; rw [ha, eulerLocalHeatFrequency]; field_simp; ring
  simp only [hlhs, hP, hrhs]

/-- **Real-time form.**  `L (π/t)^{½} Σ_{k∈ℤ} e^{−k²L²/(4t) − kL/2} = 2π Σ_m e^{−t w_m}`. -/
theorem eulerFactor_heat_duality_real {L t : ℝ} (hL : 0 < L) (ht : 0 < t) :
    ((L * Real.sqrt (Real.pi / t) : ℝ) : ℂ) *
        ∑' k : ℤ, Complex.exp (-(k : ℂ) ^ 2 * (L : ℂ) ^ 2 / (4 * (t : ℂ)) - k * L / 2) =
      2 * Real.pi * ∑' m : ℤ, Complex.exp (-(t : ℂ) * eulerLocalHeatFrequency L m) := by
  have htre : 0 < (t : ℂ).re := by rw [ofReal_re]; exact ht
  rw [tsum_eulerFactor_heat_eq hL htre, ← mul_assoc]
  congr 1
  have hx : (0 : ℝ) ≤ L ^ 2 / (4 * Real.pi * t) := by positivity
  have hcast : ((L : ℂ) ^ 2 / (4 * Real.pi * (t : ℂ))) = ((L ^ 2 / (4 * Real.pi * t) : ℝ) : ℂ) := by
    push_cast; ring
  have hc : ((L ^ 2 / (4 * Real.pi * t) : ℝ) : ℂ) ^ (1 / 2 : ℂ) =
      ((Real.sqrt (L ^ 2 / (4 * Real.pi * t)) : ℝ) : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hx]
    norm_num
  rw [hcast, hc]
  have hs : Real.sqrt (L ^ 2 / (4 * Real.pi * t)) = L / (2 * Real.sqrt (Real.pi * t)) := by
    rw [Real.sqrt_div' _ (by positivity), Real.sqrt_sq hL.le, show 4 * Real.pi * t = 2 ^ 2 * (Real.pi * t)
      by ring, Real.sqrt_mul' _ (by positivity), Real.sqrt_sq (by norm_num)]
  rw [hs]
  have hπt : 0 < Real.sqrt (Real.pi * t) := Real.sqrt_pos.2 (by positivity)
  have hprod : Real.sqrt (Real.pi / t) * Real.sqrt (Real.pi * t) = Real.pi := by
    rw [← Real.sqrt_mul (by positivity), show Real.pi / t * (Real.pi * t) = Real.pi ^ 2 by
      field_simp, Real.sqrt_sq Real.pi_pos.le]
  have hL0 : (L : ℂ) ≠ 0 := ofReal_ne_zero.2 hL.ne'
  have hfin : ((L * Real.sqrt (Real.pi / t) : ℝ) : ℂ) * ((Real.sqrt (Real.pi * t) : ℝ) : ℂ) / L =
      Real.pi := by
    rw [← ofReal_mul, show L * Real.sqrt (Real.pi / t) * Real.sqrt (Real.pi * t) = L * Real.pi by
      rw [mul_assoc, hprod], ofReal_mul]
    field_simp
  push_cast
  field_simp
  push_cast at hfin
  field_simp at hfin
  linear_combination hfin

end

end RHTower
