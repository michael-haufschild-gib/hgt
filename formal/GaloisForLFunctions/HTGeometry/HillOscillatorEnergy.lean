import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# The energy of an oscillator with a time-dependent frequency

A wave equation whose principal part depends on time but not on the point becomes, frequency by
frequency, the Hill equation `u'' + ω(t)²u = 0` with `ω(t) = c(t)·s` and `s` the frequency. Its
energy `u'² + ω²u²` is not conserved, but its logarithmic derivative is controlled by that of the
frequency alone:

`E' = 2ωω'u² ≤ 2(ω'/ω)E`.

The resulting Grönwall bound is therefore *uniform in the frequency* — the scaling `ω = c·s` cancels
in `ω'/ω` — which is what a synthesis over all frequencies needs.
-/

namespace GaloisForLFunctions.HTGeometry

open Set

/-- The energy of an oscillator with time-dependent frequency. -/
noncomputable def hillEnergy (ω u du : ℝ → ℝ) (t : ℝ) : ℝ := du t ^ 2 + ω t ^ 2 * u t ^ 2

theorem hillEnergy_nonneg (ω u du : ℝ → ℝ) (t : ℝ) : 0 ≤ hillEnergy ω u du t := by
  have h₁ : (0 : ℝ) ≤ du t ^ 2 := sq_nonneg _
  have h₂ : (0 : ℝ) ≤ ω t ^ 2 * u t ^ 2 := mul_nonneg (sq_nonneg _) (sq_nonneg _)
  exact add_nonneg h₁ h₂

/-- **The energy of a Hill oscillator moves only with its frequency.** -/
theorem hasDerivAt_hillEnergy {ω dω u du ddu : ℝ → ℝ}
    (hω : ∀ t, HasDerivAt ω (dω t) t) (hu : ∀ t, HasDerivAt u (du t) t)
    (hdu : ∀ t, HasDerivAt du (ddu t) t) (heq : ∀ t, ddu t + ω t ^ 2 * u t = 0) (t : ℝ) :
    HasDerivAt (hillEnergy ω u du) (2 * (ω t * dω t) * u t ^ 2) t := by
  have h₁ : HasDerivAt (fun s => du s ^ 2) (2 * du t ^ 1 * ddu t) t := (hdu t).pow 2
  have h₂ : HasDerivAt (fun s => ω s ^ 2) (2 * ω t ^ 1 * dω t) t := (hω t).pow 2
  have h₃ : HasDerivAt (fun s => u s ^ 2) (2 * u t ^ 1 * du t) t := (hu t).pow 2
  have hsum := h₁.add (h₂.mul h₃)
  have hddu : ddu t = -(ω t ^ 2 * u t) := by
    have := heq t
    linarith
  refine hsum.congr_deriv ?_
  rw [hddu]
  ring

/-- **Grönwall bound for the energy.** If the frequency is positive and its logarithmic derivative is
bounded by `K`, the energy grows at most like `e^{2K t}`. -/
theorem hillEnergy_le_of_logDeriv_le {ω dω u du ddu : ℝ → ℝ} {K a b : ℝ}
    (hω : ∀ t, HasDerivAt ω (dω t) t) (hu : ∀ t, HasDerivAt u (du t) t)
    (hdu : ∀ t, HasDerivAt du (ddu t) t) (heq : ∀ t, ddu t + ω t ^ 2 * u t = 0)
    (hωpos : ∀ t, 0 < ω t) (hK : ∀ t, |dω t| ≤ K * ω t) {t : ℝ} (ht : t ∈ Icc a b) :
    hillEnergy ω u du t ≤ hillEnergy ω u du a * Real.exp (2 * K * (t - a)) := by
  have hderiv := fun s => hasDerivAt_hillEnergy hω hu hdu heq s
  have hcont : ContinuousOn (hillEnergy ω u du) (Icc a b) := fun s _ =>
    ((hderiv s).continuousAt).continuousWithinAt
  have hbound : ∀ s ∈ Ico a b,
      ‖2 * (ω s * dω s) * u s ^ 2‖ ≤ 2 * K * ‖hillEnergy ω u du s‖ + 0 := by
    intro s _
    have hωs : 0 < ω s := hωpos s
    have habs : |dω s| ≤ K * ω s := hK s
    have hnorm : ‖2 * (ω s * dω s) * u s ^ 2‖ = 2 * (ω s * |dω s|) * u s ^ 2 := by
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2),
        abs_of_pos hωs, abs_of_nonneg (sq_nonneg (u s))]
    have hE : ‖hillEnergy ω u du s‖ = hillEnergy ω u du s :=
      Real.norm_of_nonneg (hillEnergy_nonneg ω u du s)
    rw [hnorm, hE, add_zero]
    have hstep : 2 * (ω s * |dω s|) * u s ^ 2 ≤ 2 * (ω s * (K * ω s)) * u s ^ 2 := by
      have := mul_le_mul_of_nonneg_left habs (le_of_lt hωs)
      nlinarith [sq_nonneg (u s)]
    refine hstep.trans ?_
    have hdu2 : (0 : ℝ) ≤ du s ^ 2 := sq_nonneg _
    have hKnn : 0 ≤ K := by
      have h0 : (0 : ℝ) ≤ |dω s| := abs_nonneg _
      nlinarith
    have : 2 * (ω s * (K * ω s)) * u s ^ 2 = 2 * K * (ω s ^ 2 * u s ^ 2) := by ring
    rw [this, hillEnergy]
    nlinarith
  have hgron := norm_le_gronwallBound_of_norm_deriv_right_le hcont
    (fun s hs => ((hderiv s).hasDerivWithinAt)) (le_of_eq (Real.norm_of_nonneg
      (hillEnergy_nonneg ω u du a))) hbound t ht
  rw [gronwallBound_ε0] at hgron
  have hE : ‖hillEnergy ω u du t‖ = hillEnergy ω u du t :=
    Real.norm_of_nonneg (hillEnergy_nonneg ω u du t)
  rw [hE] at hgron
  exact hgron

/-- **The bound does not see the frequency.** For `ω = c·s` with a positive scale `s`, the
logarithmic derivative of `ω` is that of `c`, so one constant serves every frequency. -/
theorem abs_deriv_le_of_scaled {c dc : ℝ → ℝ} {K s : ℝ} (hs : 0 < s)
    (hc : ∀ t, |dc t| ≤ K * c t) (t : ℝ) : |dc t * s| ≤ K * (c t * s) := by
  rw [abs_mul, abs_of_pos hs]
  have := mul_le_mul_of_nonneg_right (hc t) (le_of_lt hs)
  calc |dc t| * s ≤ K * c t * s := this
    _ = K * (c t * s) := by ring

end GaloisForLFunctions.HTGeometry
