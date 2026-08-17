import GaloisForLFunctions.RHTower.SuzukiUltravioletMultiplicityClock
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The amplitude-phase form of the parity clock and its Cesàro balance

The two source amplitudes of one ordinate are a single rotated pair: `cos(γa) + γ sin(γa)` and
`sin(γa) - γ cos(γa)` are `√(1+γ²)` times the cosine and sine of the inhomogeneous phase
`θ_γ(a) = γa - arctan γ`, because `arctan γ` is exactly the angle whose cosine and sine are
`1/√(1+γ²)` and `γ/√(1+γ²)`.

Averaging the squared phase over apertures gives the balanced value `1/2` for every nonzero
ordinate: the oscillatory part of `cos²` integrates to a bounded quantity, so its Cesàro mean
vanishes.  That is the parity balance of the long-aperture mean, and it holds with an explicit
`O(1/A)` rate rather than only in the limit.
-/

open Filter Topology intervalIntegral

noncomputable section

namespace GaloisForLFunctions.RHTower

/-! ## The amplitude-phase rewriting -/

theorem cos_amplitude_phase (γ a : ℝ) :
    Real.cos (γ * a) + γ * Real.sin (γ * a)
      = Real.sqrt (1 + γ ^ 2) * Real.cos (parityPhase γ a) := by
  have hpos : (0 : ℝ) < 1 + γ ^ 2 := by positivity
  have hsq : (0 : ℝ) < Real.sqrt (1 + γ ^ 2) := Real.sqrt_pos.mpr hpos
  rw [parityPhase, Real.cos_sub, Real.cos_arctan, Real.sin_arctan]
  field_simp

theorem sin_amplitude_phase (γ a : ℝ) :
    Real.sin (γ * a) - γ * Real.cos (γ * a)
      = Real.sqrt (1 + γ ^ 2) * Real.sin (parityPhase γ a) := by
  have hpos : (0 : ℝ) < 1 + γ ^ 2 := by positivity
  have hsq : (0 : ℝ) < Real.sqrt (1 + γ ^ 2) := Real.sqrt_pos.mpr hpos
  rw [parityPhase, Real.sin_sub, Real.cos_arctan, Real.sin_arctan]
  field_simp

/-! ## The Cesàro balance of the squared phase -/

/-- The exact aperture integral of the squared phase. -/
theorem integral_cos_sq_parityPhase {γ : ℝ} (hγ : γ ≠ 0) (A : ℝ) :
    (∫ a in (1 : ℝ)..A, Real.cos (parityPhase γ a) ^ 2)
      = (A - 1) / 2
        + (Real.sin (2 * (γ * A - Real.arctan γ))
            - Real.sin (2 * (γ * 1 - Real.arctan γ))) / (4 * γ) := by
  have hcongr : ∀ a : ℝ, Real.cos (parityPhase γ a) ^ 2
      = 1 / 2 + Real.cos (2 * (γ * a - Real.arctan γ)) / 2 := by
    intro a
    rw [parityPhase, Real.cos_sq]
  have hderiv : ∀ a ∈ Set.uIcc (1 : ℝ) A,
      HasDerivAt (fun a : ℝ => a / 2 + Real.sin (2 * (γ * a - Real.arctan γ)) / (4 * γ))
        (1 / 2 + Real.cos (2 * (γ * a - Real.arctan γ)) / 2) a := by
    intro a _
    have hin : HasDerivAt (fun a : ℝ => 2 * (γ * a - Real.arctan γ)) (2 * γ) a := by
      have h1 : HasDerivAt (fun a : ℝ => γ * a - Real.arctan γ) γ a := by
        simpa using ((hasDerivAt_id a).const_mul γ).sub_const (Real.arctan γ)
      simpa using h1.const_mul (2 : ℝ)
    have hsin : HasDerivAt (fun a : ℝ => Real.sin (2 * (γ * a - Real.arctan γ)))
        (Real.cos (2 * (γ * a - Real.arctan γ)) * (2 * γ)) a := hin.sin
    have h2 : HasDerivAt (fun a : ℝ => Real.sin (2 * (γ * a - Real.arctan γ)) / (4 * γ))
        (Real.cos (2 * (γ * a - Real.arctan γ)) * (2 * γ) / (4 * γ)) a := hsin.div_const _
    have h3 : HasDerivAt (fun a : ℝ => a / 2) (1 / 2 : ℝ) a := by
      simpa using (hasDerivAt_id a).div_const 2
    have hsimp : Real.cos (2 * (γ * a - Real.arctan γ)) * (2 * γ) / (4 * γ)
        = Real.cos (2 * (γ * a - Real.arctan γ)) / 2 := by
      have h4γ : (4 : ℝ) * γ ≠ 0 := by
        intro h
        exact hγ (by linarith [h])
      field_simp
      ring
    have h2' : HasDerivAt (fun a : ℝ => Real.sin (2 * (γ * a - Real.arctan γ)) / (4 * γ))
        (Real.cos (2 * (γ * a - Real.arctan γ)) / 2) a := by
      rw [← hsimp]
      exact h2
    have hres : HasDerivAt
        (fun a : ℝ => a / 2 + Real.sin (2 * (γ * a - Real.arctan γ)) / (4 * γ))
        (1 / 2 + Real.cos (2 * (γ * a - Real.arctan γ)) / 2) a := h3.add h2'
    exact hres
  have hcont : IntervalIntegrable
      (fun a : ℝ => 1 / 2 + Real.cos (2 * (γ * a - Real.arctan γ)) / 2) MeasureTheory.volume 1 A :=
    Continuous.intervalIntegrable (by fun_prop) _ _
  rw [intervalIntegral.integral_congr (g := fun a : ℝ =>
      1 / 2 + Real.cos (2 * (γ * a - Real.arctan γ)) / 2) (fun a _ => hcongr a),
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont]
  ring

/-- **`(359)`: the aperture Cesàro mean of the squared phase is `1/2` for every nonzero
ordinate.** -/
theorem tendsto_cesaro_cos_sq_parityPhase {γ : ℝ} (hγ : γ ≠ 0) :
    Tendsto (fun A : ℝ => (1 / A) * ∫ a in (1 : ℝ)..A, Real.cos (parityPhase γ a) ^ 2)
      atTop (𝓝 (1 / 2)) := by
  have hγabs : (0 : ℝ) < |γ| := abs_pos.mpr hγ
  have hbound : ∀ A : ℝ, 1 ≤ A →
      ‖(1 / A) * (∫ a in (1 : ℝ)..A, Real.cos (parityPhase γ a) ^ 2) - 1 / 2‖
        ≤ (1 / 2 + 2 / (4 * |γ|)) / A := by
    intro A hA
    have hApos : (0 : ℝ) < A := by linarith
    rw [integral_cos_sq_parityPhase hγ A]
    set X : ℝ := 2 * (γ * A - Real.arctan γ) with hX
    set Y : ℝ := 2 * (γ * 1 - Real.arctan γ) with hY
    have hval : (1 / A) * ((A - 1) / 2 + (Real.sin X - Real.sin Y) / (4 * γ)) - 1 / 2
        = (-(1 / 2) + (Real.sin X - Real.sin Y) / (4 * γ)) / A := by
      field_simp
      ring
    rw [hval, Real.norm_eq_abs, abs_div, abs_of_pos hApos]
    have hnum : |Real.sin X - Real.sin Y| ≤ 2 := by
      have h1 := Real.neg_one_le_sin X
      have h2 := Real.sin_le_one X
      have h3 := Real.neg_one_le_sin Y
      have h4 := Real.sin_le_one Y
      rw [abs_le]
      constructor <;> linarith
    have h2 : |(Real.sin X - Real.sin Y) / (4 * γ)| ≤ 2 / (4 * |γ|) := by
      rw [abs_div]
      have hden : |4 * γ| = 4 * |γ| := by
        rw [abs_mul]
        norm_num
      rw [hden]
      have hpos : (0 : ℝ) < 4 * |γ| := by linarith
      rw [div_le_div_iff₀ hpos hpos]
      nlinarith [hnum, hpos]
    have habs : |(-(1 / 2) + (Real.sin X - Real.sin Y) / (4 * γ))| ≤ 1 / 2 + 2 / (4 * |γ|) := by
      refine le_trans (abs_add_le _ _) ?_
      have h1 : |(-(1 / 2) : ℝ)| = 1 / 2 := by norm_num
      rw [h1]
      linarith
    rw [div_le_div_iff₀ hApos hApos]
    nlinarith [habs, hApos]
  have hrate : Tendsto (fun A : ℝ => (1 / 2 + 2 / (4 * |γ|)) / A) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hzero : Tendsto
      (fun A : ℝ => (1 / A) * (∫ a in (1 : ℝ)..A, Real.cos (parityPhase γ a) ^ 2) - 1 / 2)
      atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hrate
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with A hA
    exact hbound A hA
  have hsum := hzero.add (tendsto_const_nhds (x := (1 / 2 : ℝ)))
  rw [zero_add] at hsum
  exact Filter.Tendsto.congr (fun A => by ring) hsum

end GaloisForLFunctions.RHTower
