import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Thermal Poisson bulk symbol: magnitude and orientation

The full-line kernel `sech²(x/2)` has Fourier symbol
`4πξ / sinh(πξ)`. Its evenness loses frequency orientation; strict
decrease on positive frequencies lets the clock commutator recover it.
The Fourier-transform identification and operator transport remain
paper results, not assertions of this file.
-/

namespace RHTower

open Real Set

private noncomputable def edgeNumerator (t : ℝ) : ℝ :=
  Real.sinh t - t * Real.cosh t

private theorem hasDerivAt_edgeNumerator (t : ℝ) :
    HasDerivAt edgeNumerator (-t * Real.sinh t) t := by
  have h := (Real.hasDerivAt_sinh t).sub
    ((hasDerivAt_id t).mul (Real.hasDerivAt_cosh t))
  have hfun : (Real.sinh - id * Real.cosh : ℝ → ℝ) = edgeNumerator := by
    funext x
    rfl
  have hcoeff : Real.cosh t - (1 * Real.cosh t + id t * Real.sinh t) =
      -t * Real.sinh t := by
    dsimp
    ring
  rw [hfun, hcoeff] at h
  exact h

private theorem edgeNumerator_neg {t : ℝ} (ht : 0 < t) :
    edgeNumerator t < 0 := by
  have hcont : ContinuousOn edgeNumerator (Ici (0 : ℝ)) := by
    exact (Real.continuous_sinh.sub
      (continuous_id.mul Real.continuous_cosh)).continuousOn
  have hanti : StrictAntiOn edgeNumerator (Ici (0 : ℝ)) := by
    apply strictAntiOn_of_deriv_neg (convex_Ici (0 : ℝ)) hcont
    intro x hx
    have hx0 : 0 < x := by simpa using hx
    rw [(hasDerivAt_edgeNumerator x).deriv]
    have hs : 0 < Real.sinh x := Real.sinh_pos_iff.mpr hx0
    nlinarith [mul_pos hx0 hs]
  have h := hanti (by simp : (0 : ℝ) ∈ Ici 0)
    (by simp [le_of_lt ht] : t ∈ Ici (0 : ℝ)) ht
  simpa [edgeNumerator] using h

private noncomputable def thermalRatio (t : ℝ) : ℝ :=
  t / Real.sinh t

private theorem hasDerivAt_thermalRatio {t : ℝ} (ht : 0 < t) :
    HasDerivAt thermalRatio
      (edgeNumerator t / Real.sinh t ^ 2) t := by
  have hs : Real.sinh t ≠ 0 := ne_of_gt (Real.sinh_pos_iff.mpr ht)
  have h := (hasDerivAt_id t).div (Real.hasDerivAt_sinh t) hs
  have hfun : (id / Real.sinh : ℝ → ℝ) = thermalRatio := by
    funext x
    rfl
  have hcoeff :
      (1 * Real.sinh t - id t * Real.cosh t) / Real.sinh t ^ 2 =
        edgeNumerator t / Real.sinh t ^ 2 := by
    dsimp [edgeNumerator]
    ring
  rw [hfun, hcoeff] at h
  exact h

private theorem thermalRatio_strictAntiOn_pos :
    StrictAntiOn thermalRatio (Ioi (0 : ℝ)) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioi (0 : ℝ))
  · have hc : ContinuousOn (fun x : ℝ => x / Real.sinh x)
        (Ioi (0 : ℝ)) :=
      continuous_id.continuousOn.div Real.continuous_sinh.continuousOn
        (fun x hx => ne_of_gt (Real.sinh_pos_iff.mpr hx))
    exact hc
  · intro x hx
    have hx0 : 0 < x := by simpa using hx
    rw [(hasDerivAt_thermalRatio hx0).deriv]
    exact div_neg_of_neg_of_pos (edgeNumerator_neg hx0)
      (sq_pos_of_pos (Real.sinh_pos_iff.mpr hx0))

private theorem thermalRatio_even (t : ℝ) :
    thermalRatio (-t) = thermalRatio t := by
  simp [thermalRatio, Real.sinh_neg]

/-- The thermal Poisson bulk multiplier, with its continuous value at zero. -/
noncomputable def stcPoissonThermalSymbol (ξ : ℝ) : ℝ :=
  if ξ = 0 then 4 else 4 * thermalRatio (Real.pi * ξ)

theorem stcPoissonThermalSymbol_even (ξ : ℝ) :
    stcPoissonThermalSymbol (-ξ) = stcPoissonThermalSymbol ξ := by
  by_cases hξ : ξ = 0
  · subst ξ
    simp [stcPoissonThermalSymbol]
  · have hn : -ξ ≠ 0 := neg_ne_zero.mpr hξ
    have harg : Real.pi * (-ξ) = -(Real.pi * ξ) := by ring
    simp [stcPoissonThermalSymbol, hξ, hn, harg, thermalRatio_even]

theorem stcPoissonThermalSymbol_strictAntiOn_pos :
    StrictAntiOn stcPoissonThermalSymbol (Ioi (0 : ℝ)) := by
  intro a ha b hb hab
  have hpa : 0 < Real.pi * a := mul_pos Real.pi_pos ha
  have hpb : 0 < Real.pi * b := mul_pos Real.pi_pos hb
  have hpab : Real.pi * a < Real.pi * b :=
    mul_lt_mul_of_pos_left hab Real.pi_pos
  have h := thermalRatio_strictAntiOn_pos hpa hpb hpab
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hb0 : b ≠ 0 := ne_of_gt hb
  simpa [stcPoissonThermalSymbol, ha0, hb0] using
    (mul_lt_mul_of_pos_left h (by norm_num : (0 : ℝ) < 4))

end RHTower
