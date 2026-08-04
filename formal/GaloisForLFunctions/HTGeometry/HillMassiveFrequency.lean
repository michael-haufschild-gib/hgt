import GaloisForLFunctions.HTGeometry.HillFlowFrequencyDependence

/-!
# The massive frequency of a time-dependent principal part

For the field equation of a massive species on the chart `-dt² + c(t)²δ`, the frequency of the
fibrewise oscillator is not `c(t)·s` but

`ω(t) = √(m² + c(t)²s²)`.

The energy estimate needs the logarithmic derivative of that frequency to be bounded independently of
both parameters, and it is: differentiating the square root gives `ω' = c c' s²/ω`, and `c²s² ≤ ω²`
absorbs the frequency, leaving `|ω'| ≤ (|c'|/c)·ω`. The constant is the one of the speed alone — the
mass and the spatial frequency drop out.
-/

namespace GaloisForLFunctions.HTGeometry

open Set

section MassiveFrequency

variable {c dc : ℝ → ℝ} {m s K C S : ℝ}

/-- The frequency of the massive oscillator at spatial frequency `s`. -/
noncomputable def massiveFreq (m : ℝ) (c : ℝ → ℝ) (s : ℝ) (t : ℝ) : ℝ :=
  Real.sqrt (m ^ 2 + (c t * s) ^ 2)

theorem massiveFreq_pos (hm : 0 < m) (c : ℝ → ℝ) (s t : ℝ) : 0 < massiveFreq m c s t := by
  refine Real.sqrt_pos.mpr ?_
  have h1 : (0 : ℝ) < m ^ 2 := by positivity
  have h2 : (0 : ℝ) ≤ (c t * s) ^ 2 := sq_nonneg _
  linarith

theorem massiveFreq_sq (hm : 0 < m) (c : ℝ → ℝ) (s t : ℝ) :
    massiveFreq m c s t ^ 2 = m ^ 2 + (c t * s) ^ 2 := by
  refine Real.sq_sqrt ?_
  have h1 : (0 : ℝ) < m ^ 2 := by positivity
  have h2 : (0 : ℝ) ≤ (c t * s) ^ 2 := sq_nonneg _
  linarith

theorem continuous_massiveFreq (hc : Continuous c) (m s : ℝ) :
    Continuous (massiveFreq m c s) := by
  refine Real.continuous_sqrt.comp ?_
  exact continuous_const.add ((hc.mul continuous_const).pow 2)

/-- The frequency is bounded by the mass and the speed. -/
theorem massiveFreq_sq_le (hm : 0 < m) (hC : ∀ r, c r ^ 2 ≤ C ^ 2) (hs : s ^ 2 ≤ S ^ 2)
    (t : ℝ) :
    massiveFreq m c s t ^ 2 ≤ m ^ 2 + C ^ 2 * S ^ 2 := by
  rw [massiveFreq_sq hm]
  have hfac : (c t * s) ^ 2 = c t ^ 2 * s ^ 2 := by ring
  have hle : c t ^ 2 * s ^ 2 ≤ C ^ 2 * S ^ 2 := by
    have h1 : (0 : ℝ) ≤ c t ^ 2 := sq_nonneg _
    have h2 : (0 : ℝ) ≤ s ^ 2 := sq_nonneg _
    nlinarith [hC t, sq_nonneg C, sq_nonneg S]
  rw [hfac]
  linarith

/-- **The derivative of the massive frequency.** -/
theorem hasDerivAt_massiveFreq (hm : 0 < m) (hc : ∀ t, HasDerivAt c (dc t) t) (s t : ℝ) :
    HasDerivAt (massiveFreq m c s) (c t * dc t * s ^ 2 / massiveFreq m c s t) t := by
  have hinner : HasDerivAt (fun r => m ^ 2 + (c r * s) ^ 2)
      (2 * (c t * s) * (dc t * s)) t := by
    have h := ((hc t).mul_const s).pow 2
    simpa using (h.const_add (m ^ 2))
  have hpos : 0 < m ^ 2 + (c t * s) ^ 2 := by
    have h1 : (0 : ℝ) < m ^ 2 := by positivity
    have h2 : (0 : ℝ) ≤ (c t * s) ^ 2 := sq_nonneg _
    linarith
  have hsqrt := hinner.sqrt (ne_of_gt hpos)
  have hval : 2 * (c t * s) * (dc t * s) / (2 * Real.sqrt (m ^ 2 + (c t * s) ^ 2))
      = c t * dc t * s ^ 2 / massiveFreq m c s t := by
    rw [massiveFreq]
    have hne : Real.sqrt (m ^ 2 + (c t * s) ^ 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hpos)
    field_simp
    ring
  rw [hval] at hsqrt
  exact hsqrt

/-- **The logarithmic derivative of the massive frequency is that of the speed** — uniformly in the
mass and in the spatial frequency. -/
theorem abs_deriv_massiveFreq_le (hm : 0 < m) (hcpos : ∀ t, 0 < c t)
    (hK : ∀ t, |dc t| ≤ K * c t) (s t : ℝ) :
    |c t * dc t * s ^ 2 / massiveFreq m c s t| ≤ K * massiveFreq m c s t := by
  have hωpos : 0 < massiveFreq m c s t := massiveFreq_pos hm c s t
  have hct : 0 < c t := hcpos t
  have hK0 : 0 ≤ K := by
    have h0 : (0 : ℝ) ≤ |dc t| := abs_nonneg _
    have := hK t
    nlinarith
  have hnum : |c t * dc t * s ^ 2| ≤ K * (c t * s) ^ 2 := by
    have habs : |c t * dc t * s ^ 2| = c t * |dc t| * s ^ 2 := by
      rw [abs_mul, abs_mul, abs_of_pos hct, abs_of_nonneg (sq_nonneg s)]
    rw [habs]
    have := hK t
    nlinarith [sq_nonneg s, le_of_lt hct]
  have hsq : (c t * s) ^ 2 ≤ massiveFreq m c s t ^ 2 := by
    rw [massiveFreq_sq hm]
    nlinarith [sq_nonneg m]
  rw [abs_div, abs_of_pos hωpos, div_le_iff₀ hωpos]
  calc |c t * dc t * s ^ 2| ≤ K * (c t * s) ^ 2 := hnum
    _ ≤ K * massiveFreq m c s t ^ 2 := mul_le_mul_of_nonneg_left hsq hK0
    _ = K * massiveFreq m c s t * massiveFreq m c s t := by ring

/-- **The massive oscillator inherits the energy bound**, with a constant that sees neither the mass
nor the spatial frequency. -/
theorem hillEnergy_massive_le (hm : 0 < m) (hc : Continuous c) (hcd : ∀ t, HasDerivAt c (dc t) t)
    (hcpos : ∀ t, 0 < c t) (hK : ∀ t, |dc t| ≤ K * c t) (hC : ∀ r, c r ^ 2 ≤ C ^ 2)
    (hs : s ^ 2 ≤ S ^ 2) (y₀ : ℝ × ℝ) {t a b : ℝ}
    (ht : t ∈ Icc a b) :
    hillEnergy (massiveFreq m c s) (hillSolution (massiveFreq m c s) y₀)
        (hillSolutionDeriv (massiveFreq m c s) y₀) t ≤
      hillEnergy (massiveFreq m c s) (hillSolution (massiveFreq m c s) y₀)
        (hillSolutionDeriv (massiveFreq m c s) y₀) a * Real.exp (2 * K * (t - a)) :=
  hillEnergy_hillSolution_le (M := max 1 (m ^ 2 + C ^ 2 * S ^ 2))
    (continuous_massiveFreq hc m s) (le_max_left _ _)
    (fun r => (massiveFreq_sq_le hm hC hs r).trans (le_max_right _ _))
    (fun r => hasDerivAt_massiveFreq hm hcd s r) (fun r => massiveFreq_pos hm c s r)
    (fun r => abs_deriv_massiveFreq_le hm hcpos hK s r) y₀ ht

end MassiveFrequency

end GaloisForLFunctions.HTGeometry
