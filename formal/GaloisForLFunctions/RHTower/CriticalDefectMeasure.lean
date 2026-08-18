import GaloisForLFunctions.RHTower.SquarefreeCriticalNormalCone

/-!
# The prime-scale defect measure and its reflection rigidity

`prime-valuation-dyadic-fermion-normal-cone-law`, equations `(13aa)`–`(13ac)`.

The critical coherent kernel is the total mass of the *prime-scale defect measure*

`dκ_{f,g}(t) = ½ (e^{f(t)} - e^{g(t)})² dt/t`,

so the scalar affinity remembers only the mass while the source incidence remembers its location in
logarithmic prime scale.  Relative to the critical source the reflection `f ↦ -f` is rigid: the two
defect densities agree exactly when the profile vanishes, because

`(e^x - 1)² - (e^{-x} - 1)² = 4 sinh(x) (cosh(x) - 1)`

and the only real zero of the right side is `x = 0`.  On the radial line this is the statement that
the reflection-odd scalar anomaly `Φ(u) - Φ(-u)` vanishes only at `u = 0`.
-/

open Filter Topology Set intervalIntegral

namespace RHTower

noncomputable section

/-- **`(13ac)`: the reflection anomaly of the defect density.** -/
theorem reflectionAnomaly_eq (x : ℝ) :
    (Real.exp x - 1) ^ 2 - (Real.exp (-x) - 1) ^ 2
      = 4 * Real.sinh x * (Real.cosh x - 1) := by
  rw [Real.sinh_eq, Real.cosh_eq, Real.exp_neg]
  have hx : Real.exp x ≠ 0 := Real.exp_ne_zero x
  field_simp
  ring

/-- **`(13ac)`: the anomaly vanishes exactly at the critical source.** -/
theorem reflectionAnomaly_eq_zero_iff (x : ℝ) :
    (Real.exp x - 1) ^ 2 = (Real.exp (-x) - 1) ^ 2 ↔ x = 0 := by
  constructor
  · intro h
    have h0 : (Real.exp x - 1) ^ 2 - (Real.exp (-x) - 1) ^ 2 = 0 := by rw [h]; ring
    rw [reflectionAnomaly_eq] at h0
    rcases mul_eq_zero.mp h0 with h1 | h2
    · rcases mul_eq_zero.mp h1 with h3 | h4
      · norm_num at h3
      · exact Real.sinh_eq_zero.mp h4
    · have hc : Real.cosh x = 1 := by linarith
      by_contra hx
      exact absurd hc (ne_of_gt (Real.one_lt_cosh.mpr hx))
  · intro h
    rw [h]
    norm_num

/-- **`(13ab)`: reflection rigidity of the prime-scale defect measure.**  If the two reflected
defect densities agree at every prime scale then the profile is identically zero. -/
theorem profileReflection_rigid {f : ℝ → ℝ}
    (h : ∀ t, (Real.exp (f t) - 1) ^ 2 = (Real.exp (-(f t)) - 1) ^ 2) : ∀ t, f t = 0 :=
  fun t => (reflectionAnomaly_eq_zero_iff (f t)).mp (h t)

/-- The reflection-odd anomaly density on the radial line, strictly positive off the origin. -/
theorem radialAnomaly_pos {u t : ℝ} (hu : 0 < u) (ht : 0 < t) :
    0 < divProfile (coherentProfile u 0) t - divProfile (coherentProfile (-u) 0) t := by
  have hne : t ≠ 0 := ne_of_gt ht
  have hval : divProfile (coherentProfile u 0) t - divProfile (coherentProfile (-u) 0) t
      = ((Real.exp (u * t) - 1) ^ 2 - (Real.exp (-(u * t)) - 1) ^ 2) / t := by
    rw [divProfile, divProfile, if_neg hne, if_neg hne, coherentProfile, coherentProfile]
    rw [show (0 : ℝ) * t = 0 by ring, Real.exp_zero]
    rw [show -u * t = -(u * t) by ring]
    ring
  rw [hval, reflectionAnomaly_eq]
  have hut : 0 < u * t := mul_pos hu ht
  have hs : 0 < Real.sinh (u * t) := Real.sinh_pos_iff.mpr hut
  have hc : 1 < Real.cosh (u * t) := Real.one_lt_cosh.mpr (ne_of_gt hut)
  have : 0 < 4 * Real.sinh (u * t) * (Real.cosh (u * t) - 1) := by nlinarith
  positivity

/-- **The reflection-odd scalar anomaly is strictly positive off the critical source.** -/
theorem coherentExponent_lt_of_pos {u : ℝ} (hu : 0 < u) :
    coherentExponent (-u) 0 < coherentExponent u 0 := by
  have hcont1 : ContinuousOn (divProfile (coherentProfile u 0)) (Set.Icc 0 1) :=
    continuousOn_divProfile_coherentProfile u 0
  have hcont2 : ContinuousOn (divProfile (coherentProfile (-u) 0)) (Set.Icc 0 1) :=
    continuousOn_divProfile_coherentProfile (-u) 0
  have hint1 : IntervalIntegrable (divProfile (coherentProfile u 0)) MeasureTheory.volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)]
    exact hcont1.integrableOn_compact isCompact_Icc
  have hint2 : IntervalIntegrable (divProfile (coherentProfile (-u) 0)) MeasureTheory.volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)]
    exact hcont2.integrableOn_compact isCompact_Icc
  have hpos : 0 < ∫ t in (0 : ℝ)..1,
      (divProfile (coherentProfile u 0) t - divProfile (coherentProfile (-u) 0) t) := by
    refine intervalIntegral.intervalIntegral_pos_of_pos_on (hint1.sub hint2) ?_ (by norm_num)
    intro t ht
    exact radialAnomaly_pos hu ht.1
  rw [intervalIntegral.integral_sub hint1 hint2] at hpos
  rw [coherentExponent, coherentExponent]
  linarith

/-- **`(13ab)` on the radial line.**  The reflection-odd anomaly `Φ(u) − Φ(−u)` vanishes exactly at
the critical source. -/
theorem coherentExponent_reflection_eq_iff (u : ℝ) :
    coherentExponent u 0 = coherentExponent (-u) 0 ↔ u = 0 := by
  constructor
  · intro h
    rcases lt_trichotomy u 0 with hu | hu | hu
    · have := coherentExponent_lt_of_pos (u := -u) (by linarith)
      rw [neg_neg] at this
      linarith
    · exact hu
    · have := coherentExponent_lt_of_pos hu
      linarith
  · intro h
    rw [h, neg_zero]

end

end RHTower
