import Mathlib

/-!
# The physical logarithmic chart

The substitution `s = e^{-L}` carries the punctured unit interval onto the positive logarithmic
ray, and it is the chart in which the boundary germ of a Suzuki profile becomes a profile on
`[0, ∞)`.  Two statements are needed downstream: the integral transfer, and the fact that the
half-weight `e^{-L/2}` is exactly what makes the chart an `L²` isometry — which is why the *half*
weight, and no other, is critical.
-/

open MeasureTheory Set

namespace GaloisForLFunctions.HTGeometry

/-- The physical logarithmic chart `L ↦ e^{-L}`, carrying the ray onto the unit interval. -/
noncomputable def logChart (L : ℝ) : ℝ := Real.exp (-L)

theorem logChart_pos (L : ℝ) : 0 < logChart L := Real.exp_pos _

theorem hasDerivAt_logChart (L : ℝ) : HasDerivAt logChart (-Real.exp (-L)) L := by
  show HasDerivAt (fun L : ℝ => Real.exp (-L)) (-Real.exp (-L)) L
  have h : HasDerivAt (fun L : ℝ => -L) (-1 : ℝ) L := hasDerivAt_neg L
  simpa using h.exp

theorem injOn_logChart : InjOn logChart (Ioi (0 : ℝ)) := by
  intro a _ b _ hab
  have := Real.exp_injective hab
  linarith

theorem image_logChart_Ioi : logChart '' Ioi (0 : ℝ) = Ioo (0 : ℝ) 1 := by
  ext s
  constructor
  · rintro ⟨L, hL, rfl⟩
    refine ⟨Real.exp_pos _, ?_⟩
    rw [logChart, show (1 : ℝ) = Real.exp 0 by simp]
    exact Real.exp_lt_exp.mpr (by simpa using hL)
  · rintro ⟨hs0, hs1⟩
    refine ⟨-Real.log s, ?_, ?_⟩
    · simp only [mem_Ioi, neg_pos]
      exact Real.log_neg hs0 hs1
    · rw [logChart, neg_neg, Real.exp_log hs0]

/-- **The chart transfers integrals.**  `∫_0^1 f = ∫_0^∞ f(e^{-L}) e^{-L} dL`. -/
theorem integral_Ioo_eq_integral_logChart (f : ℝ → ℝ) :
    (∫ s in Ioo (0 : ℝ) 1, f s) = ∫ L in Ioi (0 : ℝ), Real.exp (-L) * f (Real.exp (-L)) := by
  have hderiv : ∀ L ∈ Ioi (0 : ℝ),
      HasDerivWithinAt logChart (-Real.exp (-L)) (Ioi (0 : ℝ)) L :=
    fun L _ => (hasDerivAt_logChart L).hasDerivWithinAt
  have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hderiv injOn_logChart f
  rw [image_logChart_Ioi] at h
  rw [h]
  refine setIntegral_congr_fun measurableSet_Ioi fun L _ => ?_
  rw [abs_neg, abs_of_pos (Real.exp_pos _), smul_eq_mul, logChart]

/-- **The half weight is the critical one.**  Conjugating by `e^{-L/2}` makes the chart an `L²`
isometry, so the boundary energy of a profile on the unit interval is the ordinary energy of its
half-weighted transport on the ray. -/
theorem integral_sq_logChart (u : ℝ → ℝ) :
    (∫ s in Ioo (0 : ℝ) 1, u s ^ 2)
      = ∫ L in Ioi (0 : ℝ), (Real.exp (-L / 2) * u (Real.exp (-L))) ^ 2 := by
  rw [integral_Ioo_eq_integral_logChart (fun s => u s ^ 2)]
  refine setIntegral_congr_fun measurableSet_Ioi fun L _ => ?_
  have hsq : (Real.exp (-L / 2)) ^ 2 = Real.exp (-L) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [mul_pow, hsq]

end GaloisForLFunctions.HTGeometry
