import GaloisForLFunctions.RHTower.XiShiftedHardEdgeRationalTest

/-!
# The angular change of variables for the rational hard-edge test

The map `θ ↦ a·tan(θ/2)` is a bijection from `(-π, π)` onto the whole line, and the half-density
factor `cos(θ/2)` of the rational test exactly cancels the Jacobian `(a/2)·cos^{-2}(θ/2)`.  Hence

`∫_ℝ g_{a,p}(x)² dx = (a/2)·∫_{-π}^{π} q_{a,p}(θ)² dθ`,

with `q_{a,p}` a real trigonometric polynomial of degree at most `deg p`.  Every weighted quantity
of the completed source transports the same way; this is the identity that turns a spectral integral
into a finite-aperture angular integral.
-/

open Set MeasureTheory

noncomputable section

namespace RHTower

/-- The Cayley angular chart of the hard-edge mass. -/
def routeUHardEdgeAngularChart (a θ : ℝ) : ℝ := a * Real.tan (θ / 2)

/-- The Jacobian of the angular chart. -/
def routeUHardEdgeAngularJacobian (a θ : ℝ) : ℝ := a * (1 / Real.cos (θ / 2) ^ 2 * (1 / 2))

theorem cos_half_pos_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo (-Real.pi) Real.pi) :
    0 < Real.cos (θ / 2) := by
  refine Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩
  · linarith [hθ.1]
  · linarith [hθ.2]

theorem hasDerivAt_routeUHardEdgeAngularChart {a θ : ℝ}
    (hθ : Real.cos (θ / 2) ≠ 0) :
    HasDerivAt (routeUHardEdgeAngularChart a) (routeUHardEdgeAngularJacobian a θ) θ := by
  have h1 : HasDerivAt (fun u : ℝ => u / 2) (1 / 2 : ℝ) θ := (hasDerivAt_id θ).div_const 2
  exact ((Real.hasDerivAt_tan hθ).comp θ h1).const_mul a

/-- The angular chart is injective on the principal interval. -/
theorem injOn_routeUHardEdgeAngularChart {a : ℝ} (ha : 0 < a) :
    Set.InjOn (routeUHardEdgeAngularChart a) (Set.Ioo (-Real.pi) Real.pi) := by
  intro u hu v hv huv
  have hmem : ∀ w ∈ Set.Ioo (-Real.pi) Real.pi,
      w / 2 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    intro w hw
    exact ⟨by linarith [hw.1], by linarith [hw.2]⟩
  have htan : Real.tan (u / 2) = Real.tan (v / 2) := by
    have := huv
    rw [routeUHardEdgeAngularChart, routeUHardEdgeAngularChart] at this
    exact mul_left_cancel₀ (ne_of_gt ha) this
  have := Real.injOn_tan (hmem u hu) (hmem v hv) htan
  linarith

/-- The angular chart covers the whole spectral line. -/
theorem image_routeUHardEdgeAngularChart {a : ℝ} (ha : 0 < a) :
    routeUHardEdgeAngularChart a '' Set.Ioo (-Real.pi) Real.pi = Set.univ := by
  refine Set.eq_univ_of_forall fun y => ?_
  have hsurj : Real.tan '' Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) = Set.univ :=
    Real.image_tan_Ioo
  have hy : y / a ∈ (Set.univ : Set ℝ) := Set.mem_univ _
  rw [← hsurj] at hy
  obtain ⟨u, hu, hval⟩ := hy
  refine ⟨2 * u, ⟨by linarith [hu.1], by linarith [hu.2]⟩, ?_⟩
  rw [routeUHardEdgeAngularChart, show 2 * u / 2 = u by ring, hval]
  field_simp

/-- **(CSHC.8) The angular `L²` identity.**  The half-density factor of the rational test cancels
the Jacobian of the Cayley chart. -/
theorem integral_routeUHardEdgeRationalTest_sq {a : ℝ} (ha : 0 < a) (p : Polynomial ℝ) :
    (∫ x : ℝ, routeUHardEdgeRationalTest a p x ^ 2)
      = (a / 2) * ∫ θ in Set.Ioo (-Real.pi) Real.pi,
          ((routeUHardEdgeAngularPoly a p).eval (Real.cos θ)) ^ 2 := by
  have hchange := MeasureTheory.integral_image_eq_integral_abs_deriv_smul
    (s := Set.Ioo (-Real.pi) Real.pi)
    (f := routeUHardEdgeAngularChart a) (f' := routeUHardEdgeAngularJacobian a)
    measurableSet_Ioo
    (fun θ hθ => (hasDerivAt_routeUHardEdgeAngularChart
      (ne_of_gt (cos_half_pos_of_mem_Ioo hθ))).hasDerivWithinAt)
    (injOn_routeUHardEdgeAngularChart ha)
    (fun x => routeUHardEdgeRationalTest a p x ^ 2)
  rw [image_routeUHardEdgeAngularChart ha, setIntegral_univ] at hchange
  rw [hchange, ← MeasureTheory.integral_const_mul]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo fun θ hθ => ?_
  have hcos := cos_half_pos_of_mem_Ioo hθ
  have hjac : |routeUHardEdgeAngularJacobian a θ| = a * (1 / Real.cos (θ / 2) ^ 2 * (1 / 2)) := by
    rw [routeUHardEdgeAngularJacobian, abs_of_pos (by positivity)]
  have hval : routeUHardEdgeRationalTest a p (routeUHardEdgeAngularChart a θ)
      = Real.cos (θ / 2) * (routeUHardEdgeAngularPoly a p).eval (Real.cos θ) :=
    routeUHardEdgeRationalTest_tan ha p hcos
  rw [smul_eq_mul, hjac, hval, mul_pow]
  have hne : Real.cos (θ / 2) ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hcos)
  field_simp

end RHTower

end
