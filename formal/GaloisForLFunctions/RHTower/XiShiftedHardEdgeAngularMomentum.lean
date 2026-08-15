import GaloisForLFunctions.RHTower.XiShiftedHardEdgeBernstein
import GaloisForLFunctions.RHTower.CosinePhaseParseval

/-!
# The Cayley angular-momentum operator

Lifting a function of the angle through the Cayley half-density,

`(U F)(x) = cos(psi(x)/2)·F(psi(x))`,   `psi(x) = 2 arctan(x/a)`,

turns the angular derivative into the first-order operator

`A_a = ((a² + x²)/(2a))·d/dx + x/(2a)`,

which is the real form of the card's `L_a = ((a²+x²)/(2a))(-i∂_x) − ix/(2a)`: the half-density
factor supplies exactly the extra `x/(2a)` term.  The lift is an isometry up to the factor `a/2`,

`∫_R (U F)² dx = (a/2)·∫_{-pi}^{pi} F²`,

so the `L²` Bernstein inequality for cosine polynomials transports verbatim: every angular-momentum
descendant of the rational hard-edge test obeys `‖(A_a/a)^m g‖₂ ≤ (N/a)^m ‖g‖₂`.
-/

open Set MeasureTheory

noncomputable section

namespace RHTower

/-- The Cayley half-density lift of a function of the angle. -/
def routeUCayleyLift (a : ℝ) (F : ℝ → ℝ) (x : ℝ) : ℝ :=
  Real.cos (routeUHardEdgeInverseChart a x / 2) * F (routeUHardEdgeInverseChart a x)

theorem routeUHardEdgeInverseChart_half (a x : ℝ) :
    routeUHardEdgeInverseChart a x / 2 = Real.arctan (x / a) := by
  rw [routeUHardEdgeInverseChart]
  ring

theorem cos_half_inverseChart_pos (a x : ℝ) :
    0 < Real.cos (routeUHardEdgeInverseChart a x / 2) := by
  rw [routeUHardEdgeInverseChart_half]
  exact Real.cos_arctan_pos _

theorem tan_half_inverseChart (a x : ℝ) :
    Real.tan (routeUHardEdgeInverseChart a x / 2) = x / a := by
  rw [routeUHardEdgeInverseChart_half, Real.tan_arctan]

theorem sin_half_inverseChart {a : ℝ} (ha : 0 < a) (x : ℝ) :
    Real.sin (routeUHardEdgeInverseChart a x / 2)
      = (x / a) * Real.cos (routeUHardEdgeInverseChart a x / 2) := by
  have hcos := cos_half_inverseChart_pos a x
  have htan := tan_half_inverseChart a x
  rw [Real.tan_eq_sin_div_cos] at htan
  have hane : a ≠ 0 := ne_of_gt ha
  field_simp at htan ⊢
  linarith [htan]

/-- The derivative of a Cayley lift. -/
theorem hasDerivAt_routeUCayleyLift {a : ℝ} (ha : 0 < a) {F F' : ℝ → ℝ}
    (hF : ∀ θ : ℝ, HasDerivAt F (F' θ) θ) (x : ℝ) :
    HasDerivAt (routeUCayleyLift a F)
      ((2 * a / (a ^ 2 + x ^ 2)) *
        (-(1 / 2) * Real.sin (routeUHardEdgeInverseChart a x / 2)
            * F (routeUHardEdgeInverseChart a x)
          + Real.cos (routeUHardEdgeInverseChart a x / 2)
            * F' (routeUHardEdgeInverseChart a x))) x := by
  have hchart := hasDerivAt_routeUHardEdgeInverseChart ha x
  have hhalf : HasDerivAt (fun y : ℝ => routeUHardEdgeInverseChart a y / 2)
      ((2 * a / (a ^ 2 + x ^ 2)) / 2) x := hchart.div_const 2
  have hcos : HasDerivAt (fun y : ℝ => Real.cos (routeUHardEdgeInverseChart a y / 2))
      (-Real.sin (routeUHardEdgeInverseChart a x / 2) * ((2 * a / (a ^ 2 + x ^ 2)) / 2)) x :=
    (Real.hasDerivAt_cos _).comp x hhalf
  have hFc : HasDerivAt (fun y : ℝ => F (routeUHardEdgeInverseChart a y))
      (F' (routeUHardEdgeInverseChart a x) * (2 * a / (a ^ 2 + x ^ 2))) x :=
    (hF (routeUHardEdgeInverseChart a x)).comp x hchart
  have hprod := hcos.mul hFc
  refine hprod.congr_deriv ?_
  ring

/-- **(CSHC.18) The Cayley angular-momentum operator is the angular derivative.** -/
theorem routeUCayleyMomentum_lift {a : ℝ} (ha : 0 < a) {F F' : ℝ → ℝ}
    (hF : ∀ θ : ℝ, HasDerivAt F (F' θ) θ) (x : ℝ) {D : ℝ}
    (hD : HasDerivAt (routeUCayleyLift a F) D x) :
    ((a ^ 2 + x ^ 2) / (2 * a)) * D + (x / (2 * a)) * routeUCayleyLift a F x
      = routeUCayleyLift a F' x := by
  have hane : a ≠ 0 := ne_of_gt ha
  have hpos : (0 : ℝ) < a ^ 2 + x ^ 2 := by positivity
  have hbase := hasDerivAt_routeUCayleyLift ha hF x
  have hDeq : D = (2 * a / (a ^ 2 + x ^ 2)) *
      (-(1 / 2) * Real.sin (routeUHardEdgeInverseChart a x / 2)
          * F (routeUHardEdgeInverseChart a x)
        + Real.cos (routeUHardEdgeInverseChart a x / 2)
          * F' (routeUHardEdgeInverseChart a x)) := hD.unique hbase
  rw [hDeq, routeUCayleyLift, routeUCayleyLift, sin_half_inverseChart ha x]
  field_simp
  ring

/-- The angular-momentum descendants of a Cayley lift. -/
def routeUAngularDescendant (a : ℝ) (m N : ℕ) (b : ℕ → ℝ) : ℝ → ℝ :=
  routeUCayleyLift a (cosPhasePoly m N b)

theorem hasDerivAt_routeUAngularDescendant {a : ℝ} (ha : 0 < a) (m N : ℕ) (b : ℕ → ℝ) (x : ℝ) :
    HasDerivAt (routeUAngularDescendant a m N b)
      ((2 * a / (a ^ 2 + x ^ 2)) *
        (-(1 / 2) * Real.sin (routeUHardEdgeInverseChart a x / 2)
            * cosPhasePoly m N b (routeUHardEdgeInverseChart a x)
          + Real.cos (routeUHardEdgeInverseChart a x / 2)
            * cosPhasePoly (m + 1) N b (routeUHardEdgeInverseChart a x))) x :=
  hasDerivAt_routeUCayleyLift ha (fun θ => hasDerivAt_cosPhasePoly m N b θ) x

/-- **(CSHC.18) on the descendants.**  The angular-momentum operator raises the descendant index. -/
theorem routeUCayleyMomentum_descendant {a : ℝ} (ha : 0 < a) (m N : ℕ) (b : ℕ → ℝ) (x : ℝ)
    {D : ℝ} (hD : HasDerivAt (routeUAngularDescendant a m N b) D x) :
    ((a ^ 2 + x ^ 2) / (2 * a)) * D + (x / (2 * a)) * routeUAngularDescendant a m N b x
      = routeUAngularDescendant a (m + 1) N b x :=
  routeUCayleyMomentum_lift ha (fun θ => hasDerivAt_cosPhasePoly m N b θ) x hD


/-! ## The lift is an isometry up to the mass factor -/

/-- **The Cayley `L²` identity for an arbitrary angular profile.** -/
theorem integral_routeUCayleyLift_sq {a : ℝ} (ha : 0 < a) (F : ℝ → ℝ) :
    (∫ x : ℝ, routeUCayleyLift a F x ^ 2)
      = (a / 2) * ∫ θ in Set.Ioo (-Real.pi) Real.pi, F θ ^ 2 := by
  have hchange := MeasureTheory.integral_image_eq_integral_abs_deriv_smul
    (s := Set.Ioo (-Real.pi) Real.pi)
    (f := routeUHardEdgeAngularChart a) (f' := routeUHardEdgeAngularJacobian a)
    measurableSet_Ioo
    (fun θ hθ => (hasDerivAt_routeUHardEdgeAngularChart
      (ne_of_gt (cos_half_pos_of_mem_Ioo hθ))).hasDerivWithinAt)
    (injOn_routeUHardEdgeAngularChart ha)
    (fun x => routeUCayleyLift a F x ^ 2)
  rw [image_routeUHardEdgeAngularChart ha, setIntegral_univ] at hchange
  rw [hchange, ← MeasureTheory.integral_const_mul]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo fun θ hθ => ?_
  have hcos := cos_half_pos_of_mem_Ioo hθ
  have hjac : |routeUHardEdgeAngularJacobian a θ| = a * (1 / Real.cos (θ / 2) ^ 2 * (1 / 2)) := by
    rw [routeUHardEdgeAngularJacobian, abs_of_pos (by positivity)]
  have hval : routeUCayleyLift a F (routeUHardEdgeAngularChart a θ)
      = Real.cos (θ / 2) * F θ := by
    rw [routeUCayleyLift, routeUHardEdgeInverseChart_angularChart ha hθ]
  rw [smul_eq_mul, hjac, hval, mul_pow]
  have hne : Real.cos (θ / 2) ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hcos)
  field_simp

theorem integral_Ioo_eq_intervalIntegral (F : ℝ → ℝ) :
    (∫ θ in Set.Ioo (-Real.pi) Real.pi, F θ)
      = ∫ θ in (-Real.pi)..Real.pi, F θ := by
  have hle : (-Real.pi : ℝ) ≤ Real.pi := by linarith [Real.pi_pos]
  rw [intervalIntegral.integral_of_le hle, MeasureTheory.integral_Ioc_eq_integral_Ioo]

/-- **(CSHC.19) The angular-momentum moment bound.**  Every descendant is bounded by the degree
power times the parent. -/
theorem integral_routeUAngularDescendant_sq_le {a : ℝ} (ha : 0 < a) (m N : ℕ) (b : ℕ → ℝ) :
    (∫ x : ℝ, routeUAngularDescendant a m N b x ^ 2)
      ≤ ((N : ℝ) ^ m) ^ 2 * ∫ x : ℝ, routeUAngularDescendant a 0 N b x ^ 2 := by
  rw [routeUAngularDescendant, routeUAngularDescendant, integral_routeUCayleyLift_sq ha,
    integral_routeUCayleyLift_sq ha, integral_Ioo_eq_intervalIntegral,
    integral_Ioo_eq_intervalIntegral, cosPhasePoly_zero]
  have hbase := integral_cosPhasePoly_sq_le m N b
  have hann : (0 : ℝ) ≤ a / 2 := by positivity
  nlinarith [hbase, hann]

/-- The zeroth descendant is the rational hard-edge test itself. -/
theorem routeUAngularDescendant_zero {a : ℝ} (ha : 0 < a) (p : Polynomial ℝ) {N : ℕ} {b : ℕ → ℝ}
    (hb : routeUHardEdgeAngularPoly a p
      = ∑ j ∈ Finset.range (N + 1),
        Polynomial.C (b j) * Polynomial.Chebyshev.T ℝ (j : ℤ)) :
    routeUAngularDescendant a 0 N b = routeUHardEdgeRationalTest a p := by
  funext x
  rw [routeUAngularDescendant, routeUCayleyLift, cosPhasePoly_zero, cos_half_mul_cosPoly,
    routeUHardEdgeRationalTest_eq_halfCosPoly ha p hb x]

/-- **(CSHC.19) in the form the Paley--Wiener passage uses.** -/
theorem integral_routeUAngularDescendant_sq_le_test {a : ℝ} (ha : 0 < a) (p : Polynomial ℝ)
    {N : ℕ} {b : ℕ → ℝ}
    (hb : routeUHardEdgeAngularPoly a p
      = ∑ j ∈ Finset.range (N + 1),
        Polynomial.C (b j) * Polynomial.Chebyshev.T ℝ (j : ℤ)) (m : ℕ) :
    (∫ x : ℝ, routeUAngularDescendant a m N b x ^ 2)
      ≤ ((N : ℝ) ^ m) ^ 2 * ∫ x : ℝ, routeUHardEdgeRationalTest a p x ^ 2 := by
  have hbase := integral_routeUAngularDescendant_sq_le ha m N b
  rwa [routeUAngularDescendant_zero ha p hb] at hbase

end RHTower

end
