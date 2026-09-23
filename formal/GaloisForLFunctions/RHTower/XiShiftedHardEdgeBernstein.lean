import GaloisForLFunctions.RHTower.XiShiftedHardEdgeHalfExpansion
import GaloisForLFunctions.RHTower.XiShiftedHardEdgePrimeCone

/-!
# The rational Bernstein estimate

The inverse Cayley chart `ψ(x) = 2·arctan(x/a)` is globally smooth and maps the line onto
`(-π, π)`, so the rational hard-edge test factors as `g_{a,p} = G ∘ ψ` with `G` a half-integer
cosine polynomial of degree at most `deg p`.  No inverse function theorem is needed: the chain rule
applies directly, and the Jacobian `ψ'(x) = 2a/(a²+x²)` cancels against the chart weight.  With the
`L²` Bernstein inequality for `G` this gives the translation modulus

`‖g'‖₂² ≤ (4(N+1/2)²/a²)·‖g‖₂²`,

uniform over every coefficient vector at fixed scaled degree.
-/

open Set MeasureTheory

noncomputable section

namespace RHTower

/-- The inverse Cayley chart. -/
def routeUHardEdgeInverseChart (a x : ℝ) : ℝ := 2 * Real.arctan (x / a)

theorem routeUHardEdgeInverseChart_mem_Ioo (a x : ℝ) :
    routeUHardEdgeInverseChart a x ∈ Set.Ioo (-Real.pi) Real.pi := by
  rw [routeUHardEdgeInverseChart]
  have h := Real.arctan_mem_Ioo (x / a)
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

theorem routeUHardEdgeAngularChart_inverseChart {a : ℝ} (ha : 0 < a) (x : ℝ) :
    routeUHardEdgeAngularChart a (routeUHardEdgeInverseChart a x) = x := by
  rw [routeUHardEdgeAngularChart, routeUHardEdgeInverseChart,
    show 2 * Real.arctan (x / a) / 2 = Real.arctan (x / a) by ring, Real.tan_arctan]
  field_simp

theorem routeUHardEdgeInverseChart_angularChart {a : ℝ} (ha : 0 < a) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo (-Real.pi) Real.pi) :
    routeUHardEdgeInverseChart a (routeUHardEdgeAngularChart a θ) = θ := by
  have hmem : θ / 2 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
  rw [routeUHardEdgeInverseChart, routeUHardEdgeAngularChart,
    show a * Real.tan (θ / 2) / a = Real.tan (θ / 2) by field_simp,
    Real.arctan_tan hmem.1 hmem.2]
  ring

theorem hasDerivAt_routeUHardEdgeInverseChart {a : ℝ} (ha : 0 < a) (x : ℝ) :
    HasDerivAt (routeUHardEdgeInverseChart a) (2 * a / (a ^ (2 : ℕ) + x ^ (2 : ℕ))) x := by
  have hane : a ≠ 0 := ne_of_gt ha
  have h1 : HasDerivAt (fun u : ℝ => u / a) (1 / a) x := by
    simpa using (hasDerivAt_id x).div_const a
  have h3 : HasDerivAt (fun u : ℝ => 2 * Real.arctan (u / a))
      (2 * (1 / (1 + (x / a) ^ (2 : ℕ)) * (1 / a))) x := h1.arctan.const_mul (2 : ℝ)
  have hval : (2 : ℝ) * (1 / (1 + (x / a) ^ (2 : ℕ)) * (1 / a)) = 2 * a / (a ^ (2 : ℕ) + x ^ (2 : ℕ)) := by
    have hden : (0 : ℝ) < a ^ (2 : ℕ) + x ^ (2 : ℕ) := by positivity
    field_simp
  rw [hval] at h3
  exact h3

/-- The half-integer cosine polynomial is differentiable with the termwise derivative. -/
theorem hasDerivAt_halfCosPoly (M : ℕ) (c : ℕ → ℝ) (θ : ℝ) :
    HasDerivAt (halfCosPoly M c) (halfCosPolyDeriv M c θ) θ := by
  show HasDerivAt (fun θ => ∑ j ∈ Finset.range (M + 1), c j * Real.cos (((j : ℝ) + 1 / 2) * θ))
    (∑ j ∈ Finset.range (M + 1),
      (-(c j * ((j : ℝ) + 1 / 2))) * Real.sin (((j : ℝ) + 1 / 2) * θ)) θ
  refine HasDerivAt.fun_sum fun j _ => ?_
  have hlin : HasDerivAt (fun u : ℝ => ((j : ℝ) + 1 / 2) * u) ((j : ℝ) + 1 / 2) θ := by
    simpa using (hasDerivAt_id θ).const_mul ((j : ℝ) + 1 / 2)
  have h := hlin.cos.const_mul (c j)
  have hval : c j * (-Real.sin (((j : ℝ) + 1 / 2) * θ) * ((j : ℝ) + 1 / 2))
      = (-(c j * ((j : ℝ) + 1 / 2))) * Real.sin (((j : ℝ) + 1 / 2) * θ) := by ring
  rwa [hval] at h

/-- **The rational hard-edge test is a half-integer cosine polynomial in the inverse chart.** -/
theorem routeUHardEdgeRationalTest_eq_halfCosPoly {a : ℝ} (ha : 0 < a) (p : Polynomial ℝ)
    {N : ℕ} {b : ℕ → ℝ}
    (hb : routeUHardEdgeAngularPoly a p
      = ∑ j ∈ Finset.range (N + 1),
        Polynomial.C (b j) * Polynomial.Chebyshev.T ℝ (j : ℤ)) (x : ℝ) :
    routeUHardEdgeRationalTest a p x
      = halfCosPoly N (halfShiftCoeff N b) (routeUHardEdgeInverseChart a x) := by
  have hmem := routeUHardEdgeInverseChart_mem_Ioo a x
  have hcos := cos_half_pos_of_mem_Ioo hmem
  have hchart : routeUHardEdgeAngularChart a (routeUHardEdgeInverseChart a x) = x :=
    routeUHardEdgeAngularChart_inverseChart ha x
  have hstep : routeUHardEdgeRationalTest a p
      (routeUHardEdgeAngularChart a (routeUHardEdgeInverseChart a x))
      = Real.cos (routeUHardEdgeInverseChart a x / 2)
        * (routeUHardEdgeAngularPoly a p).eval
            (Real.cos (routeUHardEdgeInverseChart a x)) :=
    routeUHardEdgeRationalTest_tan ha p hcos
  rw [hchart] at hstep
  rw [hstep, eval_cos_of_chebyshev_expansion hb, ← cosPoly, cos_half_mul_cosPoly]

/-- The derivative of the rational hard-edge test in the inverse chart. -/
theorem hasDerivAt_routeUHardEdgeRationalTest {a : ℝ} (ha : 0 < a) (p : Polynomial ℝ)
    {N : ℕ} {b : ℕ → ℝ}
    (hb : routeUHardEdgeAngularPoly a p
      = ∑ j ∈ Finset.range (N + 1),
        Polynomial.C (b j) * Polynomial.Chebyshev.T ℝ (j : ℤ)) (x : ℝ) :
    HasDerivAt (routeUHardEdgeRationalTest a p)
      (halfCosPolyDeriv N (halfShiftCoeff N b) (routeUHardEdgeInverseChart a x)
        * (2 * a / (a ^ (2 : ℕ) + x ^ (2 : ℕ)))) x := by
  have hcomp := (hasDerivAt_halfCosPoly N (halfShiftCoeff N b)
      (routeUHardEdgeInverseChart a x)).comp x (hasDerivAt_routeUHardEdgeInverseChart ha x)
  refine hcomp.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
  simpa [Function.comp_def] using routeUHardEdgeRationalTest_eq_halfCosPoly ha p hb y

/-- **(CSHC.4)/(CSHC.17) The rational Bernstein estimate.**  The squared `L²` norm of the derivative
of the rational hard-edge test is at most `4(N+1/2)²/a²` times that of the test itself. -/
theorem integral_deriv_routeUHardEdgeRationalTest_sq_le {a : ℝ} (ha : 0 < a) (p : Polynomial ℝ)
    {N : ℕ} {b : ℕ → ℝ}
    (hb : routeUHardEdgeAngularPoly a p
      = ∑ j ∈ Finset.range (N + 1),
        Polynomial.C (b j) * Polynomial.Chebyshev.T ℝ (j : ℤ)) :
    (∫ x : ℝ, (halfCosPolyDeriv N (halfShiftCoeff N b) (routeUHardEdgeInverseChart a x)
        * (2 * a / (a ^ (2 : ℕ) + x ^ (2 : ℕ)))) ^ (2 : ℕ))
      ≤ (4 * ((N : ℝ) + 1 / 2) ^ (2 : ℕ) / a ^ (2 : ℕ))
          * ∫ x : ℝ, routeUHardEdgeRationalTest a p x ^ (2 : ℕ) := by
  obtain ⟨c, hcdef⟩ : ∃ c : ℕ → ℝ, c = halfShiftCoeff N b := ⟨_, rfl⟩
  rw [← hcdef]
  have hle : (-Real.pi : ℝ) ≤ Real.pi := by linarith [Real.pi_pos]
  -- the derivative integral in the angular chart
  have hchange := MeasureTheory.integral_image_eq_integral_abs_deriv_smul
    (s := Set.Ioo (-Real.pi) Real.pi)
    (f := routeUHardEdgeAngularChart a) (f' := routeUHardEdgeAngularJacobian a)
    measurableSet_Ioo
    (fun θ hθ => (hasDerivAt_routeUHardEdgeAngularChart
      (ne_of_gt (cos_half_pos_of_mem_Ioo hθ))).hasDerivWithinAt)
    (injOn_routeUHardEdgeAngularChart ha)
    (fun x : ℝ => (halfCosPolyDeriv N c (routeUHardEdgeInverseChart a x)
      * (2 * a / (a ^ (2 : ℕ) + x ^ (2 : ℕ)))) ^ (2 : ℕ))
  rw [image_routeUHardEdgeAngularChart ha, setIntegral_univ] at hchange
  have hpt : ∀ θ ∈ Set.Ioo (-Real.pi) Real.pi,
      |routeUHardEdgeAngularJacobian a θ|
          • (halfCosPolyDeriv N c (routeUHardEdgeInverseChart a
              (routeUHardEdgeAngularChart a θ))
            * (2 * a / (a ^ (2 : ℕ) + routeUHardEdgeAngularChart a θ ^ (2 : ℕ)))) ^ (2 : ℕ)
        = 2 / a * (halfCosPolyDeriv N c θ ^ (2 : ℕ) * Real.cos (θ / 2) ^ (2 : ℕ)) := by
    intro θ hθ
    have hcos := cos_half_pos_of_mem_Ioo hθ
    have hcosne : Real.cos (θ / 2) ≠ 0 := ne_of_gt hcos
    have hinv : routeUHardEdgeInverseChart a (routeUHardEdgeAngularChart a θ) = θ :=
      routeUHardEdgeInverseChart_angularChart ha hθ
    have hsum : a ^ (2 : ℕ) + routeUHardEdgeAngularChart a θ ^ (2 : ℕ) = a ^ (2 : ℕ) / Real.cos (θ / 2) ^ (2 : ℕ) := by
      rw [routeUHardEdgeAngularChart]
      have h := tan_sq_add_one_of_cos_ne_zero hcosne
      calc a ^ (2 : ℕ) + (a * Real.tan (θ / 2)) ^ (2 : ℕ) = a ^ (2 : ℕ) * (Real.tan (θ / 2) ^ (2 : ℕ) + 1) := by ring
        _ = a ^ (2 : ℕ) * (1 / Real.cos (θ / 2) ^ (2 : ℕ)) := by rw [h]
        _ = a ^ (2 : ℕ) / Real.cos (θ / 2) ^ (2 : ℕ) := by ring
    have hjac : |routeUHardEdgeAngularJacobian a θ|
        = a * (1 / Real.cos (θ / 2) ^ (2 : ℕ) * (1 / 2)) := by
      rw [routeUHardEdgeAngularJacobian, abs_of_pos (by positivity)]
    rw [hinv, hsum, hjac, smul_eq_mul]
    field_simp
  rw [hchange, MeasureTheory.setIntegral_congr_fun measurableSet_Ioo hpt]
  -- compare with the Bernstein bound
  have hcosle : ∀ θ ∈ Set.Ioo (-Real.pi) Real.pi,
      2 / a * (halfCosPolyDeriv N c θ ^ (2 : ℕ) * Real.cos (θ / 2) ^ (2 : ℕ))
        ≤ 2 / a * halfCosPolyDeriv N c θ ^ (2 : ℕ) := by
    intro θ _
    have hbound : Real.cos (θ / 2) ^ (2 : ℕ) ≤ 1 := Real.cos_sq_le_one (θ / 2)
    have h2a : (0 : ℝ) ≤ 2 / a := by positivity
    have hkey : halfCosPolyDeriv N c θ ^ (2 : ℕ) * Real.cos (θ / 2) ^ (2 : ℕ)
        ≤ halfCosPolyDeriv N c θ ^ (2 : ℕ) := by
      nlinarith [sq_nonneg (halfCosPolyDeriv N c θ), hbound,
        mul_nonneg (sq_nonneg (halfCosPolyDeriv N c θ)) (sub_nonneg.2 hbound)]
    exact mul_le_mul_of_nonneg_left hkey h2a
  have hint1 : MeasureTheory.IntegrableOn
      (fun θ : ℝ => 2 / a * (halfCosPolyDeriv N c θ ^ (2 : ℕ) * Real.cos (θ / 2) ^ (2 : ℕ)))
      (Set.Ioo (-Real.pi) Real.pi) := by
    refine MeasureTheory.IntegrableOn.mono_set ?_ Set.Ioo_subset_Icc_self
    refine Continuous.integrableOn_Icc ?_
    refine continuous_const.mul (((continuous_finsetSum _ fun j _ => continuous_const.mul
      (Real.continuous_sin.comp (continuous_const.mul continuous_id))).pow 2).mul
      ((Real.continuous_cos.comp (continuous_id.div_const 2)).pow 2))
  have hint2 : MeasureTheory.IntegrableOn
      (fun θ : ℝ => 2 / a * halfCosPolyDeriv N c θ ^ (2 : ℕ)) (Set.Ioo (-Real.pi) Real.pi) := by
    refine MeasureTheory.IntegrableOn.mono_set ?_ Set.Ioo_subset_Icc_self
    refine Continuous.integrableOn_Icc ?_
    exact continuous_const.mul ((continuous_finsetSum _ fun j _ => continuous_const.mul
      (Real.continuous_sin.comp (continuous_const.mul continuous_id))).pow 2)
  have hstep1 : (∫ θ in Set.Ioo (-Real.pi) Real.pi,
      2 / a * (halfCosPolyDeriv N c θ ^ (2 : ℕ) * Real.cos (θ / 2) ^ (2 : ℕ)))
      ≤ ∫ θ in Set.Ioo (-Real.pi) Real.pi, 2 / a * halfCosPolyDeriv N c θ ^ (2 : ℕ) :=
    MeasureTheory.setIntegral_mono_on hint1 hint2 measurableSet_Ioo hcosle
  -- the Bernstein bound in the angular chart
  have hbern := integral_halfCosPolyDeriv_sq_le N c
  rw [intervalIntegral.integral_of_le hle, intervalIntegral.integral_of_le hle,
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo] at hbern
  -- the half-density factor only decreases the mass
  have hval : ∀ θ : ℝ, Real.cos (θ / 2) * ((routeUHardEdgeAngularPoly a p).eval (Real.cos θ))
      = halfCosPoly N c θ := by
    intro θ
    rw [eval_cos_of_chebyshev_expansion hb θ, ← cosPoly, cos_half_mul_cosPoly, hcdef]
  have hCint1 : MeasureTheory.IntegrableOn (fun θ : ℝ => halfCosPoly N c θ ^ (2 : ℕ))
      (Set.Ioo (-Real.pi) Real.pi) := by
    refine MeasureTheory.IntegrableOn.mono_set ?_ Set.Ioo_subset_Icc_self
    refine Continuous.integrableOn_Icc ?_
    exact (continuous_finsetSum _ fun j _ => continuous_const.mul
      (Real.continuous_cos.comp (continuous_const.mul continuous_id))).pow 2
  have hCint2 : MeasureTheory.IntegrableOn
      (fun θ : ℝ => ((routeUHardEdgeAngularPoly a p).eval (Real.cos θ)) ^ (2 : ℕ))
      (Set.Ioo (-Real.pi) Real.pi) := by
    refine MeasureTheory.IntegrableOn.mono_set ?_ Set.Ioo_subset_Icc_self
    refine Continuous.integrableOn_Icc ?_
    exact ((Polynomial.continuous _).comp Real.continuous_cos).pow 2
  have hC : (∫ θ in Set.Ioo (-Real.pi) Real.pi, halfCosPoly N c θ ^ (2 : ℕ))
      ≤ ∫ θ in Set.Ioo (-Real.pi) Real.pi,
          ((routeUHardEdgeAngularPoly a p).eval (Real.cos θ)) ^ (2 : ℕ) := by
    refine MeasureTheory.setIntegral_mono_on hCint1 hCint2 measurableSet_Ioo fun θ _ => ?_
    rw [← hval θ, mul_pow]
    nlinarith [Real.cos_sq_le_one (θ / 2),
      sq_nonneg ((routeUHardEdgeAngularPoly a p).eval (Real.cos θ))]
  -- nonnegativity of the angular masses
  have hHnn : (0 : ℝ) ≤ ∫ θ in Set.Ioo (-Real.pi) Real.pi, halfCosPoly N c θ ^ (2 : ℕ) :=
    MeasureTheory.setIntegral_nonneg measurableSet_Ioo fun θ _ => sq_nonneg _
  have hDnn : (0 : ℝ) ≤ ∫ θ in Set.Ioo (-Real.pi) Real.pi, halfCosPolyDeriv N c θ ^ (2 : ℕ) :=
    MeasureTheory.setIntegral_nonneg measurableSet_Ioo fun θ _ => sq_nonneg _
  -- the `L²` mass of the test in the angular chart
  have hnorm : (∫ x : ℝ, routeUHardEdgeRationalTest a p x ^ (2 : ℕ))
      = a / 2 * ∫ θ in Set.Ioo (-Real.pi) Real.pi,
          ((routeUHardEdgeAngularPoly a p).eval (Real.cos θ)) ^ (2 : ℕ) :=
    integral_routeUHardEdgeRationalTest_sq ha p
  -- assemble
  have hconst : (∫ θ in Set.Ioo (-Real.pi) Real.pi, 2 / a * halfCosPolyDeriv N c θ ^ (2 : ℕ))
      = 2 / a * ∫ θ in Set.Ioo (-Real.pi) Real.pi, halfCosPolyDeriv N c θ ^ (2 : ℕ) :=
    MeasureTheory.integral_const_mul _ _
  rw [hconst] at hstep1
  rw [hnorm]
  have ha2 : (0 : ℝ) < 2 / a := by positivity
  have hkey : 2 / a * (∫ θ in Set.Ioo (-Real.pi) Real.pi, halfCosPolyDeriv N c θ ^ (2 : ℕ))
      ≤ 2 / a * (((N : ℝ) + 1 / 2) ^ (2 : ℕ)
          * ∫ θ in Set.Ioo (-Real.pi) Real.pi,
              ((routeUHardEdgeAngularPoly a p).eval (Real.cos θ)) ^ (2 : ℕ)) := by
    refine mul_le_mul_of_nonneg_left ?_ ha2.le
    refine le_trans hbern ?_
    exact mul_le_mul_of_nonneg_left hC (by positivity)
  have hfinal : 2 / a * (((N : ℝ) + 1 / 2) ^ (2 : ℕ)
        * ∫ θ in Set.Ioo (-Real.pi) Real.pi,
            ((routeUHardEdgeAngularPoly a p).eval (Real.cos θ)) ^ (2 : ℕ))
      = 4 * ((N : ℝ) + 1 / 2) ^ (2 : ℕ) / a ^ (2 : ℕ)
        * (a / 2 * ∫ θ in Set.Ioo (-Real.pi) Real.pi,
            ((routeUHardEdgeAngularPoly a p).eval (Real.cos θ)) ^ (2 : ℕ)) := by
    field_simp
    ring
  rw [← hfinal]
  linarith [hstep1, hkey]

end RHTower

end
