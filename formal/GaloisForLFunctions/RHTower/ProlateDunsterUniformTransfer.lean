import GaloisForLFunctions.RHTower.ProlateDunsterEndpointCoefficientBounds

/-!
# Uniform transfer from actual radial prolate modes to the leading Dunster model

The endpoint coefficient bounds are inserted into the interior Volterra estimate.  Its envelope
constant is fixed once for all parameters, and its Grönwall constant is now explicit.  The result
is a genuine uniform `O(c^-1)` approximation of the exact endpoint-normalized radial profile by
the regular Bessel model on every interval beyond the deterministic matching point.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

open Set

/-- The matching-point weighted Wronskian datum is uniformly bounded. -/
theorem radialProlateVolterraDatum_crossing_le {s c : ℝ} {R DR DDR : ℝ → ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 5 ≤ c)
    (hR1 : R 1 = 1)
    (hR : ∀ t : ℝ, HasDerivAt R (DR t) t)
    (hDR : ∀ t : ℝ, HasDerivAt DR (DDR t) t)
    (hode : ∀ t : ℝ, (t ^ 2 - 1) * DDR t + 2 * t * DR t
      - (s * c ^ 2 - c ^ 2 * t ^ 2) * R t = 0) :
    radialProlateVolterraDatum s c (dunsterEndpointCrossing c) R DR ≤ 33 := by
  let A := dunsterEndpointCrossing c
  let U := comparisonSol (prolateNormalFormSol R) s
  let DU := comparisonSolDeriv (prolateNormalFormSol R) (prolateNormalFormSolDeriv R DR) s
  have hc0 : 0 < c := lt_of_lt_of_le (by norm_num) hc
  have hreg := abs_radialProlate_regularCoefficient_crossing_le hs0 hs1 hc hR1 hR hDR hode
  have hlog := abs_radialProlate_logCoefficient_sub_pi_div_four_crossing_le
    hs0 hs1 hc hR1 hR hDR hode
  change |lgEndpointRegularIntegral s c U DU A| ≤ 18 / c at hreg
  change |lgEndpointLogIntegral s c U DU A| ≤ 141 / c at hlog
  let Flog : ℝ := lgWeight s A *
    (U A * lgBesselModel2Deriv s c A - DU A * lgBesselModel2 s c A)
  have hFlog : Flog = lgEndpointLogIntegral s c U DU A + Real.pi / 4 := by
    rw [Flog, lgEndpointLogIntegral]
    ring
  have hpi : |Real.pi / 4| ≤ 1 := by
    rw [abs_of_pos (by positivity : 0 < Real.pi / 4)]
    nlinarith [Real.pi_le_four]
  have hFlogAbs : |Flog| ≤ 141 / c + 1 := by
    rw [hFlog]
    exact (abs_add_le _ _).trans (add_le_add hlog hpi)
  have h159 : 159 / c ≤ 32 := by
    rw [div_le_iff₀ hc0]
    nlinarith
  rw [radialProlateVolterraDatum]
  change |lgEndpointRegularIntegral s c U DU A| + |Flog| ≤ 33
  linarith

/-- Explicit uniform bound for the interior Grönwall constant. -/
theorem radialProlateVolterraK_crossing_le {s c C : ℝ} {R DR DDR : ℝ → ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 5 ≤ c)
    (hR1 : R 1 = 1)
    (hR : ∀ t : ℝ, HasDerivAt R (DR t) t)
    (hDR : ∀ t : ℝ, HasDerivAt DR (DDR t) t)
    (hode : ∀ t : ℝ, (t ^ 2 - 1) * DDR t + 2 * t * DR t
      - (s * c ^ 2 - c ^ 2 * t ^ 2) * R t = 0) :
    radialProlateVolterraK s c (dunsterEndpointCrossing c) R DR C
      ≤ 44 * Real.exp (68 * C ^ 2) := by
  let A := dunsterEndpointCrossing c
  let W := besselWronskian (c * xiEndpointPhase s A)
  have hc0 : 0 < c := lt_of_lt_of_le (by norm_num) hc
  have hA1 : 1 < A := dunsterEndpointCrossing_gt_one hc0
  have harg : 0 < c * xiEndpointPhase s A :=
    mul_pos hc0 (xiEndpointPhase_pos hs0 hs1 hA1)
  have hW : W = Real.pi / 4 := besselWronskian_eq_pi_div_four harg
  have hWpos : 0 < W := by rw [hW]; positivity
  have hWlower : (3 / 4 : ℝ) ≤ W := by
    rw [hW]
    linarith [Real.pi_gt_three]
  have hDatum := radialProlateVolterraDatum_crossing_le hs0 hs1 hc hR1 hR hDR hode
  change radialProlateVolterraDatum s c A R DR ≤ 33 at hDatum
  have hcW : (15 / 4 : ℝ) ≤ c * W := by
    exact mul_le_mul hc hWlower (by norm_num) (by norm_num)
  have hden : 0 < c * W := mul_pos hc0 hWpos
  have hexponent : 2 * C ^ 2 / (c * W) * 127 ≤ 68 * C ^ 2 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hden]
    have hmul := mul_le_mul_of_nonneg_left hcW
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 68) (sq_nonneg C))
    nlinarith
  have hexp := Real.exp_le_exp.mpr hexponent
  have hnum : radialProlateVolterraDatum s c A R DR *
      Real.exp (2 * C ^ 2 / (c * W) * 127)
      ≤ 33 * Real.exp (68 * C ^ 2) :=
    mul_le_mul hDatum hexp (Real.exp_nonneg _) (by norm_num)
  have hrhs : 33 * Real.exp (68 * C ^ 2)
      ≤ 44 * Real.exp (68 * C ^ 2) * W := by
    have hmul := mul_le_mul_of_nonneg_left hWlower
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 44) (Real.exp_nonneg _))
    nlinarith
  rw [radialProlateVolterraK]
  change radialProlateVolterraDatum s c A R DR *
      Real.exp (2 * C ^ 2 / (c * W) * 127) / W
    ≤ 44 * Real.exp (68 * C ^ 2)
  rw [div_le_iff₀ hWpos]
  exact hnum.trans hrhs

/-- Fixed constant in the actual-to-leading-model radial transfer. -/
def radialProlateUniformTransferConstant : ℝ :=
  (4 / 3) *
    (2 * (44 * Real.exp (68 * lgBesselCommonEnvelopeConstant ^ 2) *
      (127 * lgBesselCommonEnvelopeConstant ^ 2)) + 159)

theorem radialProlateUniformTransferConstant_nonneg :
    0 ≤ radialProlateUniformTransferConstant := by
  rw [radialProlateUniformTransferConstant]
  positivity

/-- **Uniform actual-profile Dunster transfer.**  Beyond the explicit matching point, the exact
comparison transform differs from the regular Bessel model by `O(c^-1)` times the common Bessel
envelope, with one fixed constant independent of `s`, `c`, the solution, and the outer endpoint. -/
theorem abs_radialProlate_sub_regularModel_le {s c B x : ℝ} {R DR DDR : ℝ → ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 5 ≤ c)
    (hAB : dunsterEndpointCrossing c ≤ B)
    (hR1 : R 1 = 1)
    (hR : ∀ t : ℝ, HasDerivAt R (DR t) t)
    (hDR : ∀ t : ℝ, HasDerivAt DR (DDR t) t)
    (hode : ∀ t : ℝ, (t ^ 2 - 1) * DDR t + 2 * t * DR t
      - (s * c ^ 2 - c ^ 2 * t ^ 2) * R t = 0)
    (hx : x ∈ Icc (dunsterEndpointCrossing c) B) :
    |comparisonSol (prolateNormalFormSol R) s x - lgBesselModel s c x|
      ≤ (radialProlateUniformTransferConstant / c) *
        (lgBesselCommonEnvelopeConstant /
          Real.sqrt (c * xiEndpointPhase s x)) := by
  let A := dunsterEndpointCrossing c
  let U := comparisonSol (prolateNormalFormSol R) s
  let DU := comparisonSolDeriv (prolateNormalFormSol R) (prolateNormalFormSolDeriv R DR) s
  let C := lgBesselCommonEnvelopeConstant
  let E : ℝ → ℝ := fun y => C / Real.sqrt (c * xiEndpointPhase s y)
  have hc0 : 0 < c := lt_of_lt_of_le (by norm_num) hc
  have hA1 : 1 < A := dunsterEndpointCrossing_gt_one hc0
  have hcxiA : 1 ≤ c * xiEndpointPhase s A :=
    one_le_c_mul_xiEndpointPhase_crossing hs0 hs1 hc
  have hRI : ∀ y ∈ Icc A B, HasDerivAt R (DR y) y := fun y _ => hR y
  have hDRI : ∀ y ∈ Icc A B, HasDerivAt DR (DDR y) y := fun y _ => hDR y
  have hodeI : ∀ y ∈ Icc A B,
      (y ^ 2 - 1) * DDR y + 2 * y * DR y
        - (s * c ^ 2 - c ^ 2 * y ^ 2) * R y = 0 := fun y _ => hode y
  obtain ⟨C', K, hC'0, hC'eq, hK0, hEnv, hKeq, happ⟩ :=
    abs_radialProlate_sub_model_le hs0 hs1 hc0 hA1 hAB hcxiA hRI hDRI hodeI
  have hCC : C' = C := hC'eq
  subst C'
  have hK := radialProlateVolterraK_crossing_le (C := C)
    hs0 hs1 hc hR1 hR hDR hode
  rw [hKeq] at hK
  have hphaseMono := xiEndpointPhase_le_of_le hs0 hs1 hA1.le hx.1
  have hcxi : 1 ≤ c * xiEndpointPhase s x := by
    have := mul_le_mul_of_nonneg_left hphaseMono hc0.le
    linarith
  have hmodels := hEnv s c x hcxi
  have hE0 : 0 ≤ E x := by
    dsimp [E, C]
    positivity
  have hreg := abs_radialProlate_regularCoefficient_crossing_le
    hs0 hs1 hc hR1 hR hDR hode
  have hlog := abs_radialProlate_logCoefficient_sub_pi_div_four_crossing_le
    hs0 hs1 hc hR1 hR hDR hode
  change |lgEndpointRegularIntegral s c U DU A| ≤ 18 / c at hreg
  change |lgEndpointLogIntegral s c U DU A| ≤ 141 / c at hlog
  let Freg : ℝ := lgEndpointRegularIntegral s c U DU A
  let Ilog : ℝ := lgEndpointLogIntegral s c U DU A
  let Flog : ℝ := Ilog + Real.pi / 4
  have hFreg : |Freg| ≤ 18 / c := hreg
  have hIlog : |Ilog| ≤ 141 / c := hlog
  have hW : besselWronskian (c * xiEndpointPhase s A) = Real.pi / 4 :=
    besselWronskian_eq_pi_div_four
      (mul_pos hc0 (xiEndpointPhase_pos hs0 hs1 hA1))
  have hWlower : (3 / 4 : ℝ) ≤ Real.pi / 4 := by linarith [Real.pi_gt_three]
  have hcombo : |Ilog * lgBesselModel s c x - Freg * lgBesselModel2 s c x|
      ≤ (159 / c) * E x := by
    have h1 : |Ilog * lgBesselModel s c x| ≤ (141 / c) * E x := by
      rw [abs_mul]
      exact mul_le_mul hIlog (by simpa [E, C] using hmodels.1) (abs_nonneg _) (by positivity)
    have h2 : |Freg * lgBesselModel2 s c x| ≤ (18 / c) * E x := by
      rw [abs_mul]
      exact mul_le_mul hFreg (by simpa [E, C] using hmodels.2) (abs_nonneg _) (by positivity)
    exact (abs_sub_le _ _).trans (by
      have := add_le_add h1 h2
      convert this using 1 <;> ring)
  have happx := happ x hx
  rw [hW] at happx
  change |U x * (Real.pi / 4) -
      ((Flog) * lgBesselModel s c x - Freg * lgBesselModel2 s c x)|
      ≤ 2 * (K * (127 * C ^ 2 / c)) * E x at happx
  have hscaled : |(Real.pi / 4) * (U x - lgBesselModel s c x)|
      ≤ (2 * (44 * Real.exp (68 * C ^ 2) * (127 * C ^ 2)) + 159) / c * E x := by
    have hid : (Real.pi / 4) * (U x - lgBesselModel s c x) =
        (U x * (Real.pi / 4) -
          (Flog * lgBesselModel s c x - Freg * lgBesselModel2 s c x)) +
        (Ilog * lgBesselModel s c x - Freg * lgBesselModel2 s c x) := by
      dsimp [Flog]
      ring
    rw [hid]
    refine (abs_add_le _ _).trans ?_
    have hpert : 2 * (K * (127 * C ^ 2 / c)) * E x
        ≤ (2 * (44 * Real.exp (68 * C ^ 2) * (127 * C ^ 2)) / c) * E x := by
      have hcoef : 2 * (K * (127 * C ^ 2 / c))
          ≤ 2 * (44 * Real.exp (68 * C ^ 2) * (127 * C ^ 2)) / c := by
        have hmul := mul_le_mul_of_nonneg_right hK
          (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2 * 127)
            (div_nonneg (sq_nonneg C) hc0.le))
        convert hmul using 1 <;> ring
      exact mul_le_mul_of_nonneg_right hcoef hE0
    have hsum := add_le_add (happx.trans hpert) hcombo
    convert hsum using 1 <;> ring
  have habsW : |Real.pi / 4| = Real.pi / 4 := abs_of_pos (by positivity)
  rw [abs_mul, habsW] at hscaled
  have hdivide : |U x - lgBesselModel s c x|
      ≤ (4 / 3 : ℝ) *
        (((2 * (44 * Real.exp (68 * C ^ 2) * (127 * C ^ 2)) + 159) / c) * E x) := by
    have hmul := mul_le_mul_of_nonneg_right hWlower (abs_nonneg (U x - lgBesselModel s c x))
    nlinarith
  change |U x - lgBesselModel s c x| ≤
    (radialProlateUniformTransferConstant / c) * E x
  exact hdivide.trans (by
    rw [radialProlateUniformTransferConstant]
    dsimp only [C]
    ring_nf
    exact le_rfl)

end GaloisForLFunctions.RHTower

end
