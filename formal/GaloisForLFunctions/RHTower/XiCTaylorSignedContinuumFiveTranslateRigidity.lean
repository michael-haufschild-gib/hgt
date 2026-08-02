import GaloisForLFunctions.RHTower.XiCTaylorSignedContinuumFourVariationEscape

/-!
# Five-translate Route-J masks are target-informative

This file classifies the complete coefficient kernel of the sharp five-translate regular
construction. For a positive noncentral radius `r`, all four reflected value/dilation-derivative
rows force the coefficient vector to be a scalar multiple of

`(X - r)² (X - r⁻¹)²`.

Consequently, one nonzero fixed five-translate mask cannot cancel at two distinct positive damping
radii above one. With fixed positive spacing, it determines the damping parameter uniquely. This
is the first cross-fibre source-provenance obstruction for the sharp regular Route-J survivor.
-/

open Real

namespace RHTower

noncomputable section

/-- Value row of a five-tap translate-mask symbol. -/
def routeJFiveCoeffValue (a : Fin 5 → ℝ) (x : ℝ) : ℝ :=
  a 0 + a 1 * x + a 2 * x ^ 2 + a 3 * x ^ 3 + a 4 * x ^ 4

/-- Dilation-derivative row `x A'(x)` of a five-tap translate-mask symbol. -/
def routeJFiveCoeffDilationDerivative (a : Fin 5 → ℝ) (x : ℝ) : ℝ :=
  a 1 * x + 2 * a 2 * x ^ 2 + 3 * a 3 * x ^ 3 + 4 * a 4 * x ^ 4

/-- Simultaneous value and first-moment cancellation at `r` and `r⁻¹`. -/
def routeJFiveCoeffReflectedRows (a : Fin 5 → ℝ) (r : ℝ) : Prop :=
  routeJFiveCoeffValue a r = 0 ∧
    routeJFiveCoeffDilationDerivative a r = 0 ∧
    routeJFiveCoeffValue a r⁻¹ = 0 ∧
    routeJFiveCoeffDilationDerivative a r⁻¹ = 0

/-- Complete kernel classification: four reflected rows leave exactly the reciprocal
double-root coefficient ray. -/
theorem routeJFiveCoeffReflectedRows_classification
    {a : Fin 5 → ℝ} {r : ℝ}
    (hr : 0 < r) (hr1 : r ≠ 1)
    (hrows : routeJFiveCoeffReflectedRows a r) :
    ∀ j : Fin 5,
      a j = a 4 * routeJReciprocalDoubleRootCoeff r j := by
  have hr0 : r ≠ 0 := hr.ne'
  have hrInv0 : r⁻¹ ≠ 0 := inv_ne_zero hr0
  have hrInv : r ≠ r⁻¹ := by
    intro h
    have hmul := congrArg (fun x : ℝ => x * r) h
    simp only [inv_mul_cancel₀ hr0] at hmul
    have hfac : (r - 1) * (r + 1) = 0 := by
      calc
        _ = r * r - 1 := by ring
        _ = 0 := by rw [hmul]; ring
    rcases mul_eq_zero.mp hfac with hminus | hplus
    · exact hr1 (sub_eq_zero.mp hminus)
    · nlinarith
  let x : ℝ := r + r⁻¹
  have hxgt : 2 < x := by
    have hsq : 0 < (r - 1) ^ 2 :=
      sq_pos_of_ne_zero (sub_ne_zero.mpr hr1)
    have hquot : 0 < (r - 1) ^ 2 / r := div_pos hsq hr
    have hid : (r - 1) ^ 2 / r = r + r⁻¹ - 2 := by
      field_simp [hr0]
      ring
    rw [hid] at hquot
    dsimp [x]
    linarith
  rcases hrows with ⟨hVr, hDr, hVi, hDi⟩
  unfold routeJFiveCoeffValue at hVr hVi
  unfold routeJFiveCoeffDilationDerivative at hDr hDi
  let b0 : ℝ := a 0 - a 4 * routeJReciprocalDoubleRootCoeff r 0
  let b1 : ℝ := a 1 - a 4 * routeJReciprocalDoubleRootCoeff r 1
  let b2 : ℝ := a 2 - a 4 * routeJReciprocalDoubleRootCoeff r 2
  let b3 : ℝ := a 3 - a 4 * routeJReciprocalDoubleRootCoeff r 3
  have hcVr := routeJReciprocalDoubleRootCoeff_value_at_r hr0
  have hcDr := routeJReciprocalDoubleRootCoeff_deriv_at_r hr0
  have hcVi := routeJReciprocalDoubleRootCoeff_value_at_inv hr0
  have hcDi := routeJReciprocalDoubleRootCoeff_deriv_at_inv hr0
  simp only [routeJReciprocalDoubleRootCoeff_four] at hcVr hcDr hcVi hcDi
  have hbVr : b0 + b1 * r + b2 * r ^ 2 + b3 * r ^ 3 = 0 := by
    dsimp [b0, b1, b2, b3]
    linear_combination hVr - a 4 * hcVr
  have hbDr : b1 * r + 2 * b2 * r ^ 2 + 3 * b3 * r ^ 3 = 0 := by
    dsimp [b1, b2, b3]
    linear_combination hDr - a 4 * hcDr
  have hbVi :
      b0 + b1 * r⁻¹ + b2 * r⁻¹ ^ 2 + b3 * r⁻¹ ^ 3 = 0 := by
    dsimp [b0, b1, b2, b3]
    linear_combination hVi - a 4 * hcVi
  have hbDi :
      b1 * r⁻¹ + 2 * b2 * r⁻¹ ^ 2 + 3 * b3 * r⁻¹ ^ 3 = 0 := by
    dsimp [b1, b2, b3]
    linear_combination hDi - a 4 * hcDi
  have hbDr' : b1 + 2 * b2 * r + 3 * b3 * r ^ 2 = 0 := by
    have hfac : r * (b1 + 2 * b2 * r + 3 * b3 * r ^ 2) = 0 := by
      calc
        _ = b1 * r + 2 * b2 * r ^ 2 + 3 * b3 * r ^ 3 := by ring
        _ = 0 := hbDr
    exact (mul_eq_zero.mp hfac).resolve_left hr0
  have hbDi' :
      b1 + 2 * b2 * r⁻¹ + 3 * b3 * r⁻¹ ^ 2 = 0 := by
    have hfac :
        r⁻¹ * (b1 + 2 * b2 * r⁻¹ + 3 * b3 * r⁻¹ ^ 2) = 0 := by
      calc
        _ = b1 * r⁻¹ + 2 * b2 * r⁻¹ ^ 2 + 3 * b3 * r⁻¹ ^ 3 := by ring
        _ = 0 := hbDi
    exact (mul_eq_zero.mp hfac).resolve_left hrInv0
  have hbDelta : 2 * b2 + 3 * x * b3 = 0 := by
    have hfac : (r - r⁻¹) * (2 * b2 + 3 * x * b3) = 0 := by
      calc
        _ =
            (b1 + 2 * b2 * r + 3 * b3 * r ^ 2) -
              (b1 + 2 * b2 * r⁻¹ + 3 * b3 * r⁻¹ ^ 2) := by
                dsimp [x]
                field_simp [hr0]
                ring
        _ = 0 := by rw [hbDr', hbDi', sub_zero]
    exact (mul_eq_zero.mp hfac).resolve_left
      (sub_ne_zero.mpr hrInv)
  have hbSum :
      2 * b1 + 2 * x * b2 + 3 * (x ^ 2 - 2) * b3 = 0 := by
    calc
      _ =
          (b1 + 2 * b2 * r + 3 * b3 * r ^ 2) +
            (b1 + 2 * b2 * r⁻¹ + 3 * b3 * r⁻¹ ^ 2) := by
              dsimp [x]
              field_simp [hr0]
              ring
      _ = 0 := by rw [hbDr', hbDi', add_zero]
  have hbValueDelta :
      b1 + x * b2 + (x ^ 2 - 1) * b3 = 0 := by
    have hfac :
        (r - r⁻¹) * (b1 + x * b2 + (x ^ 2 - 1) * b3) = 0 := by
      calc
        _ =
            (b0 + b1 * r + b2 * r ^ 2 + b3 * r ^ 3) -
              (b0 + b1 * r⁻¹ + b2 * r⁻¹ ^ 2 + b3 * r⁻¹ ^ 3) := by
                dsimp [x]
                field_simp [hr0]
                ring
        _ = 0 := by rw [hbVr, hbVi, sub_zero]
    exact (mul_eq_zero.mp hfac).resolve_left
      (sub_ne_zero.mpr hrInv)
  have hbOne : b1 - 3 * b3 = 0 := by
    linear_combination (1 / 2 : ℝ) * hbSum - (x / 2) * hbDelta
  have hbMaster : (4 - x ^ 2) * b3 = 0 := by
    linear_combination
      2 * hbValueDelta - 2 * hbOne - x * hbDelta
  have hxcoef : 4 - x ^ 2 ≠ 0 := by
    nlinarith
  have hb3zero : b3 = 0 :=
    (mul_eq_zero.mp hbMaster).resolve_left hxcoef
  have hb2zero : b2 = 0 := by
    rw [hb3zero, mul_zero, add_zero] at hbDelta
    linarith
  have hb1zero : b1 = 0 := by
    rw [hb3zero, mul_zero, sub_zero] at hbOne
    exact hbOne
  have hb0zero : b0 = 0 := by
    simpa [hb1zero, hb2zero, hb3zero] using hbVr
  intro j
  fin_cases j
  · dsimp [b0] at hb0zero
    simpa using sub_eq_zero.mp hb0zero
  · dsimp [b1] at hb1zero
    simpa using sub_eq_zero.mp hb1zero
  · dsimp [b2] at hb2zero
    simpa using sub_eq_zero.mp hb2zero
  · dsimp [b3] at hb3zero
    simpa using sub_eq_zero.mp hb3zero
  · simp

/-- The four reflected rows hold exactly on the reciprocal double-root ray. -/
theorem routeJFiveCoeffReflectedRows_iff
    {a : Fin 5 → ℝ} {r : ℝ}
    (hr : 0 < r) (hr1 : r ≠ 1) :
    routeJFiveCoeffReflectedRows a r ↔
      ∀ j : Fin 5,
        a j = a 4 * routeJReciprocalDoubleRootCoeff r j := by
  constructor
  · exact routeJFiveCoeffReflectedRows_classification hr hr1
  · intro h
    have hr0 := hr.ne'
    have hcVr := routeJReciprocalDoubleRootCoeff_value_at_r hr0
    have hcDr := routeJReciprocalDoubleRootCoeff_deriv_at_r hr0
    have hcVi := routeJReciprocalDoubleRootCoeff_value_at_inv hr0
    have hcDi := routeJReciprocalDoubleRootCoeff_deriv_at_inv hr0
    simp only [routeJReciprocalDoubleRootCoeff_four] at hcVr hcDr hcVi hcDi
    have hcVr' :
        routeJReciprocalDoubleRootCoeff r 0 +
            routeJReciprocalDoubleRootCoeff r 1 * r +
            routeJReciprocalDoubleRootCoeff r 2 * r ^ 2 +
            routeJReciprocalDoubleRootCoeff r 3 * r ^ 3 + r ^ 4 = 0 := by
      simpa using hcVr
    have hcDr' :
        routeJReciprocalDoubleRootCoeff r 1 * r +
            2 * routeJReciprocalDoubleRootCoeff r 2 * r ^ 2 +
            3 * routeJReciprocalDoubleRootCoeff r 3 * r ^ 3 +
            4 * r ^ 4 = 0 := by
      simpa using hcDr
    have hcVi' :
        routeJReciprocalDoubleRootCoeff r 0 +
            routeJReciprocalDoubleRootCoeff r 1 * r⁻¹ +
            routeJReciprocalDoubleRootCoeff r 2 * r⁻¹ ^ 2 +
            routeJReciprocalDoubleRootCoeff r 3 * r⁻¹ ^ 3 + r⁻¹ ^ 4 = 0 := by
      simpa using hcVi
    have hcDi' :
        routeJReciprocalDoubleRootCoeff r 1 * r⁻¹ +
            2 * routeJReciprocalDoubleRootCoeff r 2 * r⁻¹ ^ 2 +
            3 * routeJReciprocalDoubleRootCoeff r 3 * r⁻¹ ^ 3 +
            4 * r⁻¹ ^ 4 = 0 := by
      simpa using hcDi
    unfold routeJFiveCoeffReflectedRows
    unfold routeJFiveCoeffValue routeJFiveCoeffDilationDerivative
    constructor
    · rw [h 0, h 1, h 2, h 3]
      calc
          a 4 * routeJReciprocalDoubleRootCoeff r 0 +
              a 4 * routeJReciprocalDoubleRootCoeff r 1 * r +
              a 4 * routeJReciprocalDoubleRootCoeff r 2 * r ^ 2 +
              a 4 * routeJReciprocalDoubleRootCoeff r 3 * r ^ 3 +
              a 4 * r ^ 4 =
            a 4 *
              (routeJReciprocalDoubleRootCoeff r 0 +
                routeJReciprocalDoubleRootCoeff r 1 * r +
                routeJReciprocalDoubleRootCoeff r 2 * r ^ 2 +
                routeJReciprocalDoubleRootCoeff r 3 * r ^ 3 +
                r ^ 4) := by ring
          _ = 0 := by rw [hcVr', mul_zero]
    constructor
    · rw [h 1, h 2, h 3]
      calc
          a 4 * routeJReciprocalDoubleRootCoeff r 1 * r +
              2 * (a 4 * routeJReciprocalDoubleRootCoeff r 2) * r ^ 2 +
              3 * (a 4 * routeJReciprocalDoubleRootCoeff r 3) * r ^ 3 +
              4 * a 4 * r ^ 4 =
            a 4 *
              (routeJReciprocalDoubleRootCoeff r 1 * r +
                2 * routeJReciprocalDoubleRootCoeff r 2 * r ^ 2 +
                3 * routeJReciprocalDoubleRootCoeff r 3 * r ^ 3 +
                4 * r ^ 4) := by ring
          _ = 0 := by rw [hcDr', mul_zero]
    constructor
    · rw [h 0, h 1, h 2, h 3]
      calc
          a 4 * routeJReciprocalDoubleRootCoeff r 0 +
              a 4 * routeJReciprocalDoubleRootCoeff r 1 * r⁻¹ +
              a 4 * routeJReciprocalDoubleRootCoeff r 2 * r⁻¹ ^ 2 +
              a 4 * routeJReciprocalDoubleRootCoeff r 3 * r⁻¹ ^ 3 +
              a 4 * r⁻¹ ^ 4 =
            a 4 *
              (routeJReciprocalDoubleRootCoeff r 0 +
                routeJReciprocalDoubleRootCoeff r 1 * r⁻¹ +
                routeJReciprocalDoubleRootCoeff r 2 * r⁻¹ ^ 2 +
                routeJReciprocalDoubleRootCoeff r 3 * r⁻¹ ^ 3 +
                r⁻¹ ^ 4) := by ring
          _ = 0 := by rw [hcVi', mul_zero]
    · rw [h 1, h 2, h 3]
      calc
          a 4 * routeJReciprocalDoubleRootCoeff r 1 * r⁻¹ +
              2 * (a 4 * routeJReciprocalDoubleRootCoeff r 2) * r⁻¹ ^ 2 +
              3 * (a 4 * routeJReciprocalDoubleRootCoeff r 3) * r⁻¹ ^ 3 +
              4 * a 4 * r⁻¹ ^ 4 =
            a 4 *
              (routeJReciprocalDoubleRootCoeff r 1 * r⁻¹ +
                2 * routeJReciprocalDoubleRootCoeff r 2 * r⁻¹ ^ 2 +
                3 * routeJReciprocalDoubleRootCoeff r 3 * r⁻¹ ^ 3 +
                4 * r⁻¹ ^ 4) := by ring
          _ = 0 := by rw [hcDi', mul_zero]

/-- A nonzero five-tap mask can serve two radii only on one reciprocal orbit. -/
theorem routeJFiveCoeffReflectedRows_transverse_orbit
    {a : Fin 5 → ℝ} {r s : ℝ}
    (hr : 0 < r) (hr1 : r ≠ 1)
    (hs : 0 < s) (hs1 : s ≠ 1)
    (ha : ∃ j : Fin 5, a j ≠ 0)
    (hrowsr : routeJFiveCoeffReflectedRows a r)
    (hrowss : routeJFiveCoeffReflectedRows a s) :
    s = r ∨ s = r⁻¹ := by
  have har :=
    routeJFiveCoeffReflectedRows_classification hr hr1 hrowsr
  have has :=
    routeJFiveCoeffReflectedRows_classification hs hs1 hrowss
  have ha4 : a 4 ≠ 0 := by
    intro ha4
    rcases ha with ⟨j, hj⟩
    rw [har j, ha4, zero_mul] at hj
    exact hj rfl
  have horbitSum : r + r⁻¹ = s + s⁻¹ := by
    have hscale : -2 * a 4 ≠ 0 := mul_ne_zero (by norm_num) ha4
    apply mul_left_cancel₀ hscale
    calc
      (-2 * a 4) * (r + r⁻¹) =
          a 4 * routeJReciprocalDoubleRootCoeff r 1 := by
            rw [routeJReciprocalDoubleRootCoeff_one]
            ring
      _ = a 1 := (har 1).symm
      _ = a 4 * routeJReciprocalDoubleRootCoeff s 1 := has 1
      _ = (-2 * a 4) * (s + s⁻¹) := by
            rw [routeJReciprocalDoubleRootCoeff_one]
            ring
  have hfactor : (r - s) * (r * s - 1) = 0 := by
    calc
      _ = (r * s) * ((r + r⁻¹) - (s + s⁻¹)) := by
        field_simp [hr.ne', hs.ne']
        ring
      _ = 0 := by rw [horbitSum, sub_self, mul_zero]
  rcases mul_eq_zero.mp hfactor with hrs | hrs
  · exact Or.inl (sub_eq_zero.mp hrs).symm
  · exact Or.inr
      (eq_inv_of_mul_eq_one_right (sub_eq_zero.mp hrs))

/-- On the physical branch `1 < r`, a nonzero five-tap mask determines the radius. -/
theorem routeJFiveCoeffReflectedRows_positive_orbit_injective
    {a : Fin 5 → ℝ} {r s : ℝ}
    (hr : 1 < r) (hs : 1 < s)
    (ha : ∃ j : Fin 5, a j ≠ 0)
    (hrowsr : routeJFiveCoeffReflectedRows a r)
    (hrowss : routeJFiveCoeffReflectedRows a s) :
    s = r := by
  rcases routeJFiveCoeffReflectedRows_transverse_orbit
      (zero_lt_one.trans hr) hr.ne'
      (zero_lt_one.trans hs) hs.ne'
      ha hrowsr hrowss with hsr | hsr
  · exact hsr
  · have hinv : r⁻¹ < 1 := inv_lt_one_of_one_lt₀ hr
    rw [hsr] at hs
    linarith

/-- At fixed positive translate spacing, a nonzero five-tap mask determines positive damping
uniquely. -/
theorem routeJFiveCoeffReflectedRows_damping_injective
    {a : Fin 5 → ℝ} {L c d : ℝ}
    (hL : 0 < L) (hc : 0 < c) (hd : 0 < d)
    (ha : ∃ j : Fin 5, a j ≠ 0)
    (hrowsc :
      routeJFiveCoeffReflectedRows a (Real.exp (c * L)))
    (hrowsd :
      routeJFiveCoeffReflectedRows a (Real.exp (d * L))) :
    c = d := by
  have hrc : 1 < Real.exp (c * L) := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (mul_pos hc hL)
  have hrd : 1 < Real.exp (d * L) := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (mul_pos hd hL)
  have hexp :
      Real.exp (d * L) = Real.exp (c * L) :=
    routeJFiveCoeffReflectedRows_positive_orbit_injective
      hrc hrd ha hrowsc hrowsd
  have hmul : d * L = c * L := Real.exp_injective hexp
  nlinarith

end

end RHTower
