import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# The centred-pole profile integral

The imaginary part of the centred double pole `w ↦ w^(-2) - w^(-1)` on the vertical line
`w = 1/2 - i y` is the rational profile

```text
p(y) = y (3/4 - y²)/(y² + 1/4)² ,
```

and its energy is exactly `π`:

```text
∫_ℝ p(y)² dy = π .
```

The proof is the explicit primitive

```text
P(y) = (-(1/2) y^5 + (5/12) y^3 - (1/32) y)/(y² + 1/4)^3 + arctan (2y) ,
```

whose rational part vanishes at both ends, so the whole integral is the total variation `π` of
`arctan`.  Integrability comes from the pointwise majorant `p(y)² ≤ (y² + 1/4)^(-1)`, which is the
identity `(y² + 1/4)^3 - y²(3/4 - y²)² = (9/4)(y² - 1/12)²`.
-/

open MeasureTheory Filter Topology

namespace HTGeometry

noncomputable section

/-- The centred-pole profile `y (3/4 - y²)/(y² + 1/4)²`. -/
def poleProfile (y : ℝ) : ℝ := y * (3 / 4 - y ^ 2) / (y ^ 2 + 1 / 4) ^ 2

/-- Rational part of the primitive of `poleProfile²`. -/
def poleProfilePrimitiveRat (y : ℝ) : ℝ :=
  (-(1 / 2) * y ^ 5 + 5 / 12 * y ^ 3 - 1 / 32 * y) / (y ^ 2 + 1 / 4) ^ 3

/-- Primitive of `poleProfile²`. -/
def poleProfilePrimitive (y : ℝ) : ℝ := poleProfilePrimitiveRat y + Real.arctan (2 * y)

/-! ### The primitive -/

theorem hasDerivAt_poleProfilePrimitive (y : ℝ) :
    HasDerivAt poleProfilePrimitive (poleProfile y ^ 2) y := by
  have hpos : (0 : ℝ) < y ^ 2 + 1 / 4 := by positivity
  have hne : (y ^ 2 + 1 / 4) ^ 3 ≠ 0 := by positivity
  have hne' : (y ^ 2 + 1 / 4) ≠ 0 := ne_of_gt hpos
  have harc : (1 : ℝ) + (2 * y) ^ 2 ≠ 0 := by positivity
  have h5 : HasDerivAt (fun u : ℝ => u ^ 5) ((5 : ℕ) * y ^ 4) y := by
    simpa using hasDerivAt_pow 5 y
  have h3 : HasDerivAt (fun u : ℝ => u ^ 3) ((3 : ℕ) * y ^ 2) y := by
    simpa using hasDerivAt_pow 3 y
  have hP : HasDerivAt (fun u : ℝ => -(1 / 2) * u ^ 5 + 5 / 12 * u ^ 3 - 1 / 32 * u)
      (-(1 / 2) * ((5 : ℕ) * y ^ 4) + 5 / 12 * ((3 : ℕ) * y ^ 2) - 1 / 32 * 1) y :=
    ((h5.const_mul _).add (h3.const_mul _)).sub ((hasDerivAt_id y).const_mul _)
  have hb : HasDerivAt (fun u : ℝ => u ^ 2 + 1 / 4) (2 * y) y := by
    simpa using (hasDerivAt_pow 2 y).add_const (1 / 4)
  have hD : HasDerivAt (fun u : ℝ => (u ^ 2 + 1 / 4) ^ 3)
      ((3 : ℕ) * (y ^ 2 + 1 / 4) ^ 2 * (2 * y)) y := by
    simpa using hb.pow 3
  have hR : HasDerivAt (fun u : ℝ => (-(1 / 2) * u ^ 5 + 5 / 12 * u ^ 3 - 1 / 32 * u) /
      (u ^ 2 + 1 / 4) ^ 3)
      (((-(1 / 2) * ((5 : ℕ) * y ^ 4) + 5 / 12 * ((3 : ℕ) * y ^ 2) - 1 / 32 * 1) *
          (y ^ 2 + 1 / 4) ^ 3 -
        (-(1 / 2) * y ^ 5 + 5 / 12 * y ^ 3 - 1 / 32 * y) *
          ((3 : ℕ) * (y ^ 2 + 1 / 4) ^ 2 * (2 * y))) / ((y ^ 2 + 1 / 4) ^ 3) ^ 2) y :=
    hP.div hD hne
  have hmul : HasDerivAt (fun u : ℝ => 2 * u) 2 y := by
    simpa using (hasDerivAt_id y).const_mul (2 : ℝ)
  have hA : HasDerivAt (fun u : ℝ => Real.arctan (2 * u))
      (1 / (1 + (2 * y) ^ 2) * 2) y :=
    (Real.hasDerivAt_arctan (2 * y)).comp y hmul
  have hsum := hR.add hA
  unfold poleProfilePrimitive poleProfilePrimitiveRat
  convert hsum using 1
  rw [poleProfile]
  push_cast
  field_simp
  ring

/-! ### Integrability -/

/-- The pointwise majorant `p(y)² ≤ (y² + 1/4)^(-1)`. -/
theorem poleProfile_sq_le (y : ℝ) : poleProfile y ^ 2 ≤ (y ^ 2 + 1 / 4)⁻¹ := by
  have hpos : (0 : ℝ) < y ^ 2 + 1 / 4 := by positivity
  have hkey : y ^ 2 * (3 / 4 - y ^ 2) ^ 2 ≤ (y ^ 2 + 1 / 4) ^ 3 := by
    nlinarith [sq_nonneg (y ^ 2 - 1 / 12), sq_nonneg y]
  have h2 := mul_le_mul_of_nonneg_right hkey hpos.le
  rw [poleProfile, div_pow, inv_eq_one_div,
    div_le_div_iff₀ (by positivity) hpos]
  nlinarith [h2]

theorem continuous_poleProfile : Continuous poleProfile := by
  unfold poleProfile
  refine Continuous.div (by fun_prop) (by fun_prop) fun x => ?_
  positivity

theorem integrable_poleProfile_sq : Integrable (fun y : ℝ => poleProfile y ^ 2) := by
  have hg : Integrable (fun y : ℝ => 4 * (1 + y ^ 2)⁻¹) := integrable_inv_one_add_sq.const_mul 4
  refine hg.mono' ((continuous_poleProfile.pow 2).aestronglyMeasurable) ?_
  filter_upwards with y
  have h1 := poleProfile_sq_le y
  have hA : (0 : ℝ) < y ^ 2 + 1 / 4 := by positivity
  have hB : (0 : ℝ) < 1 + y ^ 2 := by positivity
  have h2 : (y ^ 2 + 1 / 4)⁻¹ ≤ 4 * (1 + y ^ 2)⁻¹ := by
    rw [inv_eq_one_div, inv_eq_one_div, mul_one_div, div_le_div_iff₀ hA hB]
    nlinarith [sq_nonneg y]
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  linarith

/-! ### The rational part vanishes at both ends -/

theorem abs_poleProfilePrimitiveRat_le {y : ℝ} (hy : 1 ≤ y) :
    |poleProfilePrimitiveRat y| ≤ y⁻¹ := by
  have hpos : (0 : ℝ) < y := by linarith
  have hd : (0 : ℝ) < (y ^ 2 + 1 / 4) ^ 3 := by positivity
  have h35 : y ^ 3 ≤ y ^ 5 := by
    nlinarith [mul_nonneg (pow_nonneg hpos.le 3) (by nlinarith : (0 : ℝ) ≤ y ^ 2 - 1)]
  have h15 : y ≤ y ^ 5 := by
    nlinarith [mul_nonneg hpos.le (by nlinarith : (0 : ℝ) ≤ y ^ 4 - 1)]
  have hnum : |(-(1 / 2) * y ^ 5 + 5 / 12 * y ^ 3 - 1 / 32 * y)| ≤ y ^ 5 := by
    rw [abs_le]
    constructor
    · nlinarith [pow_nonneg hpos.le 5]
    · nlinarith [pow_nonneg hpos.le 5]
  have h6 : y ^ 6 ≤ (y ^ 2 + 1 / 4) ^ 3 := by
    nlinarith [pow_nonneg hpos.le 4, sq_nonneg y]
  rw [poleProfilePrimitiveRat, abs_div, abs_of_pos hd, inv_eq_one_div,
    div_le_div_iff₀ hd hpos]
  nlinarith [mul_le_mul_of_nonneg_right hnum hpos.le, h6]

theorem tendsto_poleProfilePrimitiveRat_atTop :
    Tendsto poleProfilePrimitiveRat atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun y => norm_nonneg _) ?_ tendsto_inv_atTop_zero
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with y hy
  simpa [Real.norm_eq_abs] using abs_poleProfilePrimitiveRat_le hy

theorem poleProfilePrimitiveRat_neg (y : ℝ) :
    poleProfilePrimitiveRat (-y) = -poleProfilePrimitiveRat y := by
  have hne : (y ^ 2 + 1 / 4) ≠ 0 := by positivity
  unfold poleProfilePrimitiveRat
  field_simp
  ring

theorem tendsto_poleProfilePrimitiveRat_atBot :
    Tendsto poleProfilePrimitiveRat atBot (nhds 0) := by
  have h := tendsto_poleProfilePrimitiveRat_atTop.neg
  have h2 := h.comp Filter.tendsto_neg_atBot_atTop
  rw [neg_zero] at h2
  refine h2.congr fun y => ?_
  simp [Function.comp, poleProfilePrimitiveRat_neg]

/-! ### The two half-line limits of the primitive -/

theorem tendsto_poleProfilePrimitive_atTop :
    Tendsto poleProfilePrimitive atTop (nhds (Real.pi / 2)) := by
  have harc : Tendsto (fun y : ℝ => Real.arctan (2 * y)) atTop (nhds (Real.pi / 2)) :=
    (tendsto_nhds_of_tendsto_nhdsWithin Real.tendsto_arctan_atTop).comp
      (Filter.Tendsto.const_mul_atTop (by norm_num) tendsto_id)
  have := tendsto_poleProfilePrimitiveRat_atTop.add harc
  simpa [poleProfilePrimitive] using this

theorem tendsto_poleProfilePrimitive_atBot :
    Tendsto poleProfilePrimitive atBot (nhds (-(Real.pi / 2))) := by
  have harc : Tendsto (fun y : ℝ => Real.arctan (2 * y)) atBot (nhds (-(Real.pi / 2))) :=
    (tendsto_nhds_of_tendsto_nhdsWithin Real.tendsto_arctan_atBot).comp
      (Filter.Tendsto.const_mul_atBot (by norm_num) tendsto_id)
  have := tendsto_poleProfilePrimitiveRat_atBot.add harc
  simpa [poleProfilePrimitive] using this

/-! ### The value of the profile energy -/

theorem poleProfilePrimitive_zero : poleProfilePrimitive 0 = 0 := by
  simp [poleProfilePrimitive, poleProfilePrimitiveRat]

theorem integral_Ioi_poleProfile_sq :
    ∫ y in Set.Ioi (0 : ℝ), poleProfile y ^ 2 = Real.pi / 2 := by
  have hcont : ContinuousWithinAt poleProfilePrimitive (Set.Ici 0) 0 :=
    (HasDerivAt.continuousAt (hasDerivAt_poleProfilePrimitive 0)).continuousWithinAt
  have hmain := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto hcont
    (fun x _ => hasDerivAt_poleProfilePrimitive x)
    integrable_poleProfile_sq.integrableOn tendsto_poleProfilePrimitive_atTop
  rw [hmain, poleProfilePrimitive_zero, sub_zero]

theorem integral_Iic_poleProfile_sq :
    ∫ y in Set.Iic (0 : ℝ), poleProfile y ^ 2 = Real.pi / 2 := by
  have hcont : ContinuousWithinAt poleProfilePrimitive (Set.Iic 0) 0 :=
    (HasDerivAt.continuousAt (hasDerivAt_poleProfilePrimitive 0)).continuousWithinAt
  have hmain := MeasureTheory.integral_Iic_of_hasDerivAt_of_tendsto hcont
    (fun x _ => hasDerivAt_poleProfilePrimitive x)
    integrable_poleProfile_sq.integrableOn tendsto_poleProfilePrimitive_atBot
  rw [hmain, poleProfilePrimitive_zero]
  ring

/-- **The centred-pole profile energy.** `∫_ℝ (y(3/4 - y²)/(y² + 1/4)²)² dy = π`. -/
theorem integral_poleProfile_sq : ∫ y : ℝ, poleProfile y ^ 2 = Real.pi := by
  have hsplit := MeasureTheory.integral_add_compl (s := Set.Iic (0 : ℝ)) measurableSet_Iic
    integrable_poleProfile_sq
  rw [Set.compl_Iic, integral_Iic_poleProfile_sq, integral_Ioi_poleProfile_sq] at hsplit
  rw [← hsplit]
  ring

end

end HTGeometry
