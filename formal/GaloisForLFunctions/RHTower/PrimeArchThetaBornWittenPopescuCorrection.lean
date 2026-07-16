import GaloisForLFunctions.HTGeometry.HalfLineQuadraticPopescuBoundary
import GaloisForLFunctions.RHTower.PrimeArchThetaBornWittenCurvatureGap

/-!
# Strict corrected Brascamp--Lieb weight for the theta Born--Witten clock

The first one-dimensional Popescu refinement of Brascamp--Lieb requires positivity of

`3(V''')² + 8(V'')³ - 2 V'''' V'' - 2 V''' V'' V'`.

For the exact theta Born--Witten density, all four logarithmic derivatives are rational functions
of the positive readout coordinate `q`.  Their correction numerator is a positive polynomial
divided by `q⁶`.  Thus the iterated Witten-resolvent correction is unconditionally available for
every positive theta atom; it is not a new hypothesis on the source.
-/

open Complex Real MeasureTheory Set Filter Topology Polynomial
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Third logarithmic derivative of the theta Born--Witten density in the readout coordinate. -/
def thetaCuspBornWittenLogThirdDerivative (n : ℕ) (x : ℝ) : ℝ :=
  let q := thetaCuspBornWittenWeight n x
  (2 * q + 3) * (4 - 6 / q ^ 2 - 18 / q ^ 3)

/-- Fourth logarithmic derivative of the theta Born--Witten density in the readout coordinate. -/
def thetaCuspBornWittenLogFourthDerivative (n : ℕ) (x : ℝ) : ℝ :=
  let q := thetaCuspBornWittenWeight n x
  (2 * q + 3) * (8 + 12 / q ^ 2 + 108 / q ^ 3 + 162 / q ^ 4)

/-- Denominator-free first Popescu-correction value of the exact theta density. -/
def thetaCuspBornWittenPopescuNumerator (n : ℕ) (x : ℝ) : ℝ :=
  HTGeometry.oneDimBrascampLiebFirstCorrectionNumerator
    (2 * thetaCuspBornWittenSuperpotential n x)
    (thetaCuspBornWittenLogCurvature n x)
    (thetaCuspBornWittenLogThirdDerivative n x)
    (thetaCuspBornWittenLogFourthDerivative n x)

/-- The half-line inverse-curvature observable selected by the quadratic test `f(x)=x²`. -/
def thetaCuspBornWittenQuadraticInverseCurvatureObservable
    (n : ℕ) (x : ℝ) : ℝ :=
  HTGeometry.oneDimQuadraticInverseCurvatureObservable
    (thetaCuspBornWittenLogCurvature n) x

/-- Pointwise Popescu correction density for the quadratic theta-clock observable. -/
def thetaCuspBornWittenQuadraticPopescuCorrectionDensity
    (n : ℕ) (x : ℝ) : ℝ :=
  HTGeometry.oneDimQuadraticPopescuCorrectionDensity x
    (2 * thetaCuspBornWittenSuperpotential n x)
    (thetaCuspBornWittenLogCurvature n x)
    (thetaCuspBornWittenLogThirdDerivative n x)
    (thetaCuspBornWittenLogFourthDerivative n x)

/-- Positive polynomial left after clearing the sixth power of the theta readout weight. -/
def thetaBornPopescuPolynomial (q : ℝ) : ℝ :=
  96 * q ^ 7 + 232 * q ^ 6 + 624 * q ^ 5 + 768 * q ^ 4 - 36 * q ^ 3 +
    630 * q ^ 2 + 162 * q + 324

/-- The theta readout coordinate stays strictly beyond `3/2` on the physical half-line. -/
theorem three_halves_lt_thetaCuspBornWittenWeight
    {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 ≤ x) :
    (3 / 2 : ℝ) < thetaCuspBornWittenWeight n x := by
  have ht := thetaCuspMorseScale_pi_le hn hx
  rw [thetaCuspBornWittenWeight_eq]
  nlinarith [Real.pi_gt_three]

/-- Exact readout-coordinate form of the first logarithmic derivative. -/
theorem two_thetaCuspBornWittenSuperpotential_eq_readoutProfile
    {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 ≤ x) :
    2 * thetaCuspBornWittenSuperpotential n x =
      2 * thetaCuspBornWittenWeight n x - 3 / 2 -
        3 / thetaCuspBornWittenWeight n x := by
  have hq := thetaCuspBornWittenWeight_pos hn hx
  have ht : thetaCuspMorseScale n x =
      thetaCuspBornWittenWeight n x + 3 / 2 := by
    rw [thetaCuspBornWittenWeight_eq]
    ring
  simp only [thetaCuspBornWittenSuperpotential,
    thetaCuspMorseSuperpotential]
  rw [ht]
  field_simp [hq.ne']
  ring

/-- Differentiating the exact log curvature produces the displayed third-derivative profile. -/
theorem hasDerivAt_thetaCuspBornWittenLogCurvature
    {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt (thetaCuspBornWittenLogCurvature n)
      (thetaCuspBornWittenLogThirdDerivative n x) x := by
  let q : ℝ → ℝ := thetaCuspBornWittenWeight n
  let t : ℝ → ℝ := thetaCuspMorseScale n
  have hqpos : 0 < q x := thetaCuspBornWittenWeight_pos hn hx
  have hq : HasDerivAt q (2 * t x) x :=
    hasDerivAt_thetaCuspBornWittenWeight n x
  have ht : HasDerivAt t (2 * t x) x :=
    hasDerivAt_thetaCuspMorseScale n x
  have htq : t x = q x + 3 / 2 := by
    dsimp only [q, t]
    rw [thetaCuspBornWittenWeight_eq]
    ring
  have hquot := ht.div (hq.pow 2) (pow_ne_zero 2 hqpos.ne')
  simp only [Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSubDiff, pow_one] at hquot
  have hprofile : HasDerivAt
      (fun y : ℝ => 4 * t y + 6 * t y / q y ^ 2)
      (thetaCuspBornWittenLogThirdDerivative n x) x := by
    convert (ht.const_mul 4).add (hquot.const_mul 6) using 1
    · funext y
      simp only [Pi.add_apply, Pi.div_apply, Pi.pow_apply]
      ring
    · dsimp only [thetaCuspBornWittenLogThirdDerivative, q]
      dsimp only [q, t] at htq ⊢
      rw [htq]
      field_simp [hqpos.ne']
      ring_nf
      field_simp [hqpos.ne']
      ring
  convert hprofile using 1
  funext y
  dsimp only [q, t]
  simp only [thetaCuspBornWittenLogCurvature,
    thetaCuspBornWittenCurvature]
  ring

/-- Differentiating the third profile produces the exact fourth logarithmic derivative. -/
theorem hasDerivAt_thetaCuspBornWittenLogThirdDerivative
    {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt (thetaCuspBornWittenLogThirdDerivative n)
      (thetaCuspBornWittenLogFourthDerivative n x) x := by
  let q : ℝ → ℝ := thetaCuspBornWittenWeight n
  let r : ℝ → ℝ := fun y => 2 * q y + 3
  have hqpos : 0 < q x := thetaCuspBornWittenWeight_pos hn hx
  have htq : thetaCuspMorseScale n x = q x + 3 / 2 := by
    dsimp only [q]
    rw [thetaCuspBornWittenWeight_eq]
    ring
  have hq : HasDerivAt q (r x) x := by
    convert hasDerivAt_thetaCuspBornWittenWeight n x using 1
    dsimp only [r]
    rw [htq]
    ring
  have hr : HasDerivAt r (2 * r x) x := by
    exact (hq.const_mul 2).add_const 3
  have hq2 := hq.pow 2
  have hq3 := hq.pow 3
  have hrq2 := hr.div hq2 (pow_ne_zero 2 hqpos.ne')
  have hrq3 := hr.div hq3 (pow_ne_zero 3 hqpos.ne')
  simp only [Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSubDiff, pow_one] at hrq2 hrq3
  have hprofile : HasDerivAt
      (fun y : ℝ => 4 * r y - 6 * r y / q y ^ 2 - 18 * r y / q y ^ 3)
      (thetaCuspBornWittenLogFourthDerivative n x) x := by
    convert (hr.const_mul 4).sub (hrq2.const_mul 6) |>.sub (hrq3.const_mul 18) using 1
    · funext y
      simp only [Pi.sub_apply, Pi.div_apply, Pi.pow_apply]
      ring
    · dsimp only [thetaCuspBornWittenLogFourthDerivative, r, q]
      dsimp only [r, q] at hqpos ⊢
      field_simp [hqpos.ne']
      ring
  convert hprofile using 1
  funext y
  simp only [thetaCuspBornWittenLogThirdDerivative, r, q]
  ring

/-- Clearing `q⁶` from the Popescu correction gives one explicit positive-polynomial value. -/
theorem thetaCuspBornWittenWeight_six_mul_popescuNumerator_eq
    {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 ≤ x) :
    thetaCuspBornWittenWeight n x ^ 6 *
        thetaCuspBornWittenPopescuNumerator n x =
      (2 * thetaCuspBornWittenWeight n x + 3) ^ 2 *
        thetaBornPopescuPolynomial (thetaCuspBornWittenWeight n x) := by
  have hq := thetaCuspBornWittenWeight_pos hn hx
  rw [thetaCuspBornWittenPopescuNumerator,
    HTGeometry.oneDimBrascampLiebFirstCorrectionNumerator,
    two_thetaCuspBornWittenSuperpotential_eq_readoutProfile hn hx,
    thetaCuspBornWittenLogCurvature_eq_readoutProfile hn hx]
  unfold thetaCuspBornWittenLogThirdDerivative
    thetaCuspBornWittenLogFourthDerivative thetaBornPopescuPolynomial
  field_simp [hq.ne']
  ring

/-- The cleared correction polynomial is strictly positive throughout the theta range. -/
theorem thetaBornPopescuPolynomial_pos
    {q : ℝ} (hq : (3 / 2 : ℝ) < q) :
    0 < thetaBornPopescuPolynomial q := by
  have hq0 : 0 < q := by linarith
  have hlinear : 0 < 768 * q - 36 := by nlinarith
  rw [show thetaBornPopescuPolynomial q =
      96 * q ^ 7 + 232 * q ^ 6 + 624 * q ^ 5 +
        q ^ 3 * (768 * q - 36) + 630 * q ^ 2 + 162 * q + 324 by
    unfold thetaBornPopescuPolynomial
    ring]
  positivity

/-- The actual theta Born--Witten logarithmic potential satisfies Popescu's strict first-correction
condition at every point of every positive atom. -/
theorem thetaCuspBornWittenPopescuNumerator_pos
    {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 ≤ x) :
    0 < thetaCuspBornWittenPopescuNumerator n x := by
  let q := thetaCuspBornWittenWeight n x
  have hq : 0 < q := thetaCuspBornWittenWeight_pos hn hx
  have hqRange : (3 / 2 : ℝ) < q :=
    three_halves_lt_thetaCuspBornWittenWeight hn hx
  have hpoly : 0 < thetaBornPopescuPolynomial q :=
    thetaBornPopescuPolynomial_pos hqRange
  have hr : 0 < 2 * q + 3 := by linarith
  have hcleared : 0 < q ^ 6 * thetaCuspBornWittenPopescuNumerator n x := by
    rw [thetaCuspBornWittenWeight_six_mul_popescuNumerator_eq hn hx]
    exact mul_pos (sq_pos_of_pos hr) hpoly
  by_contra hnot
  have hnonpos : thetaCuspBornWittenPopescuNumerator n x ≤ 0 := le_of_not_gt hnot
  have : q ^ 6 * thetaCuspBornWittenPopescuNumerator n x ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hq.le 6) hnonpos
  linarith

/-- The correction denominator `1 + A((V'')⁻¹)` required by the refined inequality is strictly
positive for the actual theta source. -/
theorem thetaCuspBornWittenPopescuCorrectionDenominator_pos
    {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 ≤ x) :
    0 < 1 + HTGeometry.oneDimBrascampLiebCorrectionA
      (2 * thetaCuspBornWittenSuperpotential n x)
      (thetaCuspBornWittenLogCurvature n x)
      (1 / thetaCuspBornWittenLogCurvature n x)
      (HTGeometry.inverseCurvatureFirstJet
        (thetaCuspBornWittenLogCurvature n x)
        (thetaCuspBornWittenLogThirdDerivative n x))
      (HTGeometry.inverseCurvatureSecondJet
        (thetaCuspBornWittenLogCurvature n x)
        (thetaCuspBornWittenLogThirdDerivative n x)
        (thetaCuspBornWittenLogFourthDerivative n x)) := by
  have hcurv : 0 < thetaCuspBornWittenLogCurvature n x := by
    have h := nineteen_le_thetaCuspBornWittenLogCurvature hn hx
    linarith
  rw [HTGeometry.one_add_oneDimBrascampLiebCorrectionA_inverseCurvature_pos_iff hcurv]
  exact thetaCuspBornWittenPopescuNumerator_pos hn hx

/-- Equivalently, the second iterated Witten weight itself is strictly positive. -/
theorem thetaCuspBornWittenPopescuSecondWeight_pos
    {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 ≤ x) :
    0 < HTGeometry.oneDimBrascampLiebSecondWeight
      (2 * thetaCuspBornWittenSuperpotential n x)
      (thetaCuspBornWittenLogCurvature n x)
      (thetaCuspBornWittenLogThirdDerivative n x)
      (thetaCuspBornWittenLogFourthDerivative n x) := by
  have hcurv : 0 < thetaCuspBornWittenLogCurvature n x := by
    have h := nineteen_le_thetaCuspBornWittenLogCurvature hn hx
    linarith
  rw [HTGeometry.oneDimBrascampLiebSecondWeight_pos_iff hcurv]
  exact thetaCuspBornWittenPopescuNumerator_pos hn hx

/-! ### Half-line compatibility of the quadratic correction -/

/-- The quadratic inverse-curvature observable has the required zero endpoint trace.  This
removes the first Dirichlet boundary obstruction without reflecting the nonsymmetric theta
potential across the origin. -/
@[simp] theorem thetaCuspBornWittenQuadraticInverseCurvatureObservable_zero
    (n : ℕ) :
    thetaCuspBornWittenQuadraticInverseCurvatureObservable n 0 = 0 := by
  simp [thetaCuspBornWittenQuadraticInverseCurvatureObservable]

/-- The derivative of the half-line quadratic observable is the exact local correction score. -/
theorem hasDerivAt_thetaCuspBornWittenQuadraticInverseCurvatureObservable
    {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt (thetaCuspBornWittenQuadraticInverseCurvatureObservable n)
      (HTGeometry.oneDimQuadraticInverseCurvatureScore x
        (thetaCuspBornWittenLogCurvature n x)
        (thetaCuspBornWittenLogThirdDerivative n x)) x := by
  apply HTGeometry.hasDerivAt_oneDimQuadraticInverseCurvatureObservable
    (hasDerivAt_thetaCuspBornWittenLogCurvature hn hx)
  exact (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 19)
    (nineteen_le_thetaCuspBornWittenLogCurvature hn hx)).ne'

/-- The quadratic correction score is strictly positive at the half-line endpoint. -/
theorem thetaCuspBornWittenQuadraticInverseCurvatureScore_zero_pos
    {n : ℕ} (hn : 0 < n) :
    0 < HTGeometry.oneDimQuadraticInverseCurvatureScore 0
      (thetaCuspBornWittenLogCurvature n 0)
      (thetaCuspBornWittenLogThirdDerivative n 0) := by
  rw [HTGeometry.oneDimQuadraticInverseCurvatureScore_zero]
  have hcurv : 0 < thetaCuspBornWittenLogCurvature n 0 := by
    have h := nineteen_le_thetaCuspBornWittenLogCurvature (x := 0) hn (by norm_num)
    linarith
  exact div_pos (by norm_num) hcurv

/-- The actual quadratic Popescu correction density is nonnegative at every point of every
positive theta atom. -/
theorem thetaCuspBornWittenQuadraticPopescuCorrectionDensity_nonneg
    {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ thetaCuspBornWittenQuadraticPopescuCorrectionDensity n x := by
  unfold thetaCuspBornWittenQuadraticPopescuCorrectionDensity
  apply HTGeometry.oneDimQuadraticPopescuCorrectionDensity_nonneg
  · have h := nineteen_le_thetaCuspBornWittenLogCurvature hn hx
    linarith
  · exact thetaCuspBornWittenPopescuNumerator_pos hn hx

/-- The correction density is strict exactly away from the source-defined dilation-curvature
incidence `V'' = x V'''`. -/
theorem thetaCuspBornWittenQuadraticPopescuCorrectionDensity_pos_iff
    {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 ≤ x) :
    0 < thetaCuspBornWittenQuadraticPopescuCorrectionDensity n x ↔
      thetaCuspBornWittenLogCurvature n x -
        x * thetaCuspBornWittenLogThirdDerivative n x ≠ 0 := by
  unfold thetaCuspBornWittenQuadraticPopescuCorrectionDensity
  apply HTGeometry.oneDimQuadraticPopescuCorrectionDensity_pos_iff
  · have h := nineteen_le_thetaCuspBornWittenLogCurvature hn hx
    linarith
  · exact thetaCuspBornWittenPopescuNumerator_pos hn hx

/-- In particular, the theta source supplies a genuinely nonzero Popescu correction at the
half-line endpoint; the quadratic observable is not in the equality family. -/
theorem thetaCuspBornWittenQuadraticPopescuCorrectionDensity_zero_pos
    {n : ℕ} (hn : 0 < n) :
    0 < thetaCuspBornWittenQuadraticPopescuCorrectionDensity n 0 := by
  rw [thetaCuspBornWittenQuadraticPopescuCorrectionDensity_pos_iff hn (by norm_num)]
  have hcurv : 0 < thetaCuspBornWittenLogCurvature n 0 := by
    have h := nineteen_le_thetaCuspBornWittenLogCurvature (x := 0) hn (by norm_num)
    linarith
  simpa using hcurv.ne'

/-- The source-specific quadratic correction density is continuous throughout the physical
half-line. -/
theorem continuousAt_thetaCuspBornWittenQuadraticPopescuCorrectionDensity
    {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 ≤ x) :
    ContinuousAt (thetaCuspBornWittenQuadraticPopescuCorrectionDensity n) x := by
  have hV₁ : ContinuousAt
      (fun y : ℝ => 2 * thetaCuspBornWittenSuperpotential n y) x :=
    (hasDerivAt_two_thetaCuspBornWittenSuperpotential hn hx).continuousAt
  have hV₂ : ContinuousAt (thetaCuspBornWittenLogCurvature n) x :=
    (hasDerivAt_thetaCuspBornWittenLogCurvature hn hx).continuousAt
  have hV₃ : ContinuousAt (thetaCuspBornWittenLogThirdDerivative n) x :=
    (hasDerivAt_thetaCuspBornWittenLogThirdDerivative hn hx).continuousAt
  have hq : thetaCuspBornWittenWeight n x ≠ 0 :=
    (thetaCuspBornWittenWeight_pos hn hx).ne'
  have hV₄ : ContinuousAt (thetaCuspBornWittenLogFourthDerivative n) x := by
    unfold thetaCuspBornWittenLogFourthDerivative
    have hqcont := (hasDerivAt_thetaCuspBornWittenWeight n x).continuousAt
    have hq2 : thetaCuspBornWittenWeight n x ^ 2 ≠ 0 := pow_ne_zero 2 hq
    have hq3 : thetaCuspBornWittenWeight n x ^ 3 ≠ 0 := pow_ne_zero 3 hq
    have hq4 : thetaCuspBornWittenWeight n x ^ 4 ≠ 0 := pow_ne_zero 4 hq
    fun_prop (disch := aesop)
  have hcurv : thetaCuspBornWittenLogCurvature n x ≠ 0 := by
    have h := nineteen_le_thetaCuspBornWittenLogCurvature hn hx
    linarith
  have hinv : ContinuousAt
      (fun y : ℝ => 1 / thetaCuspBornWittenLogCurvature n y) x := by
    exact continuousAt_const.div hV₂ hcurv
  have hjet₁ : ContinuousAt (fun y : ℝ =>
      HTGeometry.inverseCurvatureFirstJet
        (thetaCuspBornWittenLogCurvature n y)
        (thetaCuspBornWittenLogThirdDerivative n y)) x := by
    unfold HTGeometry.inverseCurvatureFirstJet
    fun_prop (disch := aesop)
  have hjet₂ : ContinuousAt (fun y : ℝ =>
      HTGeometry.inverseCurvatureSecondJet
        (thetaCuspBornWittenLogCurvature n y)
        (thetaCuspBornWittenLogThirdDerivative n y)
        (thetaCuspBornWittenLogFourthDerivative n y)) x := by
    unfold HTGeometry.inverseCurvatureSecondJet
    fun_prop (disch := aesop)
  have hA : ContinuousAt (fun y : ℝ =>
      HTGeometry.oneDimBrascampLiebCorrectionA
        (2 * thetaCuspBornWittenSuperpotential n y)
        (thetaCuspBornWittenLogCurvature n y)
        (1 / thetaCuspBornWittenLogCurvature n y)
        (HTGeometry.inverseCurvatureFirstJet
          (thetaCuspBornWittenLogCurvature n y)
          (thetaCuspBornWittenLogThirdDerivative n y))
        (HTGeometry.inverseCurvatureSecondJet
          (thetaCuspBornWittenLogCurvature n y)
          (thetaCuspBornWittenLogThirdDerivative n y)
          (thetaCuspBornWittenLogFourthDerivative n y))) x := by
    unfold HTGeometry.oneDimBrascampLiebCorrectionA
    fun_prop (disch := aesop)
  have hscore : ContinuousAt (fun y : ℝ =>
      HTGeometry.oneDimQuadraticInverseCurvatureScore y
        (thetaCuspBornWittenLogCurvature n y)
        (thetaCuspBornWittenLogThirdDerivative n y)) x := by
    unfold HTGeometry.oneDimQuadraticInverseCurvatureScore
    fun_prop (disch := aesop)
  have hden : 1 + HTGeometry.oneDimBrascampLiebCorrectionA
      (2 * thetaCuspBornWittenSuperpotential n x)
      (thetaCuspBornWittenLogCurvature n x)
      (1 / thetaCuspBornWittenLogCurvature n x)
      (HTGeometry.inverseCurvatureFirstJet
        (thetaCuspBornWittenLogCurvature n x)
        (thetaCuspBornWittenLogThirdDerivative n x))
      (HTGeometry.inverseCurvatureSecondJet
        (thetaCuspBornWittenLogCurvature n x)
        (thetaCuspBornWittenLogThirdDerivative n x)
        (thetaCuspBornWittenLogFourthDerivative n x)) ≠ 0 :=
    (thetaCuspBornWittenPopescuCorrectionDenominator_pos hn hx).ne'
  change ContinuousAt (fun y : ℝ =>
    HTGeometry.oneDimQuadraticInverseCurvatureScore y
        (thetaCuspBornWittenLogCurvature n y)
        (thetaCuspBornWittenLogThirdDerivative n y) ^ 2 /
      (1 + HTGeometry.oneDimBrascampLiebCorrectionA
        (2 * thetaCuspBornWittenSuperpotential n y)
        (thetaCuspBornWittenLogCurvature n y)
        (1 / thetaCuspBornWittenLogCurvature n y)
        (HTGeometry.inverseCurvatureFirstJet
          (thetaCuspBornWittenLogCurvature n y)
          (thetaCuspBornWittenLogThirdDerivative n y))
        (HTGeometry.inverseCurvatureSecondJet
          (thetaCuspBornWittenLogCurvature n y)
          (thetaCuspBornWittenLogThirdDerivative n y)
          (thetaCuspBornWittenLogFourthDerivative n y)))) x
  exact (hscore.pow 2).div (continuousAt_const.add hA) hden

/-- Endpoint specialization of continuity. -/
theorem continuousAt_thetaCuspBornWittenQuadraticPopescuCorrectionDensity_zero
    {n : ℕ} (hn : 0 < n) :
    ContinuousAt (thetaCuspBornWittenQuadraticPopescuCorrectionDensity n) 0 :=
  continuousAt_thetaCuspBornWittenQuadraticPopescuCorrectionDensity hn (by norm_num)

/-- Raw quadratic correction integrand against the exact theta Born--Witten density. -/
def thetaCuspBornWittenQuadraticPopescuCorrectionIntegrand
    (n : ℕ) (x : ℝ) : ℝ :=
  thetaCuspBornWittenQuadraticPopescuCorrectionDensity n x *
    thetaCuspBornWittenAmplitude n x ^ 2

/-- Raw correction value subtracted from the variable-curvature quadratic bound. -/
def thetaCuspBornWittenQuadraticPopescuCorrectionValue (n : ℕ) : ℝ :=
  ∫ x : ℝ in Ioi 0,
    thetaCuspBornWittenQuadraticPopescuCorrectionIntegrand n x

/-- The raw correction integrand is nonnegative throughout the physical half-line. -/
theorem thetaCuspBornWittenQuadraticPopescuCorrectionIntegrand_nonneg
    {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ thetaCuspBornWittenQuadraticPopescuCorrectionIntegrand n x := by
  unfold thetaCuspBornWittenQuadraticPopescuCorrectionIntegrand
  exact mul_nonneg
    (thetaCuspBornWittenQuadraticPopescuCorrectionDensity_nonneg hn hx)
    (sq_nonneg _)

/-- The raw correction integrand is strictly positive at the endpoint. -/
theorem thetaCuspBornWittenQuadraticPopescuCorrectionIntegrand_zero_pos
    {n : ℕ} (hn : 0 < n) :
    0 < thetaCuspBornWittenQuadraticPopescuCorrectionIntegrand n 0 := by
  unfold thetaCuspBornWittenQuadraticPopescuCorrectionIntegrand
  exact mul_pos
    (thetaCuspBornWittenQuadraticPopescuCorrectionDensity_zero_pos hn)
    (sq_pos_of_pos (thetaCuspBornWittenAmplitude_pos hn (by norm_num)))

/-- Endpoint strictness persists on a right neighborhood. -/
theorem eventually_thetaCuspBornWittenQuadraticPopescuCorrectionIntegrand_pos
    {n : ℕ} (hn : 0 < n) :
    ∀ᶠ x in 𝓝 0,
      0 < thetaCuspBornWittenQuadraticPopescuCorrectionIntegrand n x := by
  have hcontinuous : ContinuousAt
      (thetaCuspBornWittenQuadraticPopescuCorrectionIntegrand n) 0 :=
    (continuousAt_thetaCuspBornWittenQuadraticPopescuCorrectionDensity_zero hn).mul
      ((hasDerivAt_thetaCuspBornWittenAmplitude hn (by norm_num)).continuousAt.pow 2)
  exact hcontinuous (Ioi_mem_nhds
    (thetaCuspBornWittenQuadraticPopescuCorrectionIntegrand_zero_pos hn))

/-- Once integrability is available, endpoint strictness upgrades nonnegativity to a genuinely
positive correction value.  Thus the corrected certificate is source-strict, not merely formally
weaker than the uncorrected one. -/
theorem thetaCuspBornWittenQuadraticPopescuCorrectionValue_pos_of_integrable
    {n : ℕ} (hn : 0 < n)
    (hintegrable : IntegrableOn
      (thetaCuspBornWittenQuadraticPopescuCorrectionIntegrand n) (Ioi 0)) :
    0 < thetaCuspBornWittenQuadraticPopescuCorrectionValue n := by
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioi 0)]
      thetaCuspBornWittenQuadraticPopescuCorrectionIntegrand n := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact thetaCuspBornWittenQuadraticPopescuCorrectionIntegrand_nonneg hn hx.le
  rw [thetaCuspBornWittenQuadraticPopescuCorrectionValue]
  apply (setIntegral_pos_iff_support_of_nonneg_ae hnonneg hintegrable).2
  have hevent :=
    eventually_thetaCuspBornWittenQuadraticPopescuCorrectionIntegrand_pos hn
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hevent
  have hsubset : Ioo (0 : ℝ) ε ⊆
      Function.support
          (thetaCuspBornWittenQuadraticPopescuCorrectionIntegrand n) ∩ Ioi 0 := by
    intro x hx
    have hxball : x ∈ Metric.ball (0 : ℝ) ε := by
      rw [Real.ball_zero_eq_Ioo]
      have hxpos : 0 < x := hx.1
      exact ⟨by linarith, hx.2⟩
    exact ⟨ne_of_gt (hball hxball), hx.1⟩
  have hvolume : 0 < volume (Ioo (0 : ℝ) ε) := by
    rw [Real.volume_Ioo]
    simpa only [sub_zero, ENNReal.ofReal_pos] using hε
  exact hvolume.trans_le (measure_mono hsubset)

end

end RHTower
