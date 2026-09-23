import GaloisForLFunctions.RHTower.PrimeArchThetaQuadraticSteinRobertson

/-!
# Morse reweighting of the first radial theta virial energy

The observable-weighted Born--Witten state is a square-root reweighting of the exact Morse
ground state.  Applying the ground-state/hypervirial identity before estimating the rational
curvature separates the quadratic Stein energy into ordinary theta-source moments, ordinary
Morse Gibbs moments, and one positive Fisher correction.  The correction has a sharp endpoint
bound, so the open energy certificate can be replaced by a finite-moment certificate.
-/

open Complex Real MeasureTheory Set Filter Topology Polynomial
open scoped BigOperators ENNReal

namespace RHTower

noncomputable section

/-- The polynomial field which multiplies the Morse-scale term in the quadratic virial energy. -/
def thetaCuspFirstRadialQuadraticMorseField (x : ℝ) : ℝ :=
  x ^ 2 * thetaCuspQuadraticSteinField x ^ 2

/-- Derivative of the polynomial Morse field. -/
def thetaCuspFirstRadialQuadraticMorseFieldDerivative (x : ℝ) : ℝ :=
  2 * x * thetaCuspQuadraticSteinField x ^ 2 +
    2 * x ^ 2 * thetaCuspQuadraticSteinField x *
      thetaCuspQuadraticSteinFieldDerivative x

/-- The non-Morse-scale part of the radial curvature/field-gradient density. -/
def thetaCuspFirstRadialQuadraticMorseRadialField (x : ℝ) : ℝ :=
  2 * thetaCuspQuadraticSteinField x ^ 2 +
    x ^ 2 * thetaCuspQuadraticSteinFieldDerivative x ^ 2

/-- Coefficient of the observable-weighted Morse density after the hypervirial integration. -/
def thetaCuspFirstRadialQuadraticMorseSourceField (x : ℝ) : ℝ :=
  5 * thetaCuspFirstRadialQuadraticMorseField x +
    2 * thetaCuspFirstRadialQuadraticMorseFieldDerivative x +
      thetaCuspFirstRadialQuadraticMorseRadialField x

/-- Coefficient of the undressed Morse density after the hypervirial integration. -/
def thetaCuspFirstRadialQuadraticMorseGibbsField (x : ℝ) : ℝ :=
  5 * thetaCuspFirstRadialQuadraticMorseField x +
    2 * thetaCuspFirstRadialQuadraticMorseFieldDerivative x

/-- The shifted Morse density `(q+1) psi^(2 : ℕ)`, selected because its derivative cancels the
`t q psi^(2 : ℕ)` scale insertion exactly. -/
def thetaCuspFirstAtomMorseShiftDensity (x : ℝ) : ℝ :=
  (thetaCuspBornWittenWeight 1 x + 1) * thetaCuspLiouvilleGibbsAtom 1 x

/-- Polynomial-Gaussian presentation of the shifted Morse density. -/
def thetaCuspFirstAtomMorseShiftPolynomial : ℝ[X] :=
  C Real.pi * X ^ 4 - C (1 / 2 : ℝ) * X ^ 2

theorem thetaCuspFirstAtomMorseShiftDensity_eq_polynomialAtom (x : ℝ) :
    thetaCuspFirstAtomMorseShiftDensity x =
      thetaCuspPolynomialAtom thetaCuspFirstAtomMorseShiftPolynomial 1 x := by
  simp only [thetaCuspFirstAtomMorseShiftDensity,
    thetaCuspFirstAtomMorseShiftPolynomial, thetaCuspBornWittenWeight_eq,
    thetaCuspMorseScale, thetaCuspLiouvilleGibbsAtom,
    thetaCuspPolynomialAtom, eval_sub, eval_mul, eval_C, eval_pow, eval_X,
    Nat.cast_one, one_mul]
  ring

theorem hasDerivAt_thetaCuspFirstRadialQuadraticMorseField (x : ℝ) :
    HasDerivAt thetaCuspFirstRadialQuadraticMorseField
      (thetaCuspFirstRadialQuadraticMorseFieldDerivative x) x := by
  have hx2 := (hasDerivAt_pow 2 x)
  have hP := hasDerivAt_thetaCuspQuadraticSteinField x
  have hraw := hx2.mul (hP.pow 2)
  have hraw' := hraw.congr_deriv
    (g' := thetaCuspFirstRadialQuadraticMorseFieldDerivative x) (by
      simp only [Pi.pow_apply,
        thetaCuspFirstRadialQuadraticMorseFieldDerivative]
      ring)
  exact hraw'.congr_of_eventuallyEq
    (Eventually.of_forall fun _ => rfl)

theorem thetaCuspFirstRadialQuadraticMorseField_eq (x : ℝ) :
    thetaCuspFirstRadialQuadraticMorseField x =
      x ^ 4 - x ^ 5 + x ^ 6 / 4 := by
  simp only [thetaCuspFirstRadialQuadraticMorseField,
    thetaCuspQuadraticSteinField]
  ring

theorem thetaCuspFirstRadialQuadraticMorseFieldDerivative_eq (x : ℝ) :
    thetaCuspFirstRadialQuadraticMorseFieldDerivative x =
      4 * x ^ 3 - 5 * x ^ 4 + 3 * x ^ 5 / 2 := by
  simp only [thetaCuspFirstRadialQuadraticMorseFieldDerivative,
    thetaCuspQuadraticSteinField, thetaCuspQuadraticSteinFieldDerivative]
  ring

theorem thetaCuspFirstRadialQuadraticMorseGibbsField_eq (x : ℝ) :
    thetaCuspFirstRadialQuadraticMorseGibbsField x =
      8 * x ^ 3 - 5 * x ^ 4 - 2 * x ^ 5 + 5 * x ^ 6 / 4 := by
  rw [thetaCuspFirstRadialQuadraticMorseGibbsField,
    thetaCuspFirstRadialQuadraticMorseField_eq,
    thetaCuspFirstRadialQuadraticMorseFieldDerivative_eq]
  ring

theorem thetaCuspFirstRadialQuadraticMorseSourceField_eq (x : ℝ) :
    thetaCuspFirstRadialQuadraticMorseSourceField x =
      3 * x ^ 2 + 4 * x ^ 3 - 7 * x ^ 4 / 2 -
        2 * x ^ 5 + 5 * x ^ 6 / 4 := by
  rw [thetaCuspFirstRadialQuadraticMorseSourceField,
    thetaCuspFirstRadialQuadraticMorseField_eq,
    thetaCuspFirstRadialQuadraticMorseFieldDerivative_eq]
  simp only [thetaCuspFirstRadialQuadraticMorseRadialField,
    thetaCuspQuadraticSteinField, thetaCuspQuadraticSteinFieldDerivative]
  ring

/-- Exact derivative of the shifted density.  This is the source-specific hypervirial value
relation which removes the `t q psi^(2 : ℕ)` insertion after integration by parts. -/
theorem hasDerivAt_thetaCuspFirstAtomMorseShiftDensity (x : ℝ) :
    HasDerivAt thetaCuspFirstAtomMorseShiftDensity
      ((5 / 2 : ℝ) * (thetaCuspBornWittenWeight 1 x + 1) *
          thetaCuspLiouvilleGibbsAtom 1 x -
        2 * thetaCuspMorseScale 1 x * thetaCuspBornWittenWeight 1 x *
          thetaCuspLiouvilleGibbsAtom 1 x) x := by
  have hq := (hasDerivAt_thetaCuspBornWittenWeight 1 x).add_const 1
  have hb0 := hasDerivAt_thetaCuspPolynomialAtom (X ^ 2) 1 x
  have hb : HasDerivAt (thetaCuspLiouvilleGibbsAtom 1)
      (((5 / 2 : ℝ) - 2 * thetaCuspMorseScale 1 x) *
        thetaCuspLiouvilleGibbsAtom 1 x) x := by
    have hb0' := hb0.congr_deriv
      (g' := ((5 / 2 : ℝ) - 2 * thetaCuspMorseScale 1 x) *
        thetaCuspLiouvilleGibbsAtom 1 x) (by
          simp only [thetaCuspLiouvilleGibbsAtom, thetaCuspLogDerivativeStep,
            thetaCuspPolynomialAtom, thetaCuspMorseScale, derivative_pow,
            derivative_X, Nat.cast_ofNat, mul_one, eval_add, eval_sub, eval_mul,
            eval_C, eval_X, eval_pow, Nat.cast_one, one_mul]
          ring)
    exact hb0'.congr_of_eventuallyEq
      (Eventually.of_forall fun _ => rfl)
  have hraw := hq.mul hb
  have hraw' := hraw.congr_deriv
    (g' := (5 / 2 : ℝ) * (thetaCuspBornWittenWeight 1 x + 1) *
        thetaCuspLiouvilleGibbsAtom 1 x -
      2 * thetaCuspMorseScale 1 x * thetaCuspBornWittenWeight 1 x *
        thetaCuspLiouvilleGibbsAtom 1 x) (by ring)
  exact hraw'.congr_of_eventuallyEq
    (Eventually.of_forall fun _ => rfl)

/-- Sharp half-line bound for the Fisher multiplier introduced by the square-root observable
reweighting.  Equality is attained at the endpoint `x=0`. -/
theorem thetaCuspFirstAtom_morseScale_div_weight_le_pi
    {x : ℝ} (hx : 0 ≤ x) :
    thetaCuspMorseScale 1 x / thetaCuspBornWittenWeight 1 x ≤
      Real.pi / (Real.pi - 3 / 2) := by
  have ht := thetaCuspMorseScale_pi_le (n := 1) (by norm_num) hx
  have hq := thetaCuspBornWittenWeight_pos (n := 1) (by norm_num) hx
  have hq' : 0 < thetaCuspMorseScale 1 x - 3 / 2 := by
    simpa only [← thetaCuspBornWittenWeight_eq] using hq
  have hpi : 0 < Real.pi - 3 / 2 := by nlinarith [Real.pi_gt_three]
  rw [thetaCuspBornWittenWeight_eq]
  apply (div_le_div_iff₀ hq' hpi).2
  nlinarith

/-- Pointwise Morse/Fisher decomposition of the first radial quadratic virial density. -/
theorem thetaCuspFirstRadialQuadraticVirial_morseFisher_decomposition
    {x : ℝ} (hx : 0 < x) :
    ((1 / 2 : ℝ) * thetaCuspQuadraticSteinField x ^ 2 *
          thetaCuspBornWittenRadialCurvature 1 1 x +
        (1 / 4 : ℝ) * thetaCuspQuadraticSteinFieldDerivative x ^ 2) *
      thetaCuspBornWittenRadialAmplitude 1 1 x ^ 2 =
    (4 * thetaCuspFirstRadialQuadraticMorseField x *
          thetaCuspMorseScale 1 x * thetaCuspBornWittenWeight 1 x +
        6 * thetaCuspFirstRadialQuadraticMorseField x *
          (thetaCuspMorseScale 1 x / thetaCuspBornWittenWeight 1 x) +
        thetaCuspFirstRadialQuadraticMorseRadialField x *
          thetaCuspBornWittenWeight 1 x) *
      thetaCuspLiouvilleGibbsAtom 1 x := by
  have hq := thetaCuspBornWittenWeight_pos (n := 1) (by norm_num) hx.le
  rw [thetaCuspBornWittenRadialAmplitude_sq,
    thetaCuspBornWittenAmplitude_sq (n := 1) (by norm_num) hx.le,
    thetaCuspMorseGroundState_sq]
  simp only [thetaCuspBornWittenRadialCurvature,
    thetaCuspBornWittenCurvature, thetaCuspFirstRadialQuadraticMorseField,
    thetaCuspFirstRadialQuadraticMorseRadialField, Nat.cast_one]
  field_simp [hx.ne', hq.ne']
  ring

/-- Polynomial integrability for the Morse field against any positive theta atom. -/
theorem integrableOn_thetaCuspFirstRadialQuadraticMorseField_mul_polynomialAtom
    (Q : ℝ[X]) {n : ℕ} (hn : 0 < n) :
    IntegrableOn (fun x : ℝ =>
      thetaCuspFirstRadialQuadraticMorseField x *
        thetaCuspPolynomialAtom Q n x) (Ioi 0) := by
  have h4 := integrableOn_pow_mul_thetaCuspPolynomialAtom_Ioi_of_pos 4 Q hn
  have h5 := integrableOn_pow_mul_thetaCuspPolynomialAtom_Ioi_of_pos 5 Q hn
  have h6 := integrableOn_pow_mul_thetaCuspPolynomialAtom_Ioi_of_pos 6 Q hn
  have h := (h4.sub h5).add (h6.const_mul (1 / 4 : ℝ))
  apply h.congr
  filter_upwards [] with x
  simp only [Pi.add_apply, Pi.sub_apply]
  rw [thetaCuspFirstRadialQuadraticMorseField_eq]
  ring

/-- Polynomial integrability for the derivative Morse field. -/
theorem integrableOn_thetaCuspFirstRadialQuadraticMorseFieldDerivative_mul_polynomialAtom
    (Q : ℝ[X]) {n : ℕ} (hn : 0 < n) :
    IntegrableOn (fun x : ℝ =>
      thetaCuspFirstRadialQuadraticMorseFieldDerivative x *
        thetaCuspPolynomialAtom Q n x) (Ioi 0) := by
  have h3 := integrableOn_pow_mul_thetaCuspPolynomialAtom_Ioi_of_pos 3 Q hn
  have h4 := integrableOn_pow_mul_thetaCuspPolynomialAtom_Ioi_of_pos 4 Q hn
  have h5 := integrableOn_pow_mul_thetaCuspPolynomialAtom_Ioi_of_pos 5 Q hn
  have h := ((h3.const_mul 4).sub (h4.const_mul 5)).add
    (h5.const_mul (3 / 2 : ℝ))
  apply h.congr
  filter_upwards [] with x
  simp only [Pi.add_apply, Pi.sub_apply]
  rw [thetaCuspFirstRadialQuadraticMorseFieldDerivative_eq]
  ring

theorem thetaCuspFirstAtomMorseShiftDerivative_eq_polynomialAtom (x : ℝ) :
    (5 / 2 : ℝ) * (thetaCuspBornWittenWeight 1 x + 1) *
          thetaCuspLiouvilleGibbsAtom 1 x -
        2 * thetaCuspMorseScale 1 x * thetaCuspBornWittenWeight 1 x *
          thetaCuspLiouvilleGibbsAtom 1 x =
      thetaCuspPolynomialAtom
        (thetaCuspLogDerivativeStep thetaCuspFirstAtomMorseShiftPolynomial) 1 x := by
  have hshift := hasDerivAt_thetaCuspFirstAtomMorseShiftDensity x
  have hfun : thetaCuspFirstAtomMorseShiftDensity =
      thetaCuspPolynomialAtom thetaCuspFirstAtomMorseShiftPolynomial 1 := by
    funext y
    exact thetaCuspFirstAtomMorseShiftDensity_eq_polynomialAtom y
  rw [hfun] at hshift
  exact hshift.unique
    (hasDerivAt_thetaCuspPolynomialAtom thetaCuspFirstAtomMorseShiftPolynomial 1 x)

theorem integrableOn_thetaCuspFirstRadialQuadraticMorseField_mul_shiftDerivative :
    IntegrableOn (fun x : ℝ =>
      thetaCuspFirstRadialQuadraticMorseField x *
        ((5 / 2 : ℝ) * (thetaCuspBornWittenWeight 1 x + 1) *
            thetaCuspLiouvilleGibbsAtom 1 x -
          2 * thetaCuspMorseScale 1 x * thetaCuspBornWittenWeight 1 x *
            thetaCuspLiouvilleGibbsAtom 1 x)) (Ioi 0) := by
  have h :=
    integrableOn_thetaCuspFirstRadialQuadraticMorseField_mul_polynomialAtom
      (thetaCuspLogDerivativeStep thetaCuspFirstAtomMorseShiftPolynomial)
      (by norm_num : 0 < (1 : ℕ))
  apply h.congr
  filter_upwards [] with x
  rw [thetaCuspFirstAtomMorseShiftDerivative_eq_polynomialAtom]

theorem integrableOn_thetaCuspFirstRadialQuadraticMorseFieldDerivative_mul_shiftDensity :
    IntegrableOn (fun x : ℝ =>
      thetaCuspFirstRadialQuadraticMorseFieldDerivative x *
        thetaCuspFirstAtomMorseShiftDensity x) (Ioi 0) := by
  have h :=
    integrableOn_thetaCuspFirstRadialQuadraticMorseFieldDerivative_mul_polynomialAtom
      thetaCuspFirstAtomMorseShiftPolynomial (by norm_num : 0 < (1 : ℕ))
  apply h.congr
  filter_upwards [] with x
  rw [thetaCuspFirstAtomMorseShiftDensity_eq_polynomialAtom]

theorem integrableOn_thetaCuspFirstRadialQuadraticMorseField_mul_shiftDensity :
    IntegrableOn (fun x : ℝ =>
      thetaCuspFirstRadialQuadraticMorseField x *
        thetaCuspFirstAtomMorseShiftDensity x) (Ioi 0) := by
  have h := integrableOn_thetaCuspFirstRadialQuadraticMorseField_mul_polynomialAtom
    thetaCuspFirstAtomMorseShiftPolynomial (by norm_num : 0 < (1 : ℕ))
  apply h.congr
  filter_upwards [] with x
  rw [thetaCuspFirstAtomMorseShiftDensity_eq_polynomialAtom]

theorem thetaCuspFirstRadialQuadraticMorseField_mul_shiftDensity_tendsto_zero :
    Tendsto (fun x : ℝ =>
      thetaCuspFirstRadialQuadraticMorseField x *
        thetaCuspFirstAtomMorseShiftDensity x) (𝓝[>] 0) (𝓝 0) := by
  have h4 := pow_mul_thetaCuspPolynomialAtom_tendsto_zero_of_pos
    (k := 4) (by norm_num) thetaCuspFirstAtomMorseShiftPolynomial 1
  have h5 := pow_mul_thetaCuspPolynomialAtom_tendsto_zero_of_pos
    (k := 5) (by norm_num) thetaCuspFirstAtomMorseShiftPolynomial 1
  have h6 := pow_mul_thetaCuspPolynomialAtom_tendsto_zero_of_pos
    (k := 6) (by norm_num) thetaCuspFirstAtomMorseShiftPolynomial 1
  have h := (h4.sub h5).add (h6.const_mul (1 / 4 : ℝ))
  convert h using 1
  · funext x
    rw [thetaCuspFirstRadialQuadraticMorseField_eq,
      thetaCuspFirstAtomMorseShiftDensity_eq_polynomialAtom]
    ring
  · ring

theorem thetaCuspFirstRadialQuadraticMorseField_mul_shiftDensity_tendsto_atTop_zero :
    Tendsto (fun x : ℝ =>
      thetaCuspFirstRadialQuadraticMorseField x *
        thetaCuspFirstAtomMorseShiftDensity x) atTop (𝓝 0) := by
  have h4 := pow_mul_thetaCuspPolynomialAtom_tendsto_atTop_zero_of_pos
    4 thetaCuspFirstAtomMorseShiftPolynomial (by norm_num : 0 < (1 : ℕ))
  have h5 := pow_mul_thetaCuspPolynomialAtom_tendsto_atTop_zero_of_pos
    5 thetaCuspFirstAtomMorseShiftPolynomial (by norm_num : 0 < (1 : ℕ))
  have h6 := pow_mul_thetaCuspPolynomialAtom_tendsto_atTop_zero_of_pos
    6 thetaCuspFirstAtomMorseShiftPolynomial (by norm_num : 0 < (1 : ℕ))
  have h := (h4.sub h5).add (h6.const_mul (1 / 4 : ℝ))
  convert h using 1
  · funext x
    rw [thetaCuspFirstRadialQuadraticMorseField_eq,
      thetaCuspFirstAtomMorseShiftDensity_eq_polynomialAtom]
    ring
  · ring

/-- Hypervirial integration by parts for the shifted Morse density. -/
theorem integral_morseField_mul_shiftDerivative_eq_neg :
    (∫ x : ℝ in Ioi 0,
      thetaCuspFirstRadialQuadraticMorseField x *
        ((5 / 2 : ℝ) * (thetaCuspBornWittenWeight 1 x + 1) *
            thetaCuspLiouvilleGibbsAtom 1 x -
          2 * thetaCuspMorseScale 1 x * thetaCuspBornWittenWeight 1 x *
            thetaCuspLiouvilleGibbsAtom 1 x)) =
      -(∫ x : ℝ in Ioi 0,
        thetaCuspFirstRadialQuadraticMorseFieldDerivative x *
          thetaCuspFirstAtomMorseShiftDensity x) := by
  have hibp := integral_Ioi_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ)) (a' := (0 : ℝ)) (b' := (0 : ℝ))
    (u := thetaCuspFirstRadialQuadraticMorseField)
    (u' := thetaCuspFirstRadialQuadraticMorseFieldDerivative)
    (v := thetaCuspFirstAtomMorseShiftDensity)
    (v' := fun x : ℝ =>
      (5 / 2 : ℝ) * (thetaCuspBornWittenWeight 1 x + 1) *
          thetaCuspLiouvilleGibbsAtom 1 x -
        2 * thetaCuspMorseScale 1 x * thetaCuspBornWittenWeight 1 x *
          thetaCuspLiouvilleGibbsAtom 1 x)
    (fun x _ => hasDerivAt_thetaCuspFirstRadialQuadraticMorseField x)
    (fun x _ => hasDerivAt_thetaCuspFirstAtomMorseShiftDensity x)
    integrableOn_thetaCuspFirstRadialQuadraticMorseField_mul_shiftDerivative
    integrableOn_thetaCuspFirstRadialQuadraticMorseFieldDerivative_mul_shiftDensity
    thetaCuspFirstRadialQuadraticMorseField_mul_shiftDensity_tendsto_zero
    thetaCuspFirstRadialQuadraticMorseField_mul_shiftDensity_tendsto_atTop_zero
  simpa only [Pi.mul_apply, zero_sub, sub_eq_add_neg, neg_zero, zero_add,
    neg_mul] using hibp

/-- The Morse scale insertion is exactly replaced by ordinary source and Gibbs moments. -/
theorem integral_four_morseScale_weight_eq_hypervirial :
    (∫ x : ℝ in Ioi 0,
      4 * thetaCuspFirstRadialQuadraticMorseField x *
        thetaCuspMorseScale 1 x * thetaCuspBornWittenWeight 1 x *
          thetaCuspLiouvilleGibbsAtom 1 x) =
      ∫ x : ℝ in Ioi 0,
        thetaCuspFirstRadialQuadraticMorseGibbsField x *
          thetaCuspFirstAtomMorseShiftDensity x := by
  let d : ℝ → ℝ := fun x =>
    (5 / 2 : ℝ) * (thetaCuspBornWittenWeight 1 x + 1) *
        thetaCuspLiouvilleGibbsAtom 1 x -
      2 * thetaCuspMorseScale 1 x * thetaCuspBornWittenWeight 1 x *
        thetaCuspLiouvilleGibbsAtom 1 x
  have hd := integrableOn_thetaCuspFirstRadialQuadraticMorseField_mul_shiftDerivative
  have hF := integrableOn_thetaCuspFirstRadialQuadraticMorseField_mul_shiftDensity
  have hF' :=
    integrableOn_thetaCuspFirstRadialQuadraticMorseFieldDerivative_mul_shiftDensity
  have hibp := integral_morseField_mul_shiftDerivative_eq_neg
  have hibp' :
      (∫ x : ℝ in Ioi 0,
        thetaCuspFirstRadialQuadraticMorseField x * d x) =
        -(∫ x : ℝ in Ioi 0,
          thetaCuspFirstRadialQuadraticMorseFieldDerivative x *
            thetaCuspFirstAtomMorseShiftDensity x) := hibp
  change (∫ x : ℝ in Ioi 0,
      4 * thetaCuspFirstRadialQuadraticMorseField x *
        thetaCuspMorseScale 1 x * thetaCuspBornWittenWeight 1 x *
          thetaCuspLiouvilleGibbsAtom 1 x) = _
  calc
    _ = ∫ x : ℝ in Ioi 0,
        (5 * (thetaCuspFirstRadialQuadraticMorseField x *
              thetaCuspFirstAtomMorseShiftDensity x) -
          2 * (thetaCuspFirstRadialQuadraticMorseField x * d x)) := by
            apply integral_congr_ae
            filter_upwards [] with x
            dsimp [d, thetaCuspFirstAtomMorseShiftDensity]
            ring
    _ = 5 * (∫ x : ℝ in Ioi 0,
          thetaCuspFirstRadialQuadraticMorseField x *
            thetaCuspFirstAtomMorseShiftDensity x) -
        2 * (∫ x : ℝ in Ioi 0,
          thetaCuspFirstRadialQuadraticMorseField x * d x) := by
            rw [integral_sub (hF.const_mul 5) (hd.const_mul 2),
              integral_const_mul, integral_const_mul]
    _ = 5 * (∫ x : ℝ in Ioi 0,
          thetaCuspFirstRadialQuadraticMorseField x *
            thetaCuspFirstAtomMorseShiftDensity x) +
        2 * (∫ x : ℝ in Ioi 0,
          thetaCuspFirstRadialQuadraticMorseFieldDerivative x *
            thetaCuspFirstAtomMorseShiftDensity x) := by
            rw [hibp']
            ring
    _ = ∫ x : ℝ in Ioi 0,
        thetaCuspFirstRadialQuadraticMorseGibbsField x *
          thetaCuspFirstAtomMorseShiftDensity x := by
            rw [← integral_const_mul, ← integral_const_mul,
              ← integral_add (hF.const_mul 5) (hF'.const_mul 2)]
            apply integral_congr_ae
            filter_upwards [] with x
            simp only [thetaCuspFirstRadialQuadraticMorseGibbsField]
            ring

/-- The remaining positive term is the Fisher correction of the square-root observable
reweighting. -/
def thetaCuspFirstRadialQuadraticMorseFisherResidual : ℝ :=
  ∫ x : ℝ in Ioi 0,
    thetaCuspFirstRadialQuadraticMorseField x *
      (thetaCuspMorseScale 1 x / thetaCuspBornWittenWeight 1 x) *
        thetaCuspLiouvilleGibbsAtom 1 x

/-- Exact Morse-reweighted value of the quadratic virial energy. -/
def thetaCuspFirstRadialQuadraticMorseReducedEnergy : ℝ :=
  (∫ x : ℝ in Ioi 0,
      thetaCuspFirstRadialQuadraticMorseSourceField x *
        thetaCuspBornWittenWeight 1 x * thetaCuspLiouvilleGibbsAtom 1 x) +
    (∫ x : ℝ in Ioi 0,
      thetaCuspFirstRadialQuadraticMorseGibbsField x *
        thetaCuspLiouvilleGibbsAtom 1 x) +
    6 * thetaCuspFirstRadialQuadraticMorseFisherResidual

theorem integrableOn_thetaCuspFirstRadialQuadraticMorseGibbsField_mul_gibbs :
    IntegrableOn (fun x : ℝ =>
      thetaCuspFirstRadialQuadraticMorseGibbsField x *
        thetaCuspLiouvilleGibbsAtom 1 x) (Ioi 0) := by
  have h3 := integrableOn_pow_mul_thetaCuspPolynomialAtom_Ioi_of_pos
    3 (X ^ 2) (by norm_num : 0 < (1 : ℕ))
  have h4 := integrableOn_pow_mul_thetaCuspPolynomialAtom_Ioi_of_pos
    4 (X ^ 2) (by norm_num : 0 < (1 : ℕ))
  have h5 := integrableOn_pow_mul_thetaCuspPolynomialAtom_Ioi_of_pos
    5 (X ^ 2) (by norm_num : 0 < (1 : ℕ))
  have h6 := integrableOn_pow_mul_thetaCuspPolynomialAtom_Ioi_of_pos
    6 (X ^ 2) (by norm_num : 0 < (1 : ℕ))
  have h := (((h3.const_mul 8).sub (h4.const_mul 5)).sub
    (h5.const_mul 2)).add (h6.const_mul (5 / 4 : ℝ))
  apply h.congr
  filter_upwards [] with x
  simp only [Pi.add_apply, Pi.sub_apply, thetaCuspLiouvilleGibbsAtom]
  rw [thetaCuspFirstRadialQuadraticMorseGibbsField_eq]
  ring

theorem integrableOn_thetaCuspFirstRadialQuadraticMorseRadialField_mul_weight_gibbs :
    IntegrableOn (fun x : ℝ =>
      thetaCuspFirstRadialQuadraticMorseRadialField x *
        thetaCuspBornWittenWeight 1 x * thetaCuspLiouvilleGibbsAtom 1 x)
      (Ioi 0) := by
  have h2 := integrableOn_pow_mul_thetaCuspBornWittenRadialAmplitude_sq
    2 0 (by norm_num : 0 < (1 : ℕ))
  have h3 := integrableOn_pow_mul_thetaCuspBornWittenRadialAmplitude_sq
    3 0 (by norm_num : 0 < (1 : ℕ))
  have h4 := integrableOn_pow_mul_thetaCuspBornWittenRadialAmplitude_sq
    4 0 (by norm_num : 0 < (1 : ℕ))
  have h := (((h2.const_mul 3).sub (h3.const_mul 4)).add
    (h4.const_mul (3 / 2 : ℝ))).const_mul (1 / 4 : ℝ)
  apply h.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  simp only [Pi.add_apply, Pi.sub_apply]
  rw [thetaCuspBornWittenRadialAmplitude_sq,
    thetaCuspBornWittenAmplitude_sq (n := 1) (by norm_num) hx.le,
    thetaCuspMorseGroundState_sq]
  simp only [thetaCuspFirstRadialQuadraticMorseRadialField,
    thetaCuspQuadraticSteinField, thetaCuspQuadraticSteinFieldDerivative,
    Nat.reduceMul, pow_zero, one_mul]
  ring

theorem integrableOn_thetaCuspFirstRadialQuadraticMorseSourceField_mul_weight_gibbs :
    IntegrableOn (fun x : ℝ =>
      thetaCuspFirstRadialQuadraticMorseSourceField x *
        thetaCuspBornWittenWeight 1 x * thetaCuspLiouvilleGibbsAtom 1 x)
      (Ioi 0) := by
  have h2 := integrableOn_pow_mul_thetaCuspBornWittenRadialAmplitude_sq
    2 0 (by norm_num : 0 < (1 : ℕ))
  have h3 := integrableOn_pow_mul_thetaCuspBornWittenRadialAmplitude_sq
    3 0 (by norm_num : 0 < (1 : ℕ))
  have h4 := integrableOn_pow_mul_thetaCuspBornWittenRadialAmplitude_sq
    4 0 (by norm_num : 0 < (1 : ℕ))
  have h5 := integrableOn_pow_mul_thetaCuspBornWittenRadialAmplitude_sq
    5 0 (by norm_num : 0 < (1 : ℕ))
  have h6 := integrableOn_pow_mul_thetaCuspBornWittenRadialAmplitude_sq
    6 0 (by norm_num : 0 < (1 : ℕ))
  have h := (((((h2.const_mul 3).add (h3.const_mul 4)).sub
    (h4.const_mul (7 / 2 : ℝ))).sub (h5.const_mul 2)).add
      (h6.const_mul (5 / 4 : ℝ))).const_mul (1 / 4 : ℝ)
  apply h.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  simp only [Pi.add_apply, Pi.sub_apply]
  rw [thetaCuspBornWittenRadialAmplitude_sq,
    thetaCuspBornWittenAmplitude_sq (n := 1) (by norm_num) hx.le,
    thetaCuspMorseGroundState_sq]
  simp only [thetaCuspFirstRadialQuadraticMorseSourceField_eq,
    Nat.reduceMul, pow_zero, one_mul]
  ring

theorem integrableOn_four_morseScale_weight :
    IntegrableOn (fun x : ℝ =>
      4 * thetaCuspFirstRadialQuadraticMorseField x *
        thetaCuspMorseScale 1 x * thetaCuspBornWittenWeight 1 x *
          thetaCuspLiouvilleGibbsAtom 1 x) (Ioi 0) := by
  have hF := integrableOn_thetaCuspFirstRadialQuadraticMorseField_mul_shiftDensity
  have hd := integrableOn_thetaCuspFirstRadialQuadraticMorseField_mul_shiftDerivative
  have h := (hF.const_mul 5).sub (hd.const_mul 2)
  apply h.congr
  filter_upwards [] with x
  simp only [Pi.sub_apply]
  dsimp [thetaCuspFirstAtomMorseShiftDensity]
  ring

theorem integrableOn_thetaCuspFirstRadialQuadraticMorseFisherResidual :
    IntegrableOn (fun x : ℝ =>
      thetaCuspFirstRadialQuadraticMorseField x *
        (thetaCuspMorseScale 1 x / thetaCuspBornWittenWeight 1 x) *
          thetaCuspLiouvilleGibbsAtom 1 x) (Ioi 0) := by
  let v : ℝ → ℝ := fun x =>
    ((1 / 2 : ℝ) * thetaCuspQuadraticSteinField x ^ 2 *
          thetaCuspBornWittenRadialCurvature 1 1 x +
        (1 / 4 : ℝ) * thetaCuspQuadraticSteinFieldDerivative x ^ 2) *
      thetaCuspBornWittenRadialAmplitude 1 1 x ^ 2
  let a : ℝ → ℝ := fun x =>
    4 * thetaCuspFirstRadialQuadraticMorseField x *
      thetaCuspMorseScale 1 x * thetaCuspBornWittenWeight 1 x *
        thetaCuspLiouvilleGibbsAtom 1 x
  let c : ℝ → ℝ := fun x =>
    thetaCuspFirstRadialQuadraticMorseRadialField x *
      thetaCuspBornWittenWeight 1 x * thetaCuspLiouvilleGibbsAtom 1 x
  have hv : IntegrableOn v (Ioi 0) :=
    integrableOn_thetaCuspFirstRadialQuadraticVirialEnergy
  have ha : IntegrableOn a (Ioi 0) := integrableOn_four_morseScale_weight
  have hc : IntegrableOn c (Ioi 0) :=
    integrableOn_thetaCuspFirstRadialQuadraticMorseRadialField_mul_weight_gibbs
  have hdiff := (hv.sub ha).sub hc
  have hscaled := hdiff.const_mul (1 / 6 : ℝ)
  apply hscaled.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hdecomp := thetaCuspFirstRadialQuadraticVirial_morseFisher_decomposition hx
  dsimp [v, a, c] at hdecomp ⊢
  rw [hdecomp]
  ring

/-- Integrated ground-state/hypervirial reweighting identity.  The rational curvature is isolated
in one positive Fisher residual; every other term is an ordinary source or Morse Gibbs moment. -/
theorem thetaCuspFirstRadialQuadraticVirialEnergy_eq_morseReducedEnergy :
    thetaCuspFirstRadialQuadraticVirialEnergy =
      thetaCuspFirstRadialQuadraticMorseReducedEnergy := by
  let a : ℝ → ℝ := fun x =>
    4 * thetaCuspFirstRadialQuadraticMorseField x *
      thetaCuspMorseScale 1 x * thetaCuspBornWittenWeight 1 x *
        thetaCuspLiouvilleGibbsAtom 1 x
  let b : ℝ → ℝ := fun x =>
    6 * thetaCuspFirstRadialQuadraticMorseField x *
      (thetaCuspMorseScale 1 x / thetaCuspBornWittenWeight 1 x) *
        thetaCuspLiouvilleGibbsAtom 1 x
  let c : ℝ → ℝ := fun x =>
    thetaCuspFirstRadialQuadraticMorseRadialField x *
      thetaCuspBornWittenWeight 1 x * thetaCuspLiouvilleGibbsAtom 1 x
  have ha : IntegrableOn a (Ioi 0) := integrableOn_four_morseScale_weight
  have hb : IntegrableOn b (Ioi 0) := by
    have h :=
      integrableOn_thetaCuspFirstRadialQuadraticMorseFisherResidual.const_mul 6
    apply h.congr
    filter_upwards [] with x
    dsimp [b]
    ring
  have hc : IntegrableOn c (Ioi 0) :=
    integrableOn_thetaCuspFirstRadialQuadraticMorseRadialField_mul_weight_gibbs
  have hK : IntegrableOn (fun x : ℝ =>
      thetaCuspFirstRadialQuadraticMorseGibbsField x *
        thetaCuspLiouvilleGibbsAtom 1 x) (Ioi 0) :=
    integrableOn_thetaCuspFirstRadialQuadraticMorseGibbsField_mul_gibbs
  have hH :=
    integrableOn_thetaCuspFirstRadialQuadraticMorseSourceField_mul_weight_gibbs
  have hKq : IntegrableOn (fun x : ℝ =>
      thetaCuspFirstRadialQuadraticMorseGibbsField x *
        thetaCuspBornWittenWeight 1 x * thetaCuspLiouvilleGibbsAtom 1 x)
      (Ioi 0) := by
    have h := hH.sub hc
    apply h.congr
    filter_upwards [] with x
    simp only [Pi.sub_apply]
    dsimp [c, thetaCuspFirstRadialQuadraticMorseSourceField,
      thetaCuspFirstRadialQuadraticMorseGibbsField]
    ring
  have hbValue :
      (∫ x : ℝ in Ioi 0, b x) =
        6 * thetaCuspFirstRadialQuadraticMorseFisherResidual := by
    rw [thetaCuspFirstRadialQuadraticMorseFisherResidual,
      ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with x
    dsimp [b]
    ring
  have hshiftValue :
      (∫ x : ℝ in Ioi 0,
        thetaCuspFirstRadialQuadraticMorseGibbsField x *
          thetaCuspFirstAtomMorseShiftDensity x) =
        (∫ x : ℝ in Ioi 0,
          thetaCuspFirstRadialQuadraticMorseGibbsField x *
            thetaCuspBornWittenWeight 1 x * thetaCuspLiouvilleGibbsAtom 1 x) +
        (∫ x : ℝ in Ioi 0,
          thetaCuspFirstRadialQuadraticMorseGibbsField x *
            thetaCuspLiouvilleGibbsAtom 1 x) := by
    rw [← integral_add hKq hK]
    apply integral_congr_ae
    filter_upwards [] with x
    dsimp [thetaCuspFirstAtomMorseShiftDensity]
    ring
  have hsourceValue :
      (∫ x : ℝ in Ioi 0,
          thetaCuspFirstRadialQuadraticMorseGibbsField x *
            thetaCuspBornWittenWeight 1 x * thetaCuspLiouvilleGibbsAtom 1 x) +
        (∫ x : ℝ in Ioi 0, c x) =
      ∫ x : ℝ in Ioi 0,
        thetaCuspFirstRadialQuadraticMorseSourceField x *
          thetaCuspBornWittenWeight 1 x * thetaCuspLiouvilleGibbsAtom 1 x := by
    rw [← integral_add hKq hc]
    apply integral_congr_ae
    filter_upwards [] with x
    dsimp [c, thetaCuspFirstRadialQuadraticMorseSourceField,
      thetaCuspFirstRadialQuadraticMorseGibbsField]
    ring
  have habValue :
      (∫ x : ℝ in Ioi 0, a x + b x) =
        (∫ x : ℝ in Ioi 0, a x) + (∫ x : ℝ in Ioi 0, b x) := by
    simpa only [Pi.add_apply] using integral_add ha hb
  have habcValue :
      (∫ x : ℝ in Ioi 0, (a x + b x) + c x) =
        (∫ x : ℝ in Ioi 0, a x + b x) + (∫ x : ℝ in Ioi 0, c x) := by
    simpa only [Pi.add_apply] using integral_add (ha.add hb) hc
  rw [thetaCuspFirstRadialQuadraticVirialEnergy,
    thetaCuspFirstRadialQuadraticMorseReducedEnergy]
  calc
    _ = ∫ x : ℝ in Ioi 0, (a x + b x + c x) := by
          apply integral_congr_ae
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
          have hdecomp :=
            thetaCuspFirstRadialQuadraticVirial_morseFisher_decomposition hx
          dsimp [a, b, c]
          rw [hdecomp]
          ring
    _ = (∫ x : ℝ in Ioi 0, a x) +
        (∫ x : ℝ in Ioi 0, b x) +
          (∫ x : ℝ in Ioi 0, c x) := by
          rw [habcValue, habValue]
    _ = (∫ x : ℝ in Ioi 0,
          thetaCuspFirstRadialQuadraticMorseGibbsField x *
            thetaCuspFirstAtomMorseShiftDensity x) +
        6 * thetaCuspFirstRadialQuadraticMorseFisherResidual +
          (∫ x : ℝ in Ioi 0, c x) := by
          rw [show (∫ x : ℝ in Ioi 0, a x) =
              ∫ x : ℝ in Ioi 0,
                thetaCuspFirstRadialQuadraticMorseGibbsField x *
                  thetaCuspFirstAtomMorseShiftDensity x by
                exact integral_four_morseScale_weight_eq_hypervirial,
            hbValue]
    _ = (∫ x : ℝ in Ioi 0,
          thetaCuspFirstRadialQuadraticMorseSourceField x *
            thetaCuspBornWittenWeight 1 x * thetaCuspLiouvilleGibbsAtom 1 x) +
        (∫ x : ℝ in Ioi 0,
          thetaCuspFirstRadialQuadraticMorseGibbsField x *
            thetaCuspLiouvilleGibbsAtom 1 x) +
          6 * thetaCuspFirstRadialQuadraticMorseFisherResidual := by
          rw [hshiftValue]
          linarith

/-- Sharp endpoint factor controlling the Fisher correction. -/
def thetaCuspFirstAtomMorseFisherEndpointFactor : ℝ :=
  Real.pi / (Real.pi - 3 / 2)

/-- A rational-curvature-free upper value built only from polynomial source and Morse Gibbs
moments. -/
def thetaCuspFirstRadialQuadraticMorseMomentUpperEnergy : ℝ :=
  (∫ x : ℝ in Ioi 0,
      thetaCuspFirstRadialQuadraticMorseSourceField x *
        thetaCuspBornWittenWeight 1 x * thetaCuspLiouvilleGibbsAtom 1 x) +
    ∫ x : ℝ in Ioi 0,
      (thetaCuspFirstRadialQuadraticMorseGibbsField x +
          6 * thetaCuspFirstAtomMorseFisherEndpointFactor *
            thetaCuspFirstRadialQuadraticMorseField x) *
        thetaCuspLiouvilleGibbsAtom 1 x

theorem thetaCuspFirstAtomMorseFisherEndpointFactor_pos :
    0 < thetaCuspFirstAtomMorseFisherEndpointFactor := by
  rw [thetaCuspFirstAtomMorseFisherEndpointFactor]
  exact div_pos Real.pi_pos (by nlinarith [Real.pi_gt_three])

theorem integrableOn_thetaCuspFirstRadialQuadraticMorseField_mul_gibbs :
    IntegrableOn (fun x : ℝ =>
      thetaCuspFirstRadialQuadraticMorseField x *
        thetaCuspLiouvilleGibbsAtom 1 x) (Ioi 0) := by
  have h := integrableOn_thetaCuspFirstRadialQuadraticMorseField_mul_polynomialAtom
    (X ^ 2) (by norm_num : 0 < (1 : ℕ))
  simpa only [thetaCuspLiouvilleGibbsAtom] using h

/-- The Fisher correction is positive. -/
theorem thetaCuspFirstRadialQuadraticMorseFisherResidual_nonneg :
    0 ≤ thetaCuspFirstRadialQuadraticMorseFisherResidual := by
  rw [thetaCuspFirstRadialQuadraticMorseFisherResidual]
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hq := thetaCuspBornWittenWeight_pos (n := 1) (by norm_num) hx.le
  have ht : 0 < thetaCuspMorseScale 1 x := by
    simp only [thetaCuspMorseScale]
    positivity
  have hb : 0 ≤ thetaCuspLiouvilleGibbsAtom 1 x := by
    rw [← thetaCuspMorseGroundState_sq]
    positivity
  have hF : 0 ≤ thetaCuspFirstRadialQuadraticMorseField x := by
    simp only [thetaCuspFirstRadialQuadraticMorseField]
    positivity
  positivity

/-- The endpoint value gives the sharp constant pointwise bound on the Fisher residual. -/
theorem thetaCuspFirstRadialQuadraticMorseFisherResidual_le_endpoint :
    thetaCuspFirstRadialQuadraticMorseFisherResidual ≤
      thetaCuspFirstAtomMorseFisherEndpointFactor *
        ∫ x : ℝ in Ioi 0,
          thetaCuspFirstRadialQuadraticMorseField x *
            thetaCuspLiouvilleGibbsAtom 1 x := by
  rw [thetaCuspFirstRadialQuadraticMorseFisherResidual]
  have hmajor :=
    integrableOn_thetaCuspFirstRadialQuadraticMorseField_mul_gibbs.const_mul
      thetaCuspFirstAtomMorseFisherEndpointFactor
  rw [← integral_const_mul]
  apply integral_mono_ae
    integrableOn_thetaCuspFirstRadialQuadraticMorseFisherResidual hmajor
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hratio := thetaCuspFirstAtom_morseScale_div_weight_le_pi hx.le
  have hb : 0 ≤ thetaCuspLiouvilleGibbsAtom 1 x := by
    rw [← thetaCuspMorseGroundState_sq]
    positivity
  have hF : 0 ≤ thetaCuspFirstRadialQuadraticMorseField x := by
    simp only [thetaCuspFirstRadialQuadraticMorseField]
    positivity
  rw [thetaCuspFirstAtomMorseFisherEndpointFactor]
  nlinarith [mul_nonneg hF hb]

theorem integrableOn_thetaCuspFirstRadialQuadraticMorseMomentUpperGibbs :
    IntegrableOn (fun x : ℝ =>
      (thetaCuspFirstRadialQuadraticMorseGibbsField x +
          6 * thetaCuspFirstAtomMorseFisherEndpointFactor *
            thetaCuspFirstRadialQuadraticMorseField x) *
        thetaCuspLiouvilleGibbsAtom 1 x) (Ioi 0) := by
  have hK :=
    integrableOn_thetaCuspFirstRadialQuadraticMorseGibbsField_mul_gibbs
  have hF :=
    integrableOn_thetaCuspFirstRadialQuadraticMorseField_mul_gibbs.const_mul
      (6 * thetaCuspFirstAtomMorseFisherEndpointFactor)
  apply (hK.add hF).congr
  filter_upwards [] with x
  simp only [Pi.add_apply]
  ring

/-- The exact virial energy is bounded above by a finite polynomial-moment value; no rational
superpotential or inverse observable remains in the new sufficient certificate. -/
theorem thetaCuspFirstRadialQuadraticVirialEnergy_le_morseMomentUpperEnergy :
    thetaCuspFirstRadialQuadraticVirialEnergy ≤
      thetaCuspFirstRadialQuadraticMorseMomentUpperEnergy := by
  rw [thetaCuspFirstRadialQuadraticVirialEnergy_eq_morseReducedEnergy,
    thetaCuspFirstRadialQuadraticMorseReducedEnergy,
    thetaCuspFirstRadialQuadraticMorseMomentUpperEnergy]
  have hres :=
    thetaCuspFirstRadialQuadraticMorseFisherResidual_le_endpoint
  have hres6 := mul_le_mul_of_nonneg_left hres (by norm_num : (0 : ℝ) ≤ 6)
  have hK :=
    integrableOn_thetaCuspFirstRadialQuadraticMorseGibbsField_mul_gibbs
  have hF :=
    integrableOn_thetaCuspFirstRadialQuadraticMorseField_mul_gibbs.const_mul
      (6 * thetaCuspFirstAtomMorseFisherEndpointFactor)
  have hsplit :
      (∫ x : ℝ in Ioi 0,
        (thetaCuspFirstRadialQuadraticMorseGibbsField x +
            6 * thetaCuspFirstAtomMorseFisherEndpointFactor *
              thetaCuspFirstRadialQuadraticMorseField x) *
          thetaCuspLiouvilleGibbsAtom 1 x) =
        (∫ x : ℝ in Ioi 0,
          thetaCuspFirstRadialQuadraticMorseGibbsField x *
            thetaCuspLiouvilleGibbsAtom 1 x) +
        6 * thetaCuspFirstAtomMorseFisherEndpointFactor *
          ∫ x : ℝ in Ioi 0,
            thetaCuspFirstRadialQuadraticMorseField x *
              thetaCuspLiouvilleGibbsAtom 1 x := by
    calc
      _ = (∫ x : ℝ in Ioi 0,
            thetaCuspFirstRadialQuadraticMorseGibbsField x *
              thetaCuspLiouvilleGibbsAtom 1 x) +
          (∫ x : ℝ in Ioi 0,
            (6 * thetaCuspFirstAtomMorseFisherEndpointFactor) *
              (thetaCuspFirstRadialQuadraticMorseField x *
                thetaCuspLiouvilleGibbsAtom 1 x)) := by
            rw [← integral_add hK hF]
            apply integral_congr_ae
            filter_upwards [] with x
            ring
      _ = _ := by rw [integral_const_mul]
  rw [hsplit]
  linarith

/-- Literal finite-moment form of the rational-curvature-free upper value. -/
def thetaCuspFirstRadialQuadraticMorseFiniteMomentUpperValue : ℝ :=
  (3 / 4 : ℝ) * thetaCuspBornWittenRadialPowerMoment 0 1 1 +
    thetaCuspBornWittenRadialPowerMoment 1 1 1 -
    (7 / 8 : ℝ) * thetaCuspBornWittenRadialPowerMoment 2 1 1 -
    (1 / 2 : ℝ) * thetaCuspBornWittenRadialPowerMoment 3 1 1 +
    (5 / 16 : ℝ) * thetaCuspBornWittenRadialPowerMoment 4 1 1 +
    8 * thetaCuspLiouvilleGibbsMoment 3 1 +
    (6 * thetaCuspFirstAtomMorseFisherEndpointFactor - 5) *
      thetaCuspLiouvilleGibbsMoment 4 1 -
    (2 + 6 * thetaCuspFirstAtomMorseFisherEndpointFactor) *
      thetaCuspLiouvilleGibbsMoment 5 1 +
    ((5 / 4 : ℝ) +
      (3 / 2 : ℝ) * thetaCuspFirstAtomMorseFisherEndpointFactor) *
      thetaCuspLiouvilleGibbsMoment 6 1

theorem integral_morseSourceField_weight_gibbs_eq_radialPowerMoments :
    (∫ x : ℝ in Ioi 0,
      thetaCuspFirstRadialQuadraticMorseSourceField x *
        thetaCuspBornWittenWeight 1 x * thetaCuspLiouvilleGibbsAtom 1 x) =
      (3 / 4 : ℝ) * thetaCuspBornWittenRadialPowerMoment 0 1 1 +
        thetaCuspBornWittenRadialPowerMoment 1 1 1 -
        (7 / 8 : ℝ) * thetaCuspBornWittenRadialPowerMoment 2 1 1 -
        (1 / 2 : ℝ) * thetaCuspBornWittenRadialPowerMoment 3 1 1 +
        (5 / 16 : ℝ) * thetaCuspBornWittenRadialPowerMoment 4 1 1 := by
  let r : ℕ → ℝ → ℝ := fun m x =>
    x ^ m * thetaCuspBornWittenRadialAmplitude 1 1 x ^ 2
  let f0 : ℝ → ℝ := fun x => (3 / 4 : ℝ) * r 0 x
  let f1 : ℝ → ℝ := r 1
  let f2 : ℝ → ℝ := fun x => (-7 / 8 : ℝ) * r 2 x
  let f3 : ℝ → ℝ := fun x => (-1 / 2 : ℝ) * r 3 x
  let f4 : ℝ → ℝ := fun x => (5 / 16 : ℝ) * r 4 x
  have hr0 : IntegrableOn (r 0) (Ioi 0) :=
    integrableOn_pow_mul_thetaCuspBornWittenRadialAmplitude_sq
      0 1 (by norm_num)
  have hr1 : IntegrableOn (r 1) (Ioi 0) :=
    integrableOn_pow_mul_thetaCuspBornWittenRadialAmplitude_sq
      1 1 (by norm_num)
  have hr2 : IntegrableOn (r 2) (Ioi 0) :=
    integrableOn_pow_mul_thetaCuspBornWittenRadialAmplitude_sq
      2 1 (by norm_num)
  have hr3 : IntegrableOn (r 3) (Ioi 0) :=
    integrableOn_pow_mul_thetaCuspBornWittenRadialAmplitude_sq
      3 1 (by norm_num)
  have hr4 : IntegrableOn (r 4) (Ioi 0) :=
    integrableOn_pow_mul_thetaCuspBornWittenRadialAmplitude_sq
      4 1 (by norm_num)
  have hf0 : IntegrableOn f0 (Ioi 0) := hr0.const_mul (3 / 4 : ℝ)
  have hf1 : IntegrableOn f1 (Ioi 0) := hr1
  have hf2 : IntegrableOn f2 (Ioi 0) := hr2.const_mul (-7 / 8 : ℝ)
  have hf3 : IntegrableOn f3 (Ioi 0) := hr3.const_mul (-1 / 2 : ℝ)
  have hf4 : IntegrableOn f4 (Ioi 0) := hr4.const_mul (5 / 16 : ℝ)
  have hpoint : ∀ᵐ x ∂volume.restrict (Ioi 0),
      thetaCuspFirstRadialQuadraticMorseSourceField x *
          thetaCuspBornWittenWeight 1 x * thetaCuspLiouvilleGibbsAtom 1 x =
        (((f0 x + f1 x) + f2 x) + f3 x) + f4 x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [thetaCuspFirstRadialQuadraticMorseSourceField_eq]
    dsimp [r, f0, f1, f2, f3, f4]
    rw [thetaCuspBornWittenRadialAmplitude_sq,
      thetaCuspBornWittenAmplitude_sq (n := 1) (by norm_num) hx.le,
      thetaCuspMorseGroundState_sq]
    norm_num only [Nat.reduceMul]
    ring
  rw [integral_congr_ae hpoint]
  have h01 :
      (∫ x : ℝ in Ioi 0, f0 x + f1 x) =
        (∫ x : ℝ in Ioi 0, f0 x) + (∫ x : ℝ in Ioi 0, f1 x) := by
    simpa only [Pi.add_apply] using integral_add hf0 hf1
  have h012 :
      (∫ x : ℝ in Ioi 0, (f0 x + f1 x) + f2 x) =
        (∫ x : ℝ in Ioi 0, f0 x + f1 x) + (∫ x : ℝ in Ioi 0, f2 x) := by
    simpa only [Pi.add_apply] using integral_add (hf0.add hf1) hf2
  have h0123 :
      (∫ x : ℝ in Ioi 0, ((f0 x + f1 x) + f2 x) + f3 x) =
        (∫ x : ℝ in Ioi 0, (f0 x + f1 x) + f2 x) +
          (∫ x : ℝ in Ioi 0, f3 x) := by
    simpa only [Pi.add_apply] using integral_add ((hf0.add hf1).add hf2) hf3
  have h01234 :
      (∫ x : ℝ in Ioi 0, (((f0 x + f1 x) + f2 x) + f3 x) + f4 x) =
        (∫ x : ℝ in Ioi 0, ((f0 x + f1 x) + f2 x) + f3 x) +
          (∫ x : ℝ in Ioi 0, f4 x) := by
    simpa only [Pi.add_apply] using
      integral_add (((hf0.add hf1).add hf2).add hf3) hf4
  rw [h01234, h0123, h012, h01]
  dsimp [f0, f1, f2, f3, f4]
  rw [integral_const_mul, integral_const_mul, integral_const_mul,
    integral_const_mul]
  simp only [thetaCuspBornWittenRadialPowerMoment, r]
  ring

theorem integral_morseMomentUpperGibbs_eq_gibbsMoments :
    (∫ x : ℝ in Ioi 0,
      (thetaCuspFirstRadialQuadraticMorseGibbsField x +
          6 * thetaCuspFirstAtomMorseFisherEndpointFactor *
            thetaCuspFirstRadialQuadraticMorseField x) *
        thetaCuspLiouvilleGibbsAtom 1 x) =
      8 * thetaCuspLiouvilleGibbsMoment 3 1 +
        (6 * thetaCuspFirstAtomMorseFisherEndpointFactor - 5) *
          thetaCuspLiouvilleGibbsMoment 4 1 -
        (2 + 6 * thetaCuspFirstAtomMorseFisherEndpointFactor) *
          thetaCuspLiouvilleGibbsMoment 5 1 +
        ((5 / 4 : ℝ) +
          (3 / 2 : ℝ) * thetaCuspFirstAtomMorseFisherEndpointFactor) *
          thetaCuspLiouvilleGibbsMoment 6 1 := by
  let c := thetaCuspFirstAtomMorseFisherEndpointFactor
  let b : ℕ → ℝ → ℝ := fun m x => x ^ m * thetaCuspLiouvilleGibbsAtom 1 x
  let f3 : ℝ → ℝ := fun x => 8 * b 3 x
  let f4 : ℝ → ℝ := fun x => (6 * c - 5) * b 4 x
  let f5 : ℝ → ℝ := fun x => -(2 + 6 * c) * b 5 x
  let f6 : ℝ → ℝ := fun x => ((5 / 4 : ℝ) + (3 / 2 : ℝ) * c) * b 6 x
  have hb (m : ℕ) : IntegrableOn (b m) (Ioi 0) := by
    simpa only [b, thetaCuspLiouvilleGibbsAtom] using
      integrableOn_pow_mul_thetaCuspPolynomialAtom_Ioi_of_pos
        m (X ^ 2) (by norm_num : 0 < (1 : ℕ))
  have hf3 : IntegrableOn f3 (Ioi 0) := (hb 3).const_mul 8
  have hf4 : IntegrableOn f4 (Ioi 0) := (hb 4).const_mul (6 * c - 5)
  have hf5 : IntegrableOn f5 (Ioi 0) := (hb 5).const_mul (-(2 + 6 * c))
  have hf6 : IntegrableOn f6 (Ioi 0) :=
    (hb 6).const_mul ((5 / 4 : ℝ) + (3 / 2 : ℝ) * c)
  have hpoint : (fun x : ℝ =>
      (thetaCuspFirstRadialQuadraticMorseGibbsField x +
          6 * thetaCuspFirstAtomMorseFisherEndpointFactor *
            thetaCuspFirstRadialQuadraticMorseField x) *
        thetaCuspLiouvilleGibbsAtom 1 x) =
      fun x => ((f3 x + f4 x) + f5 x) + f6 x := by
    funext x
    rw [thetaCuspFirstRadialQuadraticMorseGibbsField_eq,
      thetaCuspFirstRadialQuadraticMorseField_eq]
    dsimp [c, b, f3, f4, f5, f6]
    ring
  rw [hpoint]
  have h34 :
      (∫ x : ℝ in Ioi 0, f3 x + f4 x) =
        (∫ x : ℝ in Ioi 0, f3 x) + (∫ x : ℝ in Ioi 0, f4 x) := by
    simpa only [Pi.add_apply] using integral_add hf3 hf4
  have h345 :
      (∫ x : ℝ in Ioi 0, (f3 x + f4 x) + f5 x) =
        (∫ x : ℝ in Ioi 0, f3 x + f4 x) + (∫ x : ℝ in Ioi 0, f5 x) := by
    simpa only [Pi.add_apply] using integral_add (hf3.add hf4) hf5
  have h3456 :
      (∫ x : ℝ in Ioi 0, ((f3 x + f4 x) + f5 x) + f6 x) =
        (∫ x : ℝ in Ioi 0, (f3 x + f4 x) + f5 x) +
          (∫ x : ℝ in Ioi 0, f6 x) := by
    simpa only [Pi.add_apply] using integral_add ((hf3.add hf4).add hf5) hf6
  rw [h3456, h345, h34]
  dsimp [f3, f4, f5, f6]
  rw [integral_const_mul, integral_const_mul, integral_const_mul,
    integral_const_mul]
  simp only [thetaCuspLiouvilleGibbsMoment, b]
  dsimp [c]
  ring

theorem thetaCuspFirstRadialQuadraticMorseMomentUpperEnergy_eq_finiteMoments :
    thetaCuspFirstRadialQuadraticMorseMomentUpperEnergy =
      thetaCuspFirstRadialQuadraticMorseFiniteMomentUpperValue := by
  rw [thetaCuspFirstRadialQuadraticMorseMomentUpperEnergy,
    thetaCuspFirstRadialQuadraticMorseFiniteMomentUpperValue,
    integral_morseSourceField_weight_gibbs_eq_radialPowerMoments,
    integral_morseMomentUpperGibbs_eq_gibbsMoments]
  ring

/-- Sufficient finite-moment replacement for the original virial-energy certificate. -/
def ThetaCuspFirstRadialQuadraticMorseMomentUpperCertificate : Prop :=
  (14 * (3005 / 2997 : ℝ) ^ 2 - 9) *
        thetaCuspBornWittenRadialPowerMoment 2 1 1 ^ 2 *
          thetaCuspFirstRadialQuadraticMorseFiniteMomentUpperValue ≤
    9 * thetaCuspBornWittenRadialPowerMoment 0 1 1 *
      thetaCuspFirstRadialQuadraticSteinCoupling ^ 2

theorem thetaCusp_quadraticVirialEnergyCertificate_of_morseMomentUpper
    (hcert : ThetaCuspFirstRadialQuadraticMorseMomentUpperCertificate) :
    ThetaCuspFirstRadialQuadraticVirialEnergyCertificate := by
  rw [ThetaCuspFirstRadialQuadraticMorseMomentUpperCertificate] at hcert
  rw [← thetaCuspFirstRadialQuadraticMorseMomentUpperEnergy_eq_finiteMoments] at hcert
  rw [ThetaCuspFirstRadialQuadraticVirialEnergyCertificate]
  have hcoeff : 0 ≤ 14 * (3005 / 2997 : ℝ) ^ 2 - 9 := by norm_num
  have hfactor : 0 ≤
      (14 * (3005 / 2997 : ℝ) ^ 2 - 9) *
        thetaCuspBornWittenRadialPowerMoment 2 1 1 ^ 2 := by positivity
  calc
    (14 * (3005 / 2997 : ℝ) ^ 2 - 9) *
          thetaCuspBornWittenRadialPowerMoment 2 1 1 ^ 2 *
            thetaCuspFirstRadialQuadraticVirialEnergy ≤
        (14 * (3005 / 2997 : ℝ) ^ 2 - 9) *
          thetaCuspBornWittenRadialPowerMoment 2 1 1 ^ 2 *
            thetaCuspFirstRadialQuadraticMorseMomentUpperEnergy :=
      mul_le_mul_of_nonneg_left
        thetaCuspFirstRadialQuadraticVirialEnergy_le_morseMomentUpperEnergy hfactor
    _ ≤ 9 * thetaCuspBornWittenRadialPowerMoment 0 1 1 *
        thetaCuspFirstRadialQuadraticSteinCoupling ^ 2 := hcert

/-- The Morse finite-moment certificate directly discharges the existing upper first-atom ratio. -/
theorem thetaCusp_firstRadial_upper_of_morseMomentUpper
    (hcert : ThetaCuspFirstRadialQuadraticMorseMomentUpperCertificate) :
    14 * ((3005 / 2997 : ℝ) *
        thetaCuspBornWittenRadialRawMoment 1 1 1) ^ 2 ≤
      9 * thetaCuspBornWittenRadialRawMoment 0 1 1 *
        thetaCuspBornWittenRadialRawMoment 2 1 1 :=
  thetaCusp_firstRadial_upper_of_quadraticVirialEnergyCertificate
    (thetaCusp_quadraticVirialEnergyCertificate_of_morseMomentUpper hcert)

/-- Direct finite-moment physics certificate for the existing linear prime--archimedean Hankel
consumer. -/
theorem forall_primeArchSourceTraceHankel_linear_nonneg_of_morseMomentUpper
    (hcert : ThetaCuspFirstRadialQuadraticMorseMomentUpperCertificate)
    (hrelaxed :
      16 * ((3005 / 2997 : ℝ) *
          thetaCuspBornWittenRadialRawMoment 0 0 1) *
          ((3005 / 2997 : ℝ) *
            thetaCuspBornWittenRadialRawMoment 2 0 1) ≤
        45 * thetaCuspBornWittenRadialRawMoment 1 0 1 ^ 2) :
    ∀ a b : ℝ, 0 ≤ (primeArchSourceTraceHankel (C a + C b * X)).re := by
  exact forall_primeArchSourceTraceHankel_linear_nonneg_of_radialBornWittenAmplitude
    (thetaCusp_firstRadial_upper_of_morseMomentUpper hcert) hrelaxed

end

end RHTower
