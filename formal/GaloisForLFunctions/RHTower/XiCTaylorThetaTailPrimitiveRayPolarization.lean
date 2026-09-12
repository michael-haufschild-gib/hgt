import GaloisForLFunctions.RHTower.XiCTaylorThetaTailConvexCore
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailDensityAtoms
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailSurvivalMixedCurrent

/-!
# Primitive-ray radial normal form for pairs of theta-density atoms

Ordered positive square indices have the unique arithmetic coordinates

`(m,n) = (a*g,b*g)`, with `g = gcd(m,n)` and `a,b` coprime.

This file records the local analytic identity behind that regrouping.  For fixed `a,b,x,y`, put

`A = a exp(x)`, `B = b exp(y)`, `exp(2r) = A^2+B^2`, and
`u = A^2/(A^2+B^2)`.

Then the product of the two exact density atoms with common scale `g` is one radial Gaussian atom
at `r`.  All dependence on the primitive direction is carried by one degree-eight polynomial
which is invariant under `u -> 1-u`.  Thus the full common-`g` ray can be summed before any
orientation estimate, while exchanging the two primitive indices is an exact angular reflection.

No sign, convergence, gcd partition, or limiting statement is asserted here.
-/

open Complex Real Polynomial

namespace RHTower

noncomputable section

/-- The second-density polynomial after the squared radial variable has been split with weight
`u`.  Evaluation at `X = gR` agrees with the canonical second-density polynomial at `gA` whenever
`u R^2 = A^2`. -/
def thetaCuspDensityRadialScaledPolynomial (u : ℝ) : ℝ[X] :=
  C (1 / 4) - C (6 * Real.pi * u) * X ^ 2 +
    C (4 * Real.pi ^ 2 * u ^ 2) * X ^ 4

/-- Angular polynomial carried by one primitive square-index direction. -/
def thetaCuspDensityPrimitiveRayPolynomial (u : ℝ) : ℝ[X] :=
  thetaCuspDensityRadialScaledPolynomial u *
    thetaCuspDensityRadialScaledPolynomial (1 - u)

/-- Exchanging the two primitive indices is exactly the angular reflection `u -> 1-u`. -/
theorem thetaCuspDensityPrimitiveRayPolynomial_one_sub (u : ℝ) :
    thetaCuspDensityPrimitiveRayPolynomial (1 - u) =
      thetaCuspDensityPrimitiveRayPolynomial u := by
  unfold thetaCuspDensityPrimitiveRayPolynomial
  ring_nf

/-- The single symmetric angular coordinate carried by a primitive ray. -/
def thetaCuspPrimitiveRayMoment (u : ℝ) : ℝ :=
  u * (1 - u)

/-- Zeroth radial derivative coefficient of the primitive-ray density packet. -/
def thetaCuspPrimitiveRayCoefficientZero (u : ℝ) : ℝ :=
  -(25 / 4 : ℝ) * thetaCuspPrimitiveRayMoment u +
    (585 / 16 : ℝ) * thetaCuspPrimitiveRayMoment u ^ 2

/-- First radial derivative coefficient of the primitive-ray density packet. -/
def thetaCuspPrimitiveRayCoefficientOne (u : ℝ) : ℝ :=
  (75 / 4 : ℝ) * thetaCuspPrimitiveRayMoment u -
    (203 / 2 : ℝ) * thetaCuspPrimitiveRayMoment u ^ 2

/-- Second radial derivative coefficient of the primitive-ray density packet. -/
def thetaCuspPrimitiveRayCoefficientTwo (u : ℝ) : ℝ :=
  (1 / 4 : ℝ) - 14 * thetaCuspPrimitiveRayMoment u +
    (127 / 2 : ℝ) * thetaCuspPrimitiveRayMoment u ^ 2

/-- Third radial derivative coefficient of the primitive-ray density packet. -/
def thetaCuspPrimitiveRayCoefficientThree (u : ℝ) : ℝ :=
  3 * thetaCuspPrimitiveRayMoment u -
    14 * thetaCuspPrimitiveRayMoment u ^ 2

/-- Fourth radial derivative coefficient of the primitive-ray density packet. -/
def thetaCuspPrimitiveRayCoefficientFour (u : ℝ) : ℝ :=
  thetaCuspPrimitiveRayMoment u ^ 2

/-- **Exact five-mode radial decomposition.**  The complete product polynomial is a linear
combination of the first five logarithmic derivatives of the one-dimensional theta tail.  The
coefficients retain the angular variable jointly through `u(1-u)`; no density factor has been
estimated separately. -/
theorem thetaCuspDensityPrimitiveRayPolynomial_eq_derivative_packet (u : ℝ) :
    thetaCuspDensityPrimitiveRayPolynomial u =
      C (thetaCuspPrimitiveRayCoefficientZero u) *
          thetaCuspTailDerivativePolynomial 0 +
        C (thetaCuspPrimitiveRayCoefficientOne u) *
          thetaCuspTailDerivativePolynomial 1 +
        C (thetaCuspPrimitiveRayCoefficientTwo u) *
          thetaCuspTailDerivativePolynomial 2 +
        C (thetaCuspPrimitiveRayCoefficientThree u) *
          thetaCuspTailDerivativePolynomial 3 +
        C (thetaCuspPrimitiveRayCoefficientFour u) *
          thetaCuspTailDerivativePolynomial 4 := by
  apply Polynomial.funext
  intro X
  simp [thetaCuspDensityPrimitiveRayPolynomial,
    thetaCuspDensityRadialScaledPolynomial,
    thetaCuspPrimitiveRayCoefficientZero,
    thetaCuspPrimitiveRayCoefficientOne,
    thetaCuspPrimitiveRayCoefficientTwo,
    thetaCuspPrimitiveRayCoefficientThree,
    thetaCuspPrimitiveRayCoefficientFour,
    thetaCuspPrimitiveRayMoment,
    thetaCuspTailDerivativePolynomial, thetaCuspLogDerivativeStep]
  ring

/-- Coefficient of the growing half-exponential after radial theta reflection. -/
def thetaCuspPrimitiveRayGrowingCoefficient (u : ℝ) : ℝ :=
  (1 / 32 : ℝ) - (39 / 4 : ℝ) * thetaCuspPrimitiveRayMoment u +
    (105 / 2 : ℝ) * thetaCuspPrimitiveRayMoment u ^ 2

/-- Degree-two symmetric Jacobi mode for the primitive angular beta weight. -/
def thetaCuspPrimitiveRayJacobiModeTwo (u : ℝ) : ℝ :=
  (1 / 4 : ℝ) - (3 / 8 : ℝ) * (2 * u - 1) ^ 2

/-- Degree-four symmetric Jacobi mode for the same angular beta weight. -/
def thetaCuspPrimitiveRayJacobiModeFour (u : ℝ) : ℝ :=
  -(3 / 32 : ℝ) + (21 / 32 : ℝ) * (2 * u - 1) ^ 2 -
    (77 / 128 : ℝ) * (2 * u - 1) ^ 4

/-- The full growing completion coefficient has exactly two nonconstant Jacobi channels. -/
theorem thetaCuspPrimitiveRayGrowingCoefficient_eq_jacobi_two_four (u : ℝ) :
    thetaCuspPrimitiveRayGrowingCoefficient u =
      (16 / 11 : ℝ) * thetaCuspPrimitiveRayJacobiModeTwo u -
        (60 / 11 : ℝ) * thetaCuspPrimitiveRayJacobiModeFour u := by
  unfold thetaCuspPrimitiveRayGrowingCoefficient thetaCuspPrimitiveRayMoment
    thetaCuspPrimitiveRayJacobiModeTwo thetaCuspPrimitiveRayJacobiModeFour
  ring

/-- Polynomial potential whose beta-weighted Jacobi divergence is the growing coefficient. -/
def thetaCuspPrimitiveRayJacobiPotential (u : ℝ) : ℝ :=
  (7 / 16 : ℝ) * (2 * u - 1) ^ 2 -
    (15 / 64 : ℝ) * (2 * u - 1) ^ 4

theorem hasDerivAt_thetaCuspPrimitiveRayJacobiPotential (u : ℝ) :
    HasDerivAt thetaCuspPrimitiveRayJacobiPotential
      ((2 * u - 1) *
        (-(1 / 8 : ℝ) + (15 / 2 : ℝ) * thetaCuspPrimitiveRayMoment u)) u := by
  unfold thetaCuspPrimitiveRayJacobiPotential thetaCuspPrimitiveRayMoment
  have hlin : HasDerivAt (fun t : ℝ => 2 * t - 1) 2 u := by
    simpa using ((hasDerivAt_id u).const_mul 2).sub_const 1
  have hsq := (hlin.pow 2).const_mul (7 / 16 : ℝ)
  have hfour := (hlin.pow 4).const_mul (15 / 64 : ℝ)
  have hfull := hsq.sub hfour
  have hfull' := hfull.congr_deriv
    (g' := (2 * u - 1) *
      (-(1 / 8 : ℝ) + (15 / 2 : ℝ) * (u * (1 - u)))) (by ring)
  simpa only [Pi.sub_apply, Pi.pow_apply] using! hfull'

/-- **Primitive-ray completion-character collapse.**  Reflection of the five radial derivative
modes produces two elementary characters.  Their complete joint coefficient simplifies so that
the decaying character has the universal coefficient `-1/32`, independent of the primitive
direction.  All angular dependence is confined to the growing character. -/
theorem thetaCuspPrimitiveRayCompletionCharacter_eq (u x : ℝ) :
    (thetaCuspPrimitiveRayCoefficientZero u +
          (1 / 4 : ℝ) * thetaCuspPrimitiveRayCoefficientTwo u +
          (1 / 16 : ℝ) * thetaCuspPrimitiveRayCoefficientFour u) *
        thetaCuspReflectionMode x -
      (thetaCuspPrimitiveRayCoefficientOne u +
          (1 / 4 : ℝ) * thetaCuspPrimitiveRayCoefficientThree u) *
        thetaCuspReflectionModeDeriv x =
      thetaCuspPrimitiveRayGrowingCoefficient u * Real.exp (x / 2) -
        (1 / 32 : ℝ) * Real.exp (-x / 2) := by
  simp [thetaCuspPrimitiveRayCoefficientZero,
    thetaCuspPrimitiveRayCoefficientOne,
    thetaCuspPrimitiveRayCoefficientTwo,
    thetaCuspPrimitiveRayCoefficientThree,
    thetaCuspPrimitiveRayCoefficientFour,
    thetaCuspPrimitiveRayGrowingCoefficient,
    thetaCuspPrimitiveRayMoment,
    thetaCuspReflectionMode, thetaCuspReflectionModeDeriv]
  ring

/-- Angular flux whose divergence is the growing primitive-ray completion character. -/
def thetaCuspPrimitiveRayAngularFlux (u : ℝ) : ℝ :=
  (2 * u - 1) * (thetaCuspPrimitiveRayMoment u) ^ (1 / 4 : ℝ) *
    (-(1 / 8 : ℝ) + (15 / 2 : ℝ) * thetaCuspPrimitiveRayMoment u)

/-- **Exact angular conservation law.**  After the primitive polar Jacobian is included, the
angle-dependent growing completion character is a pure angular derivative.  This identity is
the cancellation-compatible form: integrating it by parts keeps the swept endpoint windows and
the translated finite-core derivative together. -/
theorem hasDerivAt_thetaCuspPrimitiveRayAngularFlux
    {u : ℝ} (hu : u ∈ Set.Ioo 0 1) :
    HasDerivAt thetaCuspPrimitiveRayAngularFlux
      (thetaCuspPrimitiveRayGrowingCoefficient u *
        (thetaCuspPrimitiveRayMoment u) ^ (-(3 / 4 : ℝ))) u := by
  have hw : 0 < thetaCuspPrimitiveRayMoment u :=
    mul_pos hu.1 (sub_pos.mpr hu.2)
  have hwd : HasDerivAt thetaCuspPrimitiveRayMoment (1 - 2 * u) u := by
    unfold thetaCuspPrimitiveRayMoment
    have hraw := (hasDerivAt_id u).mul
      ((hasDerivAt_const u 1).sub (hasDerivAt_id u))
    have hraw' := hraw.congr_deriv (g' := 1 - 2 * u) (by
      simp only [Pi.sub_apply, id_eq]
      ring)
    simpa only [Pi.mul_apply, Pi.sub_apply, id_eq] using! hraw'
  have ht : HasDerivAt (fun y : ℝ => 2 * y - 1) 2 u := by
    simpa using ((hasDerivAt_id u).const_mul 2).sub_const 1
  have hpow := hwd.rpow_const (p := (1 / 4 : ℝ)) (Or.inl hw.ne')
  have hpoly : HasDerivAt
      (fun y : ℝ => -(1 / 8 : ℝ) +
        (15 / 2 : ℝ) * thetaCuspPrimitiveRayMoment y)
      ((15 / 2 : ℝ) * (1 - 2 * u)) u := by
    simpa [add_comm] using
      (hwd.const_mul (15 / 2 : ℝ)).const_add (-(1 / 8 : ℝ))
  have hfull := (ht.mul hpow).mul hpoly
  have hexp : (1 / 4 : ℝ) - 1 = -(3 / 4 : ℝ) := by ring
  have hrpow : (thetaCuspPrimitiveRayMoment u) ^ (1 / 4 : ℝ) =
      thetaCuspPrimitiveRayMoment u *
        (thetaCuspPrimitiveRayMoment u) ^ (-(3 / 4 : ℝ)) := by
    calc
      (thetaCuspPrimitiveRayMoment u) ^ (1 / 4 : ℝ) =
          (thetaCuspPrimitiveRayMoment u) ^ (1 + (-(3 / 4 : ℝ))) := by
            congr 1
            ring
      _ = (thetaCuspPrimitiveRayMoment u) ^ (1 : ℝ) *
          (thetaCuspPrimitiveRayMoment u) ^ (-(3 / 4 : ℝ)) :=
        Real.rpow_add hw 1 (-(3 / 4 : ℝ))
      _ = thetaCuspPrimitiveRayMoment u *
          (thetaCuspPrimitiveRayMoment u) ^ (-(3 / 4 : ℝ)) := by
        rw [Real.rpow_one]
  have hfull' := hfull.congr_deriv
    (g' := thetaCuspPrimitiveRayGrowingCoefficient u *
      (thetaCuspPrimitiveRayMoment u) ^ (-(3 / 4 : ℝ))) (by
      simp only [Pi.mul_apply]
      rw [hexp, hrpow]
      unfold thetaCuspPrimitiveRayGrowingCoefficient thetaCuspPrimitiveRayMoment
      ring)
  simpa only [thetaCuspPrimitiveRayAngularFlux, Pi.mul_apply] using! hfull'

@[simp] theorem thetaCuspPrimitiveRayAngularFlux_zero :
    thetaCuspPrimitiveRayAngularFlux 0 = 0 := by
  norm_num [thetaCuspPrimitiveRayAngularFlux, thetaCuspPrimitiveRayMoment]

@[simp] theorem thetaCuspPrimitiveRayAngularFlux_one :
    thetaCuspPrimitiveRayAngularFlux 1 = 0 := by
  norm_num [thetaCuspPrimitiveRayAngularFlux, thetaCuspPrimitiveRayMoment]

/-- Finite-interval angular cancellation.  On every compact subinterval of `(0,1)`, the complete
growing character with its primitive polar weight integrates to the two endpoint fluxes. -/
theorem integral_thetaCuspPrimitiveRayGrowingCoefficient_mul_rpow
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) :
    (∫ u : ℝ in a..b,
      thetaCuspPrimitiveRayGrowingCoefficient u *
        (thetaCuspPrimitiveRayMoment u) ^ (-(3 / 4 : ℝ))) =
      thetaCuspPrimitiveRayAngularFlux b -
        thetaCuspPrimitiveRayAngularFlux a := by
  have hsub : Set.uIcc a b ⊆ Set.Ioo 0 1 := by
    rw [Set.uIcc_of_le hab]
    intro u hu
    exact ⟨lt_of_lt_of_le ha hu.1, lt_of_le_of_lt hu.2 hb⟩
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro u hu
    exact hasDerivAt_thetaCuspPrimitiveRayAngularFlux (hsub hu)
  · apply ContinuousOn.intervalIntegrable
    intro u hu
    have hui := hsub hu
    have hwu : thetaCuspPrimitiveRayMoment u ≠ 0 :=
      (mul_pos hui.1 (sub_pos.mpr hui.2)).ne'
    apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.mul
    · unfold thetaCuspPrimitiveRayGrowingCoefficient thetaCuspPrimitiveRayMoment
      fun_prop
    · exact (show ContinuousAt thetaCuspPrimitiveRayMoment u by
        unfold thetaCuspPrimitiveRayMoment
        fun_prop).rpow_const (Or.inl hwu)

/-- **Seam-preserving angular bridge.**  Against an arbitrary differentiable translated core
kernel, the growing primitive-ray completion character is exactly the difference of the two
swept endpoint fluxes and one unsplit angular-translation term.  The three terms are an identity;
none is assigned a sign or estimated separately. -/
theorem integral_thetaCuspPrimitiveRayGrowingCoefficient_mul_kernel
    {K K' : ℝ → ℝ} {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb : b < 1)
    (hK : ∀ u ∈ Set.uIcc a b, HasDerivAt K (K' u) u)
    (hKint : IntervalIntegrable K' MeasureTheory.volume a b) :
    (∫ u : ℝ in a..b,
      thetaCuspPrimitiveRayGrowingCoefficient u *
          (thetaCuspPrimitiveRayMoment u) ^ (-(3 / 4 : ℝ)) * K u) =
      thetaCuspPrimitiveRayAngularFlux b * K b -
        thetaCuspPrimitiveRayAngularFlux a * K a -
        ∫ u : ℝ in a..b, thetaCuspPrimitiveRayAngularFlux u * K' u := by
  have hsub : Set.uIcc a b ⊆ Set.Ioo 0 1 := by
    rw [Set.uIcc_of_le hab]
    intro u hu
    exact ⟨lt_of_lt_of_le ha hu.1, lt_of_le_of_lt hu.2 hb⟩
  have hflux : ∀ u ∈ Set.uIcc a b,
      HasDerivAt thetaCuspPrimitiveRayAngularFlux
        (thetaCuspPrimitiveRayGrowingCoefficient u *
          (thetaCuspPrimitiveRayMoment u) ^ (-(3 / 4 : ℝ))) u :=
    fun u hu => hasDerivAt_thetaCuspPrimitiveRayAngularFlux (hsub hu)
  have hgrowing : IntervalIntegrable
      (fun u : ℝ => thetaCuspPrimitiveRayGrowingCoefficient u *
        (thetaCuspPrimitiveRayMoment u) ^ (-(3 / 4 : ℝ)))
      MeasureTheory.volume a b := by
    apply ContinuousOn.intervalIntegrable
    intro u hu
    have hui := hsub hu
    have hwu : thetaCuspPrimitiveRayMoment u ≠ 0 :=
      (mul_pos hui.1 (sub_pos.mpr hui.2)).ne'
    apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.mul
    · unfold thetaCuspPrimitiveRayGrowingCoefficient thetaCuspPrimitiveRayMoment
      fun_prop
    · exact (show ContinuousAt thetaCuspPrimitiveRayMoment u by
        unfold thetaCuspPrimitiveRayMoment
        fun_prop).rpow_const (Or.inl hwu)
  simpa only [mul_comm] using
    (intervalIntegral.integral_mul_deriv_eq_deriv_mul
      hK hflux hKint hgrowing)

/-- The `m`-th derivative of the elementary theta-reflection defect. -/
def thetaCuspReflectionModeIterate (m : ℕ) (x : ℝ) : ℝ :=
  (((1 / 2 : ℝ) ^ m) * Real.exp (x / 2) -
      ((-1 / 2 : ℝ) ^ m) * Real.exp (-x / 2)) / 2

theorem hasDerivAt_thetaCuspReflectionModeIterate (m : ℕ) (x : ℝ) :
    HasDerivAt (thetaCuspReflectionModeIterate m)
      (thetaCuspReflectionModeIterate (m + 1) x) x := by
  unfold thetaCuspReflectionModeIterate
  have hpos := ((Real.hasDerivAt_exp (x / 2)).comp x
    ((hasDerivAt_id x).div_const 2)).const_mul ((1 / 2 : ℝ) ^ m)
  have hneg := ((Real.hasDerivAt_exp (-x / 2)).comp x
    (((hasDerivAt_id x).neg).div_const 2)).const_mul ((-1 / 2 : ℝ) ^ m)
  have hraw := (hpos.sub hneg).div_const 2
  have hraw' := hraw.congr_deriv
    (g' := thetaCuspReflectionModeIterate (m + 1) x) (by
      simp only [thetaCuspReflectionModeIterate]
      rw [pow_succ]
      ring)
  simpa only [thetaCuspReflectionModeIterate, Function.comp_apply,
    Pi.sub_apply, Pi.div_apply, id_eq] using! hraw'

/-- Reflection of every derivative of the positive theta tail.  The parity sign and the complete
elementary defect are kept in one formula, so higher radial packets can be reflected without
re-deriving separate completion terms. -/
theorem thetaCuspTailDerivative_neg_all (m : ℕ) (x : ℝ) :
    thetaCuspTailDerivative m (-x) =
      (-1 : ℝ) ^ m *
        (thetaCuspTailDerivative m x + thetaCuspReflectionModeIterate m x) := by
  induction m generalizing x with
  | zero =>
      simpa [thetaCuspReflectionModeIterate, thetaCuspReflectionMode] using
        thetaCuspTailDerivative_zero_neg x
  | succ m ih =>
      have hfun : (fun y : ℝ => thetaCuspTailDerivative m (-y)) =
          fun y => (-1 : ℝ) ^ m *
            (thetaCuspTailDerivative m y + thetaCuspReflectionModeIterate m y) := by
        funext y
        exact ih y
      have hl := (hasDerivAt_thetaCuspTailDerivative m (-x)).comp x
        (hasDerivAt_neg x)
      have hr := ((hasDerivAt_thetaCuspTailDerivative m x).add
        (hasDerivAt_thetaCuspReflectionModeIterate m x)).const_mul ((-1 : ℝ) ^ m)
      have hl' : HasDerivAt (fun y : ℝ => thetaCuspTailDerivative m (-y))
          (-thetaCuspTailDerivative (m + 1) (-x)) x := by
        simpa [Function.comp_def] using hl
      have hr' : HasDerivAt
          (fun y : ℝ => (-1 : ℝ) ^ m *
            (thetaCuspTailDerivative m y + thetaCuspReflectionModeIterate m y))
          ((-1 : ℝ) ^ m *
            (thetaCuspTailDerivative (m + 1) x +
              thetaCuspReflectionModeIterate (m + 1) x)) x := by
        simpa using hr
      rw [hfun] at hl'
      have hderiv := hl'.unique hr'
      have hsign : (-1 : ℝ) ^ (m + 1) = -((-1 : ℝ) ^ m) := by
        rw [pow_succ]
        ring
      rw [hsign]
      linarith

/-- Full common-scale theta packet carried by one primitive direction. -/
def thetaCuspPrimitiveRayRadialPacket (u x : ℝ) : ℝ :=
  thetaCuspPrimitiveRayCoefficientZero u * thetaCuspTailDerivative 0 x +
    thetaCuspPrimitiveRayCoefficientOne u * thetaCuspTailDerivative 1 x +
    thetaCuspPrimitiveRayCoefficientTwo u * thetaCuspTailDerivative 2 x +
    thetaCuspPrimitiveRayCoefficientThree u * thetaCuspTailDerivative 3 x +
    thetaCuspPrimitiveRayCoefficientFour u * thetaCuspTailDerivative 4 x

/-- Parity-twisted theta packet produced by radial reflection. -/
def thetaCuspPrimitiveRayParityPacket (u x : ℝ) : ℝ :=
  thetaCuspPrimitiveRayCoefficientZero u * thetaCuspTailDerivative 0 x -
    thetaCuspPrimitiveRayCoefficientOne u * thetaCuspTailDerivative 1 x +
    thetaCuspPrimitiveRayCoefficientTwo u * thetaCuspTailDerivative 2 x -
    thetaCuspPrimitiveRayCoefficientThree u * thetaCuspTailDerivative 3 x +
    thetaCuspPrimitiveRayCoefficientFour u * thetaCuspTailDerivative 4 x

/-- **Radial packet reflection.**  The complete common-scale packet reflects to its parity twist,
one angle-dependent growing character, and the universal decaying character `-exp(-x/2)/32`. -/
theorem thetaCuspPrimitiveRayRadialPacket_neg (u x : ℝ) :
    thetaCuspPrimitiveRayRadialPacket u (-x) =
      thetaCuspPrimitiveRayParityPacket u x +
        thetaCuspPrimitiveRayGrowingCoefficient u * Real.exp (x / 2) -
        (1 / 32 : ℝ) * Real.exp (-x / 2) := by
  rw [thetaCuspPrimitiveRayRadialPacket,
    thetaCuspTailDerivative_neg_all 0 x,
    thetaCuspTailDerivative_neg_all 1 x,
    thetaCuspTailDerivative_neg_all 2 x,
    thetaCuspTailDerivative_neg_all 3 x,
    thetaCuspTailDerivative_neg_all 4 x]
  simp [thetaCuspPrimitiveRayParityPacket,
    thetaCuspReflectionModeIterate,
    thetaCuspPrimitiveRayCoefficientZero,
    thetaCuspPrimitiveRayCoefficientOne,
    thetaCuspPrimitiveRayCoefficientTwo,
    thetaCuspPrimitiveRayCoefficientThree,
    thetaCuspPrimitiveRayCoefficientFour,
    thetaCuspPrimitiveRayGrowingCoefficient,
    thetaCuspPrimitiveRayMoment]
  ring

/-- **Reflected primitive-ray integrand.**  After the polar Jacobian has supplied the outer
`exp(r/2)` factor, radial reflection leaves the parity packet, the pure angular divergence, and
the universal favorable exponential term `-exp(r)/32`. -/
theorem exp_half_mul_thetaCuspPrimitiveRayRadialPacket_eq_reflected
    (u r : ℝ) :
    Real.exp (r / 2) * thetaCuspPrimitiveRayRadialPacket u r =
      Real.exp (r / 2) * thetaCuspPrimitiveRayParityPacket u (-r) +
        thetaCuspPrimitiveRayGrowingCoefficient u -
        (1 / 32 : ℝ) * Real.exp r := by
  have hreflect := thetaCuspPrimitiveRayRadialPacket_neg u (-r)
  simp only [neg_neg] at hreflect
  rw [hreflect]
  calc
    Real.exp (r / 2) *
        (thetaCuspPrimitiveRayParityPacket u (-r) +
          thetaCuspPrimitiveRayGrowingCoefficient u * Real.exp (-r / 2) -
          (1 / 32 : ℝ) * Real.exp (r / 2)) =
      Real.exp (r / 2) * thetaCuspPrimitiveRayParityPacket u (-r) +
        thetaCuspPrimitiveRayGrowingCoefficient u *
          (Real.exp (r / 2) * Real.exp (-r / 2)) -
        (1 / 32 : ℝ) *
          (Real.exp (r / 2) * Real.exp (r / 2)) := by ring_nf
    _ = _ := by
      rw [← Real.exp_add, ← Real.exp_add]
      rw [show r / 2 + -r / 2 = 0 by ring_nf, Real.exp_zero, mul_one]
      ring_nf

/-- Atomwise form of the five-mode decomposition. -/
theorem thetaCuspPrimitiveRayPolynomialAtom_eq_derivative_packet
    (u x : ℝ) (n : ℕ) :
    thetaCuspPolynomialAtom (thetaCuspDensityPrimitiveRayPolynomial u) n x =
      thetaCuspPrimitiveRayCoefficientZero u *
          thetaCuspPolynomialAtom (thetaCuspTailDerivativePolynomial 0) n x +
        thetaCuspPrimitiveRayCoefficientOne u *
          thetaCuspPolynomialAtom (thetaCuspTailDerivativePolynomial 1) n x +
        thetaCuspPrimitiveRayCoefficientTwo u *
          thetaCuspPolynomialAtom (thetaCuspTailDerivativePolynomial 2) n x +
        thetaCuspPrimitiveRayCoefficientThree u *
          thetaCuspPolynomialAtom (thetaCuspTailDerivativePolynomial 3) n x +
        thetaCuspPrimitiveRayCoefficientFour u *
          thetaCuspPolynomialAtom (thetaCuspTailDerivativePolynomial 4) n x := by
  unfold thetaCuspPolynomialAtom
  rw [thetaCuspDensityPrimitiveRayPolynomial_eq_derivative_packet]
  simp only [eval_add, eval_mul, eval_C]
  ring

/-- The common-scale primitive ray is summable before any orientation estimate. -/
theorem summable_thetaCuspPrimitiveRayPolynomialAtom (u x : ℝ) :
    Summable (fun n : ℕ =>
      thetaCuspPolynomialAtom (thetaCuspDensityPrimitiveRayPolynomial u) (n + 1) x) := by
  have h0 := (summable_thetaCuspTailDerivative 0 x).mul_left
    (thetaCuspPrimitiveRayCoefficientZero u)
  have h1 := (summable_thetaCuspTailDerivative 1 x).mul_left
    (thetaCuspPrimitiveRayCoefficientOne u)
  have h2 := (summable_thetaCuspTailDerivative 2 x).mul_left
    (thetaCuspPrimitiveRayCoefficientTwo u)
  have h3 := (summable_thetaCuspTailDerivative 3 x).mul_left
    (thetaCuspPrimitiveRayCoefficientThree u)
  have h4 := (summable_thetaCuspTailDerivative 4 x).mul_left
    (thetaCuspPrimitiveRayCoefficientFour u)
  exact ((((h0.add h1).add h2).add h3).add h4).congr
    (fun n => (thetaCuspPrimitiveRayPolynomialAtom_eq_derivative_packet
      u x (n + 1)).symm)

/-- **Complete primitive-ray summation identity.**  Summing the common arithmetic scale converts
the two-density radial polynomial exactly into the five-mode theta packet. -/
theorem tsum_thetaCuspPrimitiveRayPolynomialAtom_eq (u x : ℝ) :
    (∑' n : ℕ,
      thetaCuspPolynomialAtom (thetaCuspDensityPrimitiveRayPolynomial u) (n + 1) x) =
      thetaCuspPrimitiveRayRadialPacket u x := by
  have h0 := (summable_thetaCuspTailDerivative 0 x).hasSum.mul_left
    (thetaCuspPrimitiveRayCoefficientZero u)
  have h1 := (summable_thetaCuspTailDerivative 1 x).hasSum.mul_left
    (thetaCuspPrimitiveRayCoefficientOne u)
  have h2 := (summable_thetaCuspTailDerivative 2 x).hasSum.mul_left
    (thetaCuspPrimitiveRayCoefficientTwo u)
  have h3 := (summable_thetaCuspTailDerivative 3 x).hasSum.mul_left
    (thetaCuspPrimitiveRayCoefficientThree u)
  have h4 := (summable_thetaCuspTailDerivative 4 x).hasSum.mul_left
    (thetaCuspPrimitiveRayCoefficientFour u)
  have hsum : HasSum
      (fun n : ℕ =>
        thetaCuspPrimitiveRayCoefficientZero u *
            thetaCuspPolynomialAtom (thetaCuspTailDerivativePolynomial 0) (n + 1) x +
          thetaCuspPrimitiveRayCoefficientOne u *
            thetaCuspPolynomialAtom (thetaCuspTailDerivativePolynomial 1) (n + 1) x +
          thetaCuspPrimitiveRayCoefficientTwo u *
            thetaCuspPolynomialAtom (thetaCuspTailDerivativePolynomial 2) (n + 1) x +
          thetaCuspPrimitiveRayCoefficientThree u *
            thetaCuspPolynomialAtom (thetaCuspTailDerivativePolynomial 3) (n + 1) x +
          thetaCuspPrimitiveRayCoefficientFour u *
            thetaCuspPolynomialAtom (thetaCuspTailDerivativePolynomial 4) (n + 1) x)
      (thetaCuspPrimitiveRayRadialPacket u x) := by
    simpa [thetaCuspPrimitiveRayRadialPacket, thetaCuspTailDerivative] using
      ((((h0.add h1).add h2).add h3).add h4)
  have hsum' : HasSum
      (fun n : ℕ =>
        thetaCuspPolynomialAtom (thetaCuspDensityPrimitiveRayPolynomial u) (n + 1) x)
      (thetaCuspPrimitiveRayRadialPacket u x) := by
    apply HasSum.congr_fun hsum
    intro n
    exact thetaCuspPrimitiveRayPolynomialAtom_eq_derivative_packet
      u x (n + 1)
  exact hsum'.tsum_eq

/-- One angularly scaled radial polynomial evaluates to the original canonical density
polynomial. -/
theorem eval_thetaCuspDensityRadialScaledPolynomial
    (u R A : ℝ) (g : ℕ) (hscale : u * R ^ 2 = A ^ 2) :
    eval ((g : ℝ) * R) (thetaCuspDensityRadialScaledPolynomial u) =
      eval ((g : ℝ) * A) (thetaCuspTailDerivativePolynomial 2) := by
  have hscaleG : u * (((g : ℝ) * R) ^ 2) = ((g : ℝ) * A) ^ 2 := by
    calc
      u * (((g : ℝ) * R) ^ 2) = (g : ℝ) ^ 2 * (u * R ^ 2) := by ring
      _ = (g : ℝ) ^ 2 * A ^ 2 := by rw [hscale]
      _ = ((g : ℝ) * A) ^ 2 := by ring
  have hscaleG4 : u ^ 2 * (((g : ℝ) * R) ^ 4) =
      ((g : ℝ) * A) ^ 4 := by
    calc
      u ^ 2 * (((g : ℝ) * R) ^ 4) =
          (u * (((g : ℝ) * R) ^ 2)) ^ 2 := by ring
      _ = (((g : ℝ) * A) ^ 2) ^ 2 := by rw [hscaleG]
      _ = ((g : ℝ) * A) ^ 4 := by ring
  rw [thetaCuspTailDerivativePolynomial_two]
  simp only [thetaCuspDensityRadialScaledPolynomial, eval_add, eval_sub, eval_mul,
    eval_C, eval_pow, eval_X]
  rw [show 6 * Real.pi * u * ((g : ℝ) * R) ^ 2 =
      6 * Real.pi * (u * ((g : ℝ) * R) ^ 2) by ring,
    hscaleG,
    show 4 * Real.pi ^ 2 * u ^ 2 * ((g : ℝ) * R) ^ 4 =
      4 * Real.pi ^ 2 * (u ^ 2 * ((g : ℝ) * R) ^ 4) by ring,
    hscaleG4]

/-- The complete angular polynomial is the product of the two original density polynomials. -/
theorem eval_thetaCuspDensityPrimitiveRayPolynomial
    (u R A B : ℝ) (g : ℕ)
    (hA : u * R ^ 2 = A ^ 2)
    (hB : (1 - u) * R ^ 2 = B ^ 2) :
    eval ((g : ℝ) * R) (thetaCuspDensityPrimitiveRayPolynomial u) =
      eval ((g : ℝ) * A) (thetaCuspTailDerivativePolynomial 2) *
        eval ((g : ℝ) * B) (thetaCuspTailDerivativePolynomial 2) := by
  unfold thetaCuspDensityPrimitiveRayPolynomial
  rw [eval_mul,
    eval_thetaCuspDensityRadialScaledPolynomial u R A g hA,
    eval_thetaCuspDensityRadialScaledPolynomial (1 - u) R B g hB]

/-- Radial logarithmic coordinate of one primitive direction. -/
def thetaCuspPrimitiveRayRadialLog (a b : ℕ) (x y : ℝ) : ℝ :=
  (1 / 2 : ℝ) * Real.log
    ((((a : ℝ) * Real.exp x) ^ 2) + (((b : ℝ) * Real.exp y) ^ 2))

/-- Squared angular coordinate of the first primitive direction. -/
def thetaCuspPrimitiveRayAngularWeight (a b : ℕ) (x y : ℝ) : ℝ :=
  (((a : ℝ) * Real.exp x) ^ 2) /
    ((((a : ℝ) * Real.exp x) ^ 2) + (((b : ℝ) * Real.exp y) ^ 2))

/-- **Primitive-ray radial normal form.**  A pair of exact density atoms with a common arithmetic
scale is one radial theta atom.  The formula keeps the entire degree-eight angular polynomial and
does not split either density factor into absolute-value estimates. -/
theorem thetaCuspTailSecondDensityAtom_primitiveRay_eq_radial
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (g : ℕ) (x y : ℝ) :
    thetaCuspTailSecondDensityAtom (a * g) x *
        thetaCuspTailSecondDensityAtom (b * g) y =
      16 * Real.exp
          ((x + y - thetaCuspPrimitiveRayRadialLog a b x y) / 2) *
        thetaCuspPolynomialAtom
          (thetaCuspDensityPrimitiveRayPolynomial
            (thetaCuspPrimitiveRayAngularWeight a b x y))
          g (thetaCuspPrimitiveRayRadialLog a b x y) := by
  let A : ℝ := (a : ℝ) * Real.exp x
  let B : ℝ := (b : ℝ) * Real.exp y
  let S : ℝ := A ^ 2 + B ^ 2
  let r : ℝ := (1 / 2 : ℝ) * Real.log S
  let u : ℝ := A ^ 2 / S
  have hApos : 0 < A := mul_pos (by exact_mod_cast ha) (Real.exp_pos x)
  have hBpos : 0 < B := mul_pos (by exact_mod_cast hb) (Real.exp_pos y)
  have hSpos : 0 < S := by
    dsimp only [S]
    positivity
  have hexpSq : Real.exp r ^ 2 = S := by
    rw [pow_two, ← Real.exp_add]
    rw [show r + r = Real.log S by dsimp only [r]; ring,
      Real.exp_log hSpos]
  have huA : u * Real.exp r ^ 2 = A ^ 2 := by
    rw [hexpSq]
    dsimp only [u]
    field_simp [hSpos.ne']
  have huB : (1 - u) * Real.exp r ^ 2 = B ^ 2 := by
    rw [hexpSq]
    dsimp only [u, S]
    field_simp [hSpos.ne']
    ring
  have hindexA : ((((a * g : ℕ) : ℝ)) * Real.exp x) = (g : ℝ) * A := by
    dsimp only [A]
    push_cast
    ring
  have hindexB : ((((b * g : ℕ) : ℝ)) * Real.exp y) = (g : ℝ) * B := by
    dsimp only [B]
    push_cast
    ring
  have hpoly :
      eval ((g : ℝ) * Real.exp r)
          (thetaCuspDensityPrimitiveRayPolynomial u) =
        eval ((((a * g : ℕ) : ℝ)) * Real.exp x)
            (thetaCuspTailDerivativePolynomial 2) *
          eval ((((b * g : ℕ) : ℝ)) * Real.exp y)
            (thetaCuspTailDerivativePolynomial 2) := by
    rw [hindexA, hindexB]
    exact eval_thetaCuspDensityPrimitiveRayPolynomial
      u (Real.exp r) A B g huA huB
  have hgaussArg : ((g : ℝ) * Real.exp r) ^ 2 =
      ((((a * g : ℕ) : ℝ)) * Real.exp x) ^ 2 +
        ((((b * g : ℕ) : ℝ)) * Real.exp y) ^ 2 := by
    rw [hindexA, hindexB]
    calc
      ((g : ℝ) * Real.exp r) ^ 2 = (g : ℝ) ^ 2 * S := by
        rw [show ((g : ℝ) * Real.exp r) ^ 2 =
          (g : ℝ) ^ 2 * Real.exp r ^ 2 by ring, hexpSq]
      _ = ((g : ℝ) * A) ^ 2 + ((g : ℝ) * B) ^ 2 := by
        dsimp only [S]
        ring
  have hgauss :
      Real.exp (-Real.pi * ((g : ℝ) * Real.exp r) ^ 2) =
        Real.exp (-Real.pi *
            ((((a * g : ℕ) : ℝ)) * Real.exp x) ^ 2) *
          Real.exp (-Real.pi *
            ((((b * g : ℕ) : ℝ)) * Real.exp y) ^ 2) := by
    rw [← Real.exp_add, hgaussArg]
    congr 1
    ring
  have hweight :
      Real.exp ((x + y - r) / 2) * Real.exp (r / 2) =
        Real.exp (x / 2) * Real.exp (y / 2) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hr : thetaCuspPrimitiveRayRadialLog a b x y = r := by
    dsimp only [thetaCuspPrimitiveRayRadialLog, r, S, A, B]
  have hu : thetaCuspPrimitiveRayAngularWeight a b x y = u := by
    dsimp only [thetaCuspPrimitiveRayAngularWeight, u, S, A, B]
  rw [hr, hu]
  unfold thetaCuspTailSecondDensityAtom thetaCuspPolynomialAtom
  rw [hpoly, hgauss]
  calc
    4 *
          (Real.exp (x / 2) *
              eval (((a * g : ℕ) : ℝ) * Real.exp x)
                (thetaCuspTailDerivativePolynomial 2) *
            Real.exp (-Real.pi *
              (((a * g : ℕ) : ℝ) * Real.exp x) ^ 2)) *
        (4 *
          (Real.exp (y / 2) *
              eval (((b * g : ℕ) : ℝ) * Real.exp y)
                (thetaCuspTailDerivativePolynomial 2) *
            Real.exp (-Real.pi *
              (((b * g : ℕ) : ℝ) * Real.exp y) ^ 2))) =
      16 * (Real.exp (x / 2) * Real.exp (y / 2)) *
        (eval (((a * g : ℕ) : ℝ) * Real.exp x)
            (thetaCuspTailDerivativePolynomial 2) *
          eval (((b * g : ℕ) : ℝ) * Real.exp y)
            (thetaCuspTailDerivativePolynomial 2)) *
        (Real.exp (-Real.pi *
            (((a * g : ℕ) : ℝ) * Real.exp x) ^ 2) *
          Real.exp (-Real.pi *
            (((b * g : ℕ) : ℝ) * Real.exp y) ^ 2)) := by ring
    _ = 16 *
        (Real.exp ((x + y - r) / 2) * Real.exp (r / 2)) *
        (eval (((a * g : ℕ) : ℝ) * Real.exp x)
            (thetaCuspTailDerivativePolynomial 2) *
          eval (((b * g : ℕ) : ℝ) * Real.exp y)
            (thetaCuspTailDerivativePolynomial 2)) *
        (Real.exp (-Real.pi *
            (((a * g : ℕ) : ℝ) * Real.exp x) ^ 2) *
          Real.exp (-Real.pi *
            (((b * g : ℕ) : ℝ) * Real.exp y) ^ 2)) := by rw [hweight]
    _ = 16 * Real.exp ((x + y - r) / 2) *
        (Real.exp (r / 2) *
          (eval (((a * g : ℕ) : ℝ) * Real.exp x)
              (thetaCuspTailDerivativePolynomial 2) *
            eval (((b * g : ℕ) : ℝ) * Real.exp y)
              (thetaCuspTailDerivativePolynomial 2)) *
          (Real.exp (-Real.pi *
              (((a * g : ℕ) : ℝ) * Real.exp x) ^ 2) *
            Real.exp (-Real.pi *
              (((b * g : ℕ) : ℝ) * Real.exp y) ^ 2))) := by ring

/-! ## The finite-core angular seam -/

private theorem hasDerivAt_star_of_real
    {f : ℝ → ℂ} {f' : ℂ} {x : ℝ} (hf : HasDerivAt f f' x) :
    HasDerivAt (fun t : ℝ => (starRingEnd ℂ) (f t)) ((starRingEnd ℂ) f') x := by
  let c : ℝ → ℂ →L[ℝ] ℂ := fun _ =>
    (RCLike.conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap
  have hc : HasDerivAt c 0 x := hasDerivAt_const x _
  have h := hc.clm_apply hf
  simpa only [c, Pi.zero_apply, _root_.zero_apply, zero_add,
    RCLike.conjCLE_apply] using! h

theorem continuous_thetaCuspTailSecondSectionSourceSpectralDerivative
    (d : ℕ) (z : ℂ) :
    Continuous (thetaCuspTailSecondSectionSourceSpectralDerivative d z) := by
  unfold thetaCuspTailSecondSectionSourceSpectralDerivative
  continuity

theorem continuous_thetaCuspTailSecondCoreAtomSourceSpectralDerivative
    (d : ℕ) (z : ℂ) :
    Continuous (thetaCuspTailSecondCoreAtomSourceSpectralDerivative d z) := by
  have hsource : Continuous (thetaCuspTailSecondSectionSourceDerivative d z) :=
    continuous_iff_continuousAt.mpr fun x =>
      (hasDerivAt_thetaCuspTailSecondSectionSourceDerivative d z x).continuousAt
  unfold thetaCuspTailSecondCoreAtomSourceSpectralDerivative
  exact ((continuous_const.mul hsource).sub
    (continuous_const.mul
      (continuous_thetaCuspTailSecondSectionSourceSpectralDerivative d z)))

theorem continuous_thetaCuspTailSecondCoreAtom (d : ℕ) (z : ℂ) :
    Continuous (thetaCuspTailSecondCoreAtom d z) :=
  continuous_iff_continuousAt.mpr fun x =>
    (hasDerivAt_thetaCuspTailSecondCoreAtom_source d z x).continuousAt

theorem continuous_thetaCuspTailSecondCoreAtomDerivative (d : ℕ) (z : ℂ) :
    Continuous (thetaCuspTailSecondCoreAtomDerivative d z) :=
  continuous_iff_continuousAt.mpr fun x =>
    (hasDerivAt_thetaCuspTailSecondCoreAtomDerivative_source d z x).continuousAt

theorem continuous_thetaCuspTailSecondCoreAtomSourceDerivative
    (d : ℕ) (z : ℂ) :
    Continuous (thetaCuspTailSecondCoreAtomSourceDerivative d z) :=
  continuous_iff_continuousAt.mpr fun x =>
    (hasDerivAt_thetaCuspTailSecondCoreAtomSourceDerivative d z x).continuousAt

/-- The first-source derivative of the finite Hermitian core-pair current.  Its swapped copy is
the second-source derivative, so the angular derivative remains one joint signed expression. -/
def thetaCuspPrimitiveRayCorePairFirstSourceCurrent
    (d : ℕ) (z : ℂ) (x y : ℝ) : ℝ :=
  ((thetaCuspTailSecondCoreAtomSourceSpectralDerivative d z x *
        (starRingEnd ℂ) (thetaCuspTailSecondCoreAtom d z y)).im +
    (thetaCuspTailSecondCoreAtomDerivative d z y *
        (starRingEnd ℂ) (thetaCuspTailSecondCoreAtomSourceDerivative d z x)).im) / 2

theorem continuous_thetaCuspPrimitiveRayCorePairFirstSourceCurrent
    (d : ℕ) (z : ℂ) :
    Continuous (fun p : ℝ × ℝ =>
      thetaCuspPrimitiveRayCorePairFirstSourceCurrent d z p.1 p.2) := by
  unfold thetaCuspPrimitiveRayCorePairFirstSourceCurrent
  have hterm1 :=
    (continuous_thetaCuspTailSecondCoreAtomSourceSpectralDerivative d z).comp
      continuous_fst |>.mul
        (Complex.continuous_conj.comp
          ((continuous_thetaCuspTailSecondCoreAtom d z).comp continuous_snd))
  have hterm2 :=
    (continuous_thetaCuspTailSecondCoreAtomDerivative d z).comp
      continuous_snd |>.mul
        (Complex.continuous_conj.comp
          ((continuous_thetaCuspTailSecondCoreAtomSourceDerivative d z).comp
            continuous_fst))
  exact ((Complex.continuous_im.comp hterm1).add
    (Complex.continuous_im.comp hterm2)).div_const 2

theorem hasDerivAt_xiCTaylorThetaTailCorePairCurrent_firstSource
    (d : ℕ) (z : ℂ) (x y : ℝ) :
    HasDerivAt (fun t : ℝ => xiCTaylorThetaTailCorePairCurrent d z (t, y))
      (thetaCuspPrimitiveRayCorePairFirstSourceCurrent d z x y) x := by
  have hDx := hasDerivAt_thetaCuspTailSecondCoreAtomDerivative_source d z x
  have hVx := hasDerivAt_thetaCuspTailSecondCoreAtom_source d z x
  have hconjVx := hasDerivAt_star_of_real hVx
  have hterm1 := hDx.mul (hasDerivAt_const x
    ((starRingEnd ℂ) (thetaCuspTailSecondCoreAtom d z y)))
  have hterm2 := (hasDerivAt_const x
    (thetaCuspTailSecondCoreAtomDerivative d z y)).mul hconjVx
  have hsum := hterm1.add hterm2
  have him := (hasDerivAt_const x Complex.imCLM).clm_apply hsum
  have hhalf := him.div_const 2
  have hhalf' := hhalf.congr_deriv
    (g' := thetaCuspPrimitiveRayCorePairFirstSourceCurrent d z x y) (by
      unfold thetaCuspPrimitiveRayCorePairFirstSourceCurrent
      simp)
  simpa [xiCTaylorThetaTailCorePairCurrent] using! hhalf'

/-- First logarithmic source coordinate on a fixed primitive radial fibre. -/
def thetaCuspPrimitiveRayCorePolarX (r alpha u : ℝ) : ℝ :=
  r + Real.log u / 2 + alpha

/-- Second logarithmic source coordinate on a fixed primitive radial fibre. -/
def thetaCuspPrimitiveRayCorePolarY (r beta u : ℝ) : ℝ :=
  r + Real.log (1 - u) / 2 + beta

/-- The active angular endpoint at which the first positive-half-line coordinate reaches zero. -/
def thetaCuspPrimitiveRayCorePolarLowerEndpoint (r alpha : ℝ) : ℝ :=
  Real.exp (-2 * (r + alpha))

/-- The active angular endpoint at which the second positive-half-line coordinate reaches zero. -/
def thetaCuspPrimitiveRayCorePolarUpperEndpoint (r beta : ℝ) : ℝ :=
  1 - Real.exp (-2 * (r + beta))

@[simp] theorem thetaCuspPrimitiveRayCorePolarX_lowerEndpoint
    (r alpha : ℝ) :
    thetaCuspPrimitiveRayCorePolarX r alpha
      (thetaCuspPrimitiveRayCorePolarLowerEndpoint r alpha) = 0 := by
  unfold thetaCuspPrimitiveRayCorePolarX
    thetaCuspPrimitiveRayCorePolarLowerEndpoint
  rw [Real.log_exp]
  ring

@[simp] theorem thetaCuspPrimitiveRayCorePolarY_upperEndpoint
    (r beta : ℝ) :
    thetaCuspPrimitiveRayCorePolarY r beta
      (thetaCuspPrimitiveRayCorePolarUpperEndpoint r beta) = 0 := by
  unfold thetaCuspPrimitiveRayCorePolarY
    thetaCuspPrimitiveRayCorePolarUpperEndpoint
  rw [show 1 - (1 - Real.exp (-2 * (r + beta))) =
      Real.exp (-2 * (r + beta)) by ring,
    Real.log_exp]
  ring

/-- The actual finite theta-tail core-pair current restricted to one primitive polar fibre. -/
def thetaCuspPrimitiveRayCorePolarKernel
    (d : ℕ) (z : ℂ) (r alpha beta u : ℝ) : ℝ :=
  xiCTaylorThetaTailCorePairCurrent d z
    (thetaCuspPrimitiveRayCorePolarX r alpha u,
      thetaCuspPrimitiveRayCorePolarY r beta u)

/-- Exact angular derivative of the finite core-pair kernel.  The two translated source edges are
kept with their opposite Jacobian signs rather than bounded separately. -/
def thetaCuspPrimitiveRayCorePolarKernelDerivative
    (d : ℕ) (z : ℂ) (r alpha beta u : ℝ) : ℝ :=
  (1 / (2 * u)) *
      thetaCuspPrimitiveRayCorePairFirstSourceCurrent d z
        (thetaCuspPrimitiveRayCorePolarX r alpha u)
        (thetaCuspPrimitiveRayCorePolarY r beta u) -
    (1 / (2 * (1 - u))) *
      thetaCuspPrimitiveRayCorePairFirstSourceCurrent d z
        (thetaCuspPrimitiveRayCorePolarY r beta u)
        (thetaCuspPrimitiveRayCorePolarX r alpha u)

theorem hasDerivAt_thetaCuspPrimitiveRayCorePolarKernel
    (d : ℕ) (z : ℂ) (r alpha beta : ℝ) {u : ℝ} (hu : u ∈ Set.Ioo 0 1) :
    HasDerivAt (thetaCuspPrimitiveRayCorePolarKernel d z r alpha beta)
      (thetaCuspPrimitiveRayCorePolarKernelDerivative d z r alpha beta u) u := by
  have hx : HasDerivAt (thetaCuspPrimitiveRayCorePolarX r alpha)
      (1 / (2 * u)) u := by
    have hraw :=
      (((Real.hasDerivAt_log hu.1.ne').div_const 2).const_add r).add_const alpha
    have hraw' := hraw.congr_deriv (g' := 1 / (2 * u)) (by field_simp)
    simpa only [thetaCuspPrimitiveRayCorePolarX, Pi.add_apply,
      Pi.div_apply] using! hraw'
  have hy : HasDerivAt (thetaCuspPrimitiveRayCorePolarY r beta)
      (-(1 / (2 * (1 - u)))) u := by
    have hsub : HasDerivAt (fun t : ℝ => 1 - t) (-1) u := by
      simpa using! (hasDerivAt_const u 1).sub (hasDerivAt_id u)
    have hlog := (Real.hasDerivAt_log (sub_pos.mpr hu.2).ne').comp u hsub
    have hraw := ((hlog.div_const 2).const_add r).add_const beta
    have hraw' := hraw.congr_deriv
      (g' := -(1 / (2 * (1 - u)))) (by field_simp)
    simpa only [thetaCuspPrimitiveRayCorePolarY, Pi.add_apply,
      Pi.div_apply] using! hraw'
  have hDx : HasDerivAt
      (fun t : ℝ => thetaCuspTailSecondCoreAtomDerivative d z
        (thetaCuspPrimitiveRayCorePolarX r alpha t))
      (((1 / (2 * u) : ℝ) : ℂ) *
        thetaCuspTailSecondCoreAtomSourceSpectralDerivative d z
          (thetaCuspPrimitiveRayCorePolarX r alpha u)) u := by
    simpa using! ((hasDerivAt_thetaCuspTailSecondCoreAtomDerivative_source d z
      (thetaCuspPrimitiveRayCorePolarX r alpha u)).hasFDerivAt.comp
        u hx.hasFDerivAt).hasDerivAt
  have hDy : HasDerivAt
      (fun t : ℝ => thetaCuspTailSecondCoreAtomDerivative d z
        (thetaCuspPrimitiveRayCorePolarY r beta t))
      (((-(1 / (2 * (1 - u))) : ℝ) : ℂ) *
        thetaCuspTailSecondCoreAtomSourceSpectralDerivative d z
          (thetaCuspPrimitiveRayCorePolarY r beta u)) u := by
    simpa using! ((hasDerivAt_thetaCuspTailSecondCoreAtomDerivative_source d z
      (thetaCuspPrimitiveRayCorePolarY r beta u)).hasFDerivAt.comp
        u hy.hasFDerivAt).hasDerivAt
  have hVx : HasDerivAt
      (fun t : ℝ => thetaCuspTailSecondCoreAtom d z
        (thetaCuspPrimitiveRayCorePolarX r alpha t))
      (((1 / (2 * u) : ℝ) : ℂ) *
        thetaCuspTailSecondCoreAtomSourceDerivative d z
          (thetaCuspPrimitiveRayCorePolarX r alpha u)) u := by
    simpa using! ((hasDerivAt_thetaCuspTailSecondCoreAtom_source d z
      (thetaCuspPrimitiveRayCorePolarX r alpha u)).hasFDerivAt.comp
        u hx.hasFDerivAt).hasDerivAt
  have hVy : HasDerivAt
      (fun t : ℝ => thetaCuspTailSecondCoreAtom d z
        (thetaCuspPrimitiveRayCorePolarY r beta t))
      (((-(1 / (2 * (1 - u))) : ℝ) : ℂ) *
        thetaCuspTailSecondCoreAtomSourceDerivative d z
          (thetaCuspPrimitiveRayCorePolarY r beta u)) u := by
    simpa using! ((hasDerivAt_thetaCuspTailSecondCoreAtom_source d z
      (thetaCuspPrimitiveRayCorePolarY r beta u)).hasFDerivAt.comp
        u hy.hasFDerivAt).hasDerivAt
  have hcVx := hasDerivAt_star_of_real hVx
  have hcVy := hasDerivAt_star_of_real hVy
  have hterm1 := hDx.mul hcVy
  have hterm2 := hDy.mul hcVx
  have hsum := hterm1.add hterm2
  have him := (hasDerivAt_const u Complex.imCLM).clm_apply hsum
  have hhalf := him.div_const 2
  have hhalf' := hhalf.congr_deriv
    (g' := thetaCuspPrimitiveRayCorePolarKernelDerivative d z r alpha beta u) (by
      unfold thetaCuspPrimitiveRayCorePolarKernelDerivative
        thetaCuspPrimitiveRayCorePairFirstSourceCurrent
      simp [Complex.normSq_apply]
      field_simp [hu.1.ne', (sub_pos.mpr hu.2).ne']
      ring)
  exact hhalf'.congr_of_eventuallyEq (by
    filter_upwards with t
    simp [thetaCuspPrimitiveRayCorePolarKernel,
      xiCTaylorThetaTailCorePairCurrent])

/-- **Canonical seam-preserving primitive-ray bridge.**  The growing reflection character paired
with the actual finite theta-tail core equals the two swept endpoint values and the single signed
cosine--sine translation derivative.  This is the concrete joint identity needed before any
anisotropic estimate: the window and finite top-edge terms have not been separated by absolute
values. -/
theorem integral_thetaCuspPrimitiveRayGrowingCoefficient_mul_corePolarKernel
    (d : ℕ) (z : ℂ) (r alpha beta : ℝ) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) :
    (∫ u : ℝ in a..b,
      thetaCuspPrimitiveRayGrowingCoefficient u *
          (thetaCuspPrimitiveRayMoment u) ^ (-(3 / 4 : ℝ)) *
          thetaCuspPrimitiveRayCorePolarKernel d z r alpha beta u) =
      thetaCuspPrimitiveRayAngularFlux b *
          thetaCuspPrimitiveRayCorePolarKernel d z r alpha beta b -
        thetaCuspPrimitiveRayAngularFlux a *
          thetaCuspPrimitiveRayCorePolarKernel d z r alpha beta a -
        ∫ u : ℝ in a..b,
          thetaCuspPrimitiveRayAngularFlux u *
            thetaCuspPrimitiveRayCorePolarKernelDerivative d z r alpha beta u := by
  have hsub : Set.uIcc a b ⊆ Set.Ioo 0 1 := by
    rw [Set.uIcc_of_le hab]
    intro u hu
    exact ⟨lt_of_lt_of_le ha hu.1, lt_of_le_of_lt hu.2 hb⟩
  apply integral_thetaCuspPrimitiveRayGrowingCoefficient_mul_kernel ha hab hb
  · intro u hu
    exact hasDerivAt_thetaCuspPrimitiveRayCorePolarKernel d z r alpha beta (hsub hu)
  · apply ContinuousOn.intervalIntegrable
    intro u hu
    have hui := hsub hu
    have htwo_u : 2 * u ≠ 0 := mul_ne_zero (by norm_num) hui.1.ne'
    have htwo_one_sub_u : 2 * (1 - u) ≠ 0 :=
      mul_ne_zero (by norm_num) (sub_pos.mpr hui.2).ne'
    have hx : ContinuousAt (thetaCuspPrimitiveRayCorePolarX r alpha) u := by
      unfold thetaCuspPrimitiveRayCorePolarX
      exact (((Real.hasDerivAt_log hui.1.ne').continuousAt.div_const 2).const_add r).add_const alpha
    have hy : ContinuousAt (thetaCuspPrimitiveRayCorePolarY r beta) u := by
      unfold thetaCuspPrimitiveRayCorePolarY
      have hsubAt : ContinuousAt (fun t : ℝ => 1 - t) u :=
        continuousAt_const.sub continuousAt_id
      exact ((((Real.hasDerivAt_log (sub_pos.mpr hui.2).ne').continuousAt.comp
        hsubAt).div_const 2).const_add r).add_const beta
    have hxy : ContinuousAt (fun t : ℝ =>
        thetaCuspPrimitiveRayCorePairFirstSourceCurrent d z
          (thetaCuspPrimitiveRayCorePolarX r alpha t)
          (thetaCuspPrimitiveRayCorePolarY r beta t)) u :=
      by
        have hcomp :=
          (continuous_thetaCuspPrimitiveRayCorePairFirstSourceCurrent d z).continuousAt.comp
            (hx.prodMk hy)
        simpa only [Function.comp_apply] using! hcomp
    have hyx : ContinuousAt (fun t : ℝ =>
        thetaCuspPrimitiveRayCorePairFirstSourceCurrent d z
          (thetaCuspPrimitiveRayCorePolarY r beta t)
          (thetaCuspPrimitiveRayCorePolarX r alpha t)) u :=
      by
        have hcomp :=
          (continuous_thetaCuspPrimitiveRayCorePairFirstSourceCurrent d z).continuousAt.comp
            (hy.prodMk hx)
        simpa only [Function.comp_apply] using! hcomp
    have hcoefx : ContinuousAt (fun t : ℝ => 1 / (2 * t)) u :=
      continuousAt_const.div (continuousAt_const.mul continuousAt_id) htwo_u
    have hcoefy : ContinuousAt (fun t : ℝ => 1 / (2 * (1 - t))) u :=
      continuousAt_const.div
        (continuousAt_const.mul (continuousAt_const.sub continuousAt_id))
        htwo_one_sub_u
    apply ContinuousAt.continuousWithinAt
    unfold thetaCuspPrimitiveRayCorePolarKernelDerivative
    exact (hcoefx.mul hxy).sub (hcoefy.mul hyx)

/-- **Active-window form of the primitive seam bridge.**  On the exact angular interval cut out by
the two positive-half-line constraints, the endpoint terms are literally the first-coordinate and
second-coordinate seams.  The identity keeps those swept windows together with the finite
cosine--sine angular derivative. -/
theorem integral_thetaCuspPrimitiveRayGrowingCoefficient_mul_corePolarKernel_activeWindow
    (d : ℕ) (z : ℂ) (r alpha beta : ℝ)
    (hactive : thetaCuspPrimitiveRayCorePolarLowerEndpoint r alpha ≤
      thetaCuspPrimitiveRayCorePolarUpperEndpoint r beta) :
    (∫ u : ℝ in
        thetaCuspPrimitiveRayCorePolarLowerEndpoint r alpha..
          thetaCuspPrimitiveRayCorePolarUpperEndpoint r beta,
      thetaCuspPrimitiveRayGrowingCoefficient u *
          (thetaCuspPrimitiveRayMoment u) ^ (-(3 / 4 : ℝ)) *
          thetaCuspPrimitiveRayCorePolarKernel d z r alpha beta u) =
      thetaCuspPrimitiveRayAngularFlux
          (thetaCuspPrimitiveRayCorePolarUpperEndpoint r beta) *
          xiCTaylorThetaTailCorePairCurrent d z
            (thetaCuspPrimitiveRayCorePolarX r alpha
                (thetaCuspPrimitiveRayCorePolarUpperEndpoint r beta), 0) -
        thetaCuspPrimitiveRayAngularFlux
          (thetaCuspPrimitiveRayCorePolarLowerEndpoint r alpha) *
          xiCTaylorThetaTailCorePairCurrent d z
            (0, thetaCuspPrimitiveRayCorePolarY r beta
                (thetaCuspPrimitiveRayCorePolarLowerEndpoint r alpha)) -
        ∫ u : ℝ in
          thetaCuspPrimitiveRayCorePolarLowerEndpoint r alpha..
            thetaCuspPrimitiveRayCorePolarUpperEndpoint r beta,
          thetaCuspPrimitiveRayAngularFlux u *
            thetaCuspPrimitiveRayCorePolarKernelDerivative d z r alpha beta u := by
  have hlower : 0 < thetaCuspPrimitiveRayCorePolarLowerEndpoint r alpha := by
    unfold thetaCuspPrimitiveRayCorePolarLowerEndpoint
    positivity
  have hupper : thetaCuspPrimitiveRayCorePolarUpperEndpoint r beta < 1 := by
    unfold thetaCuspPrimitiveRayCorePolarUpperEndpoint
    linarith [Real.exp_pos (-2 * (r + beta))]
  rw [integral_thetaCuspPrimitiveRayGrowingCoefficient_mul_corePolarKernel
    d z r alpha beta hlower hactive hupper]
  unfold thetaCuspPrimitiveRayCorePolarKernel
  rw [thetaCuspPrimitiveRayCorePolarY_upperEndpoint,
    thetaCuspPrimitiveRayCorePolarX_lowerEndpoint]

end

end RHTower
