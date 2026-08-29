import GaloisForLFunctions.RHTower.LiEvenCrossAllModeLaguerreClock
import GaloisForLFunctions.RHTower.XiShiftedHardEdgeCompletedDensity
import GaloisForLFunctions.RHTower.ReciprocalAtomTestSpaceClosure

/-!
# Completed Abel landing for the all-mode Li cross clock

This module polarizes the corpus hard-edge completed-density theorem at every
Li mode.  For mass `a > 1/2`, the prime reporter is absolutely summable and its
Fourier transform is the exact Laguerre clock

`(π a / 2) exp (-a |ξ|) Qₙ(2 a |ξ|)`.

The divisor side admits a dominated endpoint at `a = 1/2`; consequently the
joint polar--archimedean--prime expression has a rigorous right limit even
though its pieces cannot be separated at the critical boundary.  The endpoint
is exactly one eighth of the even Li prime--archimedean square source.  Thus
nonnegativity of all completed Abel endpoints is equivalent to RH.

Proof-chain burden removed:

`completed Abel endpoint nonnegative in every mode`
`→ Li prime--archimedean square source nonnegative`
`→ positive even paired Li coefficients nonnegative`
`→ Riemann hypothesis`.
-/

open Complex MeasureTheory Polynomial Real Set Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

def liEvenCrossCauchyDensityAtMass (a : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  routeUHardEdgeCrossCauchyDensity a
    (liEvenCrossLeftPolynomial n) (liEvenCrossRightPolynomial n) x

theorem liEvenCrossCauchyDensityAtMass_eq_unit_scaled
    {a : ℝ} (ha : 0 < a) (n : ℕ) (x : ℝ) :
    liEvenCrossCauchyDensityAtMass a n x =
      liUnitEvenCrossCauchyDensity n (x / a) := by
  rw [liUnitEvenCrossCauchyDensity, liCriticalEvenCrossCauchyDensity_eq_squareDefect]
  simp only [liEvenCrossCauchyDensityAtMass, routeUHardEdgeCrossCauchyDensity,
    liEvenCrossRightPolynomial, Polynomial.eval_mul, Polynomial.eval_sub,
    Polynomial.eval_one, Polynomial.eval_X]
  let u : ℝ := (a ^ 2 - x ^ 2) / (a ^ 2 + x ^ 2)
  have hden : a ^ 2 + x ^ 2 ≠ 0 := by positivity
  have hcoord : liCriticalCayleyCoordinate (x / a / 2) = u := by
    rw [liCriticalCayleyCoordinate]
    dsimp only [u]
    field_simp [ha.ne', hden]
  rw [hcoord]
  have hfactor : a ^ 2 / (a ^ 2 + x ^ 2) * (1 - u) = (1 - u ^ 2) / 2 := by
    dsimp only [u]
    field_simp [hden]
    ring
  rw [← hfactor]
  ring

def liEvenCrossLaguerreFourierProfileAtMass (a : ℝ) (n : ℕ) (ξ : ℝ) : ℂ :=
  ((Real.pi * a / 2 * Real.exp (-(a * |ξ|)) *
    (liCrossLaguerreClockPolynomial n).eval (2 * a * |ξ|) : ℝ) : ℂ)

theorem routeUFourierIntegral_liEvenCrossCauchyDensityAtMass
    {a : ℝ} (ha : 0 < a) (n : ℕ) (ξ : ℝ) :
    routeUFourierIntegral (fun x : ℝ =>
      (liEvenCrossCauchyDensityAtMass a n x : ℂ)) ξ =
      liEvenCrossLaguerreFourierProfileAtMass a n ξ := by
  let G : ℝ → ℂ := fun y =>
    (liUnitEvenCrossCauchyDensity n y : ℂ) *
      Complex.exp (-I * ((((a * ξ) * y : ℝ) : ℂ)))
  have hscale := MeasureTheory.Measure.integral_comp_mul_left G a⁻¹
  simp only [inv_inv, abs_of_pos ha] at hscale
  rw [routeUFourierIntegral]
  rw [show (fun x : ℝ => (liEvenCrossCauchyDensityAtMass a n x : ℂ) *
      Complex.exp (-I * ((ξ * x : ℝ) : ℂ))) = fun x : ℝ => G (a⁻¹ * x) by
    funext x
    dsimp only [G]
    rw [liEvenCrossCauchyDensityAtMass_eq_unit_scaled ha]
    congr 2
    · congr 1
      field_simp [ha.ne']
    · push_cast
      field_simp [ha.ne']
      ]
  rw [hscale]
  change (a : ℂ) * routeUFourierIntegral
    (fun x : ℝ => (liUnitEvenCrossCauchyDensity n x : ℂ)) (a * ξ) = _
  rw [routeUFourierIntegral_liUnitEvenCrossCauchyDensity]
  unfold liUnitEvenCrossLaguerreFourierProfile
    liEvenCrossLaguerreFourierProfileAtMass
  have habs : |a * ξ| = a * |ξ| := by rw [abs_mul, abs_of_pos ha]
  rw [habs]
  push_cast
  ring_nf

def liEvenCrossLeftReciprocalPolynomialAtMass (a : ℝ) (n : ℕ) : Polynomial ℝ :=
  xiHardEdgeReciprocalPolynomial a (liEvenCrossLeftPolynomial n)

def liEvenCrossRightReciprocalPolynomialAtMass (a : ℝ) (n : ℕ) : Polynomial ℝ :=
  xiHardEdgeReciprocalPolynomial a (liEvenCrossRightPolynomial n)

theorem routeUHardEdgeRationalTest_liEvenCrossReciprocal_mul
    {a : ℝ} (ha : 0 < a) (n : ℕ) (x : ℝ) :
    routeUHardEdgeRationalTest a (liEvenCrossLeftReciprocalPolynomialAtMass a n) x *
        routeUHardEdgeRationalTest a (liEvenCrossRightReciprocalPolynomialAtMass a n) x =
      liEvenCrossCauchyDensityAtMass a n x := by
  have hden : 0 < a ^ 2 + x ^ 2 := by positivity
  have hsqrt : Real.sqrt (a ^ 2 + x ^ 2) ^ 2 = a ^ 2 + x ^ 2 :=
    Real.sq_sqrt hden.le
  simp only [routeUHardEdgeRationalTest, liEvenCrossLeftReciprocalPolynomialAtMass,
    liEvenCrossRightReciprocalPolynomialAtMass, xiHardEdgeReciprocalPolynomial,
    Polynomial.eval_comp, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, liEvenCrossCauchyDensityAtMass,
    routeUHardEdgeCrossCauchyDensity]
  have hcoord : 2 * a ^ 2 * (a ^ 2 + x ^ 2)⁻¹ - 1 =
      (a ^ 2 - x ^ 2) / (a ^ 2 + x ^ 2) := by
    field_simp [hden.ne']
    ring
  rw [hcoord]
  field_simp [hsqrt, hden.ne']
  rw [hsqrt]

def liEvenCrossPolarAtMass (a : ℝ) (n : ℕ) : ℝ :=
  (routeUHardEdgePolar a
      (liEvenCrossLeftReciprocalPolynomialAtMass a n +
        liEvenCrossRightReciprocalPolynomialAtMass a n) -
    routeUHardEdgePolar a
      (liEvenCrossLeftReciprocalPolynomialAtMass a n -
        liEvenCrossRightReciprocalPolynomialAtMass a n)) / 4

def liEvenCrossDivisorAbelValue (a : ℝ) (n : ℕ) : ℂ :=
  ((∑' q : XiZeroCopy, routeUHardEdgeRationalTestSq a
      (liEvenCrossLeftReciprocalPolynomialAtMass a n +
        liEvenCrossRightReciprocalPolynomialAtMass a n) (xiSpectralPoint q)) -
    (∑' q : XiZeroCopy, routeUHardEdgeRationalTestSq a
      (liEvenCrossLeftReciprocalPolynomialAtMass a n -
        liEvenCrossRightReciprocalPolynomialAtMass a n) (xiSpectralPoint q))) / 4

def liEvenCrossFourierAbelReporter (a : ℝ) (n : ℕ) (ξ : ℝ) : ℂ :=
  (routeUHardEdgeFourierSq a
      (liEvenCrossLeftReciprocalPolynomialAtMass a n +
        liEvenCrossRightReciprocalPolynomialAtMass a n) ξ -
    routeUHardEdgeFourierSq a
      (liEvenCrossLeftReciprocalPolynomialAtMass a n -
        liEvenCrossRightReciprocalPolynomialAtMass a n) ξ) / 4

theorem liEvenCrossFourierAbelReporter_eq_clock
    {a : ℝ} (ha : 0 < a) (n : ℕ) (ξ : ℝ) :
    liEvenCrossFourierAbelReporter a n ξ =
      liEvenCrossLaguerreFourierProfileAtMass a n ξ := by
  let p := liEvenCrossLeftReciprocalPolynomialAtMass a n
  let q := liEvenCrossRightReciprocalPolynomialAtMass a n
  have hpq : ∀ x : ℝ,
      ((routeUHardEdgeRationalTest a (p + q) x ^ 2 : ℝ) : ℂ) -
          ((routeUHardEdgeRationalTest a (p - q) x ^ 2 : ℝ) : ℂ) =
        4 * (liEvenCrossCauchyDensityAtMass a n x : ℂ) := by
    intro x
    have hlinAdd : routeUHardEdgeRationalTest a (p + q) x =
        routeUHardEdgeRationalTest a p x + routeUHardEdgeRationalTest a q x := by
      simp [routeUHardEdgeRationalTest]
      ring
    have hlinSub : routeUHardEdgeRationalTest a (p - q) x =
        routeUHardEdgeRationalTest a p x - routeUHardEdgeRationalTest a q x := by
      simp [routeUHardEdgeRationalTest]
      ring
    rw [hlinAdd, hlinSub]
    have hmul := routeUHardEdgeRationalTest_liEvenCrossReciprocal_mul ha n x
    change routeUHardEdgeRationalTest a p x *
      routeUHardEdgeRationalTest a q x = _ at hmul
    calc
      (((routeUHardEdgeRationalTest a p x + routeUHardEdgeRationalTest a q x) ^ 2 : ℝ) : ℂ) -
          (((routeUHardEdgeRationalTest a p x - routeUHardEdgeRationalTest a q x) ^ 2 : ℝ) : ℂ) =
        4 * ((routeUHardEdgeRationalTest a p x *
          routeUHardEdgeRationalTest a q x : ℝ) : ℂ) := by
            push_cast
            ring
      _ = _ := by rw [hmul]
  have hadd := integrable_routeUHardEdgeFourierSq_integrand ha (p + q) ξ
  have hsub := integrable_routeUHardEdgeFourierSq_integrand ha (p - q) ξ
  rw [liEvenCrossFourierAbelReporter, routeUHardEdgeFourierSq,
    routeUHardEdgeFourierSq]
  dsimp only [p, q] at hadd hsub ⊢
  rw [← integral_sub hadd hsub, ← integral_div]
  change (∫ x : ℝ,
      ((((routeUHardEdgeRationalTest a
          (liEvenCrossLeftReciprocalPolynomialAtMass a n +
            liEvenCrossRightReciprocalPolynomialAtMass a n) x) ^ 2 : ℝ) : ℂ) *
          Complex.exp (((-(ξ * x) : ℝ) : ℂ) * I) -
        (((routeUHardEdgeRationalTest a
          (liEvenCrossLeftReciprocalPolynomialAtMass a n -
            liEvenCrossRightReciprocalPolynomialAtMass a n) x) ^ 2 : ℝ) : ℂ) *
          Complex.exp (((-(ξ * x) : ℝ) : ℂ) * I)) / 4) = _
  rw [show (fun x : ℝ =>
      ((((routeUHardEdgeRationalTest a
          (liEvenCrossLeftReciprocalPolynomialAtMass a n +
            liEvenCrossRightReciprocalPolynomialAtMass a n) x) ^ 2 : ℝ) : ℂ) *
          Complex.exp (((-(ξ * x) : ℝ) : ℂ) * I) -
        (((routeUHardEdgeRationalTest a
          (liEvenCrossLeftReciprocalPolynomialAtMass a n -
            liEvenCrossRightReciprocalPolynomialAtMass a n) x) ^ 2 : ℝ) : ℂ) *
          Complex.exp (((-(ξ * x) : ℝ) : ℂ) * I)) / 4) =
      fun x => (liEvenCrossCauchyDensityAtMass a n x : ℂ) *
        Complex.exp (-I * ((ξ * x : ℝ) : ℂ)) by
    funext x
    have hx := hpq x
    dsimp only [p, q] at hx
    rw [show Complex.exp (((-(ξ * x) : ℝ) : ℂ) * I) =
        Complex.exp (-I * ((ξ * x : ℝ) : ℂ)) by
      congr 1
      push_cast
      ring]
    rw [← sub_mul, hx]
    ring]
  exact routeUFourierIntegral_liEvenCrossCauchyDensityAtMass ha n ξ

theorem summable_routeUPrimeFourierAtMass
    {a : ℝ} (ha : 1 / 2 < a) (p : Polynomial ℝ) :
    Summable (fun m : ℕ =>
      ((ArithmeticFunction.vonMangoldt m / Real.sqrt m : ℝ) : ℂ) *
        routeUHardEdgeFourierSq a p (Real.log m)) := by
  have ha0 : (0 : ℝ) < a := by linarith
  have hX : (1 : ℝ) / 4 < a ^ 2 := by nlinarith
  obtain ⟨X₀, hX₀lo, hX₀hi⟩ : ∃ X₀ : ℝ, 1 / 4 < X₀ ∧ X₀ < a ^ 2 :=
    ⟨(1 / 4 + a ^ 2) / 2, by linarith, by linarith⟩
  obtain ⟨h, hh, hhX⟩ := exists_routeUPrimeAperture hX₀lo
  have hexpand : ∀ m : ℕ,
      ((ArithmeticFunction.vonMangoldt m / Real.sqrt m : ℝ) : ℂ) *
          routeUHardEdgeFourierSq a p (Real.log m) =
        ∑ k ∈ Finset.Icc 1 (routeUHardEdgeWeilPoly p).natDegree,
          ((a ^ 2 * (routeUHardEdgeWeilPoly p).coeff k : ℝ) : ℂ) *
            routeUPrimeTerm (k - 1) m (a ^ 2) := by
    intro m
    rw [routeUHardEdgeFourierSq_eq_massPairing_sum ha0 p, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [routeUPrimeTerm]
    ring
  rw [show (fun m : ℕ =>
      ((ArithmeticFunction.vonMangoldt m / Real.sqrt m : ℝ) : ℂ) *
        routeUHardEdgeFourierSq a p (Real.log m)) =
      fun m => ∑ k ∈ Finset.Icc 1 (routeUHardEdgeWeilPoly p).natDegree,
        ((a ^ 2 * (routeUHardEdgeWeilPoly p).coeff k : ℝ) : ℂ) *
          routeUPrimeTerm (k - 1) m (a ^ 2) by
    funext m
    exact hexpand m]
  exact summable_sum fun k _ =>
    (summable_routeUPrimeTerm hh hhX (k - 1) hX₀hi).mul_left _

def liEvenCrossArchimedeanAbelValue (a : ℝ) (n : ℕ) : ℝ :=
  ∫ x : ℝ, routeUArchimedeanRate x * liEvenCrossCauchyDensityAtMass a n x

def liEvenCrossPrimeAbelValue (a : ℝ) (n : ℕ) : ℂ :=
  ∑' m : ℕ,
    ((ArithmeticFunction.vonMangoldt m / Real.sqrt m : ℝ) : ℂ) *
      liEvenCrossLaguerreFourierProfileAtMass a n (Real.log m)

theorem summable_liEvenCrossPrimeAbelTerm
    {a : ℝ} (ha : 1 / 2 < a) (n : ℕ) :
    Summable (fun m : ℕ =>
      ((ArithmeticFunction.vonMangoldt m / Real.sqrt m : ℝ) : ℂ) *
        liEvenCrossLaguerreFourierProfileAtMass a n (Real.log m)) := by
  let p := liEvenCrossLeftReciprocalPolynomialAtMass a n
  let q := liEvenCrossRightReciprocalPolynomialAtMass a n
  let w : ℕ → ℂ := fun m =>
    ((ArithmeticFunction.vonMangoldt m / Real.sqrt m : ℝ) : ℂ)
  have hp := summable_routeUPrimeFourierAtMass ha (p + q)
  have hm := summable_routeUPrimeFourierAtMass ha (p - q)
  have hcomb : Summable (fun m : ℕ =>
      (w m * routeUHardEdgeFourierSq a (p + q) (Real.log m) -
        w m * routeUHardEdgeFourierSq a (p - q) (Real.log m)) / 4) :=
    (hp.sub hm).div_const 4
  refine hcomb.congr fun m => ?_
  change (w m * routeUHardEdgeFourierSq a (p + q) (Real.log m) -
      w m * routeUHardEdgeFourierSq a (p - q) (Real.log m)) / 4 =
    w m * liEvenCrossLaguerreFourierProfileAtMass a n (Real.log m)
  rw [show (w m * routeUHardEdgeFourierSq a (p + q) (Real.log m) -
      w m * routeUHardEdgeFourierSq a (p - q) (Real.log m)) / 4 =
    w m * ((routeUHardEdgeFourierSq a (p + q) (Real.log m) -
      routeUHardEdgeFourierSq a (p - q) (Real.log m)) / 4) by ring]
  change w m * liEvenCrossFourierAbelReporter a n (Real.log m) = _
  rw [liEvenCrossFourierAbelReporter_eq_clock (by linarith : 0 < a)]

theorem liEvenCrossPrimeAbelValue_eq_polarized
    {a : ℝ} (ha : 1 / 2 < a) (n : ℕ) :
    liEvenCrossPrimeAbelValue a n =
      ((∑' m : ℕ,
          ((ArithmeticFunction.vonMangoldt m / Real.sqrt m : ℝ) : ℂ) *
            routeUHardEdgeFourierSq a
              (liEvenCrossLeftReciprocalPolynomialAtMass a n +
                liEvenCrossRightReciprocalPolynomialAtMass a n) (Real.log m)) -
        (∑' m : ℕ,
          ((ArithmeticFunction.vonMangoldt m / Real.sqrt m : ℝ) : ℂ) *
            routeUHardEdgeFourierSq a
              (liEvenCrossLeftReciprocalPolynomialAtMass a n -
                liEvenCrossRightReciprocalPolynomialAtMass a n) (Real.log m))) / 4 := by
  let p := liEvenCrossLeftReciprocalPolynomialAtMass a n
  let q := liEvenCrossRightReciprocalPolynomialAtMass a n
  let fp : ℕ → ℂ := fun m =>
    ((ArithmeticFunction.vonMangoldt m / Real.sqrt m : ℝ) : ℂ) *
      routeUHardEdgeFourierSq a (p + q) (Real.log m)
  let fm : ℕ → ℂ := fun m =>
    ((ArithmeticFunction.vonMangoldt m / Real.sqrt m : ℝ) : ℂ) *
      routeUHardEdgeFourierSq a (p - q) (Real.log m)
  have hp : Summable fp := summable_routeUPrimeFourierAtMass ha (p + q)
  have hm : Summable fm := summable_routeUPrimeFourierAtMass ha (p - q)
  rw [liEvenCrossPrimeAbelValue]
  calc
    (∑' m : ℕ,
        ((ArithmeticFunction.vonMangoldt m / Real.sqrt m : ℝ) : ℂ) *
          liEvenCrossLaguerreFourierProfileAtMass a n (Real.log m)) =
      ∑' m : ℕ, (fp m - fm m) / 4 := by
        apply tsum_congr
        intro m
        change _ =
          (((ArithmeticFunction.vonMangoldt m / Real.sqrt m : ℝ) : ℂ) *
              routeUHardEdgeFourierSq a (p + q) (Real.log m) -
            ((ArithmeticFunction.vonMangoldt m / Real.sqrt m : ℝ) : ℂ) *
              routeUHardEdgeFourierSq a (p - q) (Real.log m)) / 4
        rw [show
          (((ArithmeticFunction.vonMangoldt m / Real.sqrt m : ℝ) : ℂ) *
              routeUHardEdgeFourierSq a (p + q) (Real.log m) -
            ((ArithmeticFunction.vonMangoldt m / Real.sqrt m : ℝ) : ℂ) *
              routeUHardEdgeFourierSq a (p - q) (Real.log m)) / 4 =
          ((ArithmeticFunction.vonMangoldt m / Real.sqrt m : ℝ) : ℂ) *
            ((routeUHardEdgeFourierSq a (p + q) (Real.log m) -
              routeUHardEdgeFourierSq a (p - q) (Real.log m)) / 4) by ring]
        change _ = _ * liEvenCrossFourierAbelReporter a n (Real.log m)
        rw [liEvenCrossFourierAbelReporter_eq_clock (by linarith : 0 < a)]
    _ = (1 / 4 : ℂ) * ∑' m : ℕ, (fp m - fm m) := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro m
      ring
    _ = ((∑' m : ℕ, fp m) - ∑' m : ℕ, fm m) / 4 := by
      rw [hp.tsum_sub hm]
      ring
    _ = _ := by rfl

theorem liEvenCrossArchimedeanAbelValue_eq_polarized
    {a : ℝ} (ha : 0 < a) (n : ℕ) :
    liEvenCrossArchimedeanAbelValue a n =
      ((∫ x : ℝ, routeUArchimedeanRate x *
          routeUHardEdgeRationalTest a
            (liEvenCrossLeftReciprocalPolynomialAtMass a n +
              liEvenCrossRightReciprocalPolynomialAtMass a n) x ^ 2) -
        (∫ x : ℝ, routeUArchimedeanRate x *
          routeUHardEdgeRationalTest a
            (liEvenCrossLeftReciprocalPolynomialAtMass a n -
              liEvenCrossRightReciprocalPolynomialAtMass a n) x ^ 2)) / 4 := by
  let p := liEvenCrossLeftReciprocalPolynomialAtMass a n
  let q := liEvenCrossRightReciprocalPolynomialAtMass a n
  have hp := integrable_routeUArchimedeanRate_mul_testSq ha (p + q)
  have hm := integrable_routeUArchimedeanRate_mul_testSq ha (p - q)
  rw [← integral_sub hp hm, ← integral_div]
  apply integral_congr_ae
  filter_upwards with x
  have hlinAdd : routeUHardEdgeRationalTest a (p + q) x =
      routeUHardEdgeRationalTest a p x + routeUHardEdgeRationalTest a q x := by
    simp [routeUHardEdgeRationalTest]
    ring
  have hlinSub : routeUHardEdgeRationalTest a (p - q) x =
      routeUHardEdgeRationalTest a p x - routeUHardEdgeRationalTest a q x := by
    simp [routeUHardEdgeRationalTest]
    ring
  rw [hlinAdd, hlinSub]
  have hmul := routeUHardEdgeRationalTest_liEvenCrossReciprocal_mul ha n x
  change routeUHardEdgeRationalTest a p x *
    routeUHardEdgeRationalTest a q x = _ at hmul
  rw [← hmul]
  ring

theorem liEvenCrossDivisorAbelValue_eq_completedArithmetic
    {a : ℝ} (ha : 1 / 2 < a) (n : ℕ) :
    liEvenCrossDivisorAbelValue a n =
      2 * (liEvenCrossPolarAtMass a n : ℂ) +
        (1 / (Real.pi : ℂ)) * (liEvenCrossArchimedeanAbelValue a n : ℂ) -
          (1 / (Real.pi : ℂ)) * liEvenCrossPrimeAbelValue a n := by
  let p := liEvenCrossLeftReciprocalPolynomialAtMass a n
  let q := liEvenCrossRightReciprocalPolynomialAtMass a n
  have hplus := tsum_routeUHardEdgeRationalTestSq_eq_density ha (p + q)
  have hminus := tsum_routeUHardEdgeRationalTestSq_eq_density ha (p - q)
  rw [liEvenCrossDivisorAbelValue]
  change ((∑' z : XiZeroCopy,
      routeUHardEdgeRationalTestSq a (p + q) (xiSpectralPoint z)) -
    (∑' z : XiZeroCopy,
      routeUHardEdgeRationalTestSq a (p - q) (xiSpectralPoint z))) / 4 = _
  rw [hplus, hminus]
  rw [liEvenCrossPolarAtMass]
  rw [liEvenCrossArchimedeanAbelValue_eq_polarized (by linarith : 0 < a),
    liEvenCrossPrimeAbelValue_eq_polarized ha]
  push_cast
  ring

def liEvenCrossDivisorAbelTerm (a : ℝ) (n : ℕ) (q : XiZeroCopy) : ℂ :=
  (xiHardEdgeDivisorPacketTerm a
      (liEvenCrossLeftPolynomial n + liEvenCrossRightPolynomial n) q -
    xiHardEdgeDivisorPacketTerm a
      (liEvenCrossLeftPolynomial n - liEvenCrossRightPolynomial n) q) / 4

theorem routeUHardEdgeRationalTestSq_reciprocal_eq_divisorPacket
    (a : ℝ) (P : Polynomial ℝ) (q : XiZeroCopy) :
    routeUHardEdgeRationalTestSq a (xiHardEdgeReciprocalPolynomial a P)
        (xiSpectralPoint q) =
      xiHardEdgeDivisorPacketTerm a P q := by
  rw [routeUHardEdgeRationalTestSq_xiSpectralPoint,
    xiHardEdgeDivisorPacketTerm_eq_traceTerm]

theorem liEvenCrossDivisorAbelValue_eq_tsum_term (a : ℝ) (n : ℕ) :
    liEvenCrossDivisorAbelValue a n =
      ∑' q : XiZeroCopy, liEvenCrossDivisorAbelTerm a n q := by
  let P := liEvenCrossLeftPolynomial n
  let Q := liEvenCrossRightPolynomial n
  have hp := summable_xiHardEdgeDivisorPacketTerm a (P + Q)
  have hm := summable_xiHardEdgeDivisorPacketTerm a (P - Q)
  rw [liEvenCrossDivisorAbelValue]
  have hadd : liEvenCrossLeftReciprocalPolynomialAtMass a n +
      liEvenCrossRightReciprocalPolynomialAtMass a n =
      xiHardEdgeReciprocalPolynomial a (P + Q) := by
    simpa only [liEvenCrossLeftReciprocalPolynomialAtMass,
      liEvenCrossRightReciprocalPolynomialAtMass, P, Q] using
        (xiHardEdgeReciprocalPolynomial_add a
          (liEvenCrossLeftPolynomial n) (liEvenCrossRightPolynomial n)).symm
  have hsub : liEvenCrossLeftReciprocalPolynomialAtMass a n -
      liEvenCrossRightReciprocalPolynomialAtMass a n =
      xiHardEdgeReciprocalPolynomial a (P - Q) := by
    simpa only [liEvenCrossLeftReciprocalPolynomialAtMass,
      liEvenCrossRightReciprocalPolynomialAtMass, P, Q] using
        (xiHardEdgeReciprocalPolynomial_sub a
          (liEvenCrossLeftPolynomial n) (liEvenCrossRightPolynomial n)).symm
  rw [hadd, hsub]
  have hplus : (∑' q : XiZeroCopy,
      routeUHardEdgeRationalTestSq a (xiHardEdgeReciprocalPolynomial a (P + Q))
        (xiSpectralPoint q)) =
      ∑' q : XiZeroCopy, xiHardEdgeDivisorPacketTerm a (P + Q) q := by
    apply tsum_congr
    intro q
    exact routeUHardEdgeRationalTestSq_reciprocal_eq_divisorPacket a (P + Q) q
  have hminus : (∑' q : XiZeroCopy,
      routeUHardEdgeRationalTestSq a (xiHardEdgeReciprocalPolynomial a (P - Q))
        (xiSpectralPoint q)) =
      ∑' q : XiZeroCopy, xiHardEdgeDivisorPacketTerm a (P - Q) q := by
    apply tsum_congr
    intro q
    exact routeUHardEdgeRationalTestSq_reciprocal_eq_divisorPacket a (P - Q) q
  rw [hplus, hminus, ← hp.tsum_sub hm]
  calc
    (∑' q : XiZeroCopy,
        (xiHardEdgeDivisorPacketTerm a (P + Q) q -
          xiHardEdgeDivisorPacketTerm a (P - Q) q)) / 4 =
      (1 / 4 : ℂ) * ∑' q : XiZeroCopy,
        (xiHardEdgeDivisorPacketTerm a (P + Q) q -
          xiHardEdgeDivisorPacketTerm a (P - Q) q) := by ring
    _ = ∑' q : XiZeroCopy, (1 / 4 : ℂ) *
        (xiHardEdgeDivisorPacketTerm a (P + Q) q -
          xiHardEdgeDivisorPacketTerm a (P - Q) q) := by
      rw [tsum_mul_left]
    _ = _ := by
      apply tsum_congr
      intro q
      simp only [liEvenCrossDivisorAbelTerm, P, Q]
      ring

theorem tendsto_xiHardEdgeDivisorPacketTerm_mass
    (P : Polynomial ℝ) (q : XiZeroCopy) :
    Tendsto (fun a : ℝ => xiHardEdgeDivisorPacketTerm a P q)
      (𝓝 (1 / 2 : ℝ))
      (𝓝 (xiHardEdgeDivisorPacketTerm (1 / 2) P q)) := by
  have ha : Tendsto (fun a : ℝ => a) (𝓝 (1 / 2 : ℝ)) (𝓝 (1 / 2 : ℝ)) :=
    tendsto_id
  have ha2 : Tendsto (fun a : ℝ => a ^ 2) (𝓝 (1 / 2 : ℝ)) (𝓝 ((1 / 2 : ℝ) ^ 2)) :=
    ha.pow 2
  have hlamBase : Tendsto (fun y : ℝ => xiShiftedReciprocalSquare y q)
      (𝓝 ((1 / 2 : ℝ) ^ 2))
      (𝓝 (xiShiftedReciprocalSquare ((1 / 2 : ℝ) ^ 2) q)) := by
    have h := (hasDerivAt_xiShiftedReciprocalSquare_pow
      (by norm_num : (0 : ℝ) < (1 / 2 : ℝ) ^ 2) q 0).continuousAt
    rw [ContinuousAt] at h
    simpa only [Nat.zero_add, pow_one] using h
  have hlam : Tendsto (fun a : ℝ => xiShiftedReciprocalSquare (a ^ 2) q)
      (𝓝 (1 / 2 : ℝ))
      (𝓝 (xiShiftedReciprocalSquare ((1 / 2 : ℝ) ^ 2) q)) :=
    hlamBase.comp ha2
  have ha2C : Tendsto (fun a : ℝ => ((a ^ 2 : ℝ) : ℂ))
      (𝓝 (1 / 2 : ℝ)) (𝓝 ((((1 / 2 : ℝ) ^ 2 : ℝ) : ℂ))) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp ha2
  have hcoord : Tendsto (fun a : ℝ =>
      (((2 * a ^ 2 : ℝ) : ℂ) * xiShiftedReciprocalSquare (a ^ 2) q - 1))
      (𝓝 (1 / 2 : ℝ))
      (𝓝 ((((2 * (1 / 2 : ℝ) ^ 2 : ℝ) : ℂ) *
        xiShiftedReciprocalSquare ((1 / 2 : ℝ) ^ 2) q - 1))) := by
    exact ((ha2.const_mul 2).ofReal.mul hlam).sub tendsto_const_nhds
  have hpoly : Tendsto (fun a : ℝ => evalRealPolynomial P
      (((2 * a ^ 2 : ℝ) : ℂ) * xiShiftedReciprocalSquare (a ^ 2) q - 1))
      (𝓝 (1 / 2 : ℝ))
      (𝓝 (evalRealPolynomial P
        (((2 * (1 / 2 : ℝ) ^ 2 : ℝ) : ℂ) *
          xiShiftedReciprocalSquare ((1 / 2 : ℝ) ^ 2) q - 1))) := by
    exact (Polynomial.continuous _).continuousAt.tendsto.comp hcoord
  simpa only [xiHardEdgeDivisorPacketTerm,
    xiHardEdgeCayleyCoordinate_xiSpectralPoint] using
      (ha2C.mul hlam).mul (hpoly.pow 2)

theorem norm_xiHardEdgeDivisorPacketTerm_le_reciprocalMajorant
    {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (P : Polynomial ℝ) (q : XiZeroCopy) :
    ‖xiHardEdgeDivisorPacketTerm a P q‖ ≤
      evalRealPolynomialNormBound P 2 ^ 2 * ‖xiZeroCopyReciprocalSquare q‖ := by
  have haSq : a ^ 2 ≤ 1 := by nlinarith
  have hlam := norm_xiShiftedReciprocalSquare_le (sq_nonneg a) q
  have hlamSmall : ‖xiShiftedReciprocalSquare (a ^ 2) q‖ ≤ 2 / 41 :=
    hlam.trans (le_of_lt (norm_xiZeroCopyReciprocalSquare_lt_two_over_fortyOne q))
  have hcoord : ‖(((2 * a ^ 2 : ℝ) : ℂ) *
      xiShiftedReciprocalSquare (a ^ 2) q - 1)‖ ≤ 2 := by
    calc
      ‖(((2 * a ^ 2 : ℝ) : ℂ) * xiShiftedReciprocalSquare (a ^ 2) q - 1)‖ ≤
          ‖(((2 * a ^ 2 : ℝ) : ℂ) * xiShiftedReciprocalSquare (a ^ 2) q)‖ + ‖(1 : ℂ)‖ :=
        norm_sub_le _ _
      _ = (2 * a ^ 2) * ‖xiShiftedReciprocalSquare (a ^ 2) q‖ + 1 := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (by positivity), norm_one]
      _ ≤ 2 := by nlinarith
  have hpoly := norm_evalRealPolynomial_le P hcoord
  rw [xiHardEdgeDivisorPacketTerm,
    xiHardEdgeCayleyCoordinate_xiSpectralPoint, norm_mul, norm_mul, norm_pow,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg a)]
  calc
    a ^ 2 * ‖xiShiftedReciprocalSquare (a ^ 2) q‖ *
        ‖evalRealPolynomial P
          (((2 * a ^ 2 : ℝ) : ℂ) * xiShiftedReciprocalSquare (a ^ 2) q - 1)‖ ^ 2 ≤
      1 * ‖xiZeroCopyReciprocalSquare q‖ * evalRealPolynomialNormBound P 2 ^ 2 := by
        gcongr
    _ = _ := by ring

def liEvenCrossDivisorAbelMajorant (n : ℕ) (q : XiZeroCopy) : ℝ :=
  ((evalRealPolynomialNormBound
      (liEvenCrossLeftPolynomial n + liEvenCrossRightPolynomial n) 2 ^ 2 +
    evalRealPolynomialNormBound
      (liEvenCrossLeftPolynomial n - liEvenCrossRightPolynomial n) 2 ^ 2) / 4) *
    ‖xiZeroCopyReciprocalSquare q‖

theorem summable_liEvenCrossDivisorAbelMajorant (n : ℕ) :
    Summable (liEvenCrossDivisorAbelMajorant n) := by
  exact summable_norm_xiZeroCopyReciprocalSquare.mul_left _

theorem norm_liEvenCrossDivisorAbelTerm_le_majorant
    {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (n : ℕ) (q : XiZeroCopy) :
    ‖liEvenCrossDivisorAbelTerm a n q‖ ≤
      liEvenCrossDivisorAbelMajorant n q := by
  let P := liEvenCrossLeftPolynomial n + liEvenCrossRightPolynomial n
  let Q := liEvenCrossLeftPolynomial n - liEvenCrossRightPolynomial n
  have hP := norm_xiHardEdgeDivisorPacketTerm_le_reciprocalMajorant ha0 ha1 P q
  have hQ := norm_xiHardEdgeDivisorPacketTerm_le_reciprocalMajorant ha0 ha1 Q q
  rw [liEvenCrossDivisorAbelTerm, norm_div]
  norm_num
  calc
    ‖xiHardEdgeDivisorPacketTerm a P q - xiHardEdgeDivisorPacketTerm a Q q‖ / 4 ≤
        (‖xiHardEdgeDivisorPacketTerm a P q‖ +
          ‖xiHardEdgeDivisorPacketTerm a Q q‖) / 4 := by
      gcongr
      exact norm_sub_le _ _
    _ ≤ ((evalRealPolynomialNormBound P 2 ^ 2 * ‖xiZeroCopyReciprocalSquare q‖) +
        (evalRealPolynomialNormBound Q 2 ^ 2 * ‖xiZeroCopyReciprocalSquare q‖)) / 4 := by
      gcongr
    _ = liEvenCrossDivisorAbelMajorant n q := by
      simp only [liEvenCrossDivisorAbelMajorant, P, Q]
      ring

theorem tendsto_liEvenCrossDivisorAbelValue_half (n : ℕ) :
    Tendsto (fun a : ℝ => liEvenCrossDivisorAbelValue a n)
      (𝓝 (1 / 2 : ℝ))
      (𝓝 (liEvenCrossDivisorAbelValue (1 / 2) n)) := by
  have hpoint : ∀ q : XiZeroCopy,
      Tendsto (fun a : ℝ => liEvenCrossDivisorAbelTerm a n q)
        (𝓝 (1 / 2 : ℝ))
        (𝓝 (liEvenCrossDivisorAbelTerm (1 / 2) n q)) := by
    intro q
    exact ((tendsto_xiHardEdgeDivisorPacketTerm_mass
      (liEvenCrossLeftPolynomial n + liEvenCrossRightPolynomial n) q).sub
      (tendsto_xiHardEdgeDivisorPacketTerm_mass
        (liEvenCrossLeftPolynomial n - liEvenCrossRightPolynomial n) q)).div_const 4
  have hbound : ∀ᶠ a : ℝ in 𝓝 (1 / 2 : ℝ), ∀ q : XiZeroCopy,
      ‖liEvenCrossDivisorAbelTerm a n q‖ ≤ liEvenCrossDivisorAbelMajorant n q := by
    filter_upwards [Icc_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)] with a ha q
    exact norm_liEvenCrossDivisorAbelTerm_le_majorant ha.1 ha.2 n q
  have hlim := tendsto_tsum_of_dominated_convergence
    (summable_liEvenCrossDivisorAbelMajorant n) hpoint hbound
  simpa only [← liEvenCrossDivisorAbelValue_eq_tsum_term] using hlim

def liEvenCrossCompletedArithmeticAbelValue (a : ℝ) (n : ℕ) : ℂ :=
  2 * (liEvenCrossPolarAtMass a n : ℂ) +
    (1 / (Real.pi : ℂ)) * (liEvenCrossArchimedeanAbelValue a n : ℂ) -
      (1 / (Real.pi : ℂ)) * liEvenCrossPrimeAbelValue a n

theorem liEvenCrossCompletedArithmeticAbelValue_eq_divisor
    {a : ℝ} (ha : 1 / 2 < a) (n : ℕ) :
    liEvenCrossCompletedArithmeticAbelValue a n =
      liEvenCrossDivisorAbelValue a n := by
  exact (liEvenCrossDivisorAbelValue_eq_completedArithmetic ha n).symm

theorem tendsto_liEvenCrossCompletedArithmeticAbelValue_half (n : ℕ) :
    Tendsto (fun a : ℝ => liEvenCrossCompletedArithmeticAbelValue a n)
      (𝓝[>] (1 / 2 : ℝ))
      (𝓝 (liEvenCrossDivisorAbelValue (1 / 2) n)) := by
  have hdiv : Tendsto (fun a : ℝ => liEvenCrossDivisorAbelValue a n)
      (𝓝[>] (1 / 2 : ℝ))
      (𝓝 (liEvenCrossDivisorAbelValue (1 / 2) n)) :=
    (tendsto_liEvenCrossDivisorAbelValue_half n).mono_left nhdsWithin_le_nhds
  apply hdiv.congr'
  filter_upwards [self_mem_nhdsWithin] with a ha
  exact (liEvenCrossCompletedArithmeticAbelValue_eq_divisor ha n).symm

theorem re_liEvenCrossDivisorAbelValue_eq_massSq_mul_bilinear
    (a : ℝ) (n : ℕ) :
    (liEvenCrossDivisorAbelValue a n).re =
      a ^ 2 * xiShiftedReciprocalHankelBilinear (a ^ 2)
        (routeUHardEdgeCommonLeftCoefficients a
          (liEvenCrossLeftPolynomial n) (liEvenCrossRightPolynomial n))
        (routeUHardEdgeCommonRightCoefficients a
          (liEvenCrossLeftPolynomial n) (liEvenCrossRightPolynomial n)) := by
  let P := liEvenCrossLeftPolynomial n
  let Q := liEvenCrossRightPolynomial n
  let c := routeUHardEdgeCommonLeftCoefficients a P Q
  let e := routeUHardEdgeCommonRightCoefficients a P Q
  rw [liEvenCrossDivisorAbelValue,
    tsum_routeUHardEdgeRationalTestSq_eq,
    tsum_routeUHardEdgeRationalTestSq_eq]
  have hadd : liEvenCrossLeftReciprocalPolynomialAtMass a n +
      liEvenCrossRightReciprocalPolynomialAtMass a n =
      xiHardEdgeReciprocalPolynomial a (P + Q) := by
    simpa only [liEvenCrossLeftReciprocalPolynomialAtMass,
      liEvenCrossRightReciprocalPolynomialAtMass, P, Q] using
        (xiHardEdgeReciprocalPolynomial_add a
          (liEvenCrossLeftPolynomial n) (liEvenCrossRightPolynomial n)).symm
  have hsub : liEvenCrossLeftReciprocalPolynomialAtMass a n -
      liEvenCrossRightReciprocalPolynomialAtMass a n =
      xiHardEdgeReciprocalPolynomial a (P - Q) := by
    simpa only [liEvenCrossLeftReciprocalPolynomialAtMass,
      liEvenCrossRightReciprocalPolynomialAtMass, P, Q] using
        (xiHardEdgeReciprocalPolynomial_sub a
          (liEvenCrossLeftPolynomial n) (liEvenCrossRightPolynomial n)).symm
  rw [hadd, hsub]
  have hfull := routeUHardEdgeCommonFullQuadratic_eq_trace_re a P Q
  have hanti := routeUHardEdgeCommonAntipodalQuadratic_eq_trace_re a P Q
  simp only [Complex.sub_re, Complex.div_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [← hfull, ← hanti]
  rw [show routeUHardEdgeCommonFullCoefficients a P Q = c + e by rfl,
    show routeUHardEdgeCommonAntipodalCoefficients a P Q = c - e by rfl,
    xiShiftedReciprocalHankelQuadratic_add,
    xiShiftedReciprocalHankelQuadratic_sub]
  dsimp only [c, e]
  norm_num [Complex.normSq_apply]
  ring

theorem re_liEvenCrossDivisorAbelValue_half_eq_liSource_div_eight (n : ℕ) :
    (liEvenCrossDivisorAbelValue (1 / 2) n).re =
      (liPrimeArchEvenSquareSource n).re / 8 := by
  rw [re_liEvenCrossDivisorAbelValue_eq_massSq_mul_bilinear]
  rw [re_liPrimeArchEvenSquareSource_eq_two_mul_crossBilinear]
  ring

def LiEvenCompletedAbelClockNonnegative : Prop :=
  ∀ n : ℕ, 0 ≤ (liEvenCrossDivisorAbelValue (1 / 2) n).re

theorem riemannHypothesis_iff_liEvenCompletedAbelClockNonnegative :
    RiemannHypothesis ↔ LiEvenCompletedAbelClockNonnegative := by
  rw [riemannHypothesis_iff_forall_re_liPrimeArchEvenSquareSource_nonneg]
  constructor
  · intro h n
    rw [re_liEvenCrossDivisorAbelValue_half_eq_liSource_div_eight]
    exact div_nonneg (h n) (by norm_num)
  · intro h n
    have hn := h n
    rw [re_liEvenCrossDivisorAbelValue_half_eq_liSource_div_eight] at hn
    linarith

end

end RHTower
