import GaloisForLFunctions.RHTower.LiEvenSquarePrimeGammaCrossBalanceCriterion
import GaloisForLFunctions.RHTower.CayleyLaguerreFourier
import GaloisForLFunctions.HTGeometry.OddEulerCombTemperedAdmissionWall

/-!
# LI critical Abel--Cayley boundary no-go

The first common-reversal channel in the even-Li prime--Gamma criterion has critical hard-edge
density

`g(x) = (1/2) x^(2 : ℕ) / (x^(2 : ℕ) + 1/4)^(2 : ℕ)`.

Its exact no-`2π` Fourier transform is

`(π/2) exp(-|ξ|/2) (1-|ξ|/2)`.

At prime frequency `ξ = log n`, this turns the explicit-formula half-density into the harmonic
von Mangoldt boundary. The resulting absolute prime leg is not summable. Thus any proof of the
LI common-reversal capital must keep prime, polar, and Gamma terms inside one completed Abel finite
part; separate Tonelli treatment of the critical prime leg is impossible.

Corpus provenance and RH passport: `LiEvenSquarePrimeGammaCrossBalanceCriterion` identifies these
common-reversal capitals with every positive even Li source and proves their nonnegativity equivalent
to RH. `XiShiftedHardEdgePrimeGammaSourceDisintegration` exposes the degree-free Cauchy density.
`CayleyLaguerreFourier` supplies the transform, and
`OddEulerCombTemperedAdmissionWall` supplies divergence of `∑ Λ(n)/n`.
-/

open Complex MeasureTheory Polynomial Real Set Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- First critical common-reversal density in physical Cauchy coordinates. -/
def liCriticalFirstCrossCauchyDensity (x : ℝ) : ℝ :=
  (1 / 2 : ℝ) * x ^ (2 : ℕ) / (x ^ (2 : ℕ) + 1 / 4) ^ (2 : ℕ)

/-- Polarized hard-edge Cauchy density for two polynomial channels. -/
def routeUHardEdgeCrossCauchyDensity
    (a : ℝ) (P Q : Polynomial ℝ) (x : ℝ) : ℝ :=
  a ^ (2 : ℕ) / (a ^ (2 : ℕ) + x ^ (2 : ℕ)) *
    P.eval ((a ^ (2 : ℕ) - x ^ (2 : ℕ)) / (a ^ (2 : ℕ) + x ^ (2 : ℕ))) *
    Q.eval ((a ^ (2 : ℕ) - x ^ (2 : ℕ)) / (a ^ (2 : ℕ) + x ^ (2 : ℕ)))

/-- Polarization on the diagonal recovers the existing square density. -/
theorem routeUHardEdgeCrossCauchyDensity_self
    (a : ℝ) (P : Polynomial ℝ) (x : ℝ) :
    routeUHardEdgeCrossCauchyDensity a P P x =
      routeUHardEdgeCauchyDensity a P x := by
  rw [routeUHardEdgeCrossCauchyDensity, routeUHardEdgeCauchyDensity, pow_two]
  ring

/-- The explicit density is exactly LI's zeroth common-reversal channel. -/
theorem liCriticalFirstCrossCauchyDensity_eq_hardEdgeCross (x : ℝ) :
    liCriticalFirstCrossCauchyDensity x =
      routeUHardEdgeCrossCauchyDensity (1 / 2)
        (liEvenCrossLeftPolynomial 0) (liEvenCrossRightPolynomial 0) x := by
  simp only [routeUHardEdgeCrossCauchyDensity, liCriticalFirstCrossCauchyDensity,
    liEvenCrossLeftPolynomial, liEvenCrossRightPolynomial,
    Polynomial.eval_one, Polynomial.eval_mul,
    Polynomial.eval_sub, Polynomial.eval_X]
  norm_num
  have h : x ^ (2 : ℕ) + (1 / 4 : ℝ) ≠ 0 := by positivity
  field_simp [h]
  ring

/-- Critical Cayley coordinate exposed by the hard-edge cancellation. -/
def liCriticalCayleyCoordinate (x : ℝ) : ℝ :=
  ((1 / 2 : ℝ) ^ (2 : ℕ) - x ^ (2 : ℕ)) / ((1 / 2 : ℝ) ^ (2 : ℕ) + x ^ (2 : ℕ))

/-- Every LI common-reversal mode after critical hard-edge filtering. -/
def liCriticalEvenCrossCauchyDensity (n : ℕ) (x : ℝ) : ℝ :=
  routeUHardEdgeCrossCauchyDensity (1 / 2)
    (liEvenCrossLeftPolynomial n) (liEvenCrossRightPolynomial n) x

/-- Positive survivor: every critical LI cross density is a Cayley square defect. -/
theorem liCriticalEvenCrossCauchyDensity_eq_squareDefect (n : ℕ) (x : ℝ) :
    liCriticalEvenCrossCauchyDensity n x =
      (1 - liCriticalCayleyCoordinate x ^ (2 : ℕ)) / 2 *
        ((liEvenCrossLeftPolynomial n).eval
          (liCriticalCayleyCoordinate x)) ^ (2 : ℕ) := by
  have hden : (1 / 2 : ℝ) ^ (2 : ℕ) + x ^ (2 : ℕ) ≠ 0 := by positivity
  simp only [liCriticalEvenCrossCauchyDensity,
    routeUHardEdgeCrossCauchyDensity, liEvenCrossRightPolynomial,
    Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_one,
    Polynomial.eval_X, liCriticalCayleyCoordinate]
  field_simp [hden]
  ring

/-- The critical Cayley coordinate remains in the closed unit interval. -/
theorem liCriticalCayleyCoordinate_square_le_one (x : ℝ) :
    liCriticalCayleyCoordinate x ^ (2 : ℕ) ≤ 1 := by
  have hden : (1 / 2 : ℝ) ^ (2 : ℕ) + x ^ (2 : ℕ) ≠ 0 := by positivity
  rw [liCriticalCayleyCoordinate]
  rw [show (((1 / 2 : ℝ) ^ (2 : ℕ) - x ^ (2 : ℕ)) /
      ((1 / 2 : ℝ) ^ (2 : ℕ) + x ^ (2 : ℕ))) ^ (2 : ℕ) =
      1 - 4 * (1 / 2 : ℝ) ^ (2 : ℕ) * x ^ (2 : ℕ) /
        ((1 / 2 : ℝ) ^ (2 : ℕ) + x ^ (2 : ℕ)) ^ (2 : ℕ) by
    field_simp [hden]
    ring]
  have hq : 0 ≤ 4 * (1 / 2 : ℝ) ^ (2 : ℕ) * x ^ (2 : ℕ) /
      ((1 / 2 : ℝ) ^ (2 : ℕ) + x ^ (2 : ℕ)) ^ (2 : ℕ) := by positivity
  linarith

/-- Closed, hypothesis-free nonnegativity of every critical LI cross density. -/
theorem liCriticalEvenCrossCauchyDensity_nonneg (n : ℕ) (x : ℝ) :
    0 ≤ liCriticalEvenCrossCauchyDensity n x := by
  rw [liCriticalEvenCrossCauchyDensity_eq_squareDefect]
  exact mul_nonneg (div_nonneg
    (sub_nonneg.mpr (liCriticalCayleyCoordinate_square_le_one x)) (by norm_num))
    (sq_nonneg _)

/-- Unit-scale form as Cauchy kernel minus squared Cauchy kernel. -/
def liUnitFirstCrossCauchyDensity (x : ℝ) : ℂ :=
  2 * (routeUCauchyKernel x - routeUCayleyCosineSquareKernel 1 x)

/-- Rational closed form of the unit-scale density. -/
theorem liUnitFirstCrossCauchyDensity_eq (x : ℝ) :
    liUnitFirstCrossCauchyDensity x =
      ((2 * x ^ (2 : ℕ) / (1 + x ^ (2 : ℕ)) ^ (2 : ℕ) : ℝ) : ℂ) := by
  rw [liUnitFirstCrossCauchyDensity, routeUCauchyKernel,
    routeUCayleyCosineSquareKernel_eq]
  norm_num only [Nat.cast_one, one_mul]
  rw [Real.cos_sq_arctan]
  push_cast
  have h : (1 : ℂ) + (x : ℂ) ^ (2 : ℕ) ≠ 0 := by
    norm_cast
    nlinarith [sq_nonneg x]
  field_simp [h]
  ring

/-- Critical density is the unit density pulled back by dilation two. -/
theorem liCriticalFirstCrossCauchyDensity_eq_scaled (x : ℝ) :
    (liCriticalFirstCrossCauchyDensity x : ℂ) =
      liUnitFirstCrossCauchyDensity (2 * x) := by
  rw [liUnitFirstCrossCauchyDensity_eq, liCriticalFirstCrossCauchyDensity]
  have h₁ : x ^ (2 : ℕ) + (1 / 4 : ℝ) ≠ 0 := by positivity
  have h₂ : 1 + (2 * x) ^ (2 : ℕ) ≠ 0 := by positivity
  norm_cast
  field_simp [h₁, h₂]
  ring

private theorem integrable_routeUFourierIntegrand'
    {f : ℝ → ℂ} (hf : Integrable f) (ξ : ℝ) :
    Integrable (fun x : ℝ => f x * Complex.exp (-I * ((ξ * x : ℝ) : ℂ))) := by
  apply hf.mul_bdd (by fun_prop)
  filter_upwards with x
  rw [show -I * ((ξ * x : ℝ) : ℂ) = (((-(ξ * x) : ℝ) : ℂ) * I) by
    push_cast
    ring]
  exact le_of_eq (Complex.norm_exp_ofReal_mul_I _)

private theorem integrable_routeUCayleyCosineSquareKernel_one :
    Integrable (routeUCayleyCosineSquareKernel 1) := by
  rw [show routeUCayleyCosineSquareKernel 1 = fun x : ℝ =>
      (1 / 4 : ℂ) * (((2 : ℂ) * routeUCauchyKernel x +
        routeUCayleyModeKernel 1 x) + routeUCayleyInverseModeKernel 1 x) by
    funext x
    rw [routeUCayleyCosineSquareKernel]
    ring]
  exact (((integrable_routeUCauchyKernel.const_mul (2 : ℂ)).add
    (integrable_routeUCayleyModeKernel (by norm_num))).add
      (integrable_routeUCayleyInverseModeKernel (by norm_num))).const_mul (1 / 4 : ℂ)

/-- Exact no-`2π` Fourier transform at unit scale. -/
theorem routeUFourierIntegral_liUnitFirstCrossCauchyDensity (ξ : ℝ) :
    routeUFourierIntegral liUnitFirstCrossCauchyDensity ξ =
      ((Real.pi * Real.exp (-|ξ|) * (1 - |ξ|) : ℝ) : ℂ) := by
  have hC := integrable_routeUFourierIntegrand'
    integrable_routeUCauchyKernel ξ
  have hS := integrable_routeUFourierIntegrand'
    integrable_routeUCayleyCosineSquareKernel_one ξ
  rw [routeUFourierIntegral]
  simp only [liUnitFirstCrossCauchyDensity]
  rw [show (∫ x : ℝ, 2 * (routeUCauchyKernel x -
      routeUCayleyCosineSquareKernel 1 x) *
      Complex.exp (-I * ((ξ * x : ℝ) : ℂ))) =
      2 * ((∫ x : ℝ, routeUCauchyKernel x *
        Complex.exp (-I * ((ξ * x : ℝ) : ℂ))) -
      (∫ x : ℝ, routeUCayleyCosineSquareKernel 1 x *
        Complex.exp (-I * ((ξ * x : ℝ) : ℂ)))) by
    rw [← integral_sub hC hS, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    ring]
  rw [← routeUFourierIntegral, routeUFourierIntegral_cauchyKernel]
  rw [show (∫ x : ℝ, routeUCayleyCosineSquareKernel 1 x *
      Complex.exp (-I * ((ξ * x : ℝ) : ℂ))) =
      routeUFourierIntegral (fun x : ℝ =>
        ((Real.cos (Real.arctan x) ^ (2 : ℕ) / (1 + x ^ (2 : ℕ)) : ℝ) : ℂ)) ξ by
    rw [routeUFourierIntegral]
    apply integral_congr_ae
    filter_upwards with x
    rw [routeUCayleyCosineSquareKernel_eq]
    norm_num]
  have hsq := routeUFourierIntegral_cosineSquareKernel (m := 1) (by norm_num) ξ
  simp only [Nat.cast_one, one_mul] at hsq
  rw [hsq]
  simp [routeUAssociatedLaguerreMinusOne]
  ring

/-- Exact no-`2π` Fourier transform at LI's critical half-mass. -/
theorem routeUFourierIntegral_liCriticalFirstCrossCauchyDensity (ξ : ℝ) :
    routeUFourierIntegral (fun x : ℝ =>
      (liCriticalFirstCrossCauchyDensity x : ℂ)) ξ =
      ((Real.pi / 2 * Real.exp (-|ξ| / 2) * (1 - |ξ| / 2) : ℝ) : ℂ) := by
  let G : ℝ → ℂ := fun y =>
    liUnitFirstCrossCauchyDensity y *
      Complex.exp (-I * ((((ξ / 2) * y : ℝ) : ℂ)))
  have hscale := MeasureTheory.Measure.integral_comp_mul_left G 2
  norm_num at hscale
  rw [routeUFourierIntegral]
  rw [show (fun x : ℝ => (liCriticalFirstCrossCauchyDensity x : ℂ) *
      Complex.exp (-I * ((ξ * x : ℝ) : ℂ))) = fun x : ℝ => G (2 * x) by
    funext x
    rw [liCriticalFirstCrossCauchyDensity_eq_scaled]
    dsimp only [G]
    congr 2
    push_cast
    ring]
  rw [hscale]
  dsimp only [G]
  change (1 / 2 : ℂ) * routeUFourierIntegral liUnitFirstCrossCauchyDensity (ξ / 2) = _
  rw [routeUFourierIntegral_liUnitFirstCrossCauchyDensity]
  have habs : |ξ / 2| = |ξ| / 2 := by rw [abs_div]; norm_num
  rw [habs]
  norm_num [Complex.real_smul]
  ring

/-- Literal absolute prime-leg weight after evaluating the transform at `log n`. -/
def liCriticalFirstCrossPrimeLegAbsoluteWeight (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n / Real.sqrt n *
    ‖routeUFourierIntegral (fun x : ℝ =>
      (liCriticalFirstCrossCauchyDensity x : ℂ)) (Real.log n)‖

/-- Harmonic von Mangoldt boundary remaining after the two half-densities combine. -/
def liCriticalFirstCrossPrimeAbsoluteWeight (n : ℕ) : ℝ :=
  finiteVonMangoldtRealWeight n * |1 - Real.log n / 2|

private theorem exp_neg_abs_log_nat_div_two_div_sqrt
    {n : ℕ} (hn : 0 < n) :
    Real.exp (-|Real.log (n : ℝ)| / 2) / Real.sqrt n = 1 / n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hone : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hone
  have hsqrt : Real.sqrt (n : ℝ) = Real.exp (Real.log n / 2) := by
    have hsq : Real.exp (Real.log (n : ℝ) / 2) ^ (2 : ℕ) = n := by
      rw [← Real.exp_nat_mul,
        show ((2 : ℕ) : ℝ) * (Real.log (n : ℝ) / 2) = Real.log n by
          push_cast
          ring]
      exact Real.exp_log hnR
    calc
      Real.sqrt (n : ℝ) = Real.sqrt (Real.exp (Real.log n / 2) ^ (2 : ℕ)) := by rw [hsq]
      _ = Real.exp (Real.log n / 2) := Real.sqrt_sq (Real.exp_pos _).le
  rw [abs_of_nonneg hlog, hsqrt, ← Real.exp_sub]
  rw [show -Real.log (n : ℝ) / 2 - Real.log n / 2 = -Real.log n by ring]
  rw [Real.exp_neg, Real.exp_log hnR]
  simp [one_div]

/-- Exact identification of the literal prime leg with the harmonic boundary weight. -/
theorem liCriticalFirstCrossPrimeLegAbsoluteWeight_eq (n : ℕ) :
    liCriticalFirstCrossPrimeLegAbsoluteWeight n =
      Real.pi / 2 * liCriticalFirstCrossPrimeAbsoluteWeight n := by
  rcases n with _ | n
  · simp [liCriticalFirstCrossPrimeLegAbsoluteWeight,
      liCriticalFirstCrossPrimeAbsoluteWeight, finiteVonMangoldtRealWeight]
  · have hn : 0 < n + 1 := by omega
    have hlog : 0 ≤ Real.log ((n + 1 : ℕ) : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hn)
    rw [liCriticalFirstCrossPrimeLegAbsoluteWeight,
      routeUFourierIntegral_liCriticalFirstCrossCauchyDensity,
      Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_pos (div_pos Real.pi_pos (by norm_num : (0 : ℝ) < 2)),
      abs_of_pos (Real.exp_pos _), abs_of_nonneg hlog]
    rw [liCriticalFirstCrossPrimeAbsoluteWeight, finiteVonMangoldtRealWeight]
    have hratio := exp_neg_abs_log_nat_div_two_div_sqrt hn
    rw [abs_of_nonneg hlog] at hratio
    push_cast at hratio ⊢
    calc
      ArithmeticFunction.vonMangoldt (n + 1) / Real.sqrt (n + 1) *
          (Real.pi / 2 * Real.exp (-Real.log (n + 1) / 2) *
            |1 - Real.log (n + 1) / 2|) =
          Real.pi / 2 *
            (ArithmeticFunction.vonMangoldt (n + 1) *
              (Real.exp (-Real.log (n + 1) / 2) / Real.sqrt (n + 1))) *
            |1 - Real.log (n + 1) / 2| := by ring
      _ = Real.pi / 2 *
            (ArithmeticFunction.vonMangoldt (n + 1) / (n + 1)) *
            |1 - Real.log (n + 1) / 2| := by rw [hratio]; ring
      _ = Real.pi / 2 *
            (ArithmeticFunction.vonMangoldt (n + 1) / (n + 1) *
              |1 - Real.log (n + 1) / 2|) := by ring

/-- Every normalized absolute boundary weight is nonnegative. -/
theorem liCriticalFirstCrossPrimeAbsoluteWeight_nonneg (n : ℕ) :
    0 ≤ liCriticalFirstCrossPrimeAbsoluteWeight n :=
  mul_nonneg (finiteVonMangoldtRealWeight_nonneg n) (abs_nonneg _)

/-- The normalized critical von Mangoldt boundary is not summable. -/
theorem not_summable_liCriticalFirstCrossPrimeAbsoluteWeight :
    ¬ Summable liCriticalFirstCrossPrimeAbsoluteWeight := by
  intro hsum
  have hlog : ∀ᶠ n : ℕ in atTop, 4 ≤ Real.log n :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop 4)
  obtain ⟨N, hN⟩ := (eventually_atTop.1 hlog)
  have hfactor : ∀ k : ℕ,
      1 ≤ |1 - Real.log ((k + N : ℕ) : ℝ) / 2| := by
    intro k
    have hk : N ≤ k + N := by omega
    have hlogk := hN (k + N) hk
    have hnon : 1 - Real.log ((k + N : ℕ) : ℝ) / 2 ≤ 0 := by
      linarith
    simp only [abs_of_nonpos hnon]
    linarith
  have hshiftWeight : Summable (fun k : ℕ =>
      liCriticalFirstCrossPrimeAbsoluteWeight (k + N)) := by
    exact hsum.comp_injective (fun _ _ h => Nat.add_right_cancel h)
  have hshiftBase : Summable (fun k : ℕ => finiteVonMangoldtRealWeight (k + N)) := by
    refine Summable.of_nonneg_of_le
      (fun k => finiteVonMangoldtRealWeight_nonneg (k + N)) ?_ hshiftWeight
    intro k
    rw [liCriticalFirstCrossPrimeAbsoluteWeight]
    nth_rewrite 1 [← mul_one (finiteVonMangoldtRealWeight (k + N))]
    exact mul_le_mul_of_nonneg_left (hfactor k)
      (finiteVonMangoldtRealWeight_nonneg (k + N))
  exact HTGeometry.not_summable_finiteVonMangoldtRealWeight
    ((summable_nat_add_iff N).mp hshiftBase)

/-- The literal first-mode critical prime leg is not absolutely summable. -/
theorem not_summable_liCriticalFirstCrossPrimeLegAbsoluteWeight :
    ¬ Summable liCriticalFirstCrossPrimeLegAbsoluteWeight := by
  intro hsum
  have hscaled : Summable (fun n : ℕ =>
      Real.pi / 2 * liCriticalFirstCrossPrimeAbsoluteWeight n) :=
    hsum.congr (fun n => liCriticalFirstCrossPrimeLegAbsoluteWeight_eq n)
  have hrecover := hscaled.mul_left (2 / Real.pi)
  have : Summable liCriticalFirstCrossPrimeAbsoluteWeight := by
    exact hrecover.congr (fun n => by
      field_simp [Real.pi_ne_zero])
  exact not_summable_liCriticalFirstCrossPrimeAbsoluteWeight this

end

end RHTower
